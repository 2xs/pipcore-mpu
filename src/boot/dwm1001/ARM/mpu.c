/*
 * Copyright (C) 2016 Loci Controls Inc.
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

/**
 * @ingroup     cpu_cortexm_common
 * @{
 *
 * @file        mpu.c
 * @brief       Cortex-M Memory Protection Unit (MPU) Driver
 *
 * @author      Ian Martin <ian@locicontrols.com>
 *
 * @}
 */

//#include "cpu.h"

#include "mpu.h"
#include <string.h> // include memcpy
#include <stdio.h> // include printf

int mpu_disable(void) {
#if __MPU_PRESENT
    MPU->CTRL &= ~MPU_CTRL_ENABLE_Msk;
    return 0;
#else
    return -1;
#endif
}

int mpu_enable(void) {
#if __MPU_PRESENT
    MPU->CTRL |= MPU_CTRL_PRIVDEFENA_Msk | MPU_CTRL_ENABLE_Msk;

#ifdef SCB_SHCSR_MEMFAULTENA_Msk
    /* Enable the memory fault exception if SCB SHCSR (System Handler Control
     * and State Register) has a separate bit for mem faults. That is the case
     * on ARMv7-M. ARMv6-M does not support separate exception enable for mem
     * faults and all fault conditions cause a HardFault. */
    SCB->SHCSR |= SCB_SHCSR_MEMFAULTENA_Msk;
#else
    return -1; // the Memory Management fault handler must be enabled
#endif

    return 0;
#else
    return -1;
#endif
}

int mpu_enabled(void) {
#if __MPU_PRESENT
    return (MPU->CTRL & MPU_CTRL_ENABLE_Msk) != 0;
#else
    return 0;
#endif
}

int mpu_configure_region(uint_fast8_t region, uintptr_t base, uint_fast32_t attr) {
    /* Todo enable MPU support for Cortex-M23/M33 */
#if __MPU_PRESENT && !defined(__ARM_ARCH_8M_MAIN__) && !defined(__ARM_ARCH_8M_BASE__)
    MPU->RNR  = region;
    MPU->RBAR = base & MPU_RBAR_ADDR_Msk;
    MPU->RASR = attr | MPU_RASR_ENABLE_Msk;

    return 0;
#else
    (void)region;
    (void)base;
    (void)attr;
    return -1;
#endif
}

/**
 * @brief configure the MPU based on a lookup table (LUT)
 *
 * @param[in]   LUT     MPU regions to configure
 *
 * @return 0 on success
 * @return <0 on failure
 */
int mpu_configure_from_LUT(uint32_t* LUT)
{
    __DMB();
    // Disable MPU
	mpu_disable();

	// Configure MPU
#if defined(__ARM_ARCH_7M__) || defined(__ARM_ARCH_7EM__)
	// ARM warning: You can normally use the memcpy() function in a C/C++ compiler for this sequence. However, you must verify that the compiler uses word transfers.
	/*for (int i = 0; i < MPU_NUM_REGIONS ; i = i+MPU_ALIAS_REG_NB)
	{
		// Copy a subset of the LUT into the alias registers -> MPU_ALIAS_REG_NB regions configuration
		memcpy((void*)&( MPU->RBAR), LUT+i*2*sizeof(uint32_t), MPU_ALIAS_REG_NB*2*sizeof(uint32_t));

	}*/
    for (int i = 0; i < MPU_NUM_REGIONS ; i++){
        //MPU->RNR  = i; // no need if VALID bit with REGION bits are set in RBAR
        MPU->RBAR = LUT[i*2];
        MPU->RASR = LUT[i*2+1];
    }
#endif
#if defined(__ARM_ARCH_8M_MAIN__) || defined(__ARM_ARCH_8M_BASE__)
    return -1;
#endif
	// Enable MPU with PRIVDEFENA
	mpu_enable();
	__ISB();
	__DSB();
    return 0;
}

/*
void __attribute__ ((section(".after_vectors"),weak))
MemManage_Handler (void)
{
#if defined(DEBUG)
  __DEBUG_BKPT();
#endif
  while (1)
    {
    }
}*/


/*
void __attribute__ ((section(".after_vectors"),weak,naked))
MemoryManagement_Handler (void)
{
    __asm volatile
    (
        " tst lr, #4                                                \n"
        " ite eq                                                    \n"
        " mrseq r0, msp                                             \n"
        " mrsne r0, psp                                             \n"
        " ldr r1, [r0, #24]                                         \n"
        " ldr r2, handler2_address_const                            \n"
        " bx r2                                                     \n"
        " handler2_address_const: .word prvGetRegistersFromStack    \n"
    );
}

void prvGetRegistersFromStack( uint32_t *pulFaultStackAddress )
{
// These are volatile to try and prevent the compiler/linker optimising them
//away as the variables never actually get used.  If the debugger won't show the
//values of the variables, make them global my moving their declaration outside
//of this function.
volatile uint32_t r0;
volatile uint32_t r1;
volatile uint32_t r2;
volatile uint32_t r3;
volatile uint32_t r12;
volatile uint32_t lr; // Link register.
volatile uint32_t pc; // Program counter.
volatile uint32_t psr;// Program status register.

    r0 = pulFaultStackAddress[ 0 ];
    r1 = pulFaultStackAddress[ 1 ];
    r2 = pulFaultStackAddress[ 2 ];
    r3 = pulFaultStackAddress[ 3 ];

    r12 = pulFaultStackAddress[ 4 ];
    lr = pulFaultStackAddress[ 5 ];
    pc = pulFaultStackAddress[ 6 ];
    psr = pulFaultStackAddress[ 7 ];

    // When the following line is hit, the variables contain the register values.
    for( ;; );
}*/


void __attribute__ ((section(".after_vectors"),weak,naked))
MemoryManagement_Handler (void)
{
  asm volatile(
      " tst lr,#4       \n" // Test EXC_RETURN number in LR bit 2
      " ite eq          \n" // if zero (equal) then
      " mrseq r0,msp    \n" // Main Stack was used, put MSP in R0
      " mrsne r0,psp    \n" // else, Process Stack was used, put PSP in R0
      " mov r1,lr       \n" // push lr in r1, contains EXC_RETURN of the preempted code
      " ldr r2,=MemoryManagement_Handler_C \n"
      " bx r2" // exception return to C handler

      : // Outputs
      : // Inputs
      : // Clobbers
  );
}

//void __attribute__ ((section(".after_vectors"),weak,used))
//MemoryManagement_Handler_C (ExceptionStackFrame* frame __attribute__((unused)),
//                     uint32_t lr __attribute__((unused)))
void __attribute__ ((section(".after_vectors"),weak,used))
MemoryManagement_Handler_C (uint32_t* frame __attribute__((unused)),
                     uint32_t lr __attribute__((unused)))
{
/* When the processor takes an exception, the processor pushes information onto the current stack.
The processor performs a vector fetch that reads the exception handler start address from the vector table.
When stacking is complete, the processor starts executing the exception handler.
At the same time, the processor writes an EXC_RETURN value to the LR.
This indicates which stack pointer corresponds to the stack frame and what operation mode the processor was in
before the entry occurred.
*/

    /* Copy status register contents to local stack storage, this must be
     * done before any calls to other functions to avoid corrupting the
     * register contents. */
  uint32_t mmfar = SCB->MMFAR; // MemManage Fault Address
  uint32_t bfar = SCB->BFAR; // Bus Fault Address
  uint32_t cfsr = SCB->CFSR; // Configurable Fault Status Registers



  /*
  0xFFFFFFF1 : Return to Handler mode. Exception return gets state from the main stack. Execution uses MSP after return
  0xFFFFFFF9 : Return to Thread mode. Exception Return get state from the main stack. Execution uses MSP after return.
0xFFFFFFFD : Return to Thread mode. Exception return gets state from the process stack. Execution uses PSP after return.
  */

      static const uint32_t BFARVALID_MASK = (0x80 << SCB_CFSR_BUSFAULTSR_Pos);
    static const uint32_t MMARVALID_MASK = (0x80 << SCB_CFSR_MEMFAULTSR_Pos);


/*
SCB->CFSR:  Configurable Fault Status register
SCB->MMAR:  MemManage Fault Address register

if(DACCVIOL == 1 -> MMARVALID=1 || IACCVIOL = MPU or XN in default mem map) from MFSR
-> offending code at stacked PC =  [SP + 24] (PSP or MSP)  -> get back to this once handled
if( MMARVALID == 1 ) -> address that triggered the DACCVIOL = address we attempted to access is in MMFAR

if( MUNSTKERR == 1) Error occurred during unstacking (ending of exception). -> MPU conﬁguration was changed by exception handler.
DO NOT handle if MMFSR.MSTKERR == 1 or MMFSR.MUNSTKERR == 1 or MMFSR.MLSPERR == 1
because derived exceptions (due to the exception handler itself) -> yes, in late arrival exception
If the processor handles the derived exception using late-arrival preemption,
it enters the handler for the derived exception, which becomes active.
The original exception remains in the pending state

Clear the bits by writing one to them ex wirte 1 to MMARVALID
The Fault Address register can be erased after the MMARVALID or BFARVALID is cleared.
1.Read BFAR/MMAR
Read BFARVALID/MMARVALID. If it is 0, the BFAR/MMAR read should be discarded.2.
Clear BFARVALID/MMARVALID.*/


/* NOTE : n implementations without unique BFAR and MFAR registers, the value of this register is UNKNOWN if BFSR.BFARVALID is set */
/* Initialize these variables even if they're never used uninitialized.
     * Fixes wrong compiler warning by gcc < 6.0. */
    uint32_t pc = 0;
    uint32_t* orig_sp = NULL;

uint32_t* sp = frame;
        uint32_t  r0 = sp[0];
        uint32_t  r1 = sp[1];
        uint32_t  r2 = sp[2];
        uint32_t  r3 = sp[3];
        uint32_t r12 = sp[4];
        uint32_t  lreg = sp[5];  /* Link register. */
                  pc = sp[6];  /* Program counter. */
        uint32_t psr = sp[7];  /* Program status register. */

        /* Reconstruct original stack pointer before fault occurred */
        orig_sp = sp + 8;
#ifdef SCB_CCR_STKALIGN_Msk
        if (psr & SCB_CCR_STKALIGN_Msk) {
            /* Stack was not 8-byte aligned */
            orig_sp += 1;
            printf("Stack was not 8-byte aligned\r\n");
        }
#endif /* SCB_CCR_STKALIGN_Msk */
        puts("\nContext before hardfault:");

        /* TODO: printf in ISR context might be a bad idea */
        printf("   r0 (sp): %x\n"
                "   orig_sp: %x\n"
               "   r1: %x\n"
               "   r2: %x\n"
               "   r3: %x\n",
               r0, orig_sp, r1, r2, r3);
        printf("  r12: %x\n"
               "   lr: %x\n"
               "   pc: %x\n"
               "  psr: %x\n\n",
               r12, lreg, pc, psr);


    puts("FSR/FAR:");
    printf(" CFSR: %x\n", cfsr);
    if (cfsr & BFARVALID_MASK) {
        /* BFAR valid flag set */
        printf(" BFAR: %x\n", bfar);
    }
if (cfsr & MMARVALID_MASK) {
        /* MMFAR valid flag set */
        printf("MMFAR: %x\n", mmfar);
    }

  printf ("\r\n[MemManageFault]\n");
  dumpExceptionStack ((ExceptionStackFrame*)frame, cfsr, mmfar, bfar, lr);

#if defined(DEBUG)
  __DEBUG_BKPT();
#endif
  while (1)
    {
    }

}
