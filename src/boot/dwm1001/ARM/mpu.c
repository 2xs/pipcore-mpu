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


#include "mpu.h"
#include <string.h> // include memcpy
#include <stdio.h> // include printf
#include "pip_debug.h"

/*!
 * \fn int mpu_disable(void)
 * \brief Disable the physical MPU
 * \return 0:Yes/-1:No
 */
int mpu_disable(void) {
#if __MPU_PRESENT
    MPU->CTRL &= ~MPU_CTRL_ENABLE_Msk;
    return 0;
#else
    return -1;
#endif
}

/*!
 * \fn int mpu_enable(void)
 * \brief Enable the physical MPU with the PRIVDEFENA flag
 * \return 0:Yes/-1:No
 */
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

/*!
 * \fn int mpu_enabled(void)
 * \brief Check if MPU is enabled
 * \return 1:Yes/0:No
 */
int mpu_enabled(void) {
#if __MPU_PRESENT
    return (MPU->CTRL & MPU_CTRL_ENABLE_Msk) != 0;
#else
    return 0;
#endif
}

/*!
 * \fn int mpu_init(void)
 * \brief Resets the physical MPU
 * \return 0:Success/-1:Error
 */
int mpu_init(void) {
	__DMB();
    // Disable MPU
	mpu_disable();
#if __MPU_PRESENT && !defined(__ARM_ARCH_8M_MAIN__) && !defined(__ARM_ARCH_8M_BASE__)
    for (int i = 0; i < MPU_NUM_REGIONS ; i++){
        MPU->RNR  = i; // no need if VALID bit with REGION bits are set in RBAR
        MPU->RBAR = 0;
        MPU->RASR = 0;
    }
    // Enable MPU
    mpu_enable();
    __ISB();
	__DSB();
    return 0;
#else
    return -1;
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

/** Memcopy with strictly ordered memory access, e.g. for register targets.
*   Replaces memcpy of string.h
* \param dst Destination data is copied to.
* \param src Source data is copied from.
* \param len Amount of data words to be copied.
*/
__STATIC_INLINE void orderedCpy(volatile uint32_t* dst, const uint32_t* src, uint32_t len)
{
  uint32_t i;
  for (i = 0U; i < len; ++i)
  {
    dst[i] = src[i];
  }
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
		orderedCpy((void*)&( MPU->RBAR), LUT+i*2*sizeof(uint32_t), MPU_ALIAS_REG_NB*2*sizeof(uint32_t));

	}*/
    for (int i = 0; i < MPU_NUM_REGIONS ; i++){
        //MPU->RNR  = i; // no need if VALID bit with REGION bits are set in RBAR
        MPU->RBAR = LUT[i*2];
        MPU->RASR = LUT[i*2+1];
    }
    // Enable MPU with PRIVDEFENA
	mpu_enable();
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

/*!
 * \fn uint32_t readPhysicalMPUSizeBits(uint32_t MPURegionNb)
 * \brief Reads the given physical MPU region's size (in bits)
 * \param MPURegionNb the physical MPU region to read from
 * \return the physical MPU region's size in bits (region size = 2^(size in bits+1))
 */
uint32_t readPhysicalMPUSizeBits(uint32_t MPURegionNb)
{
    MPU->RNR  = MPURegionNb;
    return (MPU->RASR & MPU_RASR_SIZE_Msk) >> MPU_RASR_SIZE_Pos;
}

/*!
 * \fn uint32_t readPhysicalMPUSizeBytes(uint32_t MPURegionNb)
 * \brief Reads the given physical MPU region's size (in bytes)
 * \param MPURegionNb the physical MPU region to read from
 * \return the physical MPU region's size in bytes (region size = 2^(size in bits+1))
 */
uint32_t readPhysicalMPUSizeBytes(uint32_t MPURegionNb)
{
    MPU->RNR  = MPURegionNb;
    uint32_t size = (MPU->RASR & MPU_RASR_SIZE_Msk) >> MPU_RASR_SIZE_Pos;
    return (size == 0) ? 0 : 1 << (size+1);
}

/*!
 * \fn uint32_t* readPhysicalMPUStartAddr(uint32_t MPURegionNb)
 * \brief Reads the given physical MPU region's start address
 * \param MPURegionNb the physical MPU region to read from
 * \return the physical MPU region's start address
 */
uint32_t* readPhysicalMPUStartAddr(uint32_t MPURegionNb)
{
    MPU->RNR  = MPURegionNb;
    return (uint32_t*)((MPU->RBAR & MPU_RBAR_ADDR_Msk));
}

/*!
 * \fn uint32_t* readPhysicalMPUEndAddr(uint32_t MPURegionNb)
 * \brief Reads the given physical MPU region's end address
 * \param MPURegionNb the physical MPU region to read from
 * \return the physical MPU region's end address
 */
uint32_t* readPhysicalMPUEndAddr(uint32_t MPURegionNb)
{
    // Cast in order to offset the start address in bytes not in addresses
    uint32_t start = (uint32_t) readPhysicalMPUStartAddr(MPURegionNb);
    uint32_t size = readPhysicalMPUSizeBytes(MPURegionNb);
    return (uint32_t*) (start + size - 1);
}

/*!
 * \fn uint32_t readPhysicalMPUAP(uint32_t MPURegionNb)
 * \brief Reads the given physical MPU region's RW permissions
 * \param MPURegionNb the physical MPU region to read from
 * \return the physical MPU region's RW permissions
 */
uint32_t readPhysicalMPUAP(uint32_t MPURegionNb)
{
    MPU->RNR  = MPURegionNb;
    return (MPU->RASR & MPU_RASR_AP_Msk) >> MPU_RASR_AP_Pos;
}


/*!
 * \fn uint32_t readPhysicalMPUXN(uint32_t MPURegionNb)
 * \brief Reads the given physical MPU region's X permission
 * \param MPURegionNb the physical MPU region to read from
 * \return the physical MPU region's X permission (XN = 0 -> execute right)
 */
uint32_t readPhysicalMPUXN(uint32_t MPURegionNb)
{
    MPU->RNR  = MPURegionNb;
    return (MPU->RASR & MPU_RASR_XN_Msk) >> MPU_RASR_XN_Pos;
}

/*!
 * \fn uint32_t readPhysicalMPURegionEnable(uint32_t MPURegionNb)
 * \brief Reads the given physical MPU region's enable bit
 * \param MPURegionNb the physical MPU region to read from
 * \return the physical MPU region's enable bit
 */
uint32_t readPhysicalMPURegionEnable(uint32_t MPURegionNb)
{
    MPU->RNR  = MPURegionNb;
    return (MPU->RASR & MPU_RASR_ENABLE_Msk);
}


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

    static const uint32_t BFARVALID_MASK = (1UL << 15);//(0x80 << SCB_CFSR_BUSFAULTSR_Pos);
    static const uint32_t IACCVIOL_MASK = (1UL);
    static const uint32_t DACCVIOL_MASK = (1UL << 1);
    static const uint32_t MUNSTKERR_MASK = (1UL << 3);
    static const uint32_t MSTKERR_MASK = (1UL << 4);
    static const uint32_t MMARVALID_MASK = (1UL << 7);//(0x80 << SCB_CFSR_MEMFAULTSR_Pos);



/* TODO: rewrite this part

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
        debug_puts("Stack was not 8-byte aligned\r\n");
    }
#endif /* SCB_CCR_STKALIGN_Msk */
    debug_puts("\nContext before memfault:");

    /* TODO: printf in ISR context might be a bad idea */
    debug_printf("   r0 (sp): %x\n"
            "   orig_sp: %x\n"
            "   r1: %x\n"
            "   r2: %x\n"
            "   r3: %x\n",
            r0, orig_sp, r1, r2, r3);
    debug_printf("  r12: %x\n"
            "   lr: %x\n"
            "   pc: %x\n"
            "  psr: %x\n\n",
            r12, lreg, pc, psr);

    debug_puts("FSR/FAR:");
    debug_printf(" CFSR: %x\n", cfsr);
    if (cfsr & BFARVALID_MASK) {
        /* BFAR valid flag set */
        debug_printf(" BFAR: %x\n", bfar);
    }
    if (cfsr & SCB_CFSR_MEMFAULTSR_Msk){
        /* MMFAR valid flag set */
        debug_printf("MMFAR: %x\n", mmfar);
    }
  debug_puts ("\r\n[MemManageFault]\n");
  dumpExceptionStack ((ExceptionStackFrame*)frame, cfsr, mmfar, bfar, lr);

#if defined(__ARM_ARCH_7M__) || defined(__ARM_ARCH_7EM__)
  int reconfigure_mpu = -1; // indicates if the fault can be recovered in case of a partially configured block
#endif

    // MemFault flags
    if (cfsr & DACCVIOL_MASK) {
        debug_puts("\r\nDACCVIOL");
        if(cfsr & MMARVALID_MASK){
            debug_printf(" on address: %x", mmfar);
            debug_printf(" at (possibly) instruction: %x\n", pc);
#if defined(__ARM_ARCH_7M__) || defined(__ARM_ARCH_7EM__)
            reconfigure_mpu = 1;
#endif
            SCB->CFSR &= MMARVALID_MASK; // Clear flag
        }
        SCB->CFSR &= DACCVIOL_MASK; // Clear flag
    }
    if (cfsr & IACCVIOL_MASK) {
        debug_puts("\r\nIACCVIOL");
        debug_printf(" at (possibly) instruction: %x\n", pc);
        SCB->CFSR &= IACCVIOL_MASK; // Clear flag
    }
    if (cfsr & MSTKERR_MASK) {
        // The stack is probably not configured in the MPU
        debug_puts("\r\nMSTKERR\r\n");
        SCB->CFSR &= MSTKERR_MASK; // Clear flag
    }
    if (cfsr & MUNSTKERR_MASK) {
        // The stack is probably not configured in the MPU
        debug_puts("\r\nMUNSTKERR\r\n");
        SCB->CFSR &= MUNSTKERR_MASK; // Clear flag
    }

  // ARMv7 MPU RECONFIGURATION BECAUSE OF THE ALIGNMENT CONSTRAINTS
  // Code snippet only to respect the alignment constraints in ARMv7.
  // In Pip-MPU, this is handled by partially configuring a partition's block in the MPU to fit the constraints,
  // which leaves the remaining part of the block out of the MPU.
  // When a partition accesses the part of the block out of the MPU, this raises a MemFault, caught here.
  // The behavior is to reconfigure the block in the MPU with the part of the block that has faulted.
  // The reconfiguration mechanism is completely invisible by the user.
#if defined(__ARM_ARCH_7M__) || defined(__ARM_ARCH_7EM__)
    if(reconfigure_mpu > 0){
        int block_in_MPU = 0;
        // Otherwise search for corresponding block in the MPU
        for (int i = 0; i < MPU_NUM_REGIONS ; i++){
            PDTable_t* currPart = (PDTable_t*) getCurPartition();
            if((currPart->mpu[i])->present && (uint32_t)(currPart->mpu[i])->blockrange.startAddr < mmfar
                && mmfar < (uint32_t)(currPart->mpu[i])->blockrange.endAddr)
            {
                // Found a block covering the faulted address
                block_in_MPU = 1;
                // Check in the MPU if this is a real MPU fault (not because the block has been partially configured)
                    if(readPhysicalMPUStartAddr(i) <= mmfar && mmfar <= readPhysicalMPUEndAddr(i)){
                    // Operation not permitted: raise fault
                    debug_printf("Block mapped in MPU, real fault on address: %x\r\n", mmfar);
                    break;
                }

                else{
                    // Operation permitted: reconfigure MPU and redo faulted legitimate operation
                    debug_printf("Block mapped in MPU, reconfiguring MPU with legitimate faulted block %x for address %x\r\n", currPart->mpu[i], mmfar);
                    configure_LUT_entry(currPart->LUT, i, currPart->mpu[i], (uint32_t*) mmfar);
                    mpu_configure_from_LUT(currPart->LUT);
                    // return to faulted operation without notifying the fault ot the user
                    return;
                }
            }
        }
        if(!block_in_MPU) {
            debug_printf("No block matches in MPU, real fault on address: %x\r\n", mmfar);
        }
    }
#endif

#if defined(DEBUG)
  __DEBUG_BKPT();
#endif

// no need for DMB instructions in exception handler

#if defined(UNIT_TESTS)
    // Set canary to 0xDEADBEEF
    uint32_t* canary = (uint32_t*) 0x20001500;
    *canary = 0xDEADBEEF;
    printf ("\r\nNew canary=%x\n", *canary);
    sp[6] = pc + 2; // continue with next instruction
    printf ("\r\nBranch to PC=%x\r\n", sp[6]);
#endif

}
