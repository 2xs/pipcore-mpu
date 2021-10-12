/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2021)                */
/*                                                                             */
/*  This software is a computer program whose purpose is to run a minimal,     */
/*  hypervisor relying on proven properties such as memory isolation.          */
/*                                                                             */
/*  This software is governed by the CeCILL license under French law and       */
/*  abiding by the rules of distribution of free software.  You can  use,      */
/*  modify and/ or redistribute the software under the terms of the CeCILL     */
/*  license as circulated by CEA, CNRS and INRIA at the following URL          */
/*  "http://www.cecill.info".                                                  */
/*                                                                             */
/*  As a counterpart to the access to the source code and  rights to copy,     */
/*  modify and redistribute granted by the license, users are provided only    */
/*  with a limited warranty  and the software's author,  the holder of the     */
/*  economic rights,  and the successive licensors  have only  limited         */
/*  liability.                                                                 */
/*                                                                             */
/*  In this respect, the user's attention is drawn to the risks associated     */
/*  with loading,  using,  modifying and/or developing or reproducing the      */
/*  software by the user in light of its specific status of free software,     */
/*  that may mean  that it is complicated to manipulate,  and  that  also      */
/*  therefore means  that it is reserved for developers  and  experienced      */
/*  professionals having in-depth computer knowledge. Users are therefore      */
/*  encouraged to load and test the software's suitability as regards their    */
/*  requirements in conditions enabling the security of their systems and/or   */
/*  data to be ensured and,  more generally, to use and operate it in the      */
/*  same conditions as regards security.                                       */
/*                                                                             */
/*  The fact that you are presently reading this means that you have had       */
/*  knowledge of the CeCILL license and that you accept its terms.             */
/*******************************************************************************/

#include <stdio.h>
#include "maldefines.h"
#include "nrf52.h"
#include "pip_debug.h"
#include "main_user_app.h"

#if defined(UART_DEBUG)
#include "uart_debug_init.h"
#endif // UART_DEBUG

#if defined(TRACE)
#include "trace.h"
#endif // TRACE

// Stack end address for the user section; defined in linker script
extern uint32_t user_stack_top;

extern paddr blockentryaddr_flash;
extern paddr blockentryaddr_ram0;
extern paddr blockentryaddr_ram1;
extern paddr blockentryaddr_ram2;
extern paddr blockentryaddr_periph;

// Trampoline to start root in unprivileged mode
void main_user_app_trampoline(int argc, char* argv[]);

/**
 * Main entry point.
 * If UART_DEBUG, sends printf messages on UART
 * If -DTRACE -DOS_USE_TRACE_SEMIHOSTING_DEBUG flags are set, send printf messages on the semihosting debug channel
 */
int main (int argc, char* argv[])
{
	/*
	// At this point, mmu is still not enabled.
	ial_get_ctx_addr(0, getRootPartition(), &ctx_p, &ctx_v);

	return ial_prepare_yield(getRootPartition(), ctx_v);*/

	// cpu_switch_context_exit(); -> Yield, switch to root partition

  // yield partition 0
#if defined(UART_DEBUG)
  init_uart();
#endif // UART_DEBUG

#if defined(TRACE)
  const char* trace_msg = "Trace is on\r\n";
  trace_printf((uint8_t const *)trace_msg);
#endif // TRACE

  // Initialize the root partition and init the MPU
  mal_init();

  paddr root = getRootPartition();
  dump_partition(root);
  activate(root);

  // set PSP to root stack
  uint32_t psp = (uint32_t) &user_stack_top;
  __set_PSP(psp);

  // select PSP to Thread Mode (can't be done in Handler mode because it would be ignored)
  __set_CONTROL(__get_CONTROL() |
                CONTROL_SPSEL_Msk);// use psp

  // Call the trampoline which will lower the privileges to UNPRIVILEGED and start root
  uint32_t* initial_blocks[6] = { root,
                                  blockentryaddr_flash,
                                  blockentryaddr_ram0,
                                  blockentryaddr_ram1,
                                  blockentryaddr_ram2,
                                  blockentryaddr_periph};

  main_user_app_trampoline(6, (char**)initial_blocks);
}

/**
 * Trampoline to main.
 * The stack and registers are correctly set up to call main in Thread Mode.
 * However, we need first to set the processor mode to unprivileged.
 * We can't use CONTROL_nPRIV_Msk here because we would return in unprivileged
 * Thread mode but not in a region defined in the MPU, resulting in a memory fault.
 * Therefore, we need to pass through a handler and lower the privilege there.
 * We use PendSV for this.
 */
void main_user_app_trampoline(int argc, char* argv[])
{
  // Pend a PendSV exception by writing 1 to PENDSVSET at bit 28
  // In ASM in order to use R4 and R5 and not disturbing the registers
  asm volatile(
    "  LDR r4,=0xE000ED04   \n" /* ICSR: Interrupt Control and State */
    "  MOV r5,#1            \n"
    "  LSL r5,r5,#28        \n" /* r5 := (1 << 28) (PENDSVSET bit) */
    "  STR r5, [r4]         \n" // set PendSV
      : // Outputs
      : // Inputs
      : // Clobbers
  );

  /********************** Start of user application ************************/
  // Trigger PendSV immediately to start root
  __DSB();
  printf("App ended\n\r");
}

void PendSV_Handler(uint32_t argc, char** argv) {
  __asm(
    ".global PendSV_Handler_Main\n"
    "TST lr, #4\n"
    "ITE EQ\n"
    "MRSEQ r0, MSP\n"
    "MRSNE r0, PSP\n"
    "B PendSV_Handler_Main\n"
  ) ;
}

/**
 * PendSV_Handler_Main returns in unprivileged Thread mode and branch on root's main.
 */
void __attribute__ ((section(".after_vectors"),weak,used))
PendSV_Handler_Main (uint32_t* frame __attribute__((unused)))
{

  uint32_t pc = 0;
  uint32_t* orig_sp = NULL;

  uint32_t* sp = frame;
  uint32_t  r0 = sp[0];
  uint32_t  r1 = sp[1];
  uint32_t  r2 = sp[2];
  uint32_t  r3 = sp[3];
  uint32_t  r12 = sp[4];
  uint32_t  lreg = sp[5];   /* Link register. */
            pc = sp[6];     /* Program counter. */
  uint32_t  psr = sp[7];    /* Program status register. */

  /* Reconstruct original stack pointer before exception occurred */
  orig_sp = sp + 8;
#ifdef SCB_CCR_STKALIGN_Msk
  if (psr & SCB_CCR_STKALIGN_Msk) {
      /* Stack was not 8-byte aligned */
      orig_sp += 1;
      debug_puts("PendSV: Stack was not 8-byte aligned\r\n");
  }
#endif /* SCB_CCR_STKALIGN_Msk */
  debug_puts("\nContext before PendSV:");

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

  // ********************** Start of user application ************************ /
  sp[6] = (uint32_t) main_user_app; // change PC to point to the main_user_app at exception return
  __set_CONTROL(__get_CONTROL() |
                CONTROL_nPRIV_Msk ); // switch to unprivileged Thread Mode
  __DMB();
  __ISB();
  __DSB();

  debug_puts("\n\r**********************Root starts***************************\n\r");
  // At exception return, the main user app will start in unprivileged Thread Mode
}
