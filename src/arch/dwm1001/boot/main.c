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
#include <stdlib.h>
#include "maldefines.h"
#include "nrf52.h"
#include "pip_debug.h"
#include "context.h"
#include "yield_c.h"
#include "scb.h"

#if defined(UART_DEBUG)
#include "uart_debug_init.h"
#endif // UART_DEBUG

#if defined(TRACE)
#include "trace.h"
#endif // TRACE

#if defined(BENCHMARK)
#include "benchmark.h"
extern void main_benchmark();//int argc, uint32_t **argv);

#endif // BENCHMARK

//extern void	main_test(void);

// Stack end address for the user section; defined in linker script
extern uint32_t user_stack_top;

extern paddr blockentryaddr_flash;
extern paddr blockentryaddr_ram0;
extern paddr blockentryaddr_ram1;
extern paddr blockentryaddr_ram2;
extern paddr blockentryaddr_periph;

extern void main_yield(int argc, uint32_t **argv);

/**
 * Pip's main entry point.
 * If UART_DEBUG, sends printf messages on UART
 * If -DTRACE -DOS_USE_TRACE_SEMIHOSTING_DEBUG flags are set, send printf messages on the semihosting debug channel
 * We are in PRIV Thread Mode and we want to switch to the root partition
 * The root partition should be in Unprivileged Thread Mode using PSP.
 * However, switching to the unprivileged root partition is not possible yet, since the current location is in Pip's protected region.
 * Hence, a direct switch would trigger a MemFault.
 * Instead, we enter the Handler Mode with PendSV and launches the root partition (UNPRIV/PSP) as an exception return.
 */
__attribute__((noreturn))
void main (void)
{
#if defined(UART_DEBUG)
	init_uart();
#endif // UART_DEBUG

	/* Set the PendSV exception as pending by writing 1 to the
	 * PENDSVSET bit. */
	ICSR.PENDSVSET = 1;

	/* Trigger the PendSV exception immediately by synchronizing the
	 * execution stream with memory accesses. */
	__DSB();

	/* We should never end up here because the DSB instruction must
	 * immediately trigger the PendSV exception. */
	__builtin_unreachable();
}

/**
 * PendSV Handler
 * Handler mode: launch the root partition during exception return.
 */
__attribute__((noreturn))
void PendSV_Handler(void)
{
	/* Get the top of the PSP */
uint8_t *sp = (uint8_t *)&user_stack_top;

#if defined BENCHMARK
	START_BENCHMARK();
#endif // BENCHMARK

#if defined BENCHMARK_BASELINE
	// Version wo Pip / wo MPU
	uint32_t frame = (uint32_t) sp - 0x20; // Build benchmark frame
	__set_PSP(frame);
	// Thread mode is unprivileged
	__set_CONTROL(__get_CONTROL() | CONTROL_nPRIV_Msk );
	__DMB(); __ISB(); __DSB();

	// exception return/exit frame
	// Stack frame when starting the benchmark
	uint32_t *framePtr = (uint32_t *)frame;
	framePtr[0] = 0;
	framePtr[1] = 0;
	framePtr[2] = 0;
	framePtr[3] = 0;
	framePtr[4] = 0;
	framePtr[5] = 0;
	framePtr[6] = (uint32_t)main_benchmark;
	framePtr[7] = 0 /*| (1<<29) | (1<<30)*/ | (1 << 24);// T bit mandatroy: ARM Cortex M only supports Thumb instruction execution

	asm volatile("cpsie   i;" // enable interrupts (CLOCK)
				 " bx %0; "	  // branch to main in UNPRIV mode with PSP (EXC_RETURN=0xFFFFFFFD)

				 /* Output operands */
				 :

				 /* Input operands */
				 : "r"(0xFFFFFFFD)

				 /* Clobbers */
				 : "memory");
#else

	// Initialize the root partition and init the MPU
	mal_init();

	/* Reserve on the stack the space necessary for the
	 * arguments. */
	uint32_t  argc = 6;
	uint32_t *argv = sp - argc*sizeof(uint32_t) ;

	/* Copy arguments onto the stack */
	argv[0] = (uint32_t) getRootPartition();
	argv[1] = (uint32_t) blockentryaddr_flash;
	argv[2] = (uint32_t) blockentryaddr_ram0;
	argv[3] = (uint32_t) blockentryaddr_ram1;
	argv[4] = (uint32_t) blockentryaddr_ram2;
	argv[5] = (uint32_t) blockentryaddr_periph;

	/* Declare the context of the root partition on the MSP in order
	 * to start it. This context is not stored in a VIDT. */
	user_context_t rootPartitionContext;

	/* Reset the structure to ensure that the restored registers do
	 * not contain undefined value */
	for (size_t i = 0; i < CONTEXT_REGISTER_NUMBER; i++)
	{
		rootPartitionContext.registers[i] = 0;
	}

	/* Initialize the root partition context. */
	rootPartitionContext.registers[R0] = argc;
	rootPartitionContext.registers[R1] = (uint32_t) argv;
#if defined BENCHMARK_PIP
	rootPartitionContext.registers[PC] = (uint32_t)main_benchmark;
#else
	rootPartitionContext.registers[PC] = (uint32_t) main_yield;
#endif // BENCHMARK_PIP
	rootPartitionContext.registers[SP] = (uint32_t) argv;
	rootPartitionContext.pipflags      = 0;
	rootPartitionContext.valid         = 1;

	/* Switch to unprivileged Thread mode. */
	__set_CONTROL(__get_CONTROL() | CONTROL_nPRIV_Msk );
	__DMB(); __ISB(); __DSB();

	/* Yield to the root partition. */
	switchContextCont(getRootPartition(), 0, &rootPartitionContext);
#endif // BENCHMARK_BASELINE

		/* We should never end up here because the switchContextCont
	 * function never returns to the caller. */
		__builtin_unreachable();
}
