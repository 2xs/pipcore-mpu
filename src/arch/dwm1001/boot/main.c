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
#include "context.h"
#include "yield_c.h"
#include "scb.h"

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

/**
 * Main entry point.
 * If UART_DEBUG, sends printf messages on UART
 * If -DTRACE -DOS_USE_TRACE_SEMIHOSTING_DEBUG flags are set, send printf messages on the semihosting debug channel
 */
__attribute__((noreturn))
void main (void)
{
#if defined(UART_DEBUG)
	init_uart();
#endif // UART_DEBUG

	// Initialize the root partition and init the MPU
	mal_init();

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

__attribute__((noreturn))
void PendSV_Handler(void)
{
	/* Get the top of the PSP */
	uint32_t *sp  = (uint32_t *) &user_stack_top;

	/* Reserve on the stack the space necessary for the
	 * arguments. */
	uint32_t  argc = 6;
	uint32_t *argv = sp - argc;

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
	rootPartitionContext.registers[PC] = (uint32_t) main_user_app;
	rootPartitionContext.registers[SP] = (uint32_t) argv;
	rootPartitionContext.pipflags      = 0;
	rootPartitionContext.valid         = 1;

	/* Switch to unprivileged Thread mode. */
	__set_CONTROL(__get_CONTROL() | CONTROL_nPRIV_Msk );
	__DMB(); __ISB(); __DSB();

	/* Yield to the root partition. */
	switchContextCont(getRootPartition(), 0, &rootPartitionContext);

	/* We should never end up here because the switchContextCont
	 * function never returns to the caller. */
	__builtin_unreachable();
}
