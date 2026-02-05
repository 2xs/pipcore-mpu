/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2024)                */
/*  Copyright (C) 2020-2024 Orange                                             */
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

#include "maldefines.h"
#include "nrf52.h"
#include "pip_debug.h"
#include "context.h"
#include "yield_c.h"
#include "scs.h"
#include "crt0_ctx.h"
#include "pip_crt0_ctx_data.h"
#include "memlayout.h"

/**
 * @brief   Initial program status register value for the root partition
 *
 * In the initial state, only the Thumb mode-bit is set
 */
#define INITIAL_XPSR (0x01000000)

extern void __attribute__((noreturn))
Boot_Handler(void)
{
#if defined(UART_DEBUG)
	init_uart();
#endif // UART_DEBUG

	// Initialize the root partition and init the MPU
	malInit();

	/* Enable full access to the FPU. */
	CPACR.as_uint32_t |= 0x00f00000;

	int externalIrqNumber = 32 * (SCnSCB->ICTR + 1);

	/* At reset, all priorities are equal to zero. Here, we want to mask
	 * interrupt using BASEPRI=1 below DebugMonitor. So set PendSV,
	 * SysTick and external interrupts at priority 1. */
	for (int irq = PendSV_IRQn; irq < externalIrqNumber; irq++)
	{
		NVIC_SetPriority(irq, 1);
	}

	/* Retrieve the root partition descriptor structure. */
	PDTable_t *rootPartitionDescriptor = getRootPartition();

	/* Get the top of the PSP */
	uint32_t sp  = (uint32_t) &__rootStackTop;

	/* Reserve on the stack the space necessary for structures. */
	sp -= sizeof(crt0_ctx_t);
	crt0_ctx_t *crt0_ctx = (crt0_ctx_t *)sp;
	sp -= sizeof(pip_crt0_ctx_data_t);
	pip_crt0_ctx_data_t *pip_crt0_ctx_data = (pip_crt0_ctx_data_t *)sp;

	/* Copy the ID of the block containing the partition descriptor
	 * of the root partition. */
	pip_crt0_ctx_data->partDescBlockId = (void *) rootPartitionDescriptor;
	pip_crt0_ctx_data->stackLimit      = &__rootStackLimit;
	pip_crt0_ctx_data->stackTop        = &__rootStackTop;
	pip_crt0_ctx_data->vidtStart       = &__rootVidtStart;
	pip_crt0_ctx_data->vidtEnd         = &__rootVidtEnd;
	pip_crt0_ctx_data->root            = &__root;

	crt0_ctx->bin_base  = &__root;
	crt0_ctx->nvm_start = &__unusedRomStart;
	crt0_ctx->nvm_end   = &__romEnd;
	crt0_ctx->ram_start = &__unusedRamStart;
	crt0_ctx->ram_end   = &__rootRamEnd;
	crt0_ctx->argv      = pip_crt0_ctx_data;

	stackedContext_t rootPartCtx;
	rootPartCtx.isBasicFrame = 1;

	/* Reset the structure to ensure that the restored registers do
	 * not contain undefined value */
	for (size_t i = 0; i < BASIC_FRAME_SIZE; i++)
	{
		rootPartCtx.basicFrame.registers[i] = 0;
	}

	/* Initialize the root partition context. */
	rootPartCtx.basicFrame.r0 = (uintptr_t)crt0_ctx;
	rootPartCtx.basicFrame.pc = (uint32_t) &__root;
	rootPartCtx.basicFrame.sp = sp;
	rootPartCtx.basicFrame.xpsr = INITIAL_XPSR;
	rootPartCtx.pipflags      = 0;

	/* Switch to unprivileged Thread mode. */
	__set_CONTROL(__get_CONTROL() | CONTROL_nPRIV_Msk );
	__DMB(); __ISB(); __DSB();

	/* Yield to the root partition. */
	switchContextCont(getRootPartition(), 0, &rootPartCtx);

	/* We should never end up here because the switchContextCont
	 * function never returns to the caller. */
	__builtin_unreachable();
}
