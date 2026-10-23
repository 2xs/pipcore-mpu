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

/*!
 * \file main.c
 * \brief Boot_Handler: the last thing Pip does before the root partition runs.
 *
 * Ports from the ARM target's main.c. Four things in that file have no
 * counterpart here and are simply gone: the FPU enable (CPACR), the
 * SCnSCB->ICTR / NVIC_SetPriority loop that set up ARM's BASEPRI masking
 * policy, the INITIAL_XPSR Thumb bit, and the __set_CONTROL(| nPRIV)
 * privilege drop. The last two are worth a word each.
 *
 * There is no Thumb bit to set, because there is no Thumb: the initial mepc
 * is just the entry address.
 *
 * The privilege drop is not an instruction here but a field. ARM switched to
 * unprivileged Thread mode before yielding; on RISC-V the privilege the
 * partition runs at is whatever mstatus.MPP says when mret executes, and
 * loadContext() forces MPP = 0. So dropping privilege and entering the
 * partition are the same act, and cannot be accidentally separated.
 *
 * Nor is there a PendSV self-trigger. ARM needed one to reach an exception
 * context, because Boot_Handler had to run in Handler mode; M-mode at reset
 * already is the privileged context, so kernel.c calls this directly.
 */

#include <stddef.h>
#include <stdint.h>

#include "ADT.h"
#include "context.h"
#include "crt0_ctx.h"
#include "mal.h"
#include "maldefines.h"
#include "memlayout.h"
#include "pip_crt0_ctx_data.h"
#include "trap_handler.h"
#include "uart.h"

void __attribute__((noreturn)) Boot_Handler(void);

void __attribute__((noreturn)) Boot_Handler(void)
{
	PDTable_t *rootPartitionDescriptor;
	crt0_ctx_t *crt0_ctx;
	pip_crt0_ctx_data_t *pip_crt0_ctx_data;
	stackedContext_t rootPartCtx;
	uint32_t sp;
	size_t i;

#if defined(UART_DEBUG)
	init_uart();
#endif // UART_DEBUG

	/* Initialize the root partition and the PMP. malInit() asserts that
	 * the PMP is the one this port assumes and then installs the deny-all
	 * background, in that order and for a reason -- see malinit.c. */
	malInit();

	/* Retrieve the root partition descriptor structure. */
	rootPartitionDescriptor = (PDTable_t *) getRootPartition();

	/* Get the top of the root partition's stack. */
	sp = (uint32_t) (uintptr_t) &__rootStackTop;

	/* Reserve on the stack the space necessary for structures. */
	sp -= sizeof(crt0_ctx_t);
	crt0_ctx = (crt0_ctx_t *) (uintptr_t) sp;
	sp -= sizeof(pip_crt0_ctx_data_t);
	pip_crt0_ctx_data = (pip_crt0_ctx_data_t *) (uintptr_t) sp;

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

	/* Reset the structure to ensure that the restored registers do
	 * not contain undefined value. */
	for (i = 0; i < CONTEXT_REGS_NB; i++) {
		rootPartCtx.regs[i] = 0;
	}

	/* Initialize the root partition context. isBasicFrame is always 1 on
	 * this target, which has no extended frame. */
	rootPartCtx.isBasicFrame = 1;
	rootPartCtx.pipflags     = 0;
	rootPartCtx.mepc         = (uint32_t) (uintptr_t) &__root;

	/* mstatus is left at zero rather than copied from the current one.
	 * The two fields that decide what mret does are set by
	 * loadContext(): it forces MPP = 0 so the partition runs in U-mode,
	 * and MPIE = 1 so interrupts are on once it does. Starting from zero
	 * also means MPRV cannot be inherited. */
	rootPartCtx.mstatus = 0;

	contextWriteRegister(&rootPartCtx, RV_REG_SP, sp);
	contextWriteRegister(&rootPartCtx, RV_REG_A0,
	                     (uint32_t) (uintptr_t) crt0_ctx);

	/* What switchContextCont() reduces to in milestone 1. Its two
	 * kernel_set_int_state() calls and its "only the root partition may
	 * choose to be interrupted" rule belong to the interrupt state
	 * machinery of section 7, which nothing enables yet; what is left is
	 * the address-space switch and the context load.
	 *
	 * TODO: section 3's ACCESSCTRL programming and ACCESSCTRL_LOCK belong
	 * here, immediately before the first U-mode entry. Deliberately not
	 * done yet: it is defence in depth over a hole the deny-all PMP entry
	 * already closes -- measured on silicon -- it governs DMA that nothing
	 * in milestone 1 uses, and whether clearing a peripheral's SU bit
	 * blocks a Hazard3 U-mode access at all is still an open question. The
	 * LOCK is irreversible until reset, so it is not something to program
	 * speculatively in a boot path that has no debugger on it yet.
	 */
	updateCurPartAndActivate(getRootPartition());
	loadContext(&rootPartCtx);
}
