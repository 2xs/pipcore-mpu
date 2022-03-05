/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2022)                */
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

#include <stdint.h>

#include "Internal.h"
#include "context.h"
#include "yield_c.h"
#include "pip_interrupt_calls.h"
#include "nrf52.h"
#include "mal.h"
#include "scs.h"
#if defined(BENCHMARK)
#include "benchmark.h"
#endif // BENCHMARK

/* Check that an address does not exceed the end of a block. */
#define IS_BLOCK_END_EXCEEDED(address, blockEnd) \
	(((blockEnd) - (address)) < sizeof(user_context_t))

/* Check that an address is aligned on a 4-byte boundary. */
#define IS_MISALIGNED(address) ((address) & 0x3)

/*!
 * \def VIDT_MAX_INDEX
 *
 * \brief The maximum index of the VIDT.
 */
#define VIDT_MAX_INDEX \
	((getMinVidtBlockSize()) / (sizeof(void *)))

/* This EXC_RETURN value allows to return to Thread mode with
 * the PSP stack. */
#define EXC_RETURN_THREAD_MODE_PSP 0xFFFFFFFD

/* The MSP top of stack defined in the link script. */
extern uint32_t __StackTop;

__attribute__((section(".text_pipcore")))
static yield_return_code_t checkIntLevelCont(
	paddr calleePartDescAddr,
	uservalue_t userTargetInterrupt,
	uservalue_t userCallerContextSaveIndex,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	user_context_t *callerInterruptedContext);

__attribute__((section(".text_pipcore")))
static yield_return_code_t checkCtxSaveIdxCont(
	paddr calleePartDescAddr,
	unsigned targetInterrupt,
	uservalue_t userCallerContextSaveIndex,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	user_context_t *callerInterruptedContext
);

__attribute__((section(".text_pipcore")))
static yield_return_code_t getChildPartDescCont(
	paddr callerPartDesc,
	paddr calleePartDescAddr,
	unsigned targetInterrupt,
	unsigned callerContextSaveIndex,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	user_context_t *callerInterruptedContext
);

__attribute__((section(".text_pipcore")))
static yield_return_code_t getTargetPartCtxCont(
	paddr calleePartDesc,
	paddr callerPartDesc,
	paddr calleeVidt,
	paddr callerContextSaveAddr,
	unsigned targetInterrupt,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	user_context_t *callerInterruptedContext
);

__attribute__((section(".text_pipcore")))
static yield_return_code_t saveSourcePartCtxCont(
	paddr calleePartDesc,
	paddr callerPartDesc,
	paddr callerContextSaveAddr,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	user_context_t *callerInterruptedContext,
	user_context_t *targetContext
);

__attribute__((section(".text_pipcore"))) static void writeContext(
	user_context_t *ctx,
	paddr ctxSaveVAddr,
	int_mask_t flagsOnWake);

__attribute__((section(".text_pipcore")))static void
loadContext(
	user_context_t *ctx,
	unsigned enforce_interrupts) __attribute__((noreturn));


__attribute__((section(".text_pipcore")))
yield_return_code_t yieldGlue(
	stacked_context_t *svc_ctx,
	paddr calleePartDescLocalId,
	uservalue_t userTargetInterrupt,
	uservalue_t userCallerContextSaveIndex,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake
) {
	user_context_t ctx;

	/* Copy of the context stacked by the SVC handler. */
	for (size_t i = 0; i < CONTEXT_REGISTER_NUMBER; i++)
	{
		ctx.registers[i] = svc_ctx->registers[i];
	}

	/* Save the value of the stack before the SVC interrupt. */
	uint32_t forceAlign = CCR.STKALIGN;
	uint32_t spMask     = ((ctx.registers[XPSR] >> 9) & forceAlign) << 2;
	ctx.registers[SP]   = (ctx.registers[SP] + FRAME_SIZE) | spMask;
	ctx.valid           = CONTEXT_VALID_VALUE;

	return checkIntLevelCont(
		calleePartDescLocalId,
		userTargetInterrupt,
		userCallerContextSaveIndex,
		flagsOnYield,
		flagsOnWake,
		&ctx
	);
}

static yield_return_code_t checkIntLevelCont(
	paddr calleePartDescLocalId,
	uservalue_t userTargetInterrupt,
	uservalue_t userCallerContextSaveIndex,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	user_context_t *callerInterruptedContext
) {
	if (!(userTargetInterrupt < VIDT_MAX_INDEX))
	{
		return CALLEE_INVALID_VIDT_INDEX;
	}

	unsigned char targetInterrupt =
		(unsigned char) userTargetInterrupt;

	return checkCtxSaveIdxCont(
		calleePartDescLocalId,
		targetInterrupt,
		userCallerContextSaveIndex,
		flagsOnYield,
		flagsOnWake,
		callerInterruptedContext
	);
}

static yield_return_code_t checkCtxSaveIdxCont(
	paddr calleePartDescLocalId,
	unsigned targetInterrupt,
	uservalue_t userCallerContextSaveIndex,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	user_context_t *callerInterruptedContext
) {
	if (!(userCallerContextSaveIndex < VIDT_MAX_INDEX))
	{
		return CALLER_INVALID_VIDT_INDEX;
	}

	unsigned char callerContextSaveIndex =
		(unsigned char) userCallerContextSaveIndex;

	paddr callerPartDescGlobalId = getCurPartition();

	if (calleePartDescLocalId == NULL)
	{
		/* The caller wants to yield to a context in the VIDT
		 * of its parent.*/
		return getParentPartDescCont(
			callerPartDescGlobalId,
			targetInterrupt,
			callerContextSaveIndex,
			flagsOnYield,
			flagsOnWake,
			callerInterruptedContext
		);
	}
	else if (calleePartDescLocalId == callerPartDescGlobalId)
	{
		/* The caller wants to yield to a context in its own
		 * VIDT. */
		return getSourcePartVidtCont(
			calleePartDescLocalId,
			callerPartDescGlobalId,
			targetInterrupt,
			callerContextSaveIndex,
			flagsOnYield,
			flagsOnWake,
			callerInterruptedContext
		);
	}
	else
	{
		/* The caller wants to yield to a context in the VIDT
		 * of one of its children. */
		return getChildPartDescCont(
			callerPartDescGlobalId,
			calleePartDescLocalId,
			targetInterrupt,
			callerContextSaveIndex,
			flagsOnYield,
			flagsOnWake,
			callerInterruptedContext
		);
	}
}

static yield_return_code_t getChildPartDescCont(
	paddr callerPartDescGlobalId,
	paddr calleePartDescLocalId,
	unsigned targetInterrupt,
	unsigned callerContextSaveIndex,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	user_context_t *callerInterruptedContext
) {
	/* Check that the callee is a child of the caller. */
	if (!(checkChildOfCurrPart(callerPartDescGlobalId, calleePartDescLocalId)))
	{
		return CALLEE_NOT_CHILD_OF_CALLER;
	}

	paddr calleePartDescGlobalId =
		readBlockStartFromBlockEntryAddr(calleePartDescLocalId);

	return getSourcePartVidtCont(
		calleePartDescGlobalId,
		callerPartDescGlobalId,
		targetInterrupt,
		callerContextSaveIndex,
		flagsOnYield,
		flagsOnWake,
		callerInterruptedContext
	);
}

yield_return_code_t getParentPartDescCont(
	paddr callerPartDescGlobalId,
	unsigned targetInterrupt,
	unsigned callerContextSaveIndex,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	user_context_t *callerInterruptedContext
) {
	paddr rootPartDescGlobalId = getRootPartition();

	/* Check that the root partition does not try to call its
	 * parent. */
	if (callerPartDescGlobalId == rootPartDescGlobalId)
	{
		return CALLEE_IS_PARENT_OF_ROOT;
	}

	paddr calleePartDescGlobalId = readPDParent(callerPartDescGlobalId);

	return getSourcePartVidtCont(
		calleePartDescGlobalId,
		callerPartDescGlobalId,
		targetInterrupt,
		callerContextSaveIndex,
		flagsOnYield,
		flagsOnWake,
		callerInterruptedContext
	);
}

yield_return_code_t getSourcePartVidtCont(
	paddr calleePartDescGlobalId,
	paddr callerPartDescGlobalId,
	unsigned targetInterrupt,
	unsigned callerContextSaveIndex,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	user_context_t *callerInterruptedContext
) {
	paddr callerVidtBlockEntryAddr = readPDVidt(callerPartDescGlobalId);

	/* Check that the address of the block containing the VIDT of
	 * the caller is not null. */
	if (compareAddrToNull(callerVidtBlockEntryAddr))
	{
		return CALLER_VIDT_IS_NULL;
	}

	/* Check that the block containing the VIDT of the caller has the
	 * present flag. */
	if (!(readBlockPresentFromBlockEntryAddr(callerVidtBlockEntryAddr)))
	{
		return CALLER_VIDT_IS_NOT_PRESENT;
	}

	/* Check that the block containing the VIDT of the caller has the
	 * accessible flag. */
	if (!(readBlockAccessibleFromBlockEntryAddr(callerVidtBlockEntryAddr)))
	{
		return CALLER_VIDT_IS_NOT_ACCESSIBLE;
	}

	uintptr_t callerVidtBlockEntryStart =
		(uintptr_t) readBlockStartFromBlockEntryAddr(callerVidtBlockEntryAddr);

	uintptr_t callerVidtBlockEntryEnd =
		(uintptr_t) readBlockEndFromBlockEntryAddr(callerVidtBlockEntryAddr);

	uintptr_t callerVidtBlockSize =
		callerVidtBlockEntryEnd - callerVidtBlockEntryStart + 1;

	/* Check that the block containing the VIDT of the caller is
	 * big enough. */
	if (callerVidtBlockSize < getMinVidtBlockSize())
	{
		return CALLER_VIDT_BLOCK_TOO_SMALL;
	}

	paddr callerVidtAddr =
		readBlockStartFromBlockEntryAddr(callerVidtBlockEntryAddr);

	paddr callerContextSaveAddr =
		((user_context_t **) callerVidtAddr)[callerContextSaveIndex];

	return getTargetPartVidtCont(
		calleePartDescGlobalId,
		callerPartDescGlobalId,
		callerContextSaveAddr,
		targetInterrupt,
		flagsOnYield,
		flagsOnWake,
		callerInterruptedContext
	);
}

yield_return_code_t getTargetPartVidtCont(
	paddr calleePartDescGlobalId,
	paddr callerPartDescGlobalId,
	paddr callerContextSaveAddr,
	unsigned targetInterrupt,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	user_context_t *callerInterruptedContext
) {
	paddr calleeVidtBlockEntryAddr = readPDVidt(calleePartDescGlobalId);

	/* Check that the address of the block containing the VIDT of
	 * the callee is not null. */
	if (compareAddrToNull(calleeVidtBlockEntryAddr))
	{
		return CALLEE_VIDT_IS_NULL;
	}

	/* Check that the block containing the VIDT of the callee has
	 * the present flag. */
	if (!(readBlockPresentFromBlockEntryAddr(calleeVidtBlockEntryAddr)))
	{
		return CALLEE_VIDT_IS_NOT_PRESENT;
	}

	/* Check that the block containing the VIDT of the callee has
	 * the accessible flag. */
	if (!(readBlockAccessibleFromBlockEntryAddr(calleeVidtBlockEntryAddr)))
	{
		return CALLEE_VIDT_IS_NOT_ACCESSIBLE;
	}

	uintptr_t calleeVidtBlockEntryStart =
		(uintptr_t) readBlockStartFromBlockEntryAddr(calleeVidtBlockEntryAddr);

	uintptr_t calleeVidtBlockEntryEnd =
		(uintptr_t) readBlockEndFromBlockEntryAddr(calleeVidtBlockEntryAddr);

	uintptr_t calleeVidtBlockSize =
		calleeVidtBlockEntryEnd - calleeVidtBlockEntryStart + 1;

	/* Check that the block containing the VIDT of the callee is
	 * big enough. */
	if (calleeVidtBlockSize < getMinVidtBlockSize())
	{
		return CALLEE_VIDT_BLOCK_TOO_SMALL;
	}

	paddr calleeVidtAddr =
		readBlockStartFromBlockEntryAddr(calleeVidtBlockEntryAddr);

	return getTargetPartCtxCont(
		calleePartDescGlobalId,
		callerPartDescGlobalId,
		calleeVidtAddr,
		callerContextSaveAddr,
		targetInterrupt,
		flagsOnYield,
		flagsOnWake,
		callerInterruptedContext
	);
}

static yield_return_code_t getTargetPartCtxCont(
	paddr calleePartDescGlobalId,
	paddr callerPartDescGlobalId,
	paddr calleeVidtAddr,
	paddr callerContextSaveAddr,
	unsigned targetInterrupt,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	user_context_t *callerInterruptedContext
) {
	paddr calleeContextAddr =
		((user_context_t **) calleeVidtAddr)[targetInterrupt];

	paddr calleeContextBlockLocalId =
		findBelongingBlock(calleePartDescGlobalId, calleeContextAddr);

	/* Check that a block were found in the callee's address space
	 * that match the context address read from the VIDT. */
	if (compareAddrToNull(calleeContextBlockLocalId))
	{
		return CALLEE_CONTEXT_BLOCK_NOT_FOUND;
	}

	/* Check that the block containing the address at which the
	 * context of the callee is to be read has the present
	 * flag. */
	if (!(readBlockPresentFromBlockEntryAddr(calleeContextBlockLocalId)))
	{
		return CALLEE_CONTEXT_BLOCK_IS_NOT_PRESENT;
	}

	/* Check that the block containing the address at which the
	 * context of the callee is to be read has the accessible
	 * flag. */
	if (!(readBlockAccessibleFromBlockEntryAddr(calleeContextBlockLocalId)))
	{
		return CALLEE_CONTEXT_BLOCK_IS_NOT_ACCESSIBLE;
	}

	/* Check that the block containing the address at which the
	 * context of the callee is to be read has the readable flag. */
	if (!(readBlockRFromBlockEntryAddr(calleeContextBlockLocalId)))
	{
		return CALLEE_CONTEXT_BLOCK_IS_NOT_READABLE;
	}

	uintptr_t calleeContextBlockEndAddress =
		(uintptr_t) readBlockEndFromBlockEntryAddr(calleeContextBlockLocalId);

	int isCalleeContextExceedBlockEnd =
		IS_BLOCK_END_EXCEEDED((uintptr_t) calleeContextAddr,
			calleeContextBlockEndAddress);

	/* Check that the address of the callee's context, added to the
	 * size of a context, does not exceed the end of the block. */
	if (isCalleeContextExceedBlockEnd)
	{
		return CALLEE_CONTEXT_EXCEED_BLOCK_END;
	}

	int isCalleeContextMisaligned =
			IS_MISALIGNED((uintptr_t) calleeContextAddr);

	/* Check that the address at which the callee's context should
	 * be read is aligned on a 4-byte boundary. */
	if (isCalleeContextMisaligned)
	{
		return CALLEE_CONTEXT_MISALIGNED;
	}

	user_context_t *targetContext = (user_context_t *) calleeContextAddr;

	/* Check that the target context has a valid context value in
	 * the valid field of the structure. */
	if (targetContext->valid != CONTEXT_VALID_VALUE)
	{
		return CALLEE_CONTEXT_INVALID;
	}

	if (!(callerContextSaveAddr == NULL))
	{
		return saveSourcePartCtxCont(
			calleePartDescGlobalId,
			callerPartDescGlobalId,
			callerContextSaveAddr,
			flagsOnYield,
			flagsOnWake,
			callerInterruptedContext,
			targetContext
		);
	}
	else
	{
		return switchContextCont(
			calleePartDescGlobalId,
			flagsOnYield,
			targetContext
		);
	}
}

static yield_return_code_t saveSourcePartCtxCont(
	paddr calleePartDescGlobalId,
	paddr callerPartDescGlobalId,
	paddr callerContextSaveAddr,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	user_context_t *callerInterruptedContext,
	user_context_t *targetContext
) {
	paddr callerContextBlockLocalId =
		findBelongingBlock(callerPartDescGlobalId, callerContextSaveAddr);

	/* Check that a block were found in the caller's address space
	 * that match the context address read from the VIDT. */
	if (compareAddrToNull(callerContextBlockLocalId))
	{
		return CALLER_CONTEXT_BLOCK_NOT_FOUND;
	}

	/* Check that the block containing the address to which the
	 * context of the caller is to be written has the present
	 * flag. */
	if (!(readBlockPresentFromBlockEntryAddr(callerContextBlockLocalId)))
	{
		return CALLER_CONTEXT_BLOCK_IS_NOT_PRESENT;
	}

	/* Check that the block containing the address to which the
	 * context of the caller is to be written has the accessible
	 * flag. */
	if (!(readBlockAccessibleFromBlockEntryAddr(callerContextBlockLocalId)))
	{
		return CALLER_CONTEXT_BLOCK_IS_NOT_ACCESSIBLE;
	}

	/* Check that the block containing the address to which the
	 * context of the caller is to be written has the writable
	 * flag. */
	if (!(readBlockWFromBlockEntryAddr(callerContextBlockLocalId)))
	{
		return CALLER_CONTEXT_BLOCK_IS_NOT_WRITABLE;
	}

	uintptr_t callerContextBlockEndAddress =
		(uintptr_t) readBlockEndFromBlockEntryAddr(callerContextBlockLocalId);

	int isCallerContextExceedBlockEnd =
		IS_BLOCK_END_EXCEEDED((uintptr_t) callerContextSaveAddr,
			callerContextBlockEndAddress);

	/* Check that the address of the caller's context, added to the
	 * size of a context, does not exceed the end of the block. */
	if (isCallerContextExceedBlockEnd)
	{
		return CALLER_CONTEXT_EXCEED_BLOCK_END;
	}

	int isCallerContextMisaligned =
		IS_MISALIGNED((uintptr_t) callerContextSaveAddr);

	/* Check that the address to which the caller's context should
	 * be written is aligned on a 4-byte boundary. */
	if (isCallerContextMisaligned)
	{
		return CALLER_CONTEXT_MISALIGNED;
	}

	writeContext(
		callerInterruptedContext,
		callerContextSaveAddr,
		flagsOnWake
	);

	return switchContextCont(
		calleePartDescGlobalId,
		flagsOnYield,
		targetContext
	);
}

static void writeContext(
	user_context_t *ctx,
	paddr ctxSaveAddr,
	int_mask_t flagsOnWake
) {
	user_context_t *userland_save_ptr = (user_context_t *) ctxSaveAddr;

	/* Copy the context of the caller to the write address. */
	for (size_t i = 0; i < CONTEXT_REGISTER_NUMBER; i++)
	{
		userland_save_ptr->registers[i] = ctx->registers[i];
	}
	userland_save_ptr->pipflags = flagsOnWake;
	userland_save_ptr->valid = CONTEXT_VALID_VALUE;
}

yield_return_code_t switchContextCont(
	paddr calleePartDescGlobalId,
	int_mask_t flagsOnYield,
	user_context_t *ctx
) {
	/* Set the interrupt state of the caller before activating the
	 * callee's address space. */
	kernel_set_int_state(flagsOnYield);

	/* Update the current partition with the child's partition
	 * descriptor and activate its address space. */
	updateCurPartAndActivate(calleePartDescGlobalId);

	/* Set the interrupt state of the callee */
	kernel_set_int_state(ctx->pipflags);

	unsigned enforce_interrupts = 1;

	/* Only the root partition can choose to be interrupted or not. */
	if (calleePartDescGlobalId == getRootPartition() && ctx->pipflags == 0)
	{
		enforce_interrupts = 0;
	}

	loadContext(ctx, enforce_interrupts);

	/* The code below is never reached because the loadContext
	 * function never returns to the caller. However, it is required
	 * for the future Coq implementation of the service. */
	return YIELD_SUCCESS;
}

__attribute__((noreturn))
static void loadContext(
	user_context_t *ctx,
	unsigned enforce_interrupts
) {
	/* Forces the callee's stack to be aligned to 8 bytes when the
	 * STKALIGN bit is set to 1. */
	uint32_t forceAlign    = CCR.STKALIGN;
	uint32_t spMask        = ~(forceAlign << 2);
	uint32_t framePtrAlign = (ctx->registers[SP] >> 2) & forceAlign;
	uint32_t frame         = (ctx->registers[SP] - FRAME_SIZE) & spMask;

	/* Copy registers R0 to R3, R12, LR, PC and xPSR to the stack of
	 * the callee. */
	uint32_t *framePtr = (uint32_t *) frame;
	framePtr[0]        = ctx->registers[R0];
	framePtr[1]        = ctx->registers[R1];
	framePtr[2]        = ctx->registers[R2];
	framePtr[3]        = ctx->registers[R3];
	framePtr[4]        = ctx->registers[R12];
	framePtr[5]        = ctx->registers[LR];
	framePtr[6]        = ctx->registers[PC];
	framePtr[7]        = ctx->registers[XPSR] | (framePtrAlign << 9) | (1 << 24);

	if (!enforce_interrupts)
	{
		/* Enable BASEPRI masking. All interrupts lower
		 * or equal to the priority 1, i.e. interrupts
		 * below the SVCall in the vector table, are
		 * disabled. */
		__set_BASEPRI(1 << (8 - __NVIC_PRIO_BITS));
	}
	else
	{
		/* Disable BASEPRI masking. */
		__set_BASEPRI(0);
	}

#if defined BENCHMARK
	cycles.global_privileged_counter += GetCycleCounter() - cycles.handler_start_timestamp;
#endif

	asm volatile
	(
		/* Restore registers R4 to R11 from the
		 * context. */
		"ldmia   %0!, {r4-r11};"

		/* Reset the MSP to its top of stack. */
		"msr     msp, %1;"

		/* Set the PSP to the stacked frame.  */
		"msr     psp, %2;"

		/* Enable interrupts by setting the PRIMASK
                 * register to 0. */
		"cpsie   i;"

		/* The exception returns to Thread mode and uses
		 * the PSP. */
		"bx      %3;"

		/* Output operands */
		:

		/* Input operands */
		: "r" (&(ctx->registers[R4])),
		  "r" (&__StackTop),
		  "r" (frame),
		  "r" (EXC_RETURN_THREAD_MODE_PSP)

		/* Clobbers */
		: "r4", "r5", "r6",
		  /*"r7",*/ "r8", "r9",
		  "r10", "r11", "memory"
	);

	/* We should never end up here because we are in Handler mode
	 * and we have executed the BX instruction with the special
	 * value EXC_RETURN_THREAD_MODE_PSP. */
	__builtin_unreachable();
}

