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
#include "memlayout.h"
#include "stack.h"

/* Check that an address is aligned on a 4-byte boundary. */
#define IS_MISALIGNED(address) ((address) & 0x3)

/* This EXC_RETURN value allows to return to Thread mode with
 * the PSP stack. */
#define EXC_RETURN_THREAD_MODE_PSP 0xFFFFFFFD

#define EXC_RETURN_THREAD_MODE_PSP_EXTENDED 0xFFFFFFED

/*!
 * \brief Specifies whether the interrupted context is an FPU context.
 *
 *        Its initial value is 0 because the context executed after
 *        the initialization of PIP is always a context without FPU.
 */
static uint32_t previousContextUseFpu = 0;

static yield_return_code_t checkIntLevelCont(
	paddr calleePartDescAddr,
	uservalue_t userTargetInterrupt,
	uservalue_t userCallerContextSaveIndex,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	stackedContext_t *callerInterruptedContext
);

static yield_return_code_t checkCtxSaveIdxCont(
	paddr calleePartDescAddr,
	unsigned targetInterrupt,
	uservalue_t userCallerContextSaveIndex,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	stackedContext_t *callerInterruptedContext
);

static yield_return_code_t getChildPartDescCont(
	paddr callerPartDesc,
	paddr calleePartDescAddr,
	unsigned targetInterrupt,
	unsigned callerContextSaveIndex,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	stackedContext_t *callerInterruptedContext
);

static yield_return_code_t getTargetPartCtxCont(
	paddr calleePartDesc,
	paddr callerPartDesc,
	paddr calleeVidt,
	paddr callerContextSaveAddr,
	unsigned targetInterrupt,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	stackedContext_t *callerInterruptedContext
);

static yield_return_code_t saveSourcePartCtxCont(
	paddr calleePartDesc,
	paddr callerPartDesc,
	paddr callerContextSaveAddr,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	stackedContext_t *callerInterruptedContext,
	stackedContext_t *targetContext
);

static void writeContext(
	stackedContext_t *ctx,
	paddr ctxSaveAddr,
	int_mask_t flagsOnWake
);

static void loadContext(
	stackedContext_t *context,
	uint32_t enforce_interrupts
) __attribute__((noreturn));

static inline uint32_t
isNotEnoughSpace(void *start, void *end, size_t size)
{
	return ((uintptr_t) end) - ((uintptr_t) start) < size;
}

/*!
 * \brief Clear the FPSCR and all the 32-bit FPU registers.
 */
static inline void
clearFpuRegs(void)
{
	/*
	 * This memory area initialized to zero allows to quickly
	 * clear all the 32-bit FPU registers.
	 */
	static const uint32_t zeros[32] =
	{
		0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0
	};

	/*
	 * Clear the FPSCR and all the 32-bit FPU registers.
	 */
	__asm__
	(
		"vmsr fpscr, %0\n"
		"vldmia %1!, {s0-s31}\n"
		:
		: "r" (0),
		  "r" (zeros)
		:
	);
}

yield_return_code_t yieldGlue(
	stackedContext_t *context,
	paddr calleePartDescLocalId,
	uservalue_t userTargetInterrupt,
	uservalue_t userCallerContextSaveIndex,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake
) {
	resetInitialSp(context);

	return checkIntLevelCont(
		calleePartDescLocalId,
		userTargetInterrupt,
		userCallerContextSaveIndex,
		flagsOnYield,
		flagsOnWake,
		context
	);
}

static yield_return_code_t checkIntLevelCont(
	paddr calleePartDescLocalId,
	uservalue_t userTargetInterrupt,
	uservalue_t userCallerContextSaveIndex,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	stackedContext_t *callerInterruptedContext
) {
	if (!(userTargetInterrupt < VIDT_INTERRUPT_NUMBER))
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
	stackedContext_t *callerInterruptedContext
) {
	if (!(userCallerContextSaveIndex < VIDT_INTERRUPT_NUMBER))
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
	stackedContext_t *callerInterruptedContext
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
	stackedContext_t *callerInterruptedContext
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
	stackedContext_t *callerInterruptedContext
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
		((vidt_t *) callerVidtAddr)->contexts[callerContextSaveIndex];

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
	stackedContext_t *callerInterruptedContext
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

	/* Save the current interrupt number into the callee's VIDT. */
	((vidt_t *) calleeVidtAddr)->currentInterrupt = targetInterrupt;

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
	stackedContext_t *callerInterruptedContext
) {
	paddr calleeContextAddr =
		((vidt_t *) calleeVidtAddr)->contexts[targetInterrupt];

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

	int isCalleeContextMisaligned =
			IS_MISALIGNED((uintptr_t) calleeContextAddr);

	/* Check that the address where to load the context of the
	 * callee is aligned. */
	if (isCalleeContextMisaligned)
	{
		return CALLEE_CONTEXT_MISALIGNED;
	}

	stackedContext_t *targetContext =
		(stackedContext_t *) calleeContextAddr;

	paddr calleeContextBlockEndAddress =
		readBlockEndFromBlockEntryAddr(calleeContextBlockLocalId);

	/* Check that there is enough space between the address of
	 * the context of the callee and the end of the MPU region
	 * to read isBasicFrame. */
	if (isNotEnoughSpace(
		calleeContextAddr,
		calleeContextBlockEndAddress,
		sizeof(targetContext->isBasicFrame)))
	{
		return CALLEE_CONTEXT_EXCEED_BLOCK_END;
	}

	if (targetContext->isBasicFrame == 1)
	{
		/* Check that there is enough space between the
		 * address of the context of the callee and the end
		 * of the MPU region to read a basic context. */
		if (isNotEnoughSpace(
			calleeContextAddr,
			calleeContextBlockEndAddress,
			sizeof(basicContext_t)))
		{
			return CALLEE_CONTEXT_EXCEED_BLOCK_END;
		}
	}
	else if (targetContext->isBasicFrame == 0)
	{
		/* Check that there is enough space between the
		 * address of the context of the callee and the end
		 * of the MPU region to read an extended context. */
		if (isNotEnoughSpace(
			calleeContextAddr,
			calleeContextBlockEndAddress,
			sizeof(extendedContext_t)))
		{
			return CALLEE_CONTEXT_EXCEED_BLOCK_END;
		}
	}
	else
	{
		/* Unknown value. */
		return CALLEE_CONTEXT_EXCEED_BLOCK_END;
	}

	/* Sets the type of the interrupted context. */
	previousContextUseFpu =
		callerInterruptedContext->isBasicFrame == 0;

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
	stackedContext_t *callerInterruptedContext,
	stackedContext_t *targetContext
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

	int isCallerContextMisaligned =
			IS_MISALIGNED((uintptr_t) callerContextSaveAddr);

	/* Check that the address where to save the caller context
	 * is aligned. */
	if (isCallerContextMisaligned)
	{
		return CALLEE_CONTEXT_MISALIGNED;
	}

	paddr callerContextBlockEndAddress =
		readBlockEndFromBlockEntryAddr(callerContextBlockLocalId);

	if (callerInterruptedContext->isBasicFrame == 1)
	{
		/* Check that there is enough space between the
		 * address where to save the context of the caller
		 * and the end of the MPU region to write a basic
		 * context. */
		if (isNotEnoughSpace(
			callerContextSaveAddr,
			callerContextBlockEndAddress,
			sizeof(basicContext_t)))
		{
			return CALLER_CONTEXT_EXCEED_BLOCK_END;
		}
	}
	else if (callerInterruptedContext->isBasicFrame == 0)
	{
		/* Check that there is enough space between the
		 * address where to save the context of the caller
		 * and the end of the MPU region to write an
		 * extended context. */
		if (isNotEnoughSpace(
			callerContextSaveAddr,
			callerContextBlockEndAddress,
			sizeof(extendedContext_t)))
		{
			return CALLER_CONTEXT_EXCEED_BLOCK_END;
		}
	}
	else
	{
		/* Unknown value. */
		return CALLER_CONTEXT_EXCEED_BLOCK_END;
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

static inline void
writeBasicContext(
	basicContext_t *srcContext,
	basicContext_t *dstContext,
	int_mask_t     flagsOnWake
) {
	for (size_t i = 0; i < BASIC_FRAME_SIZE; i++)
	{
		dstContext->frame.registers[i] =
			srcContext->frame.registers[i];
	}

	dstContext->isBasicFrame = 1;
	dstContext->pipflags     = flagsOnWake;
}

static inline void
writeExtendedContext(
	extendedContext_t *srcContext,
	extendedContext_t *dstContext,
	int_mask_t        flagsOnWake
) {
	for (size_t i = 0; i < EXTENDED_FRAME_SIZE; i++)
	{
		dstContext->frame.registers[i] =
			srcContext->frame.registers[i];
	}

	dstContext->isBasicFrame = 0;
	dstContext->pipflags     = flagsOnWake;
}

static inline void
writeContext(
	stackedContext_t *context,
	paddr             ctxSaveAddr,
	int_mask_t        flagsOnWake
) {
	if (context->isBasicFrame)
	{
		writeBasicContext
		(
			(basicContext_t *) context,
			(basicContext_t *) ctxSaveAddr,
			flagsOnWake
		);
	}
	else
	{
		writeExtendedContext
		(
			(extendedContext_t *) context,
			(extendedContext_t *) ctxSaveAddr,
			flagsOnWake
		);
	}
}

yield_return_code_t switchContextCont(
	paddr calleePartDescGlobalId,
	int_mask_t flagsOnYield,
	stackedContext_t *ctx
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

static void __attribute__((noreturn))
loadBasicContext(
	basicContext_t *context,
	uint32_t enforce_interrupts
) {
		uint32_t forceAlign    = CCR.STKALIGN;
		uint32_t frameSize     = 0x20;
		uint32_t spMask        = ~(forceAlign << 2);
		uint32_t framePtrAlign = (context->frame.sp >> 2) & forceAlign;
		uint32_t frame         = (context->frame.sp - frameSize) & spMask;
		uint32_t *framePtr     = (uint32_t *) frame;

		framePtr[0]  = context->frame.r0;
		framePtr[1]  = context->frame.r1;
		framePtr[2]  = context->frame.r2;
		framePtr[3]  = context->frame.r3;
		framePtr[4]  = context->frame.r12;
		framePtr[5]  = context->frame.lr;
		framePtr[6]  = context->frame.pc;
		framePtr[7]  = context->frame.xpsr | (framePtrAlign << 9) | (1 << 24);

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

		if (previousContextUseFpu)
		{
			/* If the interrupted context has used FPU
			 * registers, clear it in order to avoid data
			 * leakage. */
			clearFpuRegs();
		}

		asm volatile
		(
			/* Restore registers R4 to R11 from the
			 * context. */
			"ldmia %0!, {r4-r11};"

			/* Reset the MSP to its top of stack. */
			"msr msp, %1;"

			/* Set the PSP to the stacked frame.  */
			"msr psp, %2;"

			/* Enable interrupts by setting the PRIMASK
			 * register to 0. */
			"cpsie i;"

			/* The exception returns to Thread mode and uses
			 * the PSP. */
			"bx %3;"

			/* Output operands */
			:

			/* Input operands */
			: "r" (&context->frame.r4),
			  "r" (&__pipStackTop),
			  "r" (frame),
			  "r" (EXC_RETURN_THREAD_MODE_PSP)

			/* Clobbers */
			: "r4", "r5", "r6",
			  "r7", "r8", "r9",
			  "r10", "r11", "memory"
		);

	/* We should never end up here because we are in Handler mode
	 * and we have executed the BX instruction with the special
	 * value EXC_RETURN_THREAD_MODE_PSP. */
	__builtin_unreachable();
}

static void __attribute__((noreturn))
loadExtendedContext(
	extendedContext_t *context,
	uint32_t enforce_interrupts
) {
	uint32_t forceAlign    = 1;
	uint32_t frameSize     = 0x68;
	uint32_t spMask        = ~(forceAlign << 2);
	uint32_t framePtrAlign = (context->frame.sp >> 2) & forceAlign;
	uint32_t frame         = (context->frame.sp - frameSize) & spMask;
	uint32_t *framePtr     = (uint32_t *) frame;

	framePtr[0]  = context->frame.r0;
	framePtr[1]  = context->frame.r1;
	framePtr[2]  = context->frame.r2;
	framePtr[3]  = context->frame.r3;
	framePtr[4]  = context->frame.r12;
	framePtr[5]  = context->frame.lr;
	framePtr[6]  = context->frame.pc;
	framePtr[7]  = context->frame.xpsr | (framePtrAlign << 9) | (1 << 24);
	framePtr[8]  = context->frame.s0;
	framePtr[9]  = context->frame.s1;
	framePtr[10] = context->frame.s2;
	framePtr[11] = context->frame.s3;
	framePtr[12] = context->frame.s4;
	framePtr[13] = context->frame.s5;
	framePtr[14] = context->frame.s6;
	framePtr[15] = context->frame.s7;
	framePtr[16] = context->frame.s8;
	framePtr[17] = context->frame.s9;
	framePtr[18] = context->frame.s10;
	framePtr[19] = context->frame.s11;
	framePtr[20] = context->frame.s12;
	framePtr[21] = context->frame.s13;
	framePtr[22] = context->frame.s14;
	framePtr[23] = context->frame.s15;
	framePtr[24] = context->frame.fpscr;

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

	asm volatile
	(
		/* Restore registers s16 to s31 from the
		 * context. */
		"vldmia %0!, {s16-s31};"

		/* Restore registers R4 to R11 from the
		 * context. */
		"ldmia %1!, {r4-r11};"

		/* Reset the MSP to its top of stack. */
		"msr msp, %2;"

		/* Set the PSP to the stacked frame.  */
		"msr psp, %3;"

		/* Enable interrupts by setting the PRIMASK
		 * register to 0. */
		"cpsie i;"

		/* The exception returns to Thread mode and uses
		 * the PSP. */
		"bx %4;"

		/* Output operands */
		:

		/* Input operands */
		: "r" (&context->frame.s16),
		  "r" (&context->frame.r4),
		  "r" (&__pipStackTop),
		  "r" (frame),
		  "r" (EXC_RETURN_THREAD_MODE_PSP_EXTENDED)

		/* Clobbers */
		: "r4", "r5", "r6",
		  "r7", "r8", "r9",
		  "r10", "r11", "s16",
		  "s17", "s18", "s19",
		  "s20", "s21", "s22",
		  "s23", "s24", "s25",
		  "s26", "s27", "s28",
		  "s29", "s30", "s31",
		  "memory"
	);

	/* We should never end up here because we are in Handler mode
	 * and we have executed the BX instruction with the special
	 * value EXC_RETURN_THREAD_MODE_PSP_EXTENDED. */
	__builtin_unreachable();
}

static void __attribute__((noreturn))
loadContext(
	stackedContext_t *context,
	uint32_t          enforce_interrupts
) {
	if (context->isBasicFrame)
	{
		loadBasicContext
		(
			(basicContext_t *) context,
			enforce_interrupts
		);
	}
	else
	{
		loadExtendedContext
		(
			(extendedContext_t *) context,
			enforce_interrupts
		);
	}

	__builtin_unreachable();
}
