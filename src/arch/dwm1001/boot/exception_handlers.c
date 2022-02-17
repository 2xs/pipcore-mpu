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

#include <stdio.h>

#include "nrf52.h"
#include "semihosting.h"
#include "trace.h"
#include "context.h"
#include "yield_c.h"
#include "pip_interrupt_calls.h"
#include "mal.h"
#include "scs.h"
#include "mpu.h"

/*!
 * \def UNREACHABLE_ADDRESS
 *
 * \brief An unreachable address in ARMv7-M.
 */
#define UNREACHABLE_ADDRESS 0xffffffff

/*!
 * \def MMFSR_CLEAR_MASK
 *
 * \brief A mask to clear all flags of the MMFSR register.
 */
#define MMFSR_CLEAR_MASK 0xbb

/*!
 * \brief The generic interrupt handler propagates an interrupt to the
 *        root partition.
 *
 * \param stackedContext The context stacked by the Interrupt_Handler
 *        entry point.
 *
 * \see The calling code is in the exception_entry.S file.
 */
void __attribute__((section(".after_vectors"), noreturn))
Interrupt_Handler_C(stacked_context_t *stackedContext)
{
	user_context_t context;

	/* Copy of the context stacked by the entry point. */
	for (size_t i = 0; i < CONTEXT_REGISTER_NUMBER; i++)
	{
		context.registers[i] = stackedContext->registers[i];
	}

	/* Save the value of the stack before the interrupt. */
	uint32_t forceAlign   = CCR.STKALIGN;
	uint32_t spMask       = ((context.registers[XPSR] >> 9) & forceAlign) << 2;
	context.registers[SP] = (context.registers[SP] + FRAME_SIZE) | spMask;
	context.valid         = CONTEXT_VALID_VALUE;

	paddr rootPartDesc = getRootPartition();
	paddr interruptedPartDesc = getCurPartition();
	int_mask_t interruptedPartIntState = getSelfIntState();
	uint32_t saveIndex;

	if (interruptedPartIntState == 0)
	{
		saveIndex = CLI_SAVE_INDEX;
	}
	else
	{
		saveIndex = STI_SAVE_INDEX;
	}

	/* We try to propagate the interrupt to the root partition by
	 * saving the context of the interrupted partition at the address
	 * found at the saveIndex in its VIDT. Then, we restore the
	 * context pointed to by the address found at the index
	 * corresponding to the interrupt number in the VIDT of the
	 * root partition. */
	yield_return_code_t yieldErrorCode = getSourcePartVidtCont(
		rootPartDesc,
		interruptedPartDesc,
		ICSR.VECTACTIVE,
		saveIndex,
		interruptedPartIntState,
		interruptedPartIntState,
		&context
	);

	switch (yieldErrorCode)
	{
		case CALLER_VIDT_IS_NULL:
		case CALLER_VIDT_IS_NOT_PRESENT:
		case CALLER_VIDT_IS_NOT_ACCESSIBLE:
		case CALLER_CONTEXT_BLOCK_NOT_FOUND:
		case CALLER_CONTEXT_BLOCK_IS_NOT_PRESENT:
		case CALLER_CONTEXT_BLOCK_IS_NOT_ACCESSIBLE:
		case CALLER_CONTEXT_BLOCK_IS_NOT_WRITABLE:
		case CALLER_CONTEXT_EXCEED_BLOCK_END:
		case CALLER_CONTEXT_MISALIGNED:
		{
			/* An error occurred while saving the
			 * interrupted context. This is either due to a
			 * problem with the block containing the VIDT or
			 * to an invalid save address. In both cases,
			 * the save of the interrupted context is
			 * abandoned and the context of the root
			 * partition corresponding to the interrupt
			 * number is restored. */
			getTargetPartVidtCont(
				rootPartDesc,
				interruptedPartDesc,
				NULL,
				ICSR.VECTACTIVE,
				0,
				0,
				NULL
			);

			break;
		}
		default:
		{
			break;
		}
	}

	/* We end up here if PIP is in an unrecoverable state. */
	printf("PIP: UNRECOVERABLE ERROR!\n");
	for (;;);
}

/*!
 * \brief This function propagate the fault of a partition to its
 *        parent.
 *
 * \param currentPartDesc The partition descriptor of the faulted
 *        partition.
 *
 * \param targetInterrupt The fault number.
 *
 * \param saveIndex The index in the VIDT of the faulted partition where
 *        to save its context.
 *
 * \param flagOnYield The state the faulted partition wishes to be on
 *        yield.
 *
 * \param flagOnWake The state the faulted partition wishes to be on
 *        wake.
 *
 * \param context The context of the faulted partition.
 */
void __attribute__((section(".after_vectors"), noreturn))
propagateFault(
	paddr          currentPartDesc,
	unsigned       targetInterrupt,
	unsigned       saveIndex,
	int_mask_t     flagOnYield,
	int_mask_t     flagOnWake,
	user_context_t *context
) {
	/* We try to propagate the fault to the parent partition of the
	 * one that has failed by saving its context at the address
	 * found at the saveIndex in its VIDT. Then, we restore the
	 * context pointed to by the address found at the index
	 * corresponding to the fault number in the VIDT of the parent
	 * partition. */
	yield_return_code_t yieldErrorCode = getParentPartDescCont(
		currentPartDesc,
		targetInterrupt,
		saveIndex,
		flagOnYield,
		flagOnWake,
		context
	);

	switch (yieldErrorCode)
	{
		case CALLER_VIDT_IS_NULL:
		case CALLER_VIDT_IS_NOT_PRESENT:
		case CALLER_VIDT_IS_NOT_ACCESSIBLE:
		case CALLER_CONTEXT_BLOCK_NOT_FOUND:
		case CALLER_CONTEXT_BLOCK_IS_NOT_PRESENT:
		case CALLER_CONTEXT_BLOCK_IS_NOT_ACCESSIBLE:
		case CALLER_CONTEXT_BLOCK_IS_NOT_WRITABLE:
		case CALLER_CONTEXT_EXCEED_BLOCK_END:
		case CALLER_CONTEXT_MISALIGNED:
		{
			/* An error occurred while saving the
			 * interrupted context. This is either due to a
			 * problem with the block containing the VIDT or
			 * to an invalid save address. In both cases,
			 * the save of the interrupted context is
			 * abandoned and the context of the parent
			 * partition corresponding to the fault number
			 * is restored. */
			getTargetPartVidtCont(
				readPDParent(currentPartDesc),
				currentPartDesc,
				NULL,
				targetInterrupt,
				flagOnYield,
				flagOnWake,
				NULL
			);

			break;
		}
		case CALLEE_IS_PARENT_OF_ROOT:
		{
			/* We tried to propagate the fault to the parent
			 * partition of the root partition. This means
			 * that either the root partition has failed, or
			 * that one of its children has failed and could
			 * not handle the fault. */
			printf("PIP: The root partition has faulted!\n");

			break;
		}
		default:
		{
			paddr parentPartDec = readPDParent(currentPartDesc);

			printf("The parent partition (%p) cannot handle "
				"the fault.\n Propagating a double "
				"fault...", parentPartDec);

			/* The parent partition of the faulted partition
			 * could not manage the fault. Propagation of a
			 * double fault to the grandparent. */
			propagateFault(
				parentPartDec,
				targetInterrupt,
				DOUBLE_FAULT_LEVEL,
				flagOnYield,
				flagOnWake,
				context
			);

			break;
		}
	}

	/* We end up here if PIP is in an unrecoverable state. */
	printf("PIP: UNRECOVERABLE ERROR!\n");
	for (;;);
}

/*!
 * \brief The generic fault handler propagates the fault of a partition
 *        to its parent. If the index corresponding to the fault number
 *        in the parent's VIDT contains a null value or a pointer to an
 *        invalid context, the fault is propagated to the grandparent,
 *        up to the root partition. If the root partition cannot handle
 *        the fault, PIP is in an unrecoverable state.
 *
 * \param stackedContext The context stacked by the Fault_Handler entry
 *        point.
 *
 * \see The calling code is in the exception_entry.S file.
 */
void __attribute__((section(".after_vectors"), noreturn))
Fault_Handler_C(stacked_context_t *stackedContext)
{
	user_context_t context;

	/* Copy of the context stacked by the entry point. */
	for (size_t i = 0; i < CONTEXT_REGISTER_NUMBER; i++)
	{
		context.registers[i] = stackedContext->registers[i];
	}

	/* Save the value of the stack before the fault. */
	uint32_t forceAlign   = CCR.STKALIGN;
	uint32_t spMask       = ((context.registers[XPSR] >> 9) & forceAlign) << 2;
	context.registers[SP] = (context.registers[SP] + FRAME_SIZE) | spMask;
	context.valid         = CONTEXT_VALID_VALUE;

	paddr currentPartDesc = getCurPartition();
	int_mask_t interruptedPartIntState = getSelfIntState();
	uint32_t saveIndex;

	if (interruptedPartIntState == 0)
	{
		saveIndex = CLI_SAVE_INDEX;
	}
	else
	{
		saveIndex = STI_SAVE_INDEX;
	}

	printf("The current partition (%p) has faulted...\n", currentPartDesc);

	/* Propagate the fault to the parent of the faulted partition. */
	propagateFault(currentPartDesc, ICSR.VECTACTIVE, saveIndex,
		interruptedPartIntState, interruptedPartIntState, &context);

	/* We should never end up here because the propagateFault never
	 * return to the caller. */
	__builtin_unreachable();
}

/*!
 * \brief Although the MemManage exception is a fault, it has its own
 *        handler. The reason for this is that a MemManage exception can
 *        be legitimately raised as part of the MPU partial block
 *        configuration. In the case of an illegal access, the
 *        Fault_Handler is called.
 *
 * \param stackedContext The context stacked by the MemManage_Handler
 *        entry point.
 *
 * \see The calling code is in the exception_entry.S file.
 */
void __attribute__((section(".after_vectors")))
MemManage_Handler_C(stacked_context_t *stackedContext)
{
	uint32_t faultedAddress;

	if (CFSR.MMFSR.DACCVIOL && CFSR.MMFSR.MMARVALID)
	{
		/* The MemManage fault was triggered because of an MPU
		 * violation or fault caused by an explicit memory
		 * access. The faulted address is stored in the MMFAR
		 * register because the MMARVALID bit is set. */
		faultedAddress = MMFAR.ADDRESS;
	}
	else if (CFSR.MMFSR.IACCVIOL)
	{
		/* The MemManage fault was triggered because of an MPU
		 * violation or fault caused by an instruction fetch,
		 * or an instruction fetch from XN memory when there is
		 * no MPU. The faulted address is stored in the PC
		 * register of the stacked context. */
		faultedAddress = stackedContext->registers[PC];
	}
	else
	{
		/* All other MemManage faults are not due to partial
		 * path configuration. We set the faultedAddress to an
		 * inaccessible address to avoid searching for a valid
		 * block in the MPU. */
		faultedAddress = UNREACHABLE_ADDRESS;
	}

	/* Clear all MMFSR flags by writing ones. */
	CFSR.MMFSR.as_uint8_t &= MMFSR_CLEAR_MASK;

	if (faultedAddress != UNREACHABLE_ADDRESS)
	{
		PDTable_t *currentPartDesc = (PDTable_t *) getCurPartition();

		for (size_t i = 0; i < MPU_NUM_REGIONS; i++)
		{
			BlockEntry_t *currentBlock = currentPartDesc->mpu[i];

			if (!currentBlock->present)
			{
				/* We go to the next MPU block if the
				 * current block has not the present
				 * flag. */
				continue;
			}

			block_t *currentBlockRange = &currentBlock->blockrange;

			uint32_t startAddress = (uint32_t) currentBlockRange->startAddr;
			uint32_t endAddress   = (uint32_t) currentBlockRange->endAddr;

			if (startAddress > faultedAddress)
			{
				/* We go to the next MPU block if the
				 * current block start address is
				 * greater than or equal the faulted
				 * address. */
				continue;
			}

			if (faultedAddress > endAddress)
			{
				/* We go to the next MPU block if the
				 * current block end address is less
				 * than or equal the faulted address. */
				continue;
			}

			uint32_t physicalMpuStartAddress =
					(uint32_t) readPhysicalMPUStartAddr(i);

			uint32_t physicalMpuEndAddress =
					(uint32_t) readPhysicalMPUEndAddr(i);

			if (physicalMpuStartAddress <= faultedAddress &&
				faultedAddress <= physicalMpuEndAddress)
			{
				/* The address that caused a fault was
				 * in a physical MPU block. This is a
				 * real MPU fault. */
				break;
			}
			else
			{
				/* The address that caused a fault was
				 * not in a physical MPU block. We must
				 * reconfigure the MPU regions to allow
				 * access to the faulty address. */

				configure_LUT_entry(currentPartDesc->LUT, i,
					currentBlock, (uint32_t *) faultedAddress);

				mpu_configure_from_LUT(currentPartDesc->LUT);

				__enable_irq();

				/* Return to the instruction that
				 * caused the fault. */
				return;
			}
		}
	}

#if !defined(UNIT_TESTS)

	/* Call the fault handler if it is a real MemManage fault. */
	Fault_Handler_C(stackedContext);

	/* We should never end up here because the Fault_Handler_C never
	 * return to the caller. */
	__builtin_unreachable();

#else

	uint32_t* canary = (uint32_t*) 0x20001500;

	*canary = 0xDEADBEEF;

	printf("\r\nNew canary=%x\n", *canary);

	stackedContext->registers[PC] += 2;

	printf("\r\nBranch to PC=%x\r\n", stackedContext->registers[PC]);

#endif
}
