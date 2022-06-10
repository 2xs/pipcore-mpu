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

#include "nrf52.h"
#include "stdio.h"
#include "context.h"
#include "yield_c.h"
#include "pip_interrupt_calls.h"
#include "mal.h"
#include "scs.h"
#include "mpu.h"
#include "stack.h"

/*!
 * \def MMFSR_CLEAR_MASK
 *
 * \brief A mask to clear all flags of the MMFSR register.
 */
#define MMFSR_CLEAR_MASK 0xbb

extern void __attribute__((noreturn))
Kernel_Panic(stackedContext_t *context)
{
	(void) context;
	for (;;);
}

/*!
 * \brief The generic interrupt handler propagates an interrupt to the
 *        root partition.
 *
 * \param stackedContext The context stacked by the Interrupt_Handler
 *        entry point.
 *
 * \see The calling code is in the exception_entry.S file.
 */
extern void __attribute__((noreturn))
Interrupt_Handler_C(stackedContext_t *context)
{
	uint32_t currentInterrupt = ICSR.VECTACTIVE;

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

	resetInitialSp(context);

	/* We try to propagate the interrupt to the root partition by
	 * saving the context of the interrupted partition at the address
	 * found at the saveIndex in its VIDT. Then, we restore the
	 * context pointed to by the address found at the index
	 * corresponding to the interrupt number in the VIDT of the
	 * root partition. */
	yield_return_code_t yieldErrorCode = getSourcePartVidtCont(
		rootPartDesc,
		interruptedPartDesc,
		currentInterrupt,
		saveIndex,
		interruptedPartIntState,
		interruptedPartIntState,
		context
	);

	switch (yieldErrorCode)
	{
		case CALLER_VIDT_IS_NULL:
		case CALLER_VIDT_IS_NOT_PRESENT:
		case CALLER_VIDT_IS_NOT_ACCESSIBLE:
		case CALLER_VIDT_BLOCK_TOO_SMALL:
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
				currentInterrupt,
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

	Kernel_Panic(context);
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
extern void __attribute__((noreturn))
propagateFault(
	paddr          currentPartDesc,
	unsigned       targetInterrupt,
	unsigned       saveIndex,
	int_mask_t     flagOnYield,
	int_mask_t     flagOnWake,
	stackedContext_t *context
) {
	/* We try to propagate the fault to the parent partition of the
	 * one that has faulted by saving its context at the address
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
		case CALLER_VIDT_BLOCK_TOO_SMALL:
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
			 * that either the root partition has faulted,
			 * or that one of its children has faulted and
			 * could not handle the fault. */
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

	Kernel_Panic(context);
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
extern void __attribute__((noreturn))
Fault_Handler_C(stackedContext_t *context)
{
	uint32_t currentInterrupt = ICSR.VECTACTIVE;

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

	resetInitialSp(context);

	printf("The current partition (%p) has faulted...\n", currentPartDesc);

	/* Propagate the fault to the parent of the faulted partition. */
	propagateFault(currentPartDesc, currentInterrupt, saveIndex,
		interruptedPartIntState, interruptedPartIntState, context);

	/* We should never end up here because the propagateFault never
	 * return to the caller. */
	__builtin_unreachable();
}

/*!
 * \brief The enumeration of all possible MemManage
 *        exception causes.
 */
typedef enum memFaultCause_u
{
	/*!
	 * \brief A MemManage caused by a DACCVIOL.
	 */
	DACCVIOL,
	/*!
	 * \brief A MemManage caused by a IACCVIOL
	 *        of a 16-bit instruction.
	 */
	IACCVIOL16,
	/*!
	 * \brief A MemManage caused by a IACCVIOL
	 *        of a 32-bit instruction.
	 */
	IACCVIOL32,
	/*!
	 * \brief A MemManage caused by an unknown
	 *        cause.
	 */
	UNKNOWN
} memFaultCause_t;

/*!
 * \brief Retrive both the cause and the address of the
 *        MemManage exception.
 *
 * \param ctx The stacked context of the partition that cause
 *        the MemManage exception.
 *
 * \param cause The address where to store the cause of the
 *        MemManage exception.
 *
 * \param addr The address where to store the address of the
 *        MemManage exception.
 */
static inline void
getFaultedAddress(stackedContext_t *ctx, void **addr, memFaultCause_t *cause)
{
	uint16_t halfword;
	uint8_t bits;

	if (CFSR.MMFSR.DACCVIOL && CFSR.MMFSR.MMARVALID)
	{
		/* Armv7-M Architecture - Reference Manual
		 * B1.5.14 Fault behavior
		 *
		 * ``
		 * MPU violation or fault caused by an explicit
		 * memory access. The processor writes the data
		 * address of the load or store to the MemManage
		 * Address Register.
		 * ``
		 *
		 * The faulted address is stored in the MMFAR
		 * register because the MMARVALID bit is set.
		 */
		*addr = (void *) MMFAR.ADDRESS;
		*cause = DACCVIOL;
	}
	else if (CFSR.MMFSR.IACCVIOL)
	{
		/* Armv7-M Architecture - Reference Manual
		 * B1.5.14 Fault behavior
		 *
		 * ``
		 * MemManage fault on instruction access:
		 *
		 * MPU violation or fault caused by an
		 * instruction fetch, or an instruction fetch
		 * from XN memory when there is no MPU. The
		 * fault occurs only if the processor attempts
		 * to execute the instruction. The processor
		 * does not update the MemManage Address
		 * Register.
		 * ``
		 *
		 * The faulted address is the address of the
		 * instruction stored in the PC register, saved
		 * in the stacked context.
		 */
		if (ctx->isBasicFrame)
		{
			*addr = (void *) ctx->basicFrame.pc;
		}
		else
		{
			*addr = (void *) ctx->extendedFrame.pc;
		}

		/* Armv7-M Architecture - Reference Manual
		 * A5.1 Thumb instruction set encoding
		 *
		 * ``
		 * If bits [15:11] of the halfword being
		 * decoded take any of the following values,
		 * the halfword is the first halfword of a
		 * 32-bit instruction: 0b11101, 0b11110,
		 * 0b11111.
		 * ``
		 */
		halfword = *((uint16_t *) *addr);

		bits = (halfword >> 11) & 0x1f;

		if (bits == 0x1d || bits == 0x1e || bits == 0x1f)
		{
			*cause =  IACCVIOL32;
		}
		else
		{
			*cause = IACCVIOL16;
		}
	}
	else
	{
		*addr = (void *) 0;
		*cause = UNKNOWN;
	}
}

/*!
 * \brief Check that a virtual MPU register contains the
 *        address that caused a MemManage.
 *
 * \param addr The address that caused the MemManage.
 *
 * \param idx The index of the virtual MPU register.
 *
 * \return 1 if the faulted address is contained, 0 otherwise.
 */
static inline int
isMappedInVirtualMpu(void *addr, size_t idx)
{
	void *saddr, *eaddr;
	BlockEntry_t *block;
	block_t *range;
	PDTable_t *pd;

	pd = getCurPartition();
	block = pd->mpu[idx];

	if (block == NULL)
	{
		return 0;
	}

	if (!block->present)
	{
		return 0;
	}

	range = &block->blockrange;
	saddr = range->startAddr;
	eaddr = range->endAddr;

	if (saddr > addr)
	{
		return 0;
	}

	if (addr > eaddr)
	{
		return 0;
	}

	return 1;
}

/*!
 * \brief Check that a physical MPU register contains the
 *        address that caused a MemManage.
 *
 * \param addr The address that caused the MemManage.
 *
 * \param idx The index of the physical MPU register.
 *
 * \return 1 if the faulted address is contained, 0 otherwise.
 */
static inline int
isMappedInPhysicalMpu(void *addr, size_t idx)
{
	void *saddr, *eaddr;

	saddr = readPhysicalMPUStartAddr(idx);
	eaddr = readPhysicalMPUEndAddr(idx);

	return ((saddr <= addr) && (addr <= eaddr));
}

/*!
 * \brief Find the virtual MPU index containing the address
 *        that caused the MemManage.
 *
 * \param addr The address that caused the MemManage.
 *
 * \param idx The address where to store the virtual MPU
 *        index found.
 *
 * \return 1 if the function succeed, 0 otherwise.
 */
static inline int
findMpuIndex(void *addr, size_t *idx)
{
	size_t i;

	for (i = 0; i < MPU_NUM_REGIONS - 2; i++)
	{
		if (isMappedInVirtualMpu(addr, i))
		{
			*idx = i;

			return 1;
		}
	}

	return 0;
}

/*!
 * \brief Reconfigure the physical MPU in order to allow a
 *        legitimate address access.
 *
 * \param addr The legitimate address to allow.
 *
 * \param vidx The virtual MPU index containing the faulted
 *        address.
 *
 * \param pidx The physical MPU index containing the faulted
 *        the faulted address.
 */
static inline void
reconfigureMpu(void *addr, size_t vidx, size_t pidx)
{
	PDTable_t *pd;

	pd = getCurPartition();
	configure_LUT_entry(pd->LUT, pidx, pd->mpu[vidx], addr);
	mpu_configure_from_LUT(pd->LUT);
}

/*!
 * \brief Although the MemManage exception is a fault, it has
 *        its own handler. The reason for this is that a
 *        MemManage exception can be legitimately raised as part
 *        of the MPU partial block configuration. In the case of
 *        an illegal access, the Fault_Handler is called.
 *
 * \param ctx The context stacked by the MemManage_Handler
 *        entry point.
 *
 * \see The calling code is in the exception_entry.S file.
 */
extern void
MemManage_Handler_C(stackedContext_t *ctx)
{
	memFaultCause_t cause;
	static int flag = 0;
	int mapped, mapped2;
	void *addr, *addr2;
	size_t vidx, pidx;

	getFaultedAddress(ctx, &addr, &cause);

	/* Clear all MMFSR flags by writing ones. */
	CFSR.MMFSR.as_uint8_t &= MMFSR_CLEAR_MASK;

	switch (cause)
	{
		case DACCVIOL:
		{
			/* Try to find a virtual MPU region
			 * containing the faulted address. */
			if (!findMpuIndex(addr, &vidx))
			{
				goto error;
			}

			/* Check that the faulted address is
			 * not already in the physical MPU. */
			if (isMappedInPhysicalMpu(addr, vidx))
			{
				goto error;
			}

			if (flag)
			{
				pidx = MPU_NUM_REGIONS - 1;
			}
			else
			{
				pidx = vidx;
			}

			reconfigureMpu(addr, vidx, pidx);

			flag ^= 1;

			break;
		}
		case IACCVIOL16:
		{
			/* Try to find a virtual MPU region
			 * containing the faulted address. */
			if (!findMpuIndex(addr, &vidx))
			{
				goto error;
			}

			/* Check that the faulted address is
			 * not already in the physical MPU. */
			if (isMappedInPhysicalMpu(addr, vidx))
			{
				goto error;
			}

			if (flag)
			{
				pidx = MPU_NUM_REGIONS - 2;
			}
			else
			{
				pidx = vidx;
			}

			reconfigureMpu(addr, vidx, pidx);

			flag ^= 1;

			break;
		}
		case IACCVIOL32:
		{
			/* Calculate the address of the second
			 * half word of the instruction. */
			addr2 = (void *)((uintptr_t) addr + 2);

			/* Try to find a virtual MPU region
			 * containing the address of the first
			 * half word of the instruction. */
			if (!findMpuIndex(addr, &vidx))
			{
				goto error;
			}

			/* Check that the address of the second
			 * half word of the instruction is
			 * contained in the virtual block found. */
			if (!isMappedInVirtualMpu(addr2, vidx))
			{
				goto error;
			}

			pidx = MPU_NUM_REGIONS - 2;

			/* Check that the address of the first
			 * half word of the instruction is
			 * mapped into the physical MPU. */
			mapped = isMappedInPhysicalMpu(addr, vidx);

			/* Check that the address of the second
			 * half word of the instruction is
			 * mapped into the physical MPU. */
			mapped2 = isMappedInPhysicalMpu(addr2, pidx);

			/* Check that the two addresses are
			 * not already mapped in the physical
			 * MPU. If this is the case, it is a
			 * hard fault. */
			if (mapped && mapped2)
			{
				goto error;
			}

			/* Check that the address of the first
			 * half word of the instruction is
			 * mapped. */
			if (!mapped)
			{
				reconfigureMpu(addr, vidx, vidx);
			}

			/* Check that the address of the second
			 * half word of the instruction is
			 * mapped. */
			if (!mapped2)
			{
				reconfigureMpu(addr2, vidx, pidx);
			}

			break;
		}
		default:
		{
			goto error;
		}
	}

	__enable_irq();

	/* Returns to the faulted instruction. */
	return;

error:
	Fault_Handler_C(ctx);
}
