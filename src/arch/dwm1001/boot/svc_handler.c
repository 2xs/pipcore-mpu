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
#include "exception_handlers.h"
#include "Services.h"
#include "nrf52.h"
#include "core_cm4.h"
#include "pip_debug.h"
#include "context.h"
#include "yield_c.h"
#include "ADT.h"

/* The MSP top of stack defined in the link script. */
extern uint32_t __StackTop;

extern void SVC_Handler (void);

/*!
 * \brief Enumeration of the SVC numbers
 */
typedef enum svc_number_e
{
	SVC_NUMBER_CREATE_PARTITION    = 0 , /*!< The createPartition SVC number. */
	SVC_NUMBER_CUT_MEMORY_BLOCK    = 1 , /*!< The cutMemoryBlock SVC number. */
	SVC_NUMBER_MERGE_MEMORY_BLOCK  = 2 , /*!< The mergeMemoryBlocks SVC number. */
	SVC_NUMBER_PREPARE             = 3 , /*!< The prepare SVC number. */
	SVC_NUMBER_ADD_MEMORY_BLOCK    = 4 , /*!< The addMemoryBlock SVC number. */
	SVC_NUMBER_REMOVE_MEMORY_BLOCK = 5 , /*!< The removeMemoryBlock SVC number. */
	SVC_NUMBER_DELETE_PARTITION    = 6 , /*!< The deletePartition SVC number. */
	SVC_NUMBER_COLLECT             = 7 , /*!< The collect SVC number. */
	SVC_NUMBER_MAP_MPU             = 8 , /*!< The mapMPU SVC number. */
	SVC_NUMBER_READ_MPU            = 9 , /*!< The readMPU SVC number. */
	SVC_NUMBER_FIND_BLOCK          = 10, /*!< The findBlock SVC number. */
	SVC_NUMBER_SET_VIDT            = 11, /*!< The setVIDT SVC number. */
	SVC_NUMBER_YIELD               = 12  /*!< The yield SVC number. */
} svc_number_t;

/*!
 * \brief The SVC handler in the ISR vector disables interrupts, stacks
 *        registers, and calls the SVC_Handler_Main function.
 */
__attribute__((section(".after_vectors"), weak, naked))
void SVC_Handler (void)
{
	asm volatile
	(
		".global SVC_Handler_Main;"

		/* Disable interrupts. */
		"cpsid   i;"

		/* The processor necessarily runs the partition code in
		 * unprivileged Thread mode and uses the PSP. Therefore,
		 * it is not necessary to test the SPSEL bit. */
		"mrs     r1, psp;"

		/* Retrieves the SVC number encoded on the last byte of
		 * the instruction in the PC register  pushed onto the
		 * stack. */
		"ldr     r0, [r1, #24];"
		"ldrb    r0, [r0, #-2];"

		/* Copy the initial value of the PSP into R3. */
		"mov     r3, r1;"

		/* Push the registers R3 to R11 onto the stack. */
		"stmdb   r1!, {r3-r11};"

		/* Branch to the SVC_Handler_Main function without
		 * storing the return address in LR. This way, the
		 * SVC_Handler_Main function will leave the execption
		 * when it returns. */
		"b       SVC_Handler_Main;"
	);
}

/*!
 * \brief Call the PIP service associated with the SVC number.
 * \param svc_number The CSV number associated with the service to be
 *        called.
 * \param context The context stacked on the caller's stack.
 */
void SVC_Handler_Main(uint32_t svc_number, context_svc_t *context)
{
	switch (svc_number)
	{
		case SVC_NUMBER_CREATE_PARTITION:
			context->registers[R0] = (uint32_t) createPartition(
				(paddr) context->registers[R0]
			);
			break;

		case SVC_NUMBER_CUT_MEMORY_BLOCK:
			context->registers[R0] = (uint32_t) cutMemoryBlock(
				(paddr) context->registers[R0],
				(paddr) context->registers[R1],
				(Coq_index) context->registers[R2]
			);
			break;

		case SVC_NUMBER_MERGE_MEMORY_BLOCK:
			context->registers[R0] = (uint32_t) mergeMemoryBlocks(
				(paddr) context->registers[R0],
				(paddr) context->registers[R1],
				(Coq_index) context->registers[R2]
			);
			break;

		case SVC_NUMBER_PREPARE:
			context->registers[R0] = (uint32_t) prepare(
				(paddr) context->registers[R0],
				(Coq_index) context->registers[R1],
				(paddr) context->registers[R2]
			);
			break;

		case SVC_NUMBER_ADD_MEMORY_BLOCK:
			context->registers[R0] = (uint32_t) addMemoryBlock(
				(paddr) context->registers[R0],
				(paddr) context->registers[R1],
				(bool) ((context->registers[R2] >> 2) & 1),
				(bool) ((context->registers[R2] >> 1) & 1),
				(bool) context->registers[R2] & 1
			);
			break;

		case SVC_NUMBER_REMOVE_MEMORY_BLOCK:
			context->registers[R0] = (uint32_t) removeMemoryBlock(
				(paddr) context->registers[R0]
			);
			break;

		case SVC_NUMBER_DELETE_PARTITION:
			context->registers[R0] = (uint32_t) deletePartition(
				(paddr) context->registers[R0]
			);
			break;

		case SVC_NUMBER_COLLECT:
			context->registers[R0] = (uint32_t) collect(
				(paddr) context->registers[R0]
			);
			break;

		case SVC_NUMBER_MAP_MPU:
			context->registers[R0] = (uint32_t) mapMPU(
				(paddr) context->registers[R0],
				(paddr) context->registers[R1],
				(Coq_index) context->registers[R2]
			);
			break;

		case SVC_NUMBER_READ_MPU:
			context->registers[R0] = (uint32_t) readMPU(
				(paddr) context->registers[R0],
				(Coq_index) context->registers[R1]
			);
			break;

		case SVC_NUMBER_FIND_BLOCK:
		{
			// Note as the result is in memory, the parameters are passed with R1 and R2, not RO
			blockOrError block_found = findBlock(
				(paddr) context->registers[R0],
				(paddr) context->registers[R1]
			);

			// Fill R0-R3: the access permissions and accessible bit are squeezed into R3
			context->registers[R0] = (uint32_t) block_found.blockAttr.blockentryaddr;
			context->registers[R1] = (uint32_t) block_found.blockAttr.blockrange.startAddr; // displays start and end
			context->registers[R2] = (uint32_t) block_found.blockAttr.blockrange.endAddr;
			context->registers[R3] = (uint32_t) block_found.blockAttr.read |
						 (uint32_t) block_found.blockAttr.write << 1 |
						 (uint32_t) block_found.blockAttr.exec << 2 |
						 (uint32_t) block_found.blockAttr.accessible << 3;
			break;
		}

		case SVC_NUMBER_SET_VIDT:
			context->registers[R0] = setVIDT(
				(paddr) context->registers[R0],
				(paddr) context->registers[R1]
			);
			break;

		case SVC_NUMBER_YIELD:
			context->registers[R0] = (uint32_t) yieldGlue(
				context,
				(paddr) context->registers[R0],
				context->registers[R1],
				context->registers[R2],
				context->registers[R3],
				context->registers[R4]
			);
			break;

#ifdef UNIT_TESTS
		case 127: // Enable Privileged mode !TODO!: to remove with system calls in SVC instead
			__set_CONTROL( __get_CONTROL( ) & ~CONTROL_nPRIV_Msk ) ;
			break;

		case 128: // Disable Privileged mode !TODO!: to remove with system calls in SVC instead
			__set_CONTROL(__get_CONTROL() | CONTROL_nPRIV_Msk ); // switch to unprivileged Thread Mode
			__DMB();
			__ISB();
			__DSB();
			break;
#endif // UNIT_TESTS

		default:
			/* Unknown SVC */
			break;
	}

	__enable_irq();
}
