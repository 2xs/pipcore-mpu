/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2022)                */
/*  Copyright (C) 2020-2022 Orange                                             */
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

#include "Services.h"
#include "nrf52.h"
#include "core_cm4.h"
#include "pip_debug.h"
#include "context.h"
#include "yield_c.h"
#include "pip_interrupt_calls.h"
#include "ADT.h"
#include "accessor.h"
#include "stdio.h"

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
	SVC_NUMBER_YIELD               = 12, /*!< The yield SVC number. */
	SVC_NUMBER_GET_INT_STATE       = 13, /*!< The getIntState SVC number. */
	SVC_NUMBER_GET_SELF_INT_STATE  = 14, /*!< The getSelfIntState SVC number. */
	SVC_NUMBER_SET_INT_STATE       = 15, /*!< The setIntState SVC number. */
	SVC_NUMBER_IN                  = 16, /*!< The in SVC number. */
	SVC_NUMBER_OUT                 = 17  /*!< The out SVC number. */
} svc_number_t;

/*!
 * \brief Call the PIP service associated with the SVC number.
 * \param svc_number The SVC number associated with the service to be
 *        called.
 * \param context The context stacked on the caller's stack.
 */
void SVC_Handler_C(stackedContext_t *context)
{
	uint32_t pc, *r0, *r1, *r2, *r3, *r4;

	if (context->isBasicFrame)
	{
		pc = context->basicFrame.pc;
		r0 = &context->basicFrame.r0;
		r1 = &context->basicFrame.r1;
		r2 = &context->basicFrame.r2;
		r3 = &context->basicFrame.r3;
		r4 = &context->basicFrame.r4;
	}
	else
	{
		pc = context->extendedFrame.pc;
		r0 = &context->extendedFrame.r0;
		r1 = &context->extendedFrame.r1;
		r2 = &context->extendedFrame.r2;
		r3 = &context->extendedFrame.r3;
		r4 = &context->extendedFrame.r4;
	}

	/* Retrieve the SVC number encoded on the second byte of the
	 * SVC instruction. */
	uint32_t svc_number = ((uint8_t *) pc)[-2];

	switch (svc_number)
	{
		case SVC_NUMBER_CREATE_PARTITION:
		{
			*r0 = (uint32_t) createPartition(
				(paddr) *r0
			);

			break;
		}
		case SVC_NUMBER_CUT_MEMORY_BLOCK:
		{
			*r0 = (uint32_t) cutMemoryBlock(
				(paddr) *r0,
				(paddr) *r1,
				(Coq_index) *r2
			);

			break;
		}
		case SVC_NUMBER_MERGE_MEMORY_BLOCK:
		{
			*r0 = (uint32_t) mergeMemoryBlocks(
				(paddr) *r0,
				(paddr) *r1,
				(Coq_index) *r2
			);

			break;
		}
		case SVC_NUMBER_PREPARE:
		{
			*r0 = (uint32_t) prepare(
				(paddr) *r0,
				(Coq_index) *r1,
				(paddr) *r2
			);

			break;
		}
		case SVC_NUMBER_ADD_MEMORY_BLOCK:
		{
			*r0 = (uint32_t) addMemoryBlock(
				(paddr) *r0,
				(paddr) *r1,
				(bool) ((*r2 >> 2) & 1),
				(bool) ((*r2 >> 1) & 1),
				(bool) *r2 & 1
			);

			break;
		}
		case SVC_NUMBER_REMOVE_MEMORY_BLOCK:
		{
			*r0 = (uint32_t) removeMemoryBlock(
				(paddr) *r0
			);

			break;
		}
		case SVC_NUMBER_DELETE_PARTITION:
		{
			*r0 = (uint32_t) deletePartition(
				(paddr) *r0
			);

			break;
		}
		case SVC_NUMBER_COLLECT:
		{
			*r0 = (uint32_t) collect(
				(paddr) *r0
			);

			break;
		}
		case SVC_NUMBER_MAP_MPU:
		{
			*r0 = (uint32_t) mapMPU(
				(paddr) *r0,
				(paddr) *r1,
				(Coq_index) *r2
			);

			break;
		}
		case SVC_NUMBER_READ_MPU:
		{
			*r0 = (uint32_t) readMPU(
				(paddr) *r0,
				(Coq_index) *r1
			);

			break;
		}
		case SVC_NUMBER_FIND_BLOCK:
		{
			bool is_found = findBlock(
				(paddr) *r0,
				(paddr) *r1,
				(paddr) *r2
			);
			*r0 = is_found;
			break;
		}
		case SVC_NUMBER_SET_VIDT:
		{
			*r0 = setVIDT(
				(paddr) *r0,
				(paddr) *r1
			);

			break;
		}
		case SVC_NUMBER_YIELD:
		{
			*r0 = (uint32_t) yieldGlue(
				context,
				(paddr) *r0,
				*r1,
				*r2,
				*r3,
				*r4
			);

			break;
		}
		case SVC_NUMBER_GET_INT_STATE:
		{
			*r0 = (uint32_t) getIntState(
				(paddr) *r0
			);

			break;
		}
		case SVC_NUMBER_GET_SELF_INT_STATE:
		{
			*r0 = (uint32_t) getSelfIntState();

			break;
		}
		case SVC_NUMBER_SET_INT_STATE:
		{
			setIntState(
				*r0
			);

			break;
		}
		case SVC_NUMBER_IN:
		{
			in(
				context,
				*r0,
				r1
			);

			break;
		}
		case SVC_NUMBER_OUT:
		{
			out(
				context,
				*r0,
				r1
			);

			break;
		}
#ifdef UNIT_TESTS
		case 127: // Enable Privileged mode !TODO!: to remove with system calls in SVC instead
		{
			__set_CONTROL( __get_CONTROL( ) & ~CONTROL_nPRIV_Msk ) ;

			break;
		}
		case 128: // Disable Privileged mode !TODO!: to remove with system calls in SVC instead
		{
			__set_CONTROL(__get_CONTROL() | CONTROL_nPRIV_Msk ); // switch to unprivileged Thread Mode
			__DMB();
			__ISB();
			__DSB();

			break;
		}
#endif /* UNIT_TESTS */
		default:
		{
			/* Unknown SVC */
			break;
		}
	}

	__enable_irq();
}
