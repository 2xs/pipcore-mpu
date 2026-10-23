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
 * \file ecall_handler.c
 * \brief Service dispatch for the ecall syscall ABI.
 *
 * The ARM target recovered the service number from the instruction stream --
 * ((uint8_t *) pc)[-2], the immediate byte of the SVC instruction. ecall
 * carries no immediate, so the number has to travel in a register, and this
 * is the one unavoidable ABI change in the port.
 *
 * The convention is the Linux/RISC-V one: service number in a7, arguments in
 * a0 to a4, result written back to the saved a0. The service numbers
 * themselves are unchanged from the ARM target, so the enum below is still
 * the API the developer guide documents.
 *
 * One consequence of the move is a new obligation. ARM's SVC immediate is
 * eight bits wide, so its switch was implicitly bounded and an unknown number
 * could only ever be one of 256 values; its default arm did nothing at all.
 * a7 is a full 32-bit register that a partition chooses freely, so the number
 * is validated here, and anything out of range fails the call rather than
 * falling through and returning whatever was already in a0.
 */

#include <stdint.h>

/* ADT.h supplies bool, true and false itself -- it does typedef _Bool boolean
 * and then #define bool boolean -- so <stdbool.h> must not be included here
 * as well. */
#include "ADT.h"
#include "Services.h"
#include "context.h"
#include "stdio.h"
#include "trap_handler.h"

/*!
 * \brief Enumeration of the service numbers.
 *
 * Unchanged from the ARM target: these values are the partition-facing API,
 * and the root partition's stubs encode them.
 */
typedef enum ecall_number_e
{
	ECALL_NUMBER_CREATE_PARTITION    = 0 , /*!< The createPartition service number. */
	ECALL_NUMBER_CUT_MEMORY_BLOCK    = 1 , /*!< The cutMemoryBlock service number. */
	ECALL_NUMBER_MERGE_MEMORY_BLOCK  = 2 , /*!< The mergeMemoryBlocks service number. */
	ECALL_NUMBER_PREPARE             = 3 , /*!< The prepare service number. */
	ECALL_NUMBER_ADD_MEMORY_BLOCK    = 4 , /*!< The addMemoryBlock service number. */
	ECALL_NUMBER_REMOVE_MEMORY_BLOCK = 5 , /*!< The removeMemoryBlock service number. */
	ECALL_NUMBER_DELETE_PARTITION    = 6 , /*!< The deletePartition service number. */
	ECALL_NUMBER_COLLECT             = 7 , /*!< The collect service number. */
	ECALL_NUMBER_MAP_MPU             = 8 , /*!< The mapMPU service number. */
	ECALL_NUMBER_READ_MPU            = 9 , /*!< The readMPU service number. */
	ECALL_NUMBER_FIND_BLOCK          = 10, /*!< The findBlock service number. */
	ECALL_NUMBER_SET_VIDT            = 11, /*!< The setVIDT service number. */
	ECALL_NUMBER_YIELD               = 12, /*!< The yield service number. */
	ECALL_NUMBER_GET_INT_STATE       = 13, /*!< The getIntState service number. */
	ECALL_NUMBER_GET_SELF_INT_STATE  = 14, /*!< The getSelfIntState service number. */
	ECALL_NUMBER_SET_INT_STATE       = 15, /*!< The setIntState service number. */
	ECALL_NUMBER_IN                  = 16, /*!< The in service number. */
	ECALL_NUMBER_OUT                 = 17, /*!< The out service number. */
	ECALL_NUMBER_COUNT                     /*!< Not a service: the bound on a7. */
} ecall_number_t;

/*!
 * \brief What a refused call writes back to a0.
 *
 * Every service here returns either a paddr or a bool, and zero is the
 * failure value of both: NULL for the first, false for the second. So one
 * value says "this call did nothing" whichever service was asked for.
 */
#define ECALL_FAILED UINT32_C(0)

void ecallHandler(stackedContext_t *context)
{
	uint32_t number = contextReadRegister(context, RV_REG_A7);
	uint32_t a0 = contextReadRegister(context, RV_REG_A0);
	uint32_t a1 = contextReadRegister(context, RV_REG_A1);
	uint32_t a2 = contextReadRegister(context, RV_REG_A2);
	uint32_t result = ECALL_FAILED;

	/* a7 is a register the partition picks, not a bounded immediate, so
	 * it is checked before it reaches the switch. */
	if (number >= (uint32_t) ECALL_NUMBER_COUNT) {
		printf("PIP: service number %lu is out of range\n",
		       (unsigned long) number);
		contextWriteRegister(context, RV_REG_A0, ECALL_FAILED);
		return;
	}

	switch (number) {
	case ECALL_NUMBER_CREATE_PARTITION:
		result = (uint32_t) createPartition((paddr) a0);
		break;

	case ECALL_NUMBER_CUT_MEMORY_BLOCK:
		result = (uint32_t) cutMemoryBlock((paddr) a0, (paddr) a1,
		                                   (Coq_index) a2);
		break;

	case ECALL_NUMBER_MERGE_MEMORY_BLOCK:
		result = (uint32_t) mergeMemoryBlocks((paddr) a0, (paddr) a1,
		                                      (Coq_index) a2);
		break;

	case ECALL_NUMBER_PREPARE:
		result = (uint32_t) prepare((paddr) a0, (paddr) a1);
		break;

	case ECALL_NUMBER_ADD_MEMORY_BLOCK:
		/* The permissions arrive packed in one argument, r in bit 2,
		 * w in bit 1 and x in bit 0. Kept exactly as on ARM: this is
		 * the partition-facing encoding, not an internal detail. */
		result = (uint32_t) addMemoryBlock(
			(paddr) a0,
			(paddr) a1,
			((a2 >> 2) & 1) != 0,
			((a2 >> 1) & 1) != 0,
			(a2 & 1) != 0);
		break;

	case ECALL_NUMBER_REMOVE_MEMORY_BLOCK:
		result = (uint32_t) removeMemoryBlock((paddr) a0);
		break;

	case ECALL_NUMBER_DELETE_PARTITION:
		result = (uint32_t) deletePartition((paddr) a0);
		break;

	case ECALL_NUMBER_COLLECT:
		result = (uint32_t) collect((paddr) a0);
		break;

	case ECALL_NUMBER_MAP_MPU:
		result = (uint32_t) mapMPU((paddr) a0, (paddr) a1,
		                           (Coq_index) a2);
		break;

	case ECALL_NUMBER_READ_MPU:
		result = (uint32_t) readMPU((paddr) a0, (Coq_index) a1);
		break;

	case ECALL_NUMBER_FIND_BLOCK:
		result = (uint32_t) findBlock((paddr) a0, (paddr) a1,
		                              (paddr) a2);
		break;

	case ECALL_NUMBER_SET_VIDT:
		result = (uint32_t) setVIDT((paddr) a0, (paddr) a1);
		break;

	case ECALL_NUMBER_YIELD:
	case ECALL_NUMBER_GET_INT_STATE:
	case ECALL_NUMBER_GET_SELF_INT_STATE:
	case ECALL_NUMBER_SET_INT_STATE:
	case ECALL_NUMBER_IN:
	case ECALL_NUMBER_OUT:
		/* Deferred past milestone 1, and each for its own reason.
		 * yield and the interrupt-state calls need the VIDT and fault
		 * propagation chain of section 7; in and out need the RP2350
		 * register whitelist of section 9, which has no equivalent of
		 * the ARM target's regid.h yet. The numbers are reserved here
		 * so that a partition calling one fails cleanly instead of
		 * being told the number does not exist. */
		printf("PIP: service %lu is not implemented on this target"
		       " yet\n", (unsigned long) number);
		result = ECALL_FAILED;
		break;

	default:
		/* Unreachable: the range check above covers every value the
		 * enum does not name, and every value it names is handled. */
		result = ECALL_FAILED;
		break;
	}

	contextWriteRegister(context, RV_REG_A0, result);

	/* No counterpart to the ARM handler's closing __enable_irq(). That
	 * undid the cpsid i its exception entry point had issued; here trap
	 * entry clears mstatus.MIE in hardware and mret restores it from
	 * MPIE, which loadContext() sets. Interrupts come back on by
	 * returning, not by being re-enabled. */
}
