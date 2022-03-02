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

#ifndef __YIELD_C_H__
#define __YIELD_C_H__

#pragma GCC push_options
#pragma GCC optimize("O0")

#include <stdint.h>

#include "mal.h"

/*!
 * \brief Size of a basic frame without FP extension.
 */
#define FRAME_SIZE 0x20

/*!
 * \brief Enumeration of some of the VIDT index.
 */
typedef enum vidt_index_e
{
	/*!
	 * \brief The index 8 of the ISR vector is a reserved index in
	 *        the ARMv7-M architecture. We use it to save an
	 *        interrupted context when its pipflags has a value
	 *        equal to 0.
	 */
	CLI_SAVE_INDEX = 8,

	/*!
	 * \brief The index 9 of the ISR vector is a reserved index in
	 *        the ARMv7-M architecture. We use it to save an
	 *        interrupted context when its pipflags has a value
	 *        othen than 0.
	 */
	STI_SAVE_INDEX = 9,

	/*!
	 * \brief The index 10 of the ISR vector is a reserved index in
	 *        the ARMv7-M architecture. We use it to save a context
	 *        that raised a double fault.
	 */
	DOUBLE_FAULT_LEVEL = 10
} vidt_index_t;

/*!
 * \brief Enumeration of the possible return codes for the yield system
 *        call.
 */
typedef enum yield_return_code_e
{
	/*!
	 * \brief The system call succeeds without error.
	 *
	 * \warning This value is never returned by the yield system
	 *          call, but is required for a future implementation
	 *          of the service in Coq.
	 */
	YIELD_SUCCESS = 0,

	/*!
	 * \brief The VIDT index of the callee is greater than 32.
	 */
	CALLEE_INVALID_VIDT_INDEX = 1,

	/*!
	 * \brief The VIDT index of the caller is greater than 32.
	 */
	CALLER_INVALID_VIDT_INDEX = 2,

	/*!
	 * \brief The callee is not a child of the caller.
	 */
	CALLEE_NOT_CHILD_OF_CALLER = 3,

	/*!
	 * \brief The root partition tried to call its parent.
	 */
	CALLEE_IS_PARENT_OF_ROOT = 4,

	/*!
	 * \brief The address of the block containing the VIDT of the
	 *        caller is null.
	 */
	CALLER_VIDT_IS_NULL = 5,

	/*!
	 * \brief The block containing the VIDT of the caller does not
	 *        have the present flag.
	 */
	CALLER_VIDT_IS_NOT_PRESENT = 6,

	/*!
	 * \brief The block containing the VIDT of the caller does not
	 *        have the accessible flag.
	 */
	CALLER_VIDT_IS_NOT_ACCESSIBLE = 7,

	/*!
	 * \brief The block containing the VIDT of the caller is too
	 *        small.
	 */
	CALLER_VIDT_BLOCK_TOO_SMALL = 8,

	/*!
	 * \brief The address of the block containing the VIDT of the
	 *        callee is null.
	 */
	CALLEE_VIDT_IS_NULL = 9,

	/*!
	 * \brief The block containing the VIDT of the callee does not
	 *        have the present flag.
	 */
	CALLEE_VIDT_IS_NOT_PRESENT = 10,

	/*!
	 * \brief The block containing the VIDT of the callee does not
	 *        have the accessible flag.
	 */
	CALLEE_VIDT_IS_NOT_ACCESSIBLE = 11,

	/*!
	 * \brief The block containing the VIDT of the callee is too
	 *        small.
	 */
	CALLEE_VIDT_BLOCK_TOO_SMALL = 12,

	/*!
	 * \brief No block were found in the caller's address space
	 *        that match the context address read from the VIDT.
	 */
	CALLER_CONTEXT_BLOCK_NOT_FOUND = 13,

	/*!
	 * \brief The block containing the address to which the context
	 *        of the caller is to be written does not have the
	 *        present flag.
	 */
	CALLER_CONTEXT_BLOCK_IS_NOT_PRESENT = 14,

	/*!
	 * \brief The block containing the address to which the context
	 *        of the caller is to be written does not have the
	 *        accessible flag.
	 */
	CALLER_CONTEXT_BLOCK_IS_NOT_ACCESSIBLE = 15,

	/*!
	 * \brief The block containing the address to which the context
	 *        of the caller is to be written does not have the
	 *        writable flag.
	 */
	CALLER_CONTEXT_BLOCK_IS_NOT_WRITABLE = 16,

	/*!
	 * \brief The address of the caller's context, added to the
	 *        size of a context, exceeds the end of the block.
	 */
	CALLER_CONTEXT_EXCEED_BLOCK_END = 17,

	/*!
	 * \brief The address to which the caller's context should be
	 *        written is not aligned on a 4-byte boundary.
	 */
	CALLER_CONTEXT_MISALIGNED = 18,

	/*!
	 * \brief No block were found in the callee's address space
	 *        that match the context address read from the VIDT.
	 */
	CALLEE_CONTEXT_BLOCK_NOT_FOUND = 19,

	/*!
	 * \brief The block containing the address at which the context
	 *        of the callee is to be read does not have the present
	 *        flag.
	 */
	CALLEE_CONTEXT_BLOCK_IS_NOT_PRESENT = 20,

	/*!
	 * \brief The block containing the address at which the context
	 *        of the callee is to be read does not have the
	 *        accessible flag.
	 */
	CALLEE_CONTEXT_BLOCK_IS_NOT_ACCESSIBLE = 21,

	/*!
	 * \brief The block containing the address at which the context
	 *        of the callee is to be read does not have the readable
	 *        flag.
	 */
	CALLEE_CONTEXT_BLOCK_IS_NOT_READABLE = 22,

	/*!
	 * \brief The address of the callee's context, added to the size
	 *        of a context, exceeds the end of the block.
	 */
	CALLEE_CONTEXT_EXCEED_BLOCK_END = 23,

	/*!
	 * \brief The address at which the callee's context should be
	 *        read is not aligned on a 4-byte boundary.
	 */
	CALLEE_CONTEXT_MISALIGNED = 24,

	/*!
	 * \brief The valid field of the context structure does not
	 *        contain a valid context value.
	 */
	CALLEE_CONTEXT_INVALID = 25

} yield_return_code_t;

typedef uint32_t uservalue_t;

/*!
 * \brief Yield from the current partition (the caller), to its parent,
 *        itself or one of its children (the callee).
 *
 * \param calleePartDescBlockId The ID of a block containing a
 *        partition descriptor structure. An ID equals to 0 mean the
 *        partition descriptor structure of the parent of the current
 *        partition.
 *
 * \param userTargetInterrupt The index of the VIDT, which contains the
 *        address pointing to the location where the current context is
 *        to be restored.
 *
 * \param userCallerContextSaveIndex The index of the VIDT, which
 *        contains the address pointing to the location where the
 *        current context is to be stored. If this address is zero, the
 *        context is not stored.
 *
 * \param flagsOnYield The state the partition wishes to be on yield.
 *
 * \param flagsOnWake The state the partition wishes to be on wake.
 *
 * \return If the system call succeeds, no value is returned to the
 *         caller. If an error occurs, the system call returns an error
 *         code indicating the nature of the error. If the context is
 *         restored, the return value should be ignored.
 */
__attribute__((section(".text_pipcore")))
yield_return_code_t
yieldGlue(
	stacked_context_t *svc_ctx,
	paddr calleePartDescAddr,
	uservalue_t userTargetInterrupt,
	uservalue_t userCallerContextSaveIndex,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake);

__attribute__((section(".text_pipcore")))
yield_return_code_t
getSourcePartVidtCont(
	paddr calleePartDesc,
	paddr callerPartDesc,
	unsigned targetInterrupt,
	unsigned callerContextSaveIndex,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	user_context_t *callerInterruptedContext);

__attribute__((section(".text_pipcore")))
yield_return_code_t
getTargetPartVidtCont(
	paddr calleePartDesc,
	paddr callerPartDesc,
	paddr callerContextSaveAddr,
	unsigned targetInterrupt,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	user_context_t *callerInterruptedContext);

__attribute__((section(".text_pipcore")))
yield_return_code_t
getParentPartDescCont(
	paddr callerPartDesc,
	unsigned targetInterrupt,
	unsigned callerContextSaveIndex,
	int_mask_t flagsOnYield,
	int_mask_t flagsOnWake,
	user_context_t *callerInterruptedContext);

/*!
 * \brief Yield to another partition.
 *
 * \warning This function is publicly exposed only to start the root
 *          partition.
 *
 * \param calleePartDesc The ID of the block containing the partition
 *        descriptor structure of the partition on which to yield.
 *
 * \param flagsOnYield The state the partition wishes to be on yield.
 *
 * \param ctx The context from which to restore the processor registers.
 *
 * \return Although the function has a return type, it never returns to
 *         the caller. This return type is required for a future
 *         implementation of the service in Coq.
 */
__attribute__((section(".text_pipcore")))
yield_return_code_t
switchContextCont(
	paddr calleePartDesc,
	int_mask_t flagsOnYield,
	user_context_t *ctx);

#pragma GCC pop_options

#endif /* __YIELD_C_H__ */
