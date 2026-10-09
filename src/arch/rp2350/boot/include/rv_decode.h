/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2025)                */
/*  Copyright (C) 2020-2025 Orange                                             */
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
 * \file rv_decode.h
 * \brief Effective address of the memory access of an RV32IMAC instruction.
 *
 * mtval is hardwired to zero on the RP2350, so an access fault does not hand
 * the kernel the faulting address the way ARM's MMFAR does. On a load or
 * store fault the PMP refill handler has to recover it by decoding the
 * instruction at mepc, which is what this module does.
 *
 * The decoder is a pure function of the saved context and the instruction
 * halfwords: fetching them is the caller's job, since that fetch is the one
 * part that can itself fault. This also makes the module testable on the
 * host (src/arch/rp2350/test).
 */

#ifndef RV_DECODE_H
#define RV_DECODE_H

#include <stdbool.h>
#include <stdint.h>

#include "context.h"

/*!
 * \fn bool rv_insn_is_32bit(uint16_t lo)
 * \brief Tells whether an instruction is 32 bits wide from its first halfword.
 *
 * The caller must not fetch the second halfword unless this returns true: on
 * a 16-bit instruction at the end of a partition's block, that read could
 * leave the block and fault in M-mode, which panics the kernel.
 *
 * \param lo The first halfword of the instruction.
 * \return true when the instruction is 32 bits wide, false when compressed.
 */
static inline bool rv_insn_is_32bit(uint16_t lo)
{
	return (lo & UINT16_C(3)) == UINT16_C(3);
}

/*!
 * \fn bool rv_effective_address(const stackedContext_t *context, uint16_t lo,
 *                              uint16_t hi, uint32_t *effectiveAddress)
 * \brief Computes the address the instruction at mepc accesses.
 *
 * Handles every single-access load and store of RV32IMAC plus the five Zcb
 * forms, which a third-party toolchain may emit. An unrecognised encoding is
 * reported as a failure rather than guessed at, and the caller must then
 * treat the fault as genuine and propagate it to the parent partition.
 *
 * Zcmp (cm.push, cm.pop, cm.popret) is deliberately unrecognised: one such
 * instruction performs several accesses, which a refill driven by a single
 * effective address cannot satisfy. The project toolchain excludes Zcmp from
 * -march, and partition binaries must not contain it either.
 *
 * \param context The context saved by the trap stub, which holds x1 to x31.
 * \param lo The first halfword of the instruction, read from mepc.
 * \param hi The second halfword, read from mepc + 2, or anything when the
 *        instruction is compressed.
 * \param effectiveAddress Where the address is written on success.
 * \return true when the instruction was decoded, false otherwise.
 */
bool rv_effective_address(const stackedContext_t *context, uint16_t lo,
                          uint16_t hi, uint32_t *effectiveAddress);

#endif /* RV_DECODE_H */
