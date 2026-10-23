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
 * \file trap_handler.h
 * \brief The trap stub's C half, and the entry points it shares with it.
 */

#ifndef TRAP_HANDLER_H
#define TRAP_HANDLER_H

#include <stdint.h>

#include "context.h"

/*!
 * \fn void trapHandlerC(stackedContext_t *context)
 * \brief Demuxes a trap taken in U-mode on mcause. Does not return.
 *
 * Called by trapEntry in trap_entry.S, with the partition's context already
 * built on Pip's kernel stack and mscratch zeroed. It always leaves through
 * loadContext(), or does not leave at all.
 *
 * \param context The interrupted partition's context.
 */
void __attribute__((noreturn)) trapHandlerC(stackedContext_t *context);

/*!
 * \fn void pipFault(uint32_t mcause, uint32_t mepc)
 * \brief Reports a trap taken in M-mode, which is a kernel bug.
 *
 * The analogue of the ARM target's Kernel_Panic(), reached from the
 * MPP == M arm of the trap stub. It takes the two CSRs rather than a context
 * pointer, because when Pip faults there is no partition context to pass: the
 * stub saves nothing on that path, there being nothing to resume.
 *
 * \param mcause The cause of the trap.
 * \param mepc The address of the faulting instruction.
 */
void __attribute__((noreturn)) pipFault(uint32_t mcause, uint32_t mepc);

/*!
 * \fn void loadContext(stackedContext_t *context)
 * \brief Enters U-mode with the given context. Does not return.
 *
 * Defined in trap_entry.S.
 *
 * \param context The context to resume.
 */
void __attribute__((noreturn)) loadContext(stackedContext_t *context);

/*!
 * \fn void ecallHandler(stackedContext_t *context)
 * \brief Services an ecall from U-mode.
 *
 * Defined in ecall_handler.c. The service number is in the saved a7 and the
 * arguments in a0 to a4; the result is written back to the saved a0. mepc has
 * already been advanced past the ecall by the time this is called.
 *
 * \param context The calling partition's context.
 */
void ecallHandler(stackedContext_t *context);

#endif /* TRAP_HANDLER_H */
