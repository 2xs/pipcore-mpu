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
 * \file bringup.h
 * \brief What the bringup harness's C and assembly halves share.
 *
 * This directory is scaffolding for rungs 1 to 3 of the bring-up ladder, not
 * part of Pip. It exists because those rungs have to run on real silicon
 * before the MAL exists, so there is nothing to link a whole pip.elf from
 * yet. Nothing here outlives the ladder: the real trap stub is trap_entry.S
 * in the boot layer, and the real entry point is main.c's Boot_Handler.
 */

#ifndef BRINGUP_H
#define BRINGUP_H

/*!
 * \brief The value of a7 that makes the harness's trap stub resume U-mode.
 *
 * An ecall carrying it is answered by advancing mepc past the ecall and
 * returning to the partition, which is the real syscall return path and the
 * one place the port is most likely to get wrong. Any other trap hands
 * control back to M-mode instead.
 */
#define BRINGUP_A7_RESUME 1

/*!
 * \brief The value of a7 the second ecall of the resume probe carries.
 *
 * Seeing it in bringupTrapA7 is the proof that the first ecall resumed
 * rather than returning: both ecalls report the same mcause.
 */
#define BRINGUP_A7_DONE 2

#if !defined(__ASSEMBLER__)

#include <stdint.h>

/*! \brief mepc at the trap that last handed control back to M-mode. */
extern volatile uint32_t bringupTrapMepc;

/*! \brief a7 at the trap that last handed control back to M-mode. */
extern volatile uint32_t bringupTrapA7;

/*!
 * \brief Runs \p entry in U-mode until it traps.
 *
 * The trap stub hands control back here rather than resuming, unless the
 * trap is an ecall carrying BRINGUP_A7_RESUME.
 *
 * \param entry The address to enter U-mode at.
 * \param stack The value to give U-mode's sp.
 * \param argument The value to give U-mode's a0.
 * \return The mcause of the trap that ended the excursion.
 */
uint32_t bringupRunInUser(uint32_t entry, uint32_t stack, uint32_t argument);

/*! \brief U-mode probe: reads the word at a0, then ecalls. */
void bringupProbeLoad(void);

/*! \brief U-mode probe: writes a0 to the word at a0, then ecalls. */
void bringupProbeStore(void);

/*! \brief U-mode probe: ecalls immediately. */
void bringupProbeEcall(void);

/*!
 * \brief U-mode probe: ecalls twice, the first asking to be resumed.
 *
 * Returns through the second ecall only if the trap stub advanced mepc past
 * the first one.
 */
void bringupProbeResume(void);

/*!
 * \brief Reports a trap taken in M-mode, which in the harness is a bug.
 *
 * \param mcause The mcause of the trap.
 * \param mepc The mepc of the trap.
 */
void bringupMachineTrap(uint32_t mcause, uint32_t mepc);

#endif /* !__ASSEMBLER__ */

#endif /* BRINGUP_H */
