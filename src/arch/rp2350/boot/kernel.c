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

/*
 * The C half of the reset path, reached from Reset_Handler in start.S with a
 * valid sp, mtvec and mscratch, and with interrupts disabled.
 *
 * Derived from the ARM target's kernel.c, itself from the µOS++ distribution
 * (Copyright (c) 2014 Liviu Ionescu, MIT). What is gone is the PendSV
 * self-trigger it ended with: that existed only to reach an exception context
 * for Boot_Handler, and M-mode at reset already is the privileged context.
 */

#include <stdint.h>

#include "memlayout.h"
#include "uart.h"

extern void Boot_Handler(void);
extern void main_test(void);

void _start(void);

void __initialize_hardware_early(void);

/*!
 * \brief Copies the data section from its load address in ROM to RAM.
 *
 * The pointers are assumed to be word aligned, which link.ld guarantees.
 *
 * \param from The start address of the section in ROM.
 * \param regionBegin The start address of the section in RAM.
 * \param regionEnd The end address of the section in RAM.
 */
static inline __attribute__((always_inline)) void
__initialize_data(uint32_t *from, uint32_t *regionBegin, uint32_t *regionEnd)
{
	uint32_t *p = regionBegin;

	while (p < regionEnd) {
		*p++ = *from++;
	}
}

/*!
 * \brief Zeroes the bss section.
 *
 * \param regionBegin The start address of the section.
 * \param regionEnd The end address of the section.
 */
static inline __attribute__((always_inline)) void
__initialize_bss(uint32_t *regionBegin, uint32_t *regionEnd)
{
	uint32_t *p = regionBegin;

	while (p < regionEnd) {
		*p++ = 0;
	}
}

void __attribute__((noreturn)) _start(void)
{
	/* The clock the UART derives its baud rate from. Nothing before this
	 * point may print. */
	__initialize_hardware_early();

	__initialize_data((uint32_t *) &__pipDataRomStart,
	                  (uint32_t *) &__pipDataStart,
	                  (uint32_t *) &__pipDataEnd);

	__initialize_bss((uint32_t *) &__pipBssStart,
	                 (uint32_t *) &__pipBssEnd);

	init_uart();

#if defined UNIT_TESTS
	main_test();
#else
	Boot_Handler();
#endif

	while (1) {
		// Boot_Handler enters the root partition and never returns
	}
}
