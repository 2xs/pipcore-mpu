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
 * The hook _start() calls before anything else. On the ARM target this set
 * SCB->VTOR and the FPU's CPACR; here neither exists, and what has to happen
 * early instead is the clock the UART counts on.
 */

#include <stdint.h>

#include "rp2350.h"

/*!
 * \brief The crystal oscillator startup delay, in units of 256 clock cycles.
 *
 * The pico-sdk computes ((XOSC_HZ / 1000) + 128) / 256, i.e. one millisecond
 * at the Pico 2's 12 MHz crystal.
 */
#define XOSC_STARTUP_DELAY UINT32_C(47)

/*!
 * \brief Cycles to wait between disabling and reconfiguring clk_peri.
 *
 * clk_peri has no glitchless mux and therefore no handshake to poll: the
 * datasheet's requirement is simply to leave it disabled for three cycles of
 * whichever of the two sources is slower. Both are within an order of
 * magnitude of each other here, so a small fixed count covers it.
 */
#define CLK_PERI_SETTLE_CYCLES UINT32_C(32)

void __initialize_hardware_early(void);

/*!
 * \brief Starts the crystal oscillator and waits for it to stabilise.
 */
static void xoscInit(void)
{
	mmioWrite(XOSC_BASE + XOSC_STARTUP_OFFSET, XOSC_STARTUP_DELAY);

	mmioWrite(XOSC_BASE + XOSC_CTRL_OFFSET,
	          (XOSC_CTRL_FREQ_RANGE_VALUE_1_15MHZ
	           << XOSC_CTRL_FREQ_RANGE_LSB)
	          | (XOSC_CTRL_ENABLE_VALUE_ENABLE << XOSC_CTRL_ENABLE_LSB));

	while ((mmioRead(XOSC_BASE + XOSC_STATUS_OFFSET)
	        & XOSC_STATUS_STABLE_BITS) == 0) {
		// the oscillator has not stabilised yet
	}
}

/*!
 * \brief Drives clk_peri from the crystal oscillator.
 *
 * The UART's baud rate is derived from clk_peri, and clk_peri comes out of
 * reset following clk_sys, which runs on the ring oscillator at a frequency
 * that is neither specified nor stable. Taking it straight from the crystal
 * gives an exact reference without bringing up a PLL, which nothing in the
 * port needs yet.
 */
static void clkPeriInit(void)
{
	uint32_t cycles;

	mmioWrite(CLOCKS_BASE + CLOCKS_CLK_PERI_CTRL_OFFSET, 0);

	for (cycles = 0; cycles < CLK_PERI_SETTLE_CYCLES; cycles++) {
		__asm__ volatile ("nop");
	}

	mmioWrite(CLOCKS_BASE + CLOCKS_CLK_PERI_CTRL_OFFSET,
	          (CLOCKS_CLK_PERI_CTRL_AUXSRC_VALUE_XOSC_CLKSRC
	           << CLOCKS_CLK_PERI_CTRL_AUXSRC_LSB));

	mmioWrite(CLOCKS_BASE + REG_ALIAS_SET_BITS
	          + CLOCKS_CLK_PERI_CTRL_OFFSET,
	          CLOCKS_CLK_PERI_CTRL_ENABLE_BITS);

	while ((mmioRead(CLOCKS_BASE + CLOCKS_CLK_PERI_SELECTED_OFFSET)
	        & UINT32_C(1)) == 0) {
		// the clock has not been enabled yet
	}
}

void __initialize_hardware_early(void)
{
	xoscInit();
	clkPeriInit();
}
