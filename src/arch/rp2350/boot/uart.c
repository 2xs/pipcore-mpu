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

#include <stdint.h>

#include "rp2350.h"
#include "uart.h"

/*!
 * \brief The frequency clk_peri runs at, which is the UART's reference clock.
 *
 * __initialize_hardware_early() drives clk_peri straight from the crystal
 * oscillator, so this is the Pico 2's crystal frequency. Driving it from a
 * PLL instead would mean changing this value and nothing else here.
 */
#define UART_REFERENCE_CLOCK_HZ UINT32_C(12000000)

/*! \brief The baud rate of the debug output. */
#define UART_BAUD_RATE UINT32_C(115200)

/*! \brief The 8 bits per character encoding of UARTLCR_H.WLEN. */
#define UART_WLEN_8_BITS UINT32_C(3)

/*! \brief The GPIOs the Pico 2 brings out as UART0 TX and RX. */
#define UART_TX_PAD_OFFSET  PADS_BANK0_GPIO0_OFFSET
#define UART_TX_CTRL_OFFSET IO_BANK0_GPIO0_CTRL_OFFSET
#define UART_TX_FUNCSEL     IO_BANK0_GPIO0_CTRL_FUNCSEL_VALUE_UART0_TX
#define UART_RX_PAD_OFFSET  PADS_BANK0_GPIO1_OFFSET
#define UART_RX_CTRL_OFFSET IO_BANK0_GPIO1_CTRL_OFFSET
#define UART_RX_FUNCSEL     IO_BANK0_GPIO1_CTRL_FUNCSEL_VALUE_UART0_RX

/*!
 * \brief Takes a set of peripherals out of reset and waits for them.
 * \param bits The RESETS_RESET bits of the peripherals to release.
 */
static void resetsRelease(uint32_t bits)
{
	mmioWrite(RESETS_BASE + REG_ALIAS_CLR_BITS + RESETS_RESET_OFFSET,
	          bits);

	while ((mmioRead(RESETS_BASE + RESETS_RESET_DONE_OFFSET) & bits)
	       != bits) {
		// the peripherals are still in reset
	}
}

/*!
 * \brief Hands one pad over to a peripheral.
 *
 * Mirrors the pico-sdk's gpio_set_function(): enable the input, disable the
 * output override, select the function, then drop the pad isolation. The
 * isolation bit is set out of reset on this chip and nothing works until it
 * is cleared, which is the one step that has no RP2040 counterpart.
 *
 * \param padOffset The PADS_BANK0 offset of the pad.
 * \param ctrlOffset The IO_BANK0 offset of the pad's control register.
 * \param funcsel The function to select.
 */
static void padSetFunction(uint32_t padOffset, uint32_t ctrlOffset,
                           uint32_t funcsel)
{
	mmioWrite(PADS_BANK0_BASE + REG_ALIAS_SET_BITS + padOffset,
	          PADS_BANK0_GPIO0_IE_BITS);
	mmioWrite(PADS_BANK0_BASE + REG_ALIAS_CLR_BITS + padOffset,
	          PADS_BANK0_GPIO0_OD_BITS);

	mmioWrite(IO_BANK0_BASE + ctrlOffset,
	          funcsel << IO_BANK0_GPIO0_CTRL_FUNCSEL_LSB);

	mmioWrite(PADS_BANK0_BASE + REG_ALIAS_CLR_BITS + padOffset,
	          PADS_BANK0_GPIO0_ISO_BITS);
}

void init_uart(void)
{
	uint32_t divisor;

	resetsRelease(RESETS_RESET_IO_BANK0_BITS
	              | RESETS_RESET_PADS_BANK0_BITS
	              | RESETS_RESET_UART0_BITS);

	/* Disable the UART while its divisor and line control change. */
	mmioWrite(UART0_BASE + UART_UARTCR_OFFSET, 0);

	/* The PL011 divisor is a 16.6 fixed-point number, so scaling the
	 * ratio by 64 and rounding gives both halves at once:
	 * 64 * clock / (16 * baud) = 4 * clock / baud. */
	divisor = (8 * UART_REFERENCE_CLOCK_HZ / UART_BAUD_RATE + 1) / 2;
	mmioWrite(UART0_BASE + UART_UARTIBRD_OFFSET, divisor >> 6);
	mmioWrite(UART0_BASE + UART_UARTFBRD_OFFSET, divisor & UINT32_C(0x3f));

	/* Writing UARTLCR_H is what latches the two divisor halves, so it has
	 * to come after them. 8N1 with the FIFOs enabled. */
	mmioWrite(UART0_BASE + UART_UARTLCR_H_OFFSET,
	          (UART_WLEN_8_BITS << UART_UARTLCR_H_WLEN_LSB)
	          | UART_UARTLCR_H_FEN_BITS);

	/* No DMA requests: nothing in Pip drives this peripheral by DMA, and
	 * on this chip DMA is gated by ACCESSCTRL rather than by the PMP. */
	mmioWrite(UART0_BASE + UART_UARTDMACR_OFFSET, 0);

	mmioWrite(UART0_BASE + UART_UARTCR_OFFSET,
	          UART_UARTCR_UARTEN_BITS
	          | UART_UARTCR_TXE_BITS
	          | UART_UARTCR_RXE_BITS);

	padSetFunction(UART_TX_PAD_OFFSET, UART_TX_CTRL_OFFSET,
	               UART_TX_FUNCSEL);
	padSetFunction(UART_RX_PAD_OFFSET, UART_RX_CTRL_OFFSET,
	               UART_RX_FUNCSEL);
}

void uartPutChar(char character)
{
	while ((mmioRead(UART0_BASE + UART_UARTFR_OFFSET)
	        & UART_UARTFR_TXFF_BITS) != 0) {
		// the transmit FIFO is full
	}

	mmioWrite(UART0_BASE + UART_UARTDR_OFFSET, (uint32_t) character);
}

void uartWrite(const char *string)
{
	while (*string != '\0') {
		uartPutChar(*string++);
	}

	/* Drain before returning, so that a message printed just before a
	 * panic or a reset is not lost in the FIFO. */
	while ((mmioRead(UART0_BASE + UART_UARTFR_OFFSET)
	        & UART_UARTFR_BUSY_BITS) != 0) {
		// the shift register is still busy
	}
}
