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
 * \file rp2350.h
 * \brief RP2350 memory-mapped register definitions used by the boot layer.
 *
 * This is a trimmed transcription of the pico-sdk register headers under
 * src/rp2350/hardware_regs/include/hardware/regs/. The macro names are kept
 * character-for-character identical to the ones there, so checking this file
 * against the vendor definition is a mechanical grep rather than a reading of
 * the datasheet:
 *
 *     grep -h "^#define <NAME> " <pico-sdk>/src/rp2350/hardware_regs/\
 *         include/hardware/regs/
 *
 * Only what the boot layer actually touches is transcribed. Nothing is
 * derived, computed or renamed.
 */

#ifndef RP2350_H
#define RP2350_H

#include <stdint.h>

/*!
 * \brief Reads a 32-bit memory-mapped register.
 * \param addr The address of the register.
 * \return The value read.
 */
static inline uint32_t mmioRead(uint32_t addr)
{
	return *(volatile uint32_t *)(uintptr_t) addr;
}

/*!
 * \brief Writes a 32-bit memory-mapped register.
 * \param addr The address of the register.
 * \param value The value to write.
 */
static inline void mmioWrite(uint32_t addr, uint32_t value)
{
	*(volatile uint32_t *)(uintptr_t) addr = value;
}

/* --- addressmap.h ------------------------------------------------------- */

/*!
 * \brief Atomic bit-manipulation aliases of a peripheral register block.
 *
 * Adding one of these to a register address gives an alias that sets, clears
 * or toggles the bits written to it instead of replacing the whole word.
 */
#define REG_ALIAS_RW_BITS  (UINT32_C(0x0) << 12)
#define REG_ALIAS_XOR_BITS (UINT32_C(0x1) << 12)
#define REG_ALIAS_SET_BITS (UINT32_C(0x2) << 12)
#define REG_ALIAS_CLR_BITS (UINT32_C(0x3) << 12)

#define ROM_BASE        UINT32_C(0x00000000)
#define XIP_BASE        UINT32_C(0x10000000)
#define SRAM_BASE       UINT32_C(0x20000000)
#define CLOCKS_BASE     UINT32_C(0x40010000)
#define RESETS_BASE     UINT32_C(0x40020000)
#define IO_BANK0_BASE   UINT32_C(0x40028000)
#define PADS_BANK0_BASE UINT32_C(0x40038000)
#define XOSC_BASE       UINT32_C(0x40048000)
#define ACCESSCTRL_BASE UINT32_C(0x40060000)
#define UART0_BASE      UINT32_C(0x40070000)
#define SIO_BASE        UINT32_C(0xd0000000)

/* --- resets.h ---------------------------------------------------------- */

#define RESETS_RESET_OFFSET      UINT32_C(0x00000000)
#define RESETS_RESET_DONE_OFFSET UINT32_C(0x00000008)

#define RESETS_RESET_UART0_BITS      UINT32_C(0x04000000)
#define RESETS_RESET_PADS_BANK0_BITS UINT32_C(0x00000200)
#define RESETS_RESET_IO_BANK0_BITS   UINT32_C(0x00000040)

/* --- xosc.h ------------------------------------------------------------ */

#define XOSC_CTRL_OFFSET    UINT32_C(0x00000000)
#define XOSC_STATUS_OFFSET  UINT32_C(0x00000004)
#define XOSC_STARTUP_OFFSET UINT32_C(0x0000000c)

#define XOSC_CTRL_ENABLE_LSB               UINT32_C(12)
#define XOSC_CTRL_ENABLE_VALUE_ENABLE      UINT32_C(0xfab)
#define XOSC_CTRL_FREQ_RANGE_LSB           UINT32_C(0)
#define XOSC_CTRL_FREQ_RANGE_VALUE_1_15MHZ UINT32_C(0xaa0)
#define XOSC_STATUS_STABLE_BITS            UINT32_C(0x80000000)

/* --- clocks.h ---------------------------------------------------------- */

#define CLOCKS_CLK_PERI_CTRL_OFFSET     UINT32_C(0x00000048)
#define CLOCKS_CLK_PERI_SELECTED_OFFSET UINT32_C(0x00000050)

#define CLOCKS_CLK_PERI_CTRL_ENABLE_BITS              UINT32_C(0x00000800)
#define CLOCKS_CLK_PERI_CTRL_AUXSRC_LSB               UINT32_C(5)
#define CLOCKS_CLK_PERI_CTRL_AUXSRC_VALUE_XOSC_CLKSRC UINT32_C(0x4)

/* --- io_bank0.h -------------------------------------------------------- */

#define IO_BANK0_GPIO0_CTRL_OFFSET UINT32_C(0x00000004)
#define IO_BANK0_GPIO1_CTRL_OFFSET UINT32_C(0x0000000c)

#define IO_BANK0_GPIO0_CTRL_FUNCSEL_LSB            UINT32_C(0)
#define IO_BANK0_GPIO0_CTRL_FUNCSEL_VALUE_UART0_TX UINT32_C(0x02)
#define IO_BANK0_GPIO1_CTRL_FUNCSEL_VALUE_UART0_RX UINT32_C(0x02)

/* --- pads_bank0.h ------------------------------------------------------ */

#define PADS_BANK0_GPIO0_OFFSET UINT32_C(0x00000004)
#define PADS_BANK0_GPIO1_OFFSET UINT32_C(0x00000008)

#define PADS_BANK0_GPIO0_ISO_BITS UINT32_C(0x00000100)
#define PADS_BANK0_GPIO0_OD_BITS  UINT32_C(0x00000080)
#define PADS_BANK0_GPIO0_IE_BITS  UINT32_C(0x00000040)

/* --- uart.h ------------------------------------------------------------ */

#define UART_UARTDR_OFFSET    UINT32_C(0x00000000)
#define UART_UARTFR_OFFSET    UINT32_C(0x00000018)
#define UART_UARTIBRD_OFFSET  UINT32_C(0x00000024)
#define UART_UARTFBRD_OFFSET  UINT32_C(0x00000028)
#define UART_UARTLCR_H_OFFSET UINT32_C(0x0000002c)
#define UART_UARTCR_OFFSET    UINT32_C(0x00000030)
#define UART_UARTDMACR_OFFSET UINT32_C(0x00000048)

#define UART_UARTFR_TXFF_BITS UINT32_C(0x00000020)
#define UART_UARTFR_RXFE_BITS UINT32_C(0x00000010)
#define UART_UARTFR_BUSY_BITS UINT32_C(0x00000008)

#define UART_UARTLCR_H_WLEN_LSB  UINT32_C(5)
#define UART_UARTLCR_H_FEN_BITS  UINT32_C(0x00000010)

#define UART_UARTCR_RXE_BITS    UINT32_C(0x00000200)
#define UART_UARTCR_TXE_BITS    UINT32_C(0x00000100)
#define UART_UARTCR_UARTEN_BITS UINT32_C(0x00000001)

#endif /* RP2350_H */
