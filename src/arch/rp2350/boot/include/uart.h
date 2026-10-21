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
 * \file uart.h
 * \brief Debug output over UART0 of the RP2350.
 *
 * This is the only working debug backend on this target. RISC-V semihosting
 * exists and is ratified, but the ARM target's semihosting backend is itself
 * commented out, so there is none to port; configure.sh rejects
 * --debugging-mode=semihosting here.
 *
 * init_uart() keeps the name the ARM target's Nordic driver exports, so that
 * main.c and stdio.c need no divergent call.
 */

#ifndef UART_H
#define UART_H

/*!
 * \brief Brings up UART0 on GP0/GP1 at 115200 baud, 8N1, no flow control.
 *
 * __initialize_hardware_early() must have run first: the baud divisor below
 * assumes clk_peri is driven by the crystal oscillator.
 */
void init_uart(void);

/*!
 * \brief Writes one character, blocking while the transmit FIFO is full.
 * \param character The character to write.
 */
void uartPutChar(char character);

/*!
 * \brief Writes a NUL-terminated string, then waits for the line to drain.
 * \param string The string to write.
 */
void uartWrite(const char *string);

#endif /* UART_H */
