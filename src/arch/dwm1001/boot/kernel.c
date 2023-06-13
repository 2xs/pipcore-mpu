/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2023)                */
/*  Copyright (C) 2020-2023 Orange                                             */
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
 * This file is part of the µOS++ distribution.
 *   (https://github.com/micro-os-plus)
 * Copyright (c) 2014 Liviu Ionescu.
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom
 * the Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

// ----------------------------------------------------------------------------
// This module contains the startup code for a portable embedded
// C/C++ application, built with newlib.
//
// Control reaches here from the reset handler via jump or call.
//
// The actual steps performed by _start are:
// - copy the initialised data region(s)
// - clear the BSS region(s)
// - initialise the system
// - run the preinit/init array (for the C++ static constructors)
// - initialise the arc/argv
// - branch to main()
// - run the fini array (for the C++ static destructors)
// - call _exit(), directly or via exit()
//
// If OS_INCLUDE_STARTUP_INIT_MULTIPLE_RAM_SECTIONS is defined, the
// code is capable of initialising multiple regions.
//
// The normal configuration is standalone, with all support
// functions implemented locally.
//
// For this to be called, the project linker must be configured without
// the startup sequence (-nostartfiles).

// ----------------------------------------------------------------------------

// main() is the entry point for newlib based applications.
// By default, there are no arguments, but this can be customised
// by redefining __initialize_args(), which is done when the
// semihosting configurations are used.

#include <stdint.h>
#include <sys/types.h>

#include "memlayout.h"
#include "mpu.h"
#include "mal.h"
#include "pip_debug.h"
#include "scs.h"

extern void
__initialize_args (int*, char***);


extern void main_test (void);

// ----------------------------------------------------------------------------

// Forward declarations

void
_start (void);

void
__initialize_data (uint32_t* from, uint32_t* region_begin,
		   uint32_t* region_end);

void
__initialize_bss (uint32_t* region_begin, uint32_t* region_end);

void
__initialize_hardware_early (void);

void
__initialize_hardware (void);

// ----------------------------------------------------------------------------

// load data section from flash to ram
inline void
__attribute__((always_inline))
__initialize_data (uint32_t* from, uint32_t* region_begin,
		   uint32_t* region_end)
{
  // Iterate and copy word by word.
  // It is assumed that the pointers are word aligned.
  uint32_t *p = region_begin;
  while (p < region_end)
    *p++ = *from++;
}
// default bss section to zero
inline void
__attribute__((always_inline))
__initialize_bss (uint32_t* region_begin, uint32_t* region_end)
{
  // Iterate and clear word by word.
  // It is assumed that the pointers are word aligned.
  uint32_t *p = region_begin;
  while (p < region_end)
    *p++ = 0;
}

// This is the place where Cortex-M core will go immediately after reset,
// via a call or jump from the Reset_Handler.
//
// For the call to work, and for the call to __initialize_hardware_early()
// to work, the reset stack must point to a valid internal RAM area.

void __attribute__ ((noreturn, weak))
_start (void)
{

  // Initialise hardware right after reset, to switch clock to higher
  // frequency and have the rest of the initialisations run faster.
  //
  // Mandatory on platforms like Kinetis, which start with the watch dog
  // enabled and require an early sequence to disable it.
  //
  // Also useful on platform with external RAM, that need to be
  // initialised before filling the BSS section.

  __initialize_hardware_early ();

  // Use Old Style DATA and BSS section initialisation,
  // that will manage a single BSS sections.

  // Copy the DATA segment from Flash to RAM (inlined).
  __initialize_data(
  	(uint32_t *) &__pipDataRomStart,
	(uint32_t *) &__pipDataStart,
	(uint32_t *) &__pipDataEnd
  );

  // Zero fill the BSS section (inlined).
  __initialize_bss(
  	(uint32_t *) &__pipBssStart,
	(uint32_t *) &__pipBssEnd
  );

  // Hook to continue the initialisations. Usually compute and store the
  // clock frequency in the global CMSIS variable, cleared above.
  __initialize_hardware ();

#if defined UNIT_TESTS
  main_test(); // Pip test main
#else

	/* Set the PendSV exception as pending by writing 1 to the
	 * PENDSVSET bit. */
	ICSR.PENDSVSET = 1;

	/* Trigger the PendSV exception immediately by synchronizing the
	 * execution stream with memory accesses. */
	__DSB();

	/* We should never end up here because the DSB instruction must
	 * immediately trigger the PendSV exception. */
	__builtin_unreachable();

#endif // UNIT_TESTS

  while (1) {}
}
