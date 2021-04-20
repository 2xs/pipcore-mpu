//#include <mm/cache.h>
//#include <mm/memlayout.h>
//#include <lib/string.h>
//#include <pipcore/mal.h>
//#include <ial/ial.h>
//#include <drivers/gic.h>
//#include <drivers/timer.h>
#include <stdint.h>
#include <sys/types.h>
#include "mpu.h"
#include "mal.h"
#include "pip_debug.h"

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
extern void
__initialize_args (int*, char***);
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

// Begin address for the initialisation values of the .data section.
// defined in linker script
extern uint32_t _sidata;
// Begin address for the .data section; defined in linker script
extern uint32_t _sdata;
// End address for the .data section; defined in linker script
extern uint32_t _edata;

// Begin address for the .bss section; defined in linker script
extern uint32_t _sbss;
// End address for the .bss section; defined in linker script
extern uint32_t _ebss;

// main() is the entry point for newlib based applications.
// By default, there are no arguments, but this can be customised
// by redefining __initialize_args(), which is done when the
// semihosting configurations are used.
extern int
main (int argc, char* argv[]);

// The implementation for the exit routine; for embedded
// applications, a system reset will be performed.
extern void
__attribute__((noreturn))
_exit (int);

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

/*arm_ctx_t *kernel_start(void)
{
	arm_ctx_t *ctx_v, *ctx_p;

	// Clear bss
	memset(kernel_bss_start, 0, (unsigned)(kernel_bss_end-kernel_bss_start));

	// Enable D/I caches and branch predictor
	caches_enable();
	branch_pred_enable();

	// Configure interrupts & timer
	gic_init();
	timer_init(1);

	// Configure the mmu
	mmu_init();

	// Initialize the root partition
	mal_init();

	// At this point, mmu is still not enabled.
	ial_get_ctx_addr(0, getRootPartition(), &ctx_p, &ctx_v);

	return ial_prepare_yield(getRootPartition(), ctx_v);
}*/

// This is the place where Cortex-M core will go immediately after reset,
// via a call or jump from the Reset_Handler.
//
// For the call to work, and for the call to __initialize_hardware_early()
// to work, the reset stack must point to a valid internal RAM area.

void __attribute__ ((section(".after_vectors"),noreturn,weak))
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
  __initialize_data(&_sidata, &_sdata, &_edata);

  // Zero fill the BSS section (inlined).
  __initialize_bss(&_sbss, &_ebss);


  // Hook to continue the initialisations. Usually compute and store the
  // clock frequency in the global CMSIS variable, cleared above.
  __initialize_hardware ();

  // Check the MPU
  if (checkMPU()<0)
  {
    // the check doesn't pass, panic since Pip relies on the MPU
    printf("DEBUG: (kernel) MPU ERROR");
    while(1);
  }
  // Enable the MPU with PRIVDEFENA
  mpu_enable();


	/*#if MODULE_NEWLIB || MODULE_PICOLIBC
    // initialize std-c library (this must be done after board_init)
    extern void __libc_init_array(void);
    __libc_init_array();
	#endif*/

	/* Initialize the root partition */
	mal_init();

  paddr root = getRootPartition();
  dump_partition(root);
  activate(root);

	/*
	// At this point, mmu is still not enabled.
	ial_get_ctx_addr(0, getRootPartition(), &ctx_p, &ctx_v);

	return ial_prepare_yield(getRootPartition(), ctx_v);*/

	// cpu_switch_context_exit(); -> Yield, switchto root partition

    // Get the argc/argv (useful in semihosting configurations).
  int argc;
  char** argv;
  __initialize_args (&argc, &argv);

  // Call the standard library initialisation (mandatory for C++ to
  // execute the constructors for the static objects).
  //__run_init_array ();

  // Call the main entry point, and save the exit code.
  int code = main (argc, argv);

  // Run the C++ static destructors.
  //__run_fini_array ();

  _exit (code);

  // Should never reach this, _exit() should have already
  // performed a reset.
  //for (;;)
  //  ;
  while (1) {}
}

/*NORETURN void core_panic(core_panic_t crash_code, const char *message)
{
    (void)crash_code;
    (void)message;
    while (1) {}
}*/
