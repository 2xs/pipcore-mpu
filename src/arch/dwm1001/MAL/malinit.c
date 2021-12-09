/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2021)                */
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

/**
 * \file malinit.c
 * \brief ARM memory abstraction layer initializer
 */

#include <stdint.h>
/*#include <lib/string.h>
#include <mm/mmu.h>
#include <mm/memlayout.h>
#include <sys/coproc.h>
#include <sys/context.h>
#include <pipcore/debug.h>
#include <pipcore/fpinfo.h>*/
//#include <pipcore/mal.h>
/*#include <sys/elf.h>
#include <sys/defs.h>*/
//#include "ADT.h"
//#include "Services.h"
#include <stdio.h>

#include "Internal.h"
#include "mal.h"
#include "pip_debug.h"

/* TODO: implement self debug */
/**
 * \brief Strings for debugging output.
 */
/*#define CRITICAL 0 //!< Critical output
#define	ERROR 1 //!< Error output
#define WARNING	2 //!< Warning output
#define	INFO 3 //!< Information output
#define LOG	4 //!< Log output
//#define TRACE 5 //!< Annoying, verbose output

#ifndef LOGLEVEL
#define LOGLEVEL CRITICAL
#endif*/

/**
 * \brief Defines the appropriate DEBUG behavior.
 */
//#define DEBUG(loglvl,msg,...) if(loglvl<=LOGLEVEL){ printf(#loglvl " [%s:%d] " msg, __FILE__, __LINE__, ##__VA_ARGS__);}

// Start address for the user section; defined in linker script
extern uint32_t user_mem_start;
// End address for the user section; defined in linker script
extern uint32_t user_mem_end;
// Stack end address for the user section; defined in linker script
extern uint32_t user_stack_top;

extern uint32_t _sram;

static void* user_alloc_pos = NULL;

paddr blockentryaddr_flash = NULL;
paddr blockentryaddr_ram0 = NULL;
paddr blockentryaddr_ram1 = NULL;
paddr blockentryaddr_ram2 = NULL;
paddr blockentryaddr_periph = NULL;

/* Root partition initialisation.
 * All this code will run at startup.
 */
static paddr mal_create_root_part(void)
{
	uint32_t PD_SIZE = PDSTRUCTURETOTALLENGTH();//already MPU sized, in bytes
	paddr part = user_alloc_pos;
	//  # init PD root partition: zero the block + fill in [0; PD length]
	user_alloc_pos = user_alloc_pos + PD_SIZE; // PD_SIZE is in bytes
	eraseBlock(part, user_alloc_pos);

	// Cast to PDTable_t structure
	PDTable_t* pdtable = (PDTable_t*) part;
	*pdtable = getEmptyPDTable();

	return part;
}

/* mal_init_root_part: Map the root partition code, give it all user memory.
*/
void mal_init_root_part(paddr part)
{
	uint32_t KS_SIZE = KERNELSTRUCTURETOTALLENGTH();//already MPU sized, in bytes
	paddr kstructure = user_alloc_pos;
	user_alloc_pos = user_alloc_pos + KS_SIZE; // KS_SIZE is in bytes

	//  # init structure kernel of root partition: zero the block + fill in [0; kernel length]
	/*while (user_alloc_pos < (kstructure + KS_SIZE))// TODO: defined as bigger than minimal MPU region size
		*user_alloc_pos++ = 0;*/

	//*kstructure = getEmptyKernelStructure();

	/*bool isRootPrepared = initStructure(kstructure, user_alloc_pos);// TODO: defined as bigger than minimal MPU region size)

	if (!isRootPrepared)
		PANIC("Root partition kernel structure init failed!\r\n");*/

	//  init structure kernel of root partition: zero the block + fill in [0; kernel length]
	if (!initStructure(kstructure, user_alloc_pos))// TODO: defined as bigger than minimal MPU region size)
	{
		printf("mal_init_root_part( part=%p) : couldn't initialise structure\r\n", part);
		while(1);
	}
	// TODO change ed of kernel structure param ?

	// prepare the root partition with the intialized structure
	writePDStructurePointer(part, kstructure);
	writePDFirstFreeSlotPointer(part, kstructure);
	writePDNbFreeSlots(part, KERNELSTRUCTUREENTRIESNB);
	writePDNbPrepare(part, 1);

	// add user memory block(s)
#if !defined UNIT_TESTS // unit tests are prepared differently
	// One FLASH block + one RAM block + one peripheral block -> seperated compilation
	/*paddr blockentryaddr_flash = insertNewEntry(part, 0,  0x00080000, 0, true, false, true); // idpartition, start, end, origin, RWX
	paddr blockentryaddr_ram = insertNewEntry(part, user_alloc_pos, &user_mem_end, user_alloc_pos, true, true, false);
	paddr blockentryaddr_periph = insertNewEntry(part, 0x40000000, 0x5FFFFFFF, 0x40000000, true, true, false);
	// Pre-configure the MPU LUT with inserted block(s)
	enableBlockInMPU(part, blockentryaddr_flash, 0);
	enableBlockInMPU(part, blockentryaddr_ram, 1);
	enableBlockInMPU(part, blockentryaddr_periph, 2);*/

	// One FLASH block + three RAM block (RW data + available memory + stack) + peripheral block -> not separated compilation
	blockentryaddr_flash = insertNewEntry(part, (paddr) 0,  (paddr) 0x00080000, (paddr) 0, true, false, true);
	blockentryaddr_ram0 = insertNewEntry(part, (paddr) 0x20000000, user_alloc_pos-1, (paddr) 0x20000000, true, true, false);
	blockentryaddr_ram1 = insertNewEntry(part, user_alloc_pos, (paddr) 0x20007FFF, (paddr) 0x20000000, true, true, false);
	blockentryaddr_ram2 = insertNewEntry(part, (paddr) 0x20008000, &user_stack_top, (paddr) 0x20008000, true, true, false);
	blockentryaddr_periph = insertNewEntry(part, (paddr) 0x40000000, (paddr) 0x5FFFFFFF, (paddr) 0x40000000, true, true, false);

	// Map 4 blocks -> flash, 2 ram blocks + peripherals
  	enableBlockInMPU(part, blockentryaddr_flash, 0); // Entire Flash
  	enableBlockInMPU(part, blockentryaddr_ram0, 1); // RW region containing the data+bss
  	enableBlockInMPU(part, blockentryaddr_ram2, 2); // Stack: !never touch!, should always be enabled in MPU
	enableBlockInMPU(part, blockentryaddr_periph, 3); // Peripherals

	dump_mpu();


#endif // UNIT_TESTS
	//DEBUG(TRACE, "mal_init_root_part( part=%08x) : kstructure=%p, first entry=%p\r\n", part,kstructure,user_alloc_pos);
	printf("mal_init_root_part( part=%p) : kstructure=%p, first entry=%p\r\n", part,kstructure,user_alloc_pos);

	// Map stack and VIDT
/*
	arm_ctx_t *init_ctx;
	// Create first context on the stack
	init_ctx = (arm_ctx_t*)(stack + 0x1000 - sizeof(*init_ctx));
	init_ctx->reg[CTX_SP] = (unsigned)STACK_VADDR + 0x1000 - sizeof(*init_ctx);
	init_ctx->reg[CTX_PC] = (unsigned)entry_point;
	init_ctx->reg[CTX_R0] = (unsigned)FPINFO_VADDR;
	init_ctx->pipflags = 1;

	// Prepare vidt with first context address & vcli set
	vidt[0] = init_ctx->reg[CTX_SP];

	DEBUG(TRACE, "Filled vidt with &ctx=%p, pc=%08x\r\n", vidt[0], init_ctx->reg[CTX_PC]);
	*/

 	// Invalidate user page allocator (FIXME: debug purpose only)
	//user_alloc_pos = &user_mem_end;

	// Register created root partition to Pip
	updateRootPartition(part);
}

void mal_init_global_var(void)
{
	user_alloc_pos = &user_mem_start;
	min_mpu_region = MINBLOCKSIZE() << 2; // block is in words
}

void mal_init(void)
{
	// Check and clear the physical MPU
	if (checkMPU()<0 || initMPU()<0)
	{
		// the check did not pass, panic since Pip relies on the MPU
		printf("DEBUG: (kernel) MPU ERROR");
		while(1);
	}

	mal_init_global_var();
	//unsigned *part;
	paddr part;

	// Initialize root partition
	part = mal_create_root_part();

	// Prepare the root partition and give it all user memory
	mal_init_root_part(part);

	//DEBUG(TRACE, "mal_init( part=%08x) : root is initialized\r\n", part);
	printf("mal_init( part=%p) : root is initialized\r\n", part);
}
