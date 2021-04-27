/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2021)                 */
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

extern uint32_t _sram;

static uint32_t* user_alloc_pos = &user_mem_start;

/* Root partition initialisation.
 * All this code will run at startup.
 */
static paddr mal_create_root_part(void)
{
	uint32_t PD_SIZE = PDSTRUCTURETOTALLENGTH();//already MPU sized
	paddr part = user_alloc_pos;
	//  # init PD root partition: zero the block + fill in [0; PD length]
	while (user_alloc_pos < (part + PD_SIZE))// defined as bigger than minimal MPU region size
		*user_alloc_pos++ = 0;

	// Cast to PDTable_t structure
	PDTable_t* pdtable = (PDTable_t*) part;
	*pdtable = getEmptyPDTable();

	return part;
}

/* mal_init_root_part: Map the root partition code, give it all user memory.
*/
void mal_init_root_part(paddr part)
{
	uint32_t KS_SIZE = KERNELSTRUCTURETOTALLENGTH();//already MPU sized
	paddr kstructure = user_alloc_pos;

	//  # init structure kernel of root partition: zero the block + fill in [0; kernel length]
	while (user_alloc_pos < (kstructure + KS_SIZE))// TODO: defined as bigger than minimal MPU region size
		*user_alloc_pos++ = 0;

	//*kstructure = getEmptyKernelStructure();

	/*bool isRootPrepared = initStructure(kstructure, user_alloc_pos);// TODO: defined as bigger than minimal MPU region size)

	if (!isRootPrepared)
		PANIC("Root partition kernel structure init failed!\r\n");*/

	if (!initStructure(kstructure, user_alloc_pos))// TODO: defined as bigger than minimal MPU region size)
	{
		printf("mal_init_root_part( part=%08x) : couldn't initialise structure\r\n", part);
		while(1);
	}
	// TODO change ed of kernel structure param ?

	// prepare the root partition with the intialized structure
	writePDStructurePointer(part, kstructure);
	writePDFirstFreeSlotPointer(part, kstructure);
	writePDNbFreeSlots(part, kernelstructureentriesnb);
	writePDNbPrepare(part, 1);

	// add user memory block(s)
#if defined UNIT_TESTS
	// One RAM block for unit testing
	paddr mpuentryaddr_ram = insertNewEntry(part, user_alloc_pos, &user_mem_end, user_alloc_pos);// idpartition, start, end, origin

	// Pre-configure the MPU LUT with inserted block(s)
	PDTable_t* PDT = (PDTable_t*) part;
	PDT->blocks[0] = (MPUEntry_t*) mpuentryaddr_ram;
	configure_LUT_entry(PDT->LUT, 0, mpuentryaddr_ram);
#else
	// One FLASH block and one RAM block
	//paddr mpuentryaddr = insertNewEntry(part, user_alloc_pos, &user_mem_end, user_alloc_pos);// idpartition, start, end, origin
	paddr mpuentryaddr_flash = insertNewEntry(part, 0,  fit_mpu_region(0x1FFFFFFF) - 1, 0);
	paddr mpuentryaddr_ram = insertNewEntry(part, &_sram, fit_mpu_region(&user_mem_end) - 1, &_sram);
	// Pre-configure the MPU LUT with inserted block(s)
	PDTable_t* PDT = (PDTable_t*) part;
	PDT->blocks[0] = (MPUEntry_t*) mpuentryaddr_flash;
	PDT->blocks[1] = (MPUEntry_t*) mpuentryaddr_ram;
	configure_LUT_entry(PDT->LUT, 0, mpuentryaddr_flash);
	configure_LUT_entry(PDT->LUT, 1, mpuentryaddr_ram);
#endif // UNIT_TESTS
	//DEBUG(TRACE, "mal_init_root_part( part=%08x) : kstructure=%p, first entry=%p\r\n", part,kstructure,user_alloc_pos);
	printf("mal_init_root_part( part=%08x) : kstructure=%p, first entry=%p\r\n", part,kstructure,user_alloc_pos);

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
	user_alloc_pos = &user_mem_end;

	// Register created root partition to Pip
	updateRootPartition(part);
}

void mal_init_global_var(void)
{
	kernelstructureentriesnb = KERNELSTRUCTUREENTRIESNB();
	mpuentrylength = MPUENTRYLENGTH();
	sh1entrylength = SH1ENTRYLENGTH();
	scentrylength = SCENTRYLENGTH();
	mpuoffset = MPUOFFSET();
	sh1offset = SH1OFFSET();
	scoffset = SCOFFSET();
	nextoffset = NEXTOFFSET();
	min_mpu_region = MINBLOCKSIZE();
}

void mal_init(void)
{
	// Check the MPU
	if (checkMPU()<0)
	{
		// the check didnt pass, panic since Pip relies on the MPU
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
	printf("mal_init( part=%08x) : root is initialized\r\n", part);
}