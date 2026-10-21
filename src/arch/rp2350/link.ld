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

/* Memory layout:
 *
 *                       ROM (XIP flash)                   RAM (striped SRAM)
 *    0x10000000 +--> +--------------------+   +--------------------+ <--+ 0x20000000
 *               |    |                    |   |                    |    |
 *               |    |   .picobin_block   |   |     .root.stack    |    |
 *               |    |                    |   |                    |    |
 *               |    +--------------------+   +--------------------+    |
 *               |    |                    |   |                    |    |
 *         PIP --+    |       .text        |   |     .root.vidt     |    +-- R0
 *               |    |                    |   |                    |    |
 *               |    +--------------------+   +--------------------+    |
 *               |    |                    |   |                    |    |
 *               |    |       .data        |   |        ...         |    |
 *               |    |                    |   |                    |    |
 *               +--> +--------------------+   +--------------------+ <--+ 0x20040000
 *               |    |      .padding      |   |                    |    |
 *               |    +--------------------+   |       .data        |    |
 *               |    |                    |   |                    |    |
 *               |    |                    |   +--------------------+    |
 *         R1  --+    |    root partition  |   |                    |    |
 *               |    |                    |   |        .bss        |    +-- PIP
 *               |    |                    |   |                    |    |
 *               +--> +--------------------+   +--------------------+    |
 *                    |                    |   |                    |    |
 *                    |        ...         |   |       .stack       |    |
 *                    |                    |   |                    |    |
 *    0x10400000 +--> +--------------------+   +--------------------+ <--+ 0x20048000
 *                                             |                    |
 *                                             |  unassigned (224K) |
 *                                             |                    |
 *                                             +--------------------+ <--+ 0x20080000
 *
 * PMP regions mapped statically to the root partition at boot:
 *
 *   R0: the 256K of RAM accessible to the root partition.
 *   R1: the 64K of ROM holding the root partition binary.
 *
 * Unlike the ARM target, which had to tile all of its 60K of RAM into four
 * descending power-of-two regions because 60K was all there was, this target
 * spends one region on one naturally-aligned 256K block. PMP slots are the
 * scarce resource here, not RAM: there are five partition-visible regions in
 * total (see pmp.h), so the four left over are what the root partition has to
 * cut blocks out of at runtime. The remaining 224K of SRAM is deliberately
 * left unassigned rather than spent on two or three more regions.
 *
 * Pip's own RAM costs no PMP region at all: a region with L=0 does not
 * constrain M-mode, which is this target's equivalent of the ARM
 * MPU_CTRL_PRIVDEFENA. The 32K here, against the nRF52832's 4K, pays for the
 * 4K kernel stack that now also holds the trap frame, since RISC-V stacks
 * nothing in hardware.
 *
 * SCRATCH_X and SCRATCH_Y (0x20080000 and 0x20081000) are left out: they are
 * not contiguous with the striped SRAM, so including them would break the
 * single naturally-aligned region above for no gain.
 */

__romSize = 4M ;
__ramSize = 512K ;

__romStart = 0x10000000 ;
__ramStart = 0x20000000 ;

__pipStackSize = 4K ;
__rootStackSize = 4K ;
__rootVidtSize = 256 ;

__romEnd = __romStart + __romSize ;
__ramEnd = __ramStart + __ramSize ;

__pipRamSize = 32K ;
__rootRamSize = 256K ;

__pipRamStart = __ramStart + __rootRamSize ;
__rootRamStart = __ramStart ;

__pipRamEnd = __pipRamStart + __pipRamSize ;
__rootRamEnd = __rootRamStart + __rootRamSize ;

/* The root partition's RAM: one NAPOT region covering all of ROOT_RAM. */
__mpuRegion0Size = __rootRamSize ;
__mpuRegion0Start = __rootRamStart ;
__mpuRegion0End = __mpuRegion0Start + __mpuRegion0Size ;

/* The root partition's ROM. Unlike the ARM target, which gave the root
 * __unusedRomStart..__romEnd, this is a fixed power-of-two window starting at
 * __root, so that one NAPOT entry covers it exactly. Growing the root
 * partition past it means raising both this size and the .padding alignment
 * below, which must stay equal. */
__mpuRegion1Size = 64K ;
__mpuRegion1Start = __root ;
__mpuRegion1End = __mpuRegion1Start + __mpuRegion1Size ;

MEMORY
{
	ROM      (rx)  : ORIGIN = __romStart,     LENGTH = __romSize
	ROOT_RAM (xrw) : ORIGIN = __rootRamStart, LENGTH = __rootRamSize
	PIP_RAM  (xrw) : ORIGIN = __pipRamStart,  LENGTH = __pipRamSize
}

OUTPUT_FORMAT(
	"elf32-littleriscv",
	"elf32-littleriscv",
	"elf32-littleriscv"
)

OUTPUT_ARCH(riscv)

ENTRY(Reset_Handler)

SECTIONS
{
	/* The bootrom looks for a picobin block loop in the first 4K of the
	 * image and refuses to boot without one, so this section must come
	 * first and must be kept. */
	.picobin_block :
	{
		. = ALIGN( 4 ) ;
		__picobinBlockStart = . ;
		KEEP( *(.picobin_block*) )
		. = ALIGN( 4 ) ;
		__picobinBlockEnd = . ;
	} > ROM

	.text :
	{
		. = ALIGN( 4 ) ;
		*(.text*)
		*(.rodata*)
		*(.srodata*)
		. = ALIGN( 4 ) ;
	} > ROM

	.data :
	{
		. = ALIGN( 4 ) ;
		__pipDataStart = . ;
		*(.data*)
		*(.sdata*)
		. = ALIGN( 4 ) ;
		__pipDataEnd = . ;
	} > PIP_RAM AT > ROM

	__pipDataRomStart = LOADADDR(.data) ;
	__pipDataRomEnd = __pipDataRomStart +
		( __pipDataEnd - __pipDataStart ) ;

	/*
	 * Warning: this section must be the last section in ROM.
	 *
	 * It aligns __root to the size of the root partition's PMP region,
	 * which NAPOT requires. Since there are no input sections in the
	 * '.padding' output section, ld sets this section to the NOBITS type.
	 * objcopy ignores all NOBITS sections, so the size of the output
	 * binary file is not aligned. To solve this problem, we use the
	 * '--pad-to' option of objcopy with the symbol address '__root' to
	 * force the alignment.
	 */
	.padding :
	{
		. = ALIGN( 64K ) ;
		__unusedRomStart = . ;
		__root = . ;
	} > ROM

	.bss (NOLOAD) :
	{
		. = ALIGN( 4 ) ;
		__pipBssStart = . ;
		*(.bss*)
		*(.sbss*)
		*(COMMON)
		. = ALIGN( 4 ) ;
		__pipBssEnd = . ;
	} > PIP_RAM

	.stack (NOLOAD) :
	{
		. = ALIGN( 16 ) ;
		__pipStackLimit = . ;
		. += __pipStackSize ;
		. = ALIGN( 16 ) ;
		__pipStackTop = . ;
	} > PIP_RAM

	.root.stack (NOLOAD) :
	{
		. = ALIGN( 16 ) ;
		__rootStackLimit = . ;
		. += __rootStackSize ;
		__rootStackTop = . ;
		. = ALIGN( 16 ) ;
	} > ROOT_RAM

	.root.vidt (NOLOAD) :
	{
		. = ALIGN( 4 ) ;
		__rootVidtStart = . ;
		. += __rootVidtSize ;
		__rootVidtEnd = . ;
		. = ALIGN( 4 ) ;
		__unusedRamStart = . ;
	} > ROOT_RAM

	/* Nothing unwinds in Pip, and riscv64-elf-gcc emits .eh_frame by
	 * default. Left unplaced it becomes an orphan section that ld puts in
	 * ROM between the picobin block and .text, which both wastes flash
	 * and moves the entry point for no reason. */
	/DISCARD/ :
	{
		*(.eh_frame*)
		*(.comment)
	}

	/* Assert that the following values are true before linking.
	 *
	 * The two region assertions are what NAPOT needs: a power-of-two size
	 * and a base aligned on it. They are stricter than the ARM target's
	 * single 32-byte check, which is why the whole-of-RAM region above can
	 * be trusted to be expressible at all.
	 *
	 * WARNING: We check that the start address of the unused RAM plus 32
	 * does not overflow the RAM because 32 bytes is Pip's minBlockSize.
	 * The PMP granule is 4 bytes, so the hardware is not what sets this.
	 */
	ASSERT( ( __mpuRegion0Size & ( __mpuRegion0Size - 1 ) )   ==            0, "The PMP region 0 size is not a power of two..." )
	ASSERT( ( __mpuRegion0Start & ( __mpuRegion0Size - 1 ) )  ==            0, "The PMP region 0 is not naturally aligned..." )
	ASSERT( ( __mpuRegion1Size & ( __mpuRegion1Size - 1 ) )   ==            0, "The PMP region 1 size is not a power of two..." )
	ASSERT( ( __mpuRegion1Start & ( __mpuRegion1Size - 1 ) )  ==            0, "The PMP region 1 is not naturally aligned..." )
	ASSERT( ( __mpuRegion1End )                               <=     __romEnd, "The root partition region overflows the ROM..." )
	ASSERT( ( __root & 31 )                                   ==            0, "The root partition binary is not 32-byte aligned..." )
	ASSERT( ( __unusedRomStart )                              <=     __romEnd, "The sections overflow the ROM..." )
	ASSERT( ( __unusedRamStart + 32 )                         <= __rootRamEnd, "The sections overflow the RAM..." )
	ASSERT( ( __pipStackTop )                                 <=   __pipRamEnd, "The sections overflow Pip's RAM..." )
}
