/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2022)                */
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
 *                              ROM                      RAM
 *    0x00000000 +--> +--------------------+   +--------------------+ <--+ 0x20000000
 *               |    |                    |   |                    |    |
 *               |    |   .vector_table    |   |     .root.stack    |    |
 *               |    |                    |   |                    |    |
 *               |    +--------------------+   +--------------------+    |
 *               |    |                    |   |                    |    |
 *               |    |       .text        |   |      .root.vidt    |    |
 *               |    |                    |   |                    |    +-- R0
 *         PIP --+    +--------------------+   +--------------------+    |
 *               |    |                    |   |                    |    |
 *               |    |       .data        |   |                    |    |
 *               |    |                    |   |                    |    |
 *               |    +--------------------+   |                    | <--+ 0x20008000
 *               |    |                    |   |                    |    |
 *               |    |      .padding      |   |                    |    |
 *               |    |                    |   |                    |    +-- R1
 *               +--> +--------------------+   |                    |    |
 *               |    |                    |   |                    |    |
 *               |    |                    |   +--------------------+ <--+
 *               |    |                    |   |                    |    |
 *               |    |                    |   |       .data        |    |
 *               |    |                    |   |                    |    |
 *               |    |                    |   +--------------------+    |
 *         R2  --+    |        ...         |   |                    |    |
 *               |    |                    |   |        .bss        |    +-- PIP
 *               |    |                    |   |                    |    |
 *               |    |                    |   +--------------------+    |
 *               |    |                    |   |                    |    |
 *               |    |                    |   |       .stack       |    |
 *               |    |                    |   |                    |    |
 *    0x00080000 +--> +--------------------+   +--------------------+ <--+ 0x20010000
 *
 * MPU regions:
 *
 *   R0: MPU region containing the first 32K of RAM accessible to the root partition.
 *   R1: MPU region containing the remaining RAM accessible to the root partition.
 *   R2: MPU region containing the ROM accessible to the root partition.
 */

/* The size of the ROM memory. */
__romSize = 512K ;

/* The size of the RAM memory of PIP. */
__pipRamSize = 4K ;

/* The size of the RAM memory of the root partition. */
__rootRamSize = 64K - __pipRamSize ;

/* The start address of the ROM. */
__romStart = 0x00000000 ;

/* The start address of the RAM. */
__ramStart = 0x20000000 ;

/* The start address of the RAM of the root partition. */
__rootRamStart = __ramStart ;

/* The start address of RAM of PIP. */
__pipRamStart = __rootRamStart + __rootRamSize ;

/* The end address of the ROM. */
__romEnd = __romStart + __romSize ;

/* The end addres of the RAM. */
__ramEnd = 0x20010000 ;

/* The end address of the RAM of the root partition. */
__rootRamEnd = __rootRamStart + __rootRamSize ;

/* The end address of the RAM of PIP. */
__pipRamEnd = __pipRamStart + __pipRamSize;

/* The stack size of PIP. */
__pipStackSize = 1024 ;

/* The stack size of the root partition. */
__rootStackSize = 1024 ;

/* The VIDT size of the root partition. */
__rootVidtSize = 256 ;

/* The configuration of the MPU region 0. */
__mpuRegion0Size     = 32K ;
__mpuRegion0Start    = __rootRamStart ;
__mpuRegion0End      = __mpuRegion0Start + __mpuRegion0Size ;
__mpuRegion0Read     = 1 ;
__mpuRegion0Write    = 1 ;
__mpuRegion0Execute  = 0 ;

/* The configuration of the MPU region 1. */
__mpuRegion1Size     = __rootRamEnd - __mpuRegion0Size ;
__mpuRegion1Start    = __mpuRegion0End ;
__mpuRegion1End      = __mpuRegion1Start + __mpuRegion1Size ;
__mpuRegion1Read     = 1 ;
__mpuRegion1Write    = 1 ;
__mpuRegion1Execute  = 0 ;

/* The configuration of the MPU region 2. */
__mpuRegion2Size     = __romEnd - __unusedRomStart ;
__mpuRegion2Start    = __unusedRomStart ;
__mpuRegion2End      = __mpuRegion2Start + __mpuRegion2Size ;
__mpuRegion2Read     = 1 ;
__mpuRegion2Write    = 0 ;
__mpuRegion2Execute  = 1 ;

MEMORY
{
	ROM      (rx)  : ORIGIN = __romStart,     LENGTH = __romSize
	ROOT_RAM (xrw) : ORIGIN = __rootRamStart, LENGTH = __rootRamSize
	PIP_RAM  (xrw) : ORIGIN = __pipRamStart,  LENGTH = __pipRamSize
}

OUTPUT_FORMAT(
	"elf32-littlearm",
	"elf32-littlearm",
	"elf32-littlearm"
)

OUTPUT_ARCH(arm)

ENTRY(_start)

SECTIONS
{
	.vector_table :
	{
		. = ALIGN( 4 ) ;
		__vectorTableStart = . ;
		KEEP( *(.vector_table*) )
		. = ALIGN( 4 ) ;
		__vectorTableEnd = . ;
	} > ROM

	.text :
	{
		. = ALIGN( 4 ) ;
		*(.text*)
		*(.rodata*)
		. = ALIGN( 4 ) ;
	} > ROM

	.data :
	{
		. = ALIGN( 4 ) ;
		__pipDataStart = . ;
		*(.data*)
		. = ALIGN( 4 ) ;
		__pipDataEnd = . ;
	} > PIP_RAM AT > ROM

	__pipDataRomStart = LOADADDR(.data) ;
	__pipDataRomEnd = __pipDataRomStart +
		( __pipDataEnd - __pipDataStart ) ;

	/*
	 * Warning: this section must be the last section in ROM.
	 *
	 * It is only used to align the two following symbols
	 * to a multiple of 32. Since there are no input
	 * sections in the '.padding' output section, ld sets
	 * this section to the NOBITS type. objcopy ignores all
	 * NOBITS sections, so the size of the output binary
	 * file is not aligned to 32 bytes. To solve this
	 * problem, we use the '--pad-to' option of objcopy
	 * with the symbol address '__root' to force the
	 * alignment.
	 */
	.padding :
	{
		. = ALIGN( 32 ) ;
		__unusedRomStart = . ;
		__root = . ;
	} > ROM

	.bss (NOLOAD) :
	{
		. = ALIGN( 4 ) ;
		__pipBssStart = . ;
		*(.bss*)
		*(COMMON)
		. = ALIGN( 4 ) ;
		__pipBssEnd = . ;
	} > PIP_RAM

	.stack (NOLOAD) :
	{
		. = ALIGN( 8 ) ;
		__pipStackLimit = . ;
		. += __pipStackSize ;
		. = ALIGN( 8 ) ;
		__pipStackTop = . ;
	} > PIP_RAM

	.root.stack (NOLOAD) :
	{
		. = ALIGN( 8 ) ;
		__rootStackLimit = . ;
		. += __rootStackSize ;
		__rootStackTop = . ;
		. = ALIGN( 8 ) ;
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

	/* Assert that the following values are true before linking.
	 *
	 * WARNING: We check that the start address of the unused RAM
	 * plus 32 does not overflow the RAM because it is the smallest
	 * valid MPU region for ARMv7-M.
	 */
	ASSERT( ( __mpuRegion0Size  & 31 ) ==            0, "The MPU region 0 is not a power of two greater than or equal to 32..." )
	ASSERT( ( __unusedRomStart      )  <=     __romEnd, "The sections overflow the ROM..." )
	ASSERT( ( __unusedRamStart + 32 )  <= __rootRamEnd, "The sections overflow the RAM..." )
}
