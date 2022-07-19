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
 *
 *                              ROM                      RAM
 *    0x00000000 +--> +--------------------+   +--------------------+ <--+ 0x20000000
 *               |    |                    |   |                    |    |
 *               |    |   .vector_table    |   |       .data        |    |
 *               |    |                    |   |                    |    |
 *               |    +--------------------+   +--------------------+    |
 *               |    |                    |   |                    |    |
 *         PIP --+    |       .text        |   |        .bss        |    +-- PIP
 *               |    |                    |   |                    |    |
 *               |    +--------------------+   +--------------------+    |
 *               |    |                    |   |                    |    |
 *               |    |       .data        |   |       .stack       |    |
 *               |    |                    |   |                    |    |
 *               +--> +--------------------+   +--------------------+ <--+
 *               |    |                    |   |                    |    |
 *               |    |                    |   |     .root_stack    |    +-- MPU R1
 *               |    |                    |   |                    |    |
 *               |    |                    |   +--------------------+ <--+
 *               |    |                    |   |                    |    |
 *               |    |                    |   |                    |    |
 *               |    |                    |   |                    |    |
 *               |    |                    |   |                    |    |
 *      MPU R0 --+    |        ...         |   |                    |    |
 *               |    |                    |   |                    |    |
 *               |    |                    |   |                    |    +-- MPU R2
 *               |    |                    |   |                    |    |
 *               |    |                    |   |                    |    |
 *               |    |                    |   |                    |    |
 *               |    |                    |   |                    |    |
 *               |    |                    |   |                    |    |
 *               |    |                    |   |                    |    |
 *    0x00080000 +--> +--------------------+   +--------------------+ <--+ 0x20010000
 *
 * MPU regions:
 *
 *   - MPU R0: MPU region containing the ROM accessible to the root partition.
 *   - MPU R1: MPU region containing the stack of the root partition.
 *   - MPU R2: MPU region containing the RAM accessible to the root partition.
 */

/*
 * The stack size of PIP in bytes.
 */
__pipStackSize = 1024 ;

/* The stack size of the root partition in bytes.
 *
 * WARNING: Must be a power of 2 greater than or equal to 32 which is
 * the minimum valid MPU region size for ARMv7-M.
 */
__rootStackSize = 1024 ;

MEMORY
{
	ROM (rx)  : ORIGIN = 0x00000000, LENGTH = 512K
	RAM (xrw) : ORIGIN = 0x20000000, LENGTH = 64K
}

OUTPUT_FORMAT(
	"elf32-littlearm",
	"elf32-littlearm",
	"elf32-littlearm"
)

OUTPUT_ARCH(arm)

ENTRY(_start)

/*
 * The start address of the RAM.
 */
__ramStart = ORIGIN(RAM);

/*
 * The end address of the RAM.
 */
__ramEnd = ORIGIN(RAM) + LENGTH(RAM);

/*
 * The start address of the ROM.
 */
__romStart = ORIGIN(ROM);

/*
 * The end address of the ROM.
 */
__romEnd = ORIGIN(ROM) + LENGTH(ROM);

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
		__root = . ;
	} > ROM

	.data :
	{
		. = ALIGN( 4 ) ;
		__pipDataStart = . ;
		*(.data*)
		. = ALIGN( 4 ) ;
		__pipDataEnd = . ;
	} > RAM AT > ROM

	__pipDataRomStart = LOADADDR(.data) ;
	__pipDataRomEnd = __pipDataRomStart +
		( __pipDataEnd - __pipDataStart ) ;
	__unusedRomStart = __pipDataRomEnd ;

	.bss (NOLOAD) :
	{
		. = ALIGN( 4 ) ;
		__pipBssStart = . ;
		*(.bss*)
		*(COMMON)
		. = ALIGN( 4 ) ;
		__pipBssEnd = . ;
	} > RAM

	.stack (NOLOAD) :
	{
		. = ALIGN( 8 ) ;
		__pipStackLimit = . ;
		. += __pipStackSize ;
		. = ALIGN( 8 ) ;
		__pipStackTop = . ;
	} > RAM

	.root_stack (NOLOAD) :
	{
		. = ALIGN( __rootStackSize ) ;
		__rootStackLimit = . ;
		. += __rootStackSize ;
		__rootStackTop = . ;
		. = ALIGN( 32 ) ;
		__unusedRamStart = . ;
	} > RAM

	/* Assert that the following values are true before linking.
	 *
	 * WARNING: We check that the start address of the unused RAM
	 * plus 32 does not overflow the RAM because it is the smallest
	 * valid MPU region for ARMv7-M.
	 */
	ASSERT( ( __rootStackSize  & 31 ) ==        0, "The root partition stack size is not a power of two greater than or equal to 32..." )
	ASSERT( ( __unusedRomStart      ) <= __romEnd, "The sections overflow the ROM..." )
	ASSERT( ( __unusedRamStart + 32 ) <= __ramEnd, "The sections overflow the RAM..." )
}
