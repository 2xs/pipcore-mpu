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

#ifndef __MEMLAYOUT_H__
#define __MEMLAYOUT_H__

/*!
 * \brief The stack size of PIP in bytes.
 *
 * \see The definition in the link.ld file.
 */
extern void *__pipStackSize;

/*!
 * \brief The heap size of PIP in bytes.
 *
 * \see The definition in the link.ld file.
 */
extern void *__pipHeapSize;

/*!
 * \brief The stack size of the root partition in bytes.
 *
 * \see The definition in the link.ld file.
 */
extern void *__rootStackSize;

/*!
 * \brief The start address of the on-chip peripherals.
 *
 * \see The definition in the link.ld file.
 */
extern void *__periphStart;

/*!
 * \brief The end address of the on-chip peripherals.
 *
 * \see The definition in the link.ld file.
 */
extern void *__periphEnd;

/*!
 * \brief The start address of the RAM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__ramStart;

/*!
 * \brief The end address of the RAM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__ramEnd;

/*!
 * \brief The start address of the ROM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__romStart;

/*!
 * \brief The end address of the ROM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__romEnd;

/*!
 * \brief The start address of the vector table in ROM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__vectorTableStart;

/*!
 * \brief The end address of the vector table in ROM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__vectorTableEnd;

/*!
 * \brief The start address of the code section of PIP in ROM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__pipTextStart;

/*!
 * \brief The end address of the code of PIP in ROM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__pipTextEnd;

/*!
 * \brief The start address of the initialized data of PIP in RAM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__pipDataStart;

/*!
 * \brief The end address of the initialized data of PIP in RAM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__pipDataEnd;

/*!
 * \brief The start address of the initialized data of PIP in ROM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__pipDataRomStart;

/*!
 * \brief The end address of the initialized data of PIP in ROM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__pipDataRomEnd;

/*!
 * \brief The start address of the root partition binary in ROM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__rootBinaryStart;

/*!
 * \brief The entry point address of the root partition in ROM.
 *
 * \see The definition in the root-partition-linker.sh file.
 */
extern void *__rootBinaryEntryPoint;

/*!
 * \brief The end address of the root partition binary in ROM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__rootBinaryEnd;

/*!
 * \brief The start address of the unused ROM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__unusedRomStart;

/*!
 * \brief The start address of the uninitialized data of PIP in RAM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__pipBssStart;

/*!
 * \brief The end address of the uninitialized data of PIP in RAM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__pipBssEnd;

/*!
 * \brief The base address of the heap of PIP in RAM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__HeapBase;

/*!
 * \brief The limit address of the heap of PIP in RAM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__HeapLimit;

/*!
 * \brief The limit address of the stack of PIP in RAM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__pipStackLimit;

/*!
 * \brief The top address the stack of PIP in RAM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__pipStackTop;

/*!
 * \brief The start address of the root partition kernel structures in
 *        RAM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__rootKernStructStart;

/*!
 * \brief The end address of the root partition kernel structures in
 *        RAM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__rootKernStructEnd;

/*!
 * \brief The limit address of the stack of the root partition in RAM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__rootStackLimit;

/*!
 * \brief The top address of the stack of the root partition in RAM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__rootStackTop;

/*!
 * \brief The start address of the free RAM.
 *
 * \see The definition in the link.ld file.
 */
extern void *__unusedRamStart;

#endif /* __MEMLAYOUT_H__ */