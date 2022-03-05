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

/**
 * \file mal.h
 * \brief Memory Abstraction Layer common interface
 */

#ifndef __MAL__
#define __MAL__
#include "ADT.h"

#include <stddef.h>

/* Activate */
void __attribute__((section(".text_pip_mal"))) activate(paddr descriptor); //!< Sets up the Partition Descriptor's memory space (MPU configuration)

/* Current page directory */
extern paddr root_partition;
paddr __attribute__((section(".text_pip_mal"))) getCurPartition(void); //!< Gets the current Partition Descriptor
void __attribute__((section(".text_pip_mal"))) updateCurPartition(paddr descriptor); //!< Updates the current Partition Descriptor
void __attribute__((section(".text_pip_mal"))) updateCurPartAndActivate(paddr calleePartDescGlobalId); //!< Updates the current Partition Descriptor and activate it

paddr __attribute__((section(".text_pip_mal"))) getRootPartition(void); //!< Gets the root Partition Descriptor
void __attribute__((section(".text_pip_mal"))) updateRootPartition(paddr descriptor); //!< Updates the root Partition Descriptor

uint32_t __attribute__((section(".text_pip_mal"))) getTableSize(void); //!< Table size
uint32_t __attribute__((section(".text_pip_mal"))) getMaxIndex(void);  //!< Table size
uint32_t __attribute__((section(".text_pip_mal"))) addressEquals(uint32_t addr, uint32_t addr2); //!< Checks whether an address is equal to another.
uint32_t __attribute__((section(".text_pip_mal"))) toAddr(uint32_t input);                       //!< Converts a given uint32_t to an address (only for Haskell FFI purposes)

/* Coq related stuff */
int __attribute__((section(".text_pip_mal"))) geb(const int32_t a, const int32_t b); //!< Greater or equal
int __attribute__((section(".text_pip_mal"))) gtb(const int32_t a, const int32_t b); //!< Greater than
int __attribute__((section(".text_pip_mal"))) leb(const int32_t a, const int32_t b); //!< Lower or equal
int __attribute__((section(".text_pip_mal"))) ltb(const int32_t a, const int32_t b); //!< Lower than
int __attribute__((section(".text_pip_mal"))) eqb(const int32_t a, const int32_t b); //!< Equals
uint32_t __attribute__((section(".text_pip_mal"))) mul3(uint32_t v);                 //!< Multiply an integer with 3
uint32_t __attribute__((section(".text_pip_mal"))) inc(uint32_t val);                //!< Increment an integer
uint32_t __attribute__((section(".text_pip_mal"))) dec(uint32_t val);                //!< Decrement an integer
uint32_t __attribute__((section(".text_pip_mal"))) zero();                           //!< Zero. That's it.
uint32_t __attribute__((section(".text_pip_mal"))) one();                            //!< One.

/* MAL init */
void __attribute__((section(".text_pip_init"))) mal_init(void);
void __attribute__((section(".text_pip_init"))) mal_init_global_var(void);
void __attribute__((section(".text_pip_init"))) mal_init_root_part(paddr part);
paddr __attribute__((section(".text_pip_init"))) mal_create_root_part(void);

/* ARM */
/* MALInternal */
uint32_t __attribute__((section(".text_pip_mal"))) mul(uint32_t a, uint32_t b); //!< Multiply two integers
uint32_t __attribute__((section(".text_pip_mal"))) sub(uint32_t a, uint32_t b); //!< Substract two integers
uint32_t __attribute__((section(".text_pip_mal"))) add(uint32_t a, uint32_t b); //!< Add two integers
uint32_t __attribute__((section(".text_pip_mal"))) getKernelStructureEntriesNb(); //!< The kernel structure entries number
uint32_t __attribute__((section(".text_pip_mal"))) getMaxNbPrepare();             //!<  The maximum number of prepare
uint32_t __attribute__((section(".text_pip_mal"))) getMPURegionsNb(void);         //! The maximum number of physical MPU regions
uint32_t __attribute__((section(".text_pip_mal"))) KERNELSTRUCTURETOTALLENGTH(void);
uint32_t __attribute__((section(".text_pip_mal"))) PDSTRUCTURETOTALLENGTH(void);
uint32_t __attribute__((section(".text_pip_mal"))) MINVIDTBLOCKSIZE(void);
extern __attribute__((section(".bss_pip"))) uint32_t min_mpu_region;
uint32_t __attribute__((section(".text_pip_mal"))) MINBLOCKSIZE(void);

paddr __attribute__((section(".text_pip_mal"))) getKernelStructureStartAddr(paddr blockentryaddr, uint32_t blockentryindex); //!< The start of the kernel structure frame
paddr __attribute__((section(".text_pip_mal"))) getBlockEntryAddrFromKernelStructureStart(paddr blockentryaddr, uint32_t blockentryindex); //!< The address of the block entry given the index and the KS
paddr __attribute__((section(".text_pip_mal"))) getSh1EntryAddrFromKernelStructureStart(paddr blockentryaddr, uint32_t blockentryindex);   //!< The address of the shadow 1 entry
paddr __attribute__((section(".text_pip_mal"))) getSCEntryAddrFromKernelStructureStart(paddr blockentryaddr, uint32_t blockentryindex);    //!< The address of the shadow cut entry
paddr __attribute__((section(".text_pip_mal"))) getNextAddrFromKernelStructureStart(paddr structureaddr);                                  //!< The address of the next pointer
uint32_t __attribute__((section(".text_pip_mal"))) fit_mpu_region(uint32_t block_size);
uint32_t __attribute__((section(".text_pip_mal"))) next_pow2(uint32_t v);
uint32_t __attribute__((section(".text_pip_mal"))) powlog2(uint32_t v);
uint32_t __attribute__((section(".text_pip_mal"))) max_powlog2_alignment(uint32_t v);
block_t __attribute__((section(".text_pip_mal"))) largest_covering_MPU_region(paddr blockentryaddr, paddr addrtocover); //!< Computes the largest MPU region mathing the ARMv7 MPU alignment constraints while covering the target address

paddr __attribute__((section(".text_pip_mal"))) getNullAddr(void); //!< Returns the default null address.
bool __attribute__((section(".text_pip_mal"))) beqAddr(paddr a, paddr b); //!< Compare two addresses
bool __attribute__((section(".text_pip_mal"))) beqIdx(uint32_t a, uint32_t b); //!< Compare two indexes
paddr __attribute__((section(".text_pip_mal"))) addPaddrIdxBytes(paddr a, uint32_t b); //!< adds an offset to a paddr
uint32_t __attribute__((section(".text_pip_mal"))) subPaddr(paddr a, paddr b);         //!< substracts the first paddr to the second.
bool __attribute__((section(".text_pip_mal"))) lebPaddr(const paddr a, const paddr b); //!< the first parameter is less than or equal to the second one.
paddr __attribute__((section(".text_pip_mal"))) predPaddr(paddr a);                    //!< decrements the given address.
paddr __attribute__((section(".text_pip_mal"))) getAddr(paddr addr);                   //!< returns the address //TODO to remove

/* MAL */
PDTable_t __attribute__((section(".text_pip_mal"))) readPDTable(paddr pdaddr); //!< Gets the Partition Descriptor (PD)
paddr __attribute__((section(".text_pip_mal"))) readPDStructurePointer(paddr pdaddr); //!< Gets the first kernel structure
void __attribute__((section(".text_pip_mal"))) writePDStructurePointer(paddr pdaddr, paddr value); //!< Sets the first kernel structure
paddr __attribute__((section(".text_pip_mal"))) readPDFirstFreeSlotPointer(paddr pdaddr);          //!< Gets the first free slot's address
void __attribute__((section(".text_pip_mal"))) writePDFirstFreeSlotPointer(paddr pdaddr, paddr value); //!< Sets the first free slot's address
uint32_t __attribute__((section(".text_pip_mal"))) readPDNbFreeSlots(paddr pdaddr);                    //!< Gets the number of free slots left
void __attribute__((section(".text_pip_mal"))) writePDNbFreeSlots(paddr pdaddr, uint32_t value);       //!< Sets the number of free slots left
uint32_t __attribute__((section(".text_pip_mal"))) readPDNbPrepare(paddr pdaddr);                      //!< Gets the number of prepare done util then.
void __attribute__((section(".text_pip_mal"))) writePDNbPrepare(paddr pdaddr, uint32_t value); //!< Sets the number of prepare done util then
paddr __attribute__((section(".text_pip_mal"))) readPDParent(paddr pdaddr);                    //!< Gets the parent PD's address
void __attribute__((section(".text_pip_mal"))) writePDParent(paddr pdaddr, paddr value); //!< Sets the parent PD's address
paddr __attribute__((section(".text_pip_mal"))) readPDVidt(paddr pdaddr);                //!< Read the VIDT block from the partition descriptor structure.
void __attribute__((section(".text_pip_mal"))) writePDVidt(paddr pdaddr, paddr value); //!< Write the VIDT block to the partition descriptor structure.
paddr __attribute__((section(".text_pip_mal"))) readBlockStartFromBlockEntryAddr(paddr blockentryaddr);              //!< Gets the block's start address from the given entry
void __attribute__((section(".text_pip_mal"))) writeBlockStartFromBlockEntryAddr(paddr blockentryaddr, paddr value); //!< Sets the block's start address
paddr __attribute__((section(".text_pip_mal"))) readBlockEndFromBlockEntryAddr(paddr blockentryaddr);                //!< Gets the block's end address from the given entry
void __attribute__((section(".text_pip_mal"))) writeBlockEndFromBlockEntryAddr(paddr blockentryaddr, paddr value); //!< Sets the block's end address
bool __attribute__((section(".text_pip_mal"))) readBlockAccessibleFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the Accessible flag from the given entry
void __attribute__((section(".text_pip_mal"))) writeBlockAccessibleFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets a memory block as accessible or not
bool __attribute__((section(".text_pip_mal"))) readBlockPresentFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the Present flag from the given entry
void __attribute__((section(".text_pip_mal"))) writeBlockPresentFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets a memory block as present or not
uint32_t __attribute__((section(".text_pip_mal"))) readBlockIndexFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the block index from the given entry
void __attribute__((section(".text_pip_mal"))) writeBlockIndexFromBlockEntryAddr(paddr blockentryaddr, uint32_t value); //!< Sets the block index
bool __attribute__((section(".text_pip_mal"))) readBlockRFromBlockEntryAddr(paddr blockentryaddr);                      //!< Gets the read flag
void __attribute__((section(".text_pip_mal"))) writeBlockRFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets the read flag
bool __attribute__((section(".text_pip_mal"))) readBlockWFromBlockEntryAddr(paddr blockentryaddr);              //!< Gets the write flag
void __attribute__((section(".text_pip_mal"))) writeBlockWFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets the write flag
bool __attribute__((section(".text_pip_mal"))) readBlockXFromBlockEntryAddr(paddr blockentryaddr);              //!< Gets the exec flag
void __attribute__((section(".text_pip_mal"))) writeBlockXFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets the exec flag
BlockEntry_t __attribute__((section(".text_pip_mal"))) readBlockEntryFromBlockEntryAddr(paddr blockentryaddr);  //!< Gets the block entry
void __attribute__((section(".text_pip_mal"))) writeBlockEntryFromBlockEntryAddr(paddr blockentryaddr, BlockEntry_t value); //!< Sets the block entry
void __attribute__((section(".text_pip_mal"))) writeBlockEntryWithIndexFromBlockEntryAddr(paddr blockentryaddr, uint32_t index, BlockEntry_t value); //!< Sets the block entry with given index
paddr __attribute__((section(".text_pip_mal"))) getSh1EntryAddrFromBlockEntryAddr(paddr blockentryaddr);                                             //!< Gets the Sh1 entry from the block entry
paddr __attribute__((section(".text_pip_mal"))) readSh1PDChildFromBlockEntryAddr(paddr blockentryaddr);              //!< Gets the child's PD from the given entry
void __attribute__((section(".text_pip_mal"))) writeSh1PDChildFromBlockEntryAddr(paddr blockentryaddr, paddr value); //!< Sets the entry's child PD
bool __attribute__((section(".text_pip_mal"))) readSh1PDFlagFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the child's PD from the given entry
void __attribute__((section(".text_pip_mal"))) writeSh1PDFlagFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets the entry's PD flag
paddr __attribute__((section(".text_pip_mal"))) readSh1InChildLocationFromBlockEntryAddr(paddr blockentryaddr);    //!< Gets the location of the block in the child
void __attribute__((section(".text_pip_mal"))) writeSh1InChildLocationFromBlockEntryAddr(paddr blockentryaddr, paddr value); //!<Sets the block's location in the child
void __attribute__((section(".text_pip_mal"))) writeSh1EntryFromBlockEntryAddr(paddr blockentryaddr, Sh1Entry_t newsh1entry);//! Sets the block's Sh1 entry
paddr __attribute__((section(".text_pip_mal"))) getSCEntryAddrFromBlockEntryAddr(paddr blockentryaddr);                      //! Gets the SC entry from the block entry
paddr __attribute__((section(".text_pip_mal"))) readSCOriginFromBlockEntryAddr(paddr blockentryaddr);                        //! Gets the block's origin
void __attribute__((section(".text_pip_mal"))) writeSCOriginFromBlockEntryAddr(paddr blockentryaddr, paddr value); //! Sets the block's origin
paddr __attribute__((section(".text_pip_mal"))) readSCNextFromBlockEntryAddr(paddr blockentryaddr);                //! Gets the block's next subblock
void __attribute__((section(".text_pip_mal"))) writeSCNextFromBlockEntryAddr(paddr blockentryaddr, paddr value); //! Sets the block's next subblock
void __attribute__((section(".text_pip_mal"))) writeSCEntryFromBlockEntryAddr(paddr blockentryaddr, SCEntry_t newscentry); //! Sets the block's SC entry
paddr __attribute__((section(".text_pip_mal"))) readNextFromKernelStructureStart(paddr structureaddr);                     //! Gets the block's next subblock
void __attribute__((section(".text_pip_mal"))) writeNextFromKernelStructureStart(paddr structureaddr, paddr newnextstructure); //! Sets the block's SC entry
bool __attribute__((section(".text_pip_mal"))) eraseBlock(paddr startAddr, paddr endAddr);                                     //! Erases the memory block defined by (startAddr, endAddr).
void __attribute__((section(".text_pip_mal"))) writePDTable(paddr addr, PDTable_t newpdtable); //! Sets a new PD Table at the given address
PDTable_t __attribute__((section(".text_pip_mal"))) getDefaultPDTable();                       //! Returns the default PD Table without initialisation
PDTable_t __attribute__((section(".text_pip_mal"))) getEmptyPDTable();                         //! Returns the default PD Table with initialisation
BlockEntry_t __attribute__((section(".text_pip_mal"))) getDefaultBlockEntry();                 //! Returns the default block entry
Sh1Entry_t __attribute__((section(".text_pip_mal"))) getDefaultSh1Entry();                     //! Returns the default Sh1 entry
SCEntry_t __attribute__((section(".text_pip_mal"))) getDefaultSCEntry();                       //! Returns the default SC entry
BlockEntry_t __attribute__((section(".text_pip_mal"))) buildBlockEntry(paddr startaddr, paddr endaddr, bool accessiblebit, bool presentbit); //! Constructs a block entry given the attributes
paddr __attribute__((section(".text_pip_mal"))) getPDStructurePointerAddrFromPD(paddr pdaddr);                                               //! Gets the structure pointer of the given PD
bool __attribute__((section(".text_pip_mal"))) checkEntry(paddr kstructurestart, paddr blockentryaddr);                                      //! Checks a block entry is valid in the kernel structure
bool __attribute__((section(".text_pip_mal"))) checkBlockInRAM(paddr blockentryaddr);                                                        //! Checks whether the block is entirely in RAM
bool __attribute__((section(".text_pip_mal"))) check32Aligned(paddr addrToCheck);                                                            //! Checks whether the address is 32-bytes aligned
blockOrError __attribute__((section(".text_pip_mal"))) blockAttr(paddr blockentryaddr, BlockEntry_t blockentry);                             //! Wrapper to create a block and its attributes

paddr __attribute__((section(".text_pip_mal"))) readBlockFromPhysicalMPU(paddr pd, uint32_t MPURegionNb);  //! Reads the block configured at the given region of the physical MPU.
void __attribute__((section(".text_pip_mal"))) removeBlockFromPhysicalMPU(paddr pd, paddr blockentryaddr); //! Removes a block from the physical MPU.
void __attribute__((section(".text_pip_mal"))) removeBlockFromPhysicalMPUIfNotAccessible (paddr pd, paddr idblock, bool accessiblebit); //! Removes a block from the physical MPU if not accessible.
void __attribute__((section(".text_pip_mal"))) replaceBlockInPhysicalMPU(paddr pd, paddr blockblockentryaddr, uint32_t MPURegionNb); //! Replaces a block in the physical MPU.
uint32_t __attribute__((section(".text_pip_mal"))) findBlockIdxInPhysicalMPU(paddr pd, paddr blockToFind, uint32_t defaultnb); //! Returns the MPU region number where the block is configured

void __attribute__((section(".text_pip_mal"))) configure_LUT_entry(uint32_t* LUT, uint32_t entryindex, paddr blockentryaddr, paddr addrtocover); //! Configures the LUT entry at given index with the given MPU entry
void __attribute__((section(".text_pip_mal"))) clear_LUT(uint32_t* LUT); //! Defaults all LUT entries
int __attribute__((section(".text_pip_mal"))) checkMPU(); //! Checks the MPU
int __attribute__((section(".text_pip_mal"))) initMPU(); //! Inits the MPU
#endif
