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
void __attribute__((section(".text_pip"))) activate(paddr descriptor); //!< Sets up the Partition Descriptor's memory space (MPU configuration)

/* Current page directory */
extern paddr root_partition;
paddr __attribute__((section(".text_pip"))) getCurPartition(void); //!< Gets the current Partition Descriptor
void __attribute__((section(".text_pip"))) updateCurPartition(paddr descriptor); //!< Updates the current Partition Descriptor
void __attribute__((section(".text_pip"))) updateCurPartAndActivate(paddr calleePartDescGlobalId); //!< Updates the current Partition Descriptor and activate it

paddr __attribute__((section(".text_pip"))) getRootPartition(void); //!< Gets the root Partition Descriptor
void __attribute__((section(".text_pip"))) updateRootPartition(paddr descriptor); //!< Updates the root Partition Descriptor

uint32_t __attribute__((section(".text_pip"))) getTableSize(void); //!< Table size
uint32_t __attribute__((section(".text_pip"))) getMaxIndex(void);  //!< Table size
uint32_t __attribute__((section(".text_pip"))) addressEquals(uint32_t addr, uint32_t addr2); //!< Checks whether an address is equal to another.
uint32_t __attribute__((section(".text_pip"))) toAddr(uint32_t input);                       //!< Converts a given uint32_t to an address (only for Haskell FFI purposes)

/* Coq related stuff */
int __attribute__((section(".text_pip"))) geb(const int32_t a, const int32_t b); //!< Greater or equal
int __attribute__((section(".text_pip"))) gtb(const int32_t a, const int32_t b); //!< Greater than
int __attribute__((section(".text_pip"))) leb(const int32_t a, const int32_t b); //!< Lower or equal
int __attribute__((section(".text_pip"))) ltb(const int32_t a, const int32_t b); //!< Lower than
int __attribute__((section(".text_pip"))) eqb(const int32_t a, const int32_t b); //!< Equals
uint32_t __attribute__((section(".text_pip"))) mul3(uint32_t v);                 //!< Multiply an integer with 3
uint32_t __attribute__((section(".text_pip"))) inc(uint32_t val);                //!< Increment an integer
uint32_t __attribute__((section(".text_pip"))) dec(uint32_t val);                //!< Decrement an integer
uint32_t __attribute__((section(".text_pip"))) zero();                           //!< Zero. That's it.
uint32_t __attribute__((section(".text_pip"))) one();                            //!< One.

void __attribute__((section(".text_pip"))) mal_init(void);
void __attribute__((section(".text_pip"))) mal_init_global_var(void);
void __attribute__((section(".text_pip"))) mal_init_root_part(paddr part);
paddr __attribute__((section(".text_pip"))) mal_create_root_part(void);

/* ARM */
/* MALInternal */
uint32_t __attribute__((section(".text_pip"))) mul(uint32_t a, uint32_t b); //!< Multiply two integers
uint32_t __attribute__((section(".text_pip"))) sub(uint32_t a, uint32_t b); //!< Substract two integers
uint32_t __attribute__((section(".text_pip"))) add(uint32_t a, uint32_t b); //!< Add two integers
uint32_t __attribute__((section(".text_pip"))) getKernelStructureEntriesNb(); //!< The kernel structure entries number
uint32_t __attribute__((section(".text_pip"))) getMaxNbPrepare();             //!<  The maximum number of prepare
uint32_t __attribute__((section(".text_pip"))) getMPURegionsNb(void);         //! The maximum number of physical MPU regions
uint32_t __attribute__((section(".text_pip"))) KERNELSTRUCTURETOTALLENGTH(void);
uint32_t __attribute__((section(".text_pip"))) PDSTRUCTURETOTALLENGTH(void);
uint32_t __attribute__((section(".text_pip"))) MINVIDTBLOCKSIZE(void);
extern __attribute__((section(".bss_pip"))) uint32_t min_mpu_region;
uint32_t __attribute__((section(".text_pip"))) MINBLOCKSIZE(void);

paddr __attribute__((section(".text_pip"))) getKernelStructureStartAddr(paddr blockentryaddr, uint32_t blockentryindex); //!< The start of the kernel structure frame
paddr __attribute__((section(".text_pip"))) getBlockEntryAddrFromKernelStructureStart(paddr blockentryaddr, uint32_t blockentryindex); //!< The address of the block entry given the index and the KS
paddr __attribute__((section(".text_pip"))) getSh1EntryAddrFromKernelStructureStart(paddr blockentryaddr, uint32_t blockentryindex);   //!< The address of the shadow 1 entry
paddr __attribute__((section(".text_pip"))) getSCEntryAddrFromKernelStructureStart(paddr blockentryaddr, uint32_t blockentryindex);    //!< The address of the shadow cut entry
paddr __attribute__((section(".text_pip"))) getNextAddrFromKernelStructureStart(paddr structureaddr);                                  //!< The address of the next pointer
uint32_t __attribute__((section(".text_pip"))) fit_mpu_region(uint32_t block_size);
uint32_t __attribute__((section(".text_pip"))) next_pow2(uint32_t v);
uint32_t __attribute__((section(".text_pip"))) powlog2(uint32_t v);
uint32_t __attribute__((section(".text_pip"))) max_powlog2_alignment(uint32_t v);
block_t __attribute__((section(".text_pip"))) largest_covering_MPU_region(paddr blockentryaddr, paddr addrtocover); //!< Computes the largest MPU region mathing the ARMv7 MPU alignment constraints while covering the target address

paddr __attribute__((section(".text_pip"))) getNullAddr(void); //!< Returns the default null address.
bool __attribute__((section(".text_pip"))) beqAddr(paddr a, paddr b); //!< Compare two addresses
bool __attribute__((section(".text_pip"))) beqIdx(uint32_t a, uint32_t b); //!< Compare two indexes
paddr __attribute__((section(".text_pip"))) addPaddrIdxBytes(paddr a, uint32_t b); //!< adds an offset to a paddr
uint32_t __attribute__((section(".text_pip"))) subPaddr(paddr a, paddr b);         //!< substracts the first paddr to the second.
bool __attribute__((section(".text_pip"))) lebPaddr(const paddr a, const paddr b); //!< the first parameter is less than or equal to the second one.
paddr __attribute__((section(".text_pip"))) predPaddr(paddr a);                    //!< decrements the given address.
paddr __attribute__((section(".text_pip"))) getAddr(paddr addr);                   //!< returns the address //TODO to remove

/* MAL */
PDTable_t __attribute__((section(".text_pip"))) readPDTable(paddr pdaddr); //!< Gets the Partition Descriptor (PD)
paddr __attribute__((section(".text_pip"))) readPDStructurePointer(paddr pdaddr); //!< Gets the first kernel structure
void __attribute__((section(".text_pip"))) writePDStructurePointer(paddr pdaddr, paddr value); //!< Sets the first kernel structure
paddr __attribute__((section(".text_pip"))) readPDFirstFreeSlotPointer(paddr pdaddr);          //!< Gets the first free slot's address
void __attribute__((section(".text_pip"))) writePDFirstFreeSlotPointer(paddr pdaddr, paddr value); //!< Sets the first free slot's address
uint32_t __attribute__((section(".text_pip"))) readPDNbFreeSlots(paddr pdaddr);                    //!< Gets the number of free slots left
void __attribute__((section(".text_pip"))) writePDNbFreeSlots(paddr pdaddr, uint32_t value);       //!< Sets the number of free slots left
uint32_t __attribute__((section(".text_pip"))) readPDNbPrepare(paddr pdaddr);                      //!< Gets the number of prepare done util then.
void __attribute__((section(".text_pip"))) writePDNbPrepare(paddr pdaddr, uint32_t value); //!< Sets the number of prepare done util then
paddr __attribute__((section(".text_pip"))) readPDParent(paddr pdaddr);                    //!< Gets the parent PD's address
void __attribute__((section(".text_pip"))) writePDParent(paddr pdaddr, paddr value); //!< Sets the parent PD's address
paddr __attribute__((section(".text_pip"))) readPDVidt(paddr pdaddr);                //!< Read the VIDT block from the partition descriptor structure.
void __attribute__((section(".text_pip"))) writePDVidt(paddr pdaddr, paddr value); //!< Write the VIDT block to the partition descriptor structure.
paddr __attribute__((section(".text_pip"))) readBlockStartFromBlockEntryAddr(paddr blockentryaddr);              //!< Gets the block's start address from the given entry
void __attribute__((section(".text_pip"))) writeBlockStartFromBlockEntryAddr(paddr blockentryaddr, paddr value); //!< Sets the block's start address
paddr __attribute__((section(".text_pip"))) readBlockEndFromBlockEntryAddr(paddr blockentryaddr);                //!< Gets the block's end address from the given entry
void __attribute__((section(".text_pip"))) writeBlockEndFromBlockEntryAddr(paddr blockentryaddr, paddr value); //!< Sets the block's end address
bool __attribute__((section(".text_pip"))) readBlockAccessibleFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the Accessible flag from the given entry
void __attribute__((section(".text_pip"))) writeBlockAccessibleFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets a memory block as accessible or not
bool __attribute__((section(".text_pip"))) readBlockPresentFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the Present flag from the given entry
void __attribute__((section(".text_pip"))) writeBlockPresentFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets a memory block as present or not
uint32_t __attribute__((section(".text_pip"))) readBlockIndexFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the block index from the given entry
void __attribute__((section(".text_pip"))) writeBlockIndexFromBlockEntryAddr(paddr blockentryaddr, uint32_t value); //!< Sets the block index
bool __attribute__((section(".text_pip"))) readBlockRFromBlockEntryAddr(paddr blockentryaddr);                      //!< Gets the read flag
void __attribute__((section(".text_pip"))) writeBlockRFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets the read flag
bool __attribute__((section(".text_pip"))) readBlockWFromBlockEntryAddr(paddr blockentryaddr);              //!< Gets the write flag
void __attribute__((section(".text_pip"))) writeBlockWFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets the write flag
bool __attribute__((section(".text_pip"))) readBlockXFromBlockEntryAddr(paddr blockentryaddr);              //!< Gets the exec flag
void __attribute__((section(".text_pip"))) writeBlockXFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets the exec flag
BlockEntry_t __attribute__((section(".text_pip"))) readBlockEntryFromBlockEntryAddr(paddr blockentryaddr);  //!< Gets the block entry
void __attribute__((section(".text_pip"))) writeBlockEntryFromBlockEntryAddr(paddr blockentryaddr, BlockEntry_t value); //!< Sets the block entry
void __attribute__((section(".text_pip"))) writeBlockEntryWithIndexFromBlockEntryAddr(paddr blockentryaddr, uint32_t index, BlockEntry_t value); //!< Sets the block entry with given index
paddr __attribute__((section(".text_pip"))) getSh1EntryAddrFromBlockEntryAddr(paddr blockentryaddr);                                             //!< Gets the Sh1 entry from the block entry
paddr __attribute__((section(".text_pip"))) readSh1PDChildFromBlockEntryAddr(paddr blockentryaddr);              //!< Gets the child's PD from the given entry
void __attribute__((section(".text_pip"))) writeSh1PDChildFromBlockEntryAddr(paddr blockentryaddr, paddr value); //!< Sets the entry's child PD
bool __attribute__((section(".text_pip"))) readSh1PDFlagFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the child's PD from the given entry
void __attribute__((section(".text_pip"))) writeSh1PDFlagFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets the entry's PD flag
paddr __attribute__((section(".text_pip"))) readSh1InChildLocationFromBlockEntryAddr(paddr blockentryaddr);    //!< Gets the location of the block in the child
void __attribute__((section(".text_pip"))) writeSh1InChildLocationFromBlockEntryAddr(paddr blockentryaddr, paddr value); //!<Sets the block's location in the child
void __attribute__((section(".text_pip"))) writeSh1EntryFromBlockEntryAddr(paddr blockentryaddr, Sh1Entry_t newsh1entry);//! Sets the block's Sh1 entry
paddr __attribute__((section(".text_pip"))) getSCEntryAddrFromBlockEntryAddr(paddr blockentryaddr);                      //! Gets the SC entry from the block entry
paddr __attribute__((section(".text_pip"))) readSCOriginFromBlockEntryAddr(paddr blockentryaddr);                        //! Gets the block's origin
void __attribute__((section(".text_pip"))) writeSCOriginFromBlockEntryAddr(paddr blockentryaddr, paddr value); //! Sets the block's origin
paddr __attribute__((section(".text_pip"))) readSCNextFromBlockEntryAddr(paddr blockentryaddr);                //! Gets the block's next subblock
void __attribute__((section(".text_pip"))) writeSCNextFromBlockEntryAddr(paddr blockentryaddr, paddr value); //! Sets the block's next subblock
void __attribute__((section(".text_pip"))) writeSCEntryFromBlockEntryAddr(paddr blockentryaddr, SCEntry_t newscentry); //! Sets the block's SC entry
paddr __attribute__((section(".text_pip"))) readNextFromKernelStructureStart(paddr structureaddr);                     //! Gets the block's next subblock
void __attribute__((section(".text_pip"))) writeNextFromKernelStructureStart(paddr structureaddr, paddr newnextstructure); //! Sets the block's SC entry
bool __attribute__((section(".text_pip"))) eraseBlock(paddr startAddr, paddr endAddr);                                     //! Erases the memory block defined by (startAddr, endAddr).
void __attribute__((section(".text_pip"))) writePDTable(paddr addr, PDTable_t newpdtable); //! Sets a new PD Table at the given address
PDTable_t __attribute__((section(".text_pip"))) getDefaultPDTable();                       //! Returns the default PD Table without initialisation
PDTable_t __attribute__((section(".text_pip"))) getEmptyPDTable();                         //! Returns the default PD Table with initialisation
BlockEntry_t __attribute__((section(".text_pip"))) getDefaultBlockEntry();                 //! Returns the default block entry
Sh1Entry_t __attribute__((section(".text_pip"))) getDefaultSh1Entry();                     //! Returns the default Sh1 entry
SCEntry_t __attribute__((section(".text_pip"))) getDefaultSCEntry();                       //! Returns the default SC entry
BlockEntry_t __attribute__((section(".text_pip"))) buildBlockEntry(paddr startaddr, paddr endaddr, bool accessiblebit, bool presentbit); //! Constructs a block entry given the attributes
paddr __attribute__((section(".text_pip"))) getPDStructurePointerAddrFromPD(paddr pdaddr);                                               //! Gets the structure pointer of the given PD
bool __attribute__((section(".text_pip"))) checkEntry(paddr kstructurestart, paddr blockentryaddr);                                      //! Checks a block entry is valid in the kernel structure
bool __attribute__((section(".text_pip"))) checkBlockInRAM(paddr blockentryaddr);                                                        //! Checks whether the block is entirely in RAM
bool __attribute__((section(".text_pip"))) check32Aligned(paddr addrToCheck);                                                            //! Checks whether the address is 32-bytes aligned
blockOrError __attribute__((section(".text_pip"))) blockAttr(paddr blockentryaddr, BlockEntry_t blockentry);                             //! Wrapper to create a block and its attributes

paddr __attribute__((section(".text_pip"))) readBlockFromPhysicalMPU(paddr pd, uint32_t MPURegionNb);  //! Reads the block configured at the given region of the physical MPU.
void __attribute__((section(".text_pip"))) removeBlockFromPhysicalMPU(paddr pd, paddr blockentryaddr); //! Removes a block from the physical MPU.
void __attribute__((section(".text_pip"))) removeBlockFromPhysicalMPUIfNotAccessible (paddr pd, paddr idblock, bool accessiblebit); //! Removes a block from the physical MPU if not accessible.
void __attribute__((section(".text_pip"))) replaceBlockInPhysicalMPU(paddr pd, paddr blockblockentryaddr, uint32_t MPURegionNb); //! Replaces a block in the physical MPU.
uint32_t __attribute__((section(".text_pip"))) findBlockIdxInPhysicalMPU(paddr pd, paddr blockToFind, uint32_t defaultnb); //! Returns the MPU region number where the block is configured

void __attribute__((section(".text_pip"))) configure_LUT_entry(uint32_t* LUT, uint32_t entryindex, paddr blockentryaddr, paddr addrtocover); //! Configures the LUT entry at given index with the given MPU entry
void __attribute__((section(".text_pip"))) clear_LUT(uint32_t* LUT); //! Defaults all LUT entries
int __attribute__((section(".text_pip"))) checkMPU(); //! Checks the MPU
int __attribute__((section(".text_pip"))) initMPU(); //! Inits the MPU
#endif
