
#if defined UNIT_TESTS // include file only when testing

#include <stdio.h>
#include "Services.h"
#include "pip_debug.h"
#include "nrf52.h"
#include "Internal.h"

#include <assert.h>

#define enablePrivilegedMode() __asm("SVC #0")
#define disablePrivilegedMode() __asm("SVC #1")

// End address for the user section; defined in linker script
extern uint32_t user_mem_end;
// Start address for the user section; defined in linker script
extern uint32_t user_mem_start;
// Start and end addresses for the user stack section; defined in linker script
extern uint32_t user_stack_limit;
extern uint32_t user_stack_top;

// Start address of RAM
extern uint32_t _sram;

// Global identifiers
paddr root = NULL;
paddr root_kernel_structure_start = NULL;
paddr initial_block_start = NULL;
paddr initial_block_end = NULL;
paddr initial_block_root_address = NULL;
paddr block_flash = NULL;
paddr block_ram1 = NULL;
paddr block_ram2 = NULL;

/*!
 * \fn void init_tests_only_ram()
 * \brief Resets to the after-startup state
 */
void init_tests_only_ram()
{
	// Initialize the root partition with no blocks
	mal_init();
  root = getRootPartition();

  // add user memory block(s)
  // One RAM block for unit testing
	initial_block_root_address = insertNewEntry(root, initial_block_start, &user_mem_end - 1, initial_block_start, true, true, false);// idpartition, start, end, origin, RW = true, X = false

	// Pre-configure the MPU LUT with inserted block(s)
  enableBlockInMPU(root, initial_block_root_address, 0);

  //dump_partition(root);
  activate(root);
}

/*!
 * \fn void init_tests_flash_ram_w_stack()
 * \brief Resets to the after-startup state with user stack
 */
void init_tests_flash_ram_w_stack()
{
	// Initialize the root partition with no blocks
	mal_init();
  root = getRootPartition();

  // add user memory block(s)
  // One FLASH block and two RAM blocks (data + stack)
	block_flash = insertNewEntry(root, 0,  (paddr) 0x00080000, 0, true, false, true);
	//block_ram1 = insertNewEntry(root, &_sram, &user_stack_limit-0x200, &_sram, true, true, false);
	//block_ram2 = insertNewEntry(root, &user_stack_limit, &user_stack_top, &user_stack_limit, true, true, false);
  block_ram1 = insertNewEntry(root, 0x20000000, 0x20000FFF, 0x20000000, true, false, false);
	block_ram2 = insertNewEntry(root, 0x20001000, &user_stack_top, 0x20001000, true, true, false);

  //dump_partition(root);
  activate(root);
}


// COMMON ASSERTIONS
/*!
 * \fn void MPU_structure_is_empty(paddr kernel_structure_start)
 * \brief Check that no slot in the MPU of kernel structure <kernel_structure_start> is used by checking the
 * present flag
 */
void MPU_structure_is_empty(paddr kernel_structure_start)
{
  KStructure_t* ks = (KStructure_t*) kernel_structure_start;
  for(int i = 0 ; i < KERNELSTRUCTUREENTRIESNB ; i++)
  {
    assert(
        readMPUPresentFromMPUEntryAddr(&ks->mpu[i]) ==
        false
    );
  }
}

/*!
 * \fn void remaining_MPU_slots_form_a_linked_list(uint32_t start_index, uint32_t end_index, paddr kernel_structure_start)
 * \brief Tests that the MPU structure is well formed
          Only legitimate to a partition after one prepare and adding/removal in order
 */
void remaining_MPU_slots_form_a_linked_list(uint32_t start_index, uint32_t end_index, paddr kernel_structure_start)
{
  // test remaining empty slots: special case -> last end is 0
  KStructure_t* ks = (KStructure_t*) kernel_structure_start;
  for(int i = start_index ; i < end_index - 1 ; i++)
  {
      paddr empty_block_MPU_entry = &ks->mpu[i];
      assert(readMPUIndexFromMPUEntryAddr(empty_block_MPU_entry) == i);
      assert(readMPUStartFromMPUEntryAddr(empty_block_MPU_entry) == 0);
      assert(readMPUEndFromMPUEntryAddr(empty_block_MPU_entry) == &ks->mpu[i+1]);
      assert(readMPUAccessibleFromMPUEntryAddr(empty_block_MPU_entry) == false);
      assert(readMPUPresentFromMPUEntryAddr(empty_block_MPU_entry) == false);
  }

  paddr empty_block_MPU_entry = &ks->mpu[end_index];
  assert(readMPUIndexFromMPUEntryAddr(empty_block_MPU_entry) == end_index);
  assert(readMPUStartFromMPUEntryAddr(empty_block_MPU_entry) == NULL);
  assert(readMPUEndFromMPUEntryAddr(empty_block_MPU_entry) == NULL);
  assert(readMPUAccessibleFromMPUEntryAddr(empty_block_MPU_entry) == false);
  assert(readMPUPresentFromMPUEntryAddr(empty_block_MPU_entry) == false);
}

/*!
 * \fn void remaining_Sh1_slots_are_default(uint32_t start_index, uint32_t end_index, paddr kernel_structure_start)
 * \brief Tests that the whole Sh1 structure from <start_index> to <end_index> is default
 * All entries should be [PDchild=0, PDflag=False, inChildLocation=0]
 */
void remaining_Sh1_slots_are_default(uint32_t start_index, uint32_t end_index, paddr kernel_structure_start)
{
  KStructure_t* ks = (KStructure_t*) kernel_structure_start;
  for(int i = start_index ; i < end_index ; i++)
  {
      paddr MPU_entry_addr = &ks->mpu[i];
      assert(readSh1PDChildFromMPUEntryAddr(MPU_entry_addr) == NULL);
      assert(readSh1PDFlagFromMPUEntryAddr(MPU_entry_addr) == false);
      assert(readSh1InChildLocationFromMPUEntryAddr(MPU_entry_addr) == NULL);
  }
}

/*!
 * \fn void Sh1_structure_is_default(paddr kernel_structure_start)
 * \brief Tests that the whole Sh1 structure is default
  All entries should be [PDchild=0, PDflag=False, inChildLocation=0]
 */
void Sh1_structure_is_default(paddr kernel_structure_start)
{
  remaining_Sh1_slots_are_default(0, KERNELSTRUCTUREENTRIESNB, kernel_structure_start);
}

/*!
 * \fn void remaining_SC_slots_are_default(uint32_t start_index, uint32_t end_index, paddr kernel_structure_start)
 * \brief Tests that the SC structure from <start_index> to <end_index> is default
 *  All entries should be [origin=0, next=0]
 */
void remaining_SC_slots_are_default(uint32_t start_index, uint32_t end_index, paddr kernel_structure_start)
{
  KStructure_t* ks = (KStructure_t*) kernel_structure_start;
  for(int i = start_index ; i < end_index ; i++)
  {
      paddr MPU_entry_addr = &ks->mpu[i];
      assert(readSCOriginFromMPUEntryAddr(MPU_entry_addr) == 0);
      assert(readSCNextFromMPUEntryAddr(MPU_entry_addr) == 0);
  }
}

/*!
 * \fn void SC_structure_is_default(paddr kernel_structure_start)
 * \brief Tests that the whole SC structure is default
 * All entries should be [origin=0, next=0]
 */
void SC_structure_is_default(paddr kernel_structure_start)
{
  remaining_SC_slots_are_default(0, KERNELSTRUCTUREENTRIESNB, kernel_structure_start);
}


// INITIAL ROOT PARTITION DEFINITION

/*!
 * \fn void test_initial_root_PD_values()
 * \brief Tests that the initial values of the root PD structure are correct
 */
void test_initial_root_PD_values()
{
  assert(root == &user_mem_start);
  root_kernel_structure_start = (void*) &user_mem_start + PDSTRUCTURETOTALLENGTH();//size in bytes
  KStructure_t* ks = (KStructure_t*) root_kernel_structure_start;
  dump_partition(root);
  assert(readPDStructurePointer(root) == root_kernel_structure_start);
  assert(readPDFirstFreeSlotPointer(root) == &ks->mpu[1]);
  assert(readPDNbFreeSlots(root) == 7);
  assert(readPDNbPrepare(root) == 1);
  assert(readPDParent(root) == NULL);
}

/*!
 * \fn void test_initial_root_MPU_values()
 * \brief Tests that the initial values of the root MPU structure are correct
 *  Should be:
 *  1st entry (initial block) -> 0 (index) | initial_block_start (start) | initial_block_end (end) | 1 (accessible)
 *                             | 1 (present)
 *  2nd entry -> 1 (index) | NULL (pointer to previous free slot) | MPU[2] (pointer to third MPU entry) | 0 | 0
 *  last entry -> kernel_nb_entries (index) | MPU[kernel_entries_nb]-1 | NULL (no free slots left, end of linked list)
 *               | 0 | 0
 *  Entries in between -> i (index) | MPU[i-1] | MPU[i+1] | 0 | 0
 */
void test_initial_root_MPU_values()
{
  KStructure_t* ks = (KStructure_t*) root_kernel_structure_start;
  // first entry contains the initial blocks
  assert(readMPUIndexFromMPUEntryAddr(root_kernel_structure_start) == 0);
  assert(
      readMPUStartFromMPUEntryAddr(root_kernel_structure_start)
      == initial_block_start);
  assert(
      readMPUEndFromMPUEntryAddr(root_kernel_structure_start)
      == initial_block_end);
  assert(
      readMPUAccessibleFromMPUEntryAddr(root_kernel_structure_start) == 1);
  assert(
      readMPUPresentFromMPUEntryAddr(root_kernel_structure_start) == 1);

  // middle entries are default
  for(int i = 1 ; i < (KERNELSTRUCTUREENTRIESNB - 1) ; i++)   // 0-indexed, index nb -1 not included
  {
      assert(
          readMPUIndexFromMPUEntryAddr(
           &ks->mpu[i]) == i
      );
      assert(
          readMPUStartFromMPUEntryAddr(&ks->mpu[i]) ==
          0);
      assert(
          readMPUEndFromMPUEntryAddr(&ks->mpu[i]) ==
          &ks->mpu[i+1]);
      assert(
          readMPUAccessibleFromMPUEntryAddr(&ks->mpu[i]) ==
          0);
      assert(
          readMPUPresentFromMPUEntryAddr(&ks->mpu[i])==
          0);
  }

  // last entry is special since it ends with null
  assert(readMPUIndexFromMPUEntryAddr(&ks->mpu[KERNELSTRUCTUREENTRIESNB - 1]
                                            )==
                    KERNELSTRUCTUREENTRIESNB - 1
  );
  assert(readMPUStartFromMPUEntryAddr(&ks->mpu[KERNELSTRUCTUREENTRIESNB - 1]) ==
                    0);
  assert(readMPUEndFromMPUEntryAddr(&ks->mpu[KERNELSTRUCTUREENTRIESNB - 1]) ==
                    0);
  assert(readMPUAccessibleFromMPUEntryAddr(&ks->mpu[KERNELSTRUCTUREENTRIESNB - 1]) ==
                    0);
  assert(readMPUPresentFromMPUEntryAddr(&ks->mpu[KERNELSTRUCTUREENTRIESNB - 1]) ==
                    0);
}

/*!
 * \fn void test_initial_root_Sh1_values()
 * \brief Tests that the initial values of the root Sh1 structure are correct
 *  Should be:
 *  All entries -> NULL | 0 | NULL
 */
void test_initial_root_Sh1_values()
{
  KStructure_t* ks = (KStructure_t*) root_kernel_structure_start;
  // all values are default
  for(int i = 1 ; i < KERNELSTRUCTUREENTRIESNB ; i++)   // 0-indexed
  {
      assert(
          readSh1PDChildFromMPUEntryAddr(&ks->mpu[i])
          == 0
      );
      assert(
          readSh1PDFlagFromMPUEntryAddr(&ks->mpu[i])
          == 0
      );
      assert(
          readSh1InChildLocationFromMPUEntryAddr(&ks->mpu[i])
          == 0
      );
  }
}
/*!
 * \fn void test_initial_root_SC_values()
 * \brief Tests that the initial values of the root SC structure are correct
 * Should be:
 * 1st entry -> initial block start | NULL
 * Remaining entries -> NULL | NULL
 */
void test_initial_root_SC_values()
{
  KStructure_t* ks = (KStructure_t*) root_kernel_structure_start;
  // first entry is special since an initial block is present
  assert(readSCOriginFromMPUEntryAddr(root_kernel_structure_start) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(root_kernel_structure_start) == 0);

  // remaining entries are default
  for(int i = 1 ; i < KERNELSTRUCTUREENTRIESNB ; i++)  // 0-indexed
  {
      assert(readSCOriginFromMPUEntryAddr(&ks->mpu[i])==
                        0);
      assert(readSCNextFromMPUEntryAddr(&ks->mpu[i]) ==
                        0);
  }
}

/*!
 * \fn void test_initial_root()
 * \brief Launches the tests of the initial root partition configuration
 */
void test_initial_root()
{
  init_tests_only_ram();
  test_initial_root_PD_values();
  test_initial_root_MPU_values();
  test_initial_root_Sh1_values();
  test_initial_root_SC_values();
}

// TESTS SET UP FONCTIONS
paddr child_partition_pd;
paddr block_create_child_MPU_root_address;
paddr block_prepare_child_id;
paddr block_prepare_child_MPU_root_address;
paddr block_to_share_id;
paddr block_to_share_MPU_root_address;
paddr block_to_share_MPU_child_address;
paddr grandchild_partition_pd;
paddr block_create_grandchild_MPU_child_address;
paddr block_prepare_grandchild_id;
paddr block_prepare_grandchild_MPU_child_address;
paddr block_to_share_MPU_grandchild_address;

/*!
 * \fn void build_create_child_block_out_of_initial_block()
 * \brief  Build a block which shall be used as a child partition PD
 */
void build_create_child_block_out_of_initial_block()
{ // build block create -> block create = first block already existing
  child_partition_pd = initial_block_start + KERNELSTRUCTURETOTALLENGTH() * 40;
  block_create_child_MPU_root_address = cutMemoryBlock(initial_block_root_address, child_partition_pd, -1);

  // block_create_child_MPU_root_address = readPDStructurePointer(
  //     current_partition)
  assert(block_create_child_MPU_root_address != false);
}
/*!
 * \fn void build_prepare_child_block_out_of_initial_block()
 * \brief  Build a block which shall be used to prepare a child partition
 */
void build_prepare_child_block_out_of_initial_block()
{ // build block prepare
  block_prepare_child_id = initial_block_start + KERNELSTRUCTURETOTALLENGTH() * 25;
  block_prepare_child_MPU_root_address = cutMemoryBlock(initial_block_root_address, block_prepare_child_id, -1);
  assert(block_prepare_child_MPU_root_address != false);
}

/*!
 * \fn void build_share_block_out_of_initial_block()
 * \brief  Build a block which shall be used to be shared with a child partition
 * Size = (block_create_start + KERNELSTRUCTURETOTALLENGTH()) -> (block_prepare_start = block_create_start + KERNELSTRUCTURETOTALLENGTH() * 30)
 */
void build_share_block_out_of_initial_block()
{
  // build block to share
  block_to_share_id = initial_block_start + KERNELSTRUCTURETOTALLENGTH() * 15;
  block_to_share_MPU_root_address = cutMemoryBlock(initial_block_root_address, block_to_share_id, -1);
  assert(block_to_share_MPU_root_address != false);
}

/*!
 * \fn void init_test_with_create_without_prepare_child(standalone=true)
 * \brief  Init with a child partition without prepare
 * Can be used in standalone mode (to test with a sole child partition creation) or in combination with other
 * init_tests functions in such case they are responsible to cut the block at first (can't cut once block are
 * created or prepared)
 * \param standalone: pre-treatment by default cuts the initial block to be used, otherwise avoid this operation
 */
void init_test_with_create_without_prepare_child(int standalone)
{
  if (standalone)
  {
      build_create_child_block_out_of_initial_block();
  }
  // Create child partition
  assert(createPartition(block_create_child_MPU_root_address) != false);
}

/*!
 * \fn void init_test_with_create_prepare_child(standalone=True)
 * \brief  Init with a child partition and prepare it by cutting the initial block -> 1 block is left
 *   Can be used in standalone mode (to test with a sole child partition creation + preparation) or in combination
 *   with other init_tests functions in such case they are responsible to cut the block at first (can't cut once
 *   block are created or prepared)
 * :param standalone: pre-treatment by default cuts the initial block to be used, otherwise avoid this operation
 */
void init_test_with_create_prepare_child(int standalone)
{
  if (standalone)
  {
      // First cut the initial block
      build_create_child_block_out_of_initial_block();
      build_prepare_child_block_out_of_initial_block();
  }

  // create child partition
  init_test_with_create_without_prepare_child(false);

  // prepare child partition
  assert(
      prepare(child_partition_pd, 1, block_prepare_child_MPU_root_address) != false);
}

/*!
 * \fn void init_test_with_create_prepare_share_child(standalone=True)
 * \brief Create and prepare a child partition and add a shared block by cutting the initial block
 * Can be used in standalone mode (to test with a sole child partition creation + preparation + share) or in
 * combination with other init_tests functions in such case they are responsible to cut the block at first (can't
 * cut once block are created or prepared)
 * :param standalone: pre-treatment by default cuts the initial block to be used, otherwise avoid this operation
 */
void init_test_with_create_prepare_share_child(int standalone)
{
  if (standalone)
  {
      // First cut the initial block
      build_create_child_block_out_of_initial_block();
      build_prepare_child_block_out_of_initial_block();
      build_share_block_out_of_initial_block();
  }

  // create and prepare child partition
  init_test_with_create_prepare_child(false);

  // add the shared block to the child
  block_to_share_MPU_child_address = addMemoryBlock(child_partition_pd,
                                                    block_to_share_MPU_root_address,
                                                    true, true, false);
  assert(block_to_share_MPU_child_address != false);
}

/*!
 * \fn void build_create_grandchild_block()
 * \brief  Build a block which shall be used as a grandchild partition PD
 */
void build_create_grandchild_block(paddr base_block)
{ // build block grandchild create
  grandchild_partition_pd = readMPUStartFromMPUEntryAddr(base_block) + KERNELSTRUCTURETOTALLENGTH() * 4;
  block_create_grandchild_MPU_child_address = cutMemoryBlock(base_block, grandchild_partition_pd, -1);
  assert(block_create_grandchild_MPU_child_address != false);
}

/*!
 * \fn void build_prepare_grandchild_block()
 * \brief  Build a block which shall be used to prepare a grandchild partition
 */
void build_prepare_grandchild_block(paddr base_block)
{
  // build block grandchild prepare
  block_prepare_grandchild_id = readMPUStartFromMPUEntryAddr(base_block) + KERNELSTRUCTURETOTALLENGTH() * 2;
  block_prepare_grandchild_MPU_child_address = cutMemoryBlock(base_block, block_prepare_grandchild_id, -1);
  assert(block_prepare_grandchild_MPU_child_address != false);
}

/*!
 * \fn void init_test_with_create_prepare_child_and_create_prepare_grandchild(standalone=True)
 * \brief  Create a grandchild and prepare it
  (= create and prepare a child partition + add a shared block by cutting the initial block
  + create and prepare grandchild by cutting the shared block)
  Can be used in standalone mode (to test with a sole child partition creation + preparation + share child
  + grandchild creation + preparation) or in combination with other init_tests functions in such case they are
  responsible to cut the block at first (can't cut once block are created or prepared)
  :param standalone: pre-treatment by default cuts the initial block to be used, otherwise avoid this operation
 */
void init_test_with_create_prepare_child_and_create_prepare_grandchild(int standalone)
{
  if (standalone)
  {
      updateCurPartition(root);
      // First cut the initial block to create and prepare  the child
      build_create_child_block_out_of_initial_block();
      build_prepare_child_block_out_of_initial_block();
      build_share_block_out_of_initial_block();
      // create and prepare child partition
      init_test_with_create_prepare_share_child(false);
      // Then cut the shared block to create and prepare the grandchild
      updateCurPartition(child_partition_pd);
      build_create_grandchild_block(block_to_share_MPU_child_address);
      build_prepare_grandchild_block(block_to_share_MPU_child_address);
  }

  updateCurPartition(child_partition_pd);

  // create grandchild partition
  assert(createPartition(block_create_grandchild_MPU_child_address) != false);
  // prepare child partition
  assert(prepare(grandchild_partition_pd, 1, block_prepare_grandchild_MPU_child_address) != false);
}

/*!
 * \fn void init_test_with_create_prepare_child_and_create_prepare_share_grandchild(standalone=True)
 * \brief   Child partition shares a block with the grandchild
  (= create and prepare a child partition + create a grandchild and prepare it + share a block)
  Can be used in standalone mode (to test with a sole child partition creation + preparation + share child +
  grandchild creation + preparation + share grandchild) or in combination with other init_tests functions in such
  case they are responsible to cut the block at first (can't cut once block are created or prepared)
  :param standalone: pre-treatment by default cuts the initial block to be used, otherwise avoid this operation
 */
void init_test_with_create_prepare_child_and_create_prepare_share_grandchild(int standalone)
{
  if (standalone)
  {
      updateCurPartition(root);
      // First cut the initial block to create and prepare  the child
      build_create_child_block_out_of_initial_block();
      build_prepare_child_block_out_of_initial_block();
      build_share_block_out_of_initial_block();
      // create and prepare child partition
      init_test_with_create_prepare_share_child(false);
      // Then cut the shared block to create and prepare the grandchild
      updateCurPartition(child_partition_pd);
      build_create_grandchild_block(block_to_share_MPU_child_address);
      build_prepare_grandchild_block(block_to_share_MPU_child_address);
  }
  updateCurPartition(child_partition_pd);

  // create and prepare child and grandchild partitions
  init_test_with_create_prepare_child_and_create_prepare_grandchild(false);

  // add the shared block to the grandchild
  block_to_share_MPU_grandchild_address = addMemoryBlock(grandchild_partition_pd,
                                                        block_to_share_MPU_child_address,
                                                        true, true, false);
  assert(block_to_share_MPU_grandchild_address != false);
}


// TEST CUT SYSTEM CALL

/*!
 * \fn void three_cuts_in_a_row(paddr cut_address1, paddr cut_address2, paddr cut_address3)
 * \brief Tests that 3 cuts in a row behave as expected
 * 1st cut: cuts the initial block -> initial | cut1
 * 2nd cut: cuts the newly created subblock -> initial | cut1 | cut2
 * 3rd cut: cuts the initial block again -> initial | cut3 | cut1 | cut2

 * The MPU structure should hold the cuts in order (MPU0: initial, MPU1: cut1, MU2: cut2, MPU3: cut3)
 * The Sh1 structure should be untouched (no block shared)
 * The SC structure should link the created subblock with each other initial -> cut1 -> cut2 -> cut3
 * \param cut_address1 1st cut address
 * \param cut_address2 2nd cut address
 * \param cut_address3 3rd cut address
 */
void three_cuts_in_a_row(paddr cut_address1, paddr cut_address2, paddr cut_address3)
{
  // Test arguments
  assert(cut_address1 > initial_block_start);
  assert(cut_address2 > initial_block_start);
  assert(cut_address3 > initial_block_start);

  assert(cut_address2 > cut_address1);
  assert(cut_address3 < cut_address1);

  // ******1st cut******
  paddr cut1_MPU_root_address = cutMemoryBlock(initial_block_root_address, cut_address1, -1);
  dump_partition(root);

  KStructure_t* ks_root = (KStructure_t*) root_kernel_structure_start;

  paddr initial_block_MPU_entry = ks_root->mpu;
  assert(readMPUIndexFromMPUEntryAddr(initial_block_MPU_entry) == 0);
  assert(readMPUStartFromMPUEntryAddr(initial_block_MPU_entry) == initial_block_start);
  assert(readMPUEndFromMPUEntryAddr(initial_block_MPU_entry) == cut_address1 - 1);
  assert(readMPUAccessibleFromMPUEntryAddr(initial_block_MPU_entry) == true);
  assert(readMPUPresentFromMPUEntryAddr(initial_block_MPU_entry) == true);

  paddr cut1_block_MPU_entry = &ks_root->mpu[1];
  assert(readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry) == 1);
  assert(readMPUStartFromMPUEntryAddr(cut1_block_MPU_entry) == cut_address1);
  assert(readMPUEndFromMPUEntryAddr(cut1_block_MPU_entry) == initial_block_end);
  assert(readMPUAccessibleFromMPUEntryAddr(cut1_block_MPU_entry) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut1_block_MPU_entry) == true);

  assert(readSCOriginFromMPUEntryAddr(initial_block_MPU_entry) == initial_block_start);
  // next is the next subblock's MPU location == not the id
  assert(readSCNextFromMPUEntryAddr(initial_block_MPU_entry) == &ks_root->mpu[readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry)]);

  //paddr cut1_block_SC_entry = root_kernel_structure_start + readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry)*mpuentrylength;
  assert(readSCOriginFromMPUEntryAddr(cut1_block_MPU_entry) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut1_block_MPU_entry) == 0);

  remaining_MPU_slots_form_a_linked_list(2, KERNELSTRUCTUREENTRIESNB - 1, root_kernel_structure_start);

  Sh1_structure_is_default(root_kernel_structure_start);

  remaining_SC_slots_are_default(2, KERNELSTRUCTUREENTRIESNB, root_kernel_structure_start);

  // ******2nd cut******
  // cut the created subblock
  cutMemoryBlock(cut1_MPU_root_address, cut_address2, -1);

  assert(readMPUIndexFromMPUEntryAddr(initial_block_MPU_entry) == 0);
  assert(readMPUStartFromMPUEntryAddr(initial_block_MPU_entry) == initial_block_start);
  assert(readMPUEndFromMPUEntryAddr(initial_block_MPU_entry) == cut_address1 - 1);
  assert(readMPUAccessibleFromMPUEntryAddr(initial_block_MPU_entry) == true);
  assert(readMPUPresentFromMPUEntryAddr(initial_block_MPU_entry) == true);

  assert(readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry) == 1);
  assert(readMPUStartFromMPUEntryAddr(cut1_block_MPU_entry) == cut_address1);
  assert(readMPUEndFromMPUEntryAddr(cut1_block_MPU_entry) == (cut_address2 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(cut1_block_MPU_entry) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut1_block_MPU_entry) == true);

  paddr cut2_block_MPU_entry = &ks_root->mpu[2];
  assert(readMPUIndexFromMPUEntryAddr(cut2_block_MPU_entry) == 2);
  assert(readMPUStartFromMPUEntryAddr(cut2_block_MPU_entry) == cut_address2);
  assert(readMPUEndFromMPUEntryAddr(cut2_block_MPU_entry) == initial_block_end);
  assert(readMPUAccessibleFromMPUEntryAddr(cut2_block_MPU_entry) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut2_block_MPU_entry) == true);

  assert(readSh1PDChildFromMPUEntryAddr(initial_block_MPU_entry) == 0);
  assert(readSh1PDFlagFromMPUEntryAddr(initial_block_MPU_entry) == false);
  assert(readSh1InChildLocationFromMPUEntryAddr(initial_block_MPU_entry) == 0);

  assert(readSCOriginFromMPUEntryAddr(initial_block_MPU_entry) == initial_block_start);
  // next is the next subblock's MPU location == not the id
  assert(readSCNextFromMPUEntryAddr(initial_block_MPU_entry) == &ks_root->mpu[readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry)]);

  //paddr cut1_block_SC_entry = root_kernel_structure_start + readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry)*mpuentrylength);
  assert(readSCOriginFromMPUEntryAddr(cut1_block_MPU_entry) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut1_block_MPU_entry) == &ks_root->mpu[readMPUIndexFromMPUEntryAddr(cut2_block_MPU_entry)]);

  assert(readSCOriginFromMPUEntryAddr(cut2_block_MPU_entry) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut2_block_MPU_entry) == 0);

  remaining_MPU_slots_form_a_linked_list(3, KERNELSTRUCTUREENTRIESNB- 1, root_kernel_structure_start);
  Sh1_structure_is_default(root_kernel_structure_start);
  remaining_SC_slots_are_default(3, KERNELSTRUCTUREENTRIESNB, root_kernel_structure_start);

  // ******3rd cut******
  // cut the initial block again -> no other blocks exist so the newly created subblock will be at index 3
  cutMemoryBlock(initial_block_root_address, cut_address3, -1);

  // Test cut_address3 MPU entries
  //paddr initial_block_MPU_entry = root_kernel_structure_start;
  assert(readMPUIndexFromMPUEntryAddr(initial_block_MPU_entry) == 0);
  assert(readMPUStartFromMPUEntryAddr(initial_block_MPU_entry) == initial_block_start);
  assert(readMPUEndFromMPUEntryAddr(initial_block_MPU_entry) == (cut_address3 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(initial_block_MPU_entry) == true);
  assert(readMPUPresentFromMPUEntryAddr(initial_block_MPU_entry) == true);

  assert(readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry) == 1);
  assert(readMPUStartFromMPUEntryAddr(cut1_block_MPU_entry) == cut_address1);
  assert(readMPUEndFromMPUEntryAddr(cut1_block_MPU_entry) == (cut_address2 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(cut1_block_MPU_entry) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut1_block_MPU_entry) == true);

  assert(readMPUIndexFromMPUEntryAddr(cut2_block_MPU_entry) == 2);
  assert(readMPUStartFromMPUEntryAddr(cut2_block_MPU_entry) == cut_address2);
  assert(readMPUEndFromMPUEntryAddr(cut2_block_MPU_entry) == initial_block_end);
  assert(readMPUAccessibleFromMPUEntryAddr(cut2_block_MPU_entry) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut2_block_MPU_entry) == true);

  paddr cut3_block_MPU_entry =  &ks_root->mpu[3];;
  assert(readMPUIndexFromMPUEntryAddr(cut3_block_MPU_entry) == 3);
  assert(readMPUStartFromMPUEntryAddr(cut3_block_MPU_entry) == cut_address3);
  assert(readMPUEndFromMPUEntryAddr(cut3_block_MPU_entry) == (cut_address1 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(cut3_block_MPU_entry) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut3_block_MPU_entry) == true);

  remaining_MPU_slots_form_a_linked_list(4, KERNELSTRUCTUREENTRIESNB - 1, root_kernel_structure_start);

  // Test cut_address3 Sh1 entries
  Sh1_structure_is_default(root_kernel_structure_start);

  // Test cut_address3 SC entries
  //paddr initial_block_SC_entry = root_kernel_structure_start;
  assert(readSCOriginFromMPUEntryAddr(initial_block_MPU_entry) == initial_block_start);
  // next is the next subblock's MPU location, not the id
  assert(readSCNextFromMPUEntryAddr(initial_block_MPU_entry) ==  &ks_root->mpu[readMPUIndexFromMPUEntryAddr(cut3_block_MPU_entry)]);

  assert(readSCOriginFromMPUEntryAddr(cut1_block_MPU_entry) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut1_block_MPU_entry) == &ks_root->mpu[readMPUIndexFromMPUEntryAddr(cut2_block_MPU_entry)]);

  assert(readSCOriginFromMPUEntryAddr(cut2_block_MPU_entry) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut2_block_MPU_entry) == 0);

  assert(readSCOriginFromMPUEntryAddr(cut3_block_MPU_entry) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut3_block_MPU_entry) == &ks_root->mpu[readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry)]);

  remaining_SC_slots_are_default(4, KERNELSTRUCTUREENTRIESNB, root_kernel_structure_start);

  dump_partition(root);
}

/*!
 * \fn void test_cut_max_free_slots_used()
 * \brief  Tests 7 cuts in a row to fill the root partition initial MPU kernel structure
 * The cuts are always done on the initial block and in descending order such as each new cut should be placed
 * between the initial block and the last cut block
 * Tests after 7 cuts:
 *     - Test PD: no free slots left (count = 0 | first free slot pointer = NULL), 1 prepare
 *     - Test MPU: order of the cuts (descending) | end = previous cut | accessible = 1 | present = 1
 *     - Test Sh1: untouched
 *     - Test SC: initial -> cut7 -> cut6 -> cut5 -> cut4 -> cut3 -> cut2 -> cut1
 *     The origin block should always be the initial block since we just cut that one
 *     - Test cutting again fails: max free slots reached and should fail because no free slots
 */
void test_cut_max_free_slots_used()
{
  KStructure_t* ks_root = (KStructure_t*) root_kernel_structure_start;
  paddr block1 = initial_block_start + KERNELSTRUCTURETOTALLENGTH()*30;
  paddr block2 = initial_block_start + KERNELSTRUCTURETOTALLENGTH()*29;
  paddr block3 = initial_block_start + KERNELSTRUCTURETOTALLENGTH()*28;
  paddr block4 = initial_block_start + KERNELSTRUCTURETOTALLENGTH()*27;
  paddr block5 = initial_block_start + KERNELSTRUCTURETOTALLENGTH()*26;
  paddr block6 = initial_block_start + KERNELSTRUCTURETOTALLENGTH()*25;
  paddr block7 = initial_block_start + KERNELSTRUCTURETOTALLENGTH()*24;

  assert(cutMemoryBlock(initial_block_root_address, block1, -1) != 0);
  assert(cutMemoryBlock(initial_block_root_address, block2, -1) != 0);
  assert(cutMemoryBlock(initial_block_root_address, block3, -1) != 0);
  assert(cutMemoryBlock(initial_block_root_address, block4, -1) != 0);
  assert(cutMemoryBlock(initial_block_root_address, block5, -1) != 0);
  assert(cutMemoryBlock(initial_block_root_address, block6, -1) != 0);
  assert(cutMemoryBlock(initial_block_root_address, block7, -1) != 0);

  dump_partition(root);

  // Test PDS
  assert(readPDFirstFreeSlotPointer(root) == NULL);
  assert(readPDNbFreeSlots(root) == 0);
  assert(readPDNbPrepare(root) == 1);

  // Test MPU
  paddr initial_block_MPU_entry_address = ks_root->mpu;
  assert(readMPUIndexFromMPUEntryAddr(initial_block_MPU_entry_address) == 0);
  assert(readMPUStartFromMPUEntryAddr(initial_block_MPU_entry_address) == initial_block_start);
  assert(readMPUEndFromMPUEntryAddr(initial_block_MPU_entry_address) == (block7 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(initial_block_MPU_entry_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(initial_block_MPU_entry_address) == true);

  paddr cut1_block_MPU_entry_address = &ks_root->mpu[1];
  assert(readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry_address) == 1);
  assert(readMPUStartFromMPUEntryAddr(cut1_block_MPU_entry_address) == block1);
  assert(readMPUEndFromMPUEntryAddr(cut1_block_MPU_entry_address) == initial_block_end);
  assert(readMPUAccessibleFromMPUEntryAddr(cut1_block_MPU_entry_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut1_block_MPU_entry_address) == true);

  paddr cut2_block_MPU_entry_address = &ks_root->mpu[2];
  assert(readMPUIndexFromMPUEntryAddr(cut2_block_MPU_entry_address) == 2);
  assert(readMPUStartFromMPUEntryAddr(cut2_block_MPU_entry_address) == block2);
  assert(readMPUEndFromMPUEntryAddr(cut2_block_MPU_entry_address) == (block1 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(cut2_block_MPU_entry_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut2_block_MPU_entry_address) == true);

  paddr cut3_block_MPU_entry_address = &ks_root->mpu[3];
  assert(readMPUIndexFromMPUEntryAddr(cut3_block_MPU_entry_address) == 3);
  assert(readMPUStartFromMPUEntryAddr(cut3_block_MPU_entry_address) == block3);
  assert(readMPUEndFromMPUEntryAddr(cut3_block_MPU_entry_address) == (block2 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(cut3_block_MPU_entry_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut3_block_MPU_entry_address) == true);

  paddr cut4_block_MPU_entry_address = &ks_root->mpu[4];
  assert(readMPUIndexFromMPUEntryAddr(cut4_block_MPU_entry_address) == 4);
  assert(readMPUStartFromMPUEntryAddr(cut4_block_MPU_entry_address) == block4);
  assert(readMPUEndFromMPUEntryAddr(cut4_block_MPU_entry_address) == (block3 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(cut4_block_MPU_entry_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut4_block_MPU_entry_address) == true);

  paddr cut5_block_MPU_entry_address = &ks_root->mpu[5];
  assert(readMPUIndexFromMPUEntryAddr(cut5_block_MPU_entry_address) == 5);
  assert(readMPUStartFromMPUEntryAddr(cut5_block_MPU_entry_address) == block5);
  assert(readMPUEndFromMPUEntryAddr(cut5_block_MPU_entry_address) == (block4 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(cut5_block_MPU_entry_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut5_block_MPU_entry_address) == true);

  paddr cut6_block_MPU_entry_address = &ks_root->mpu[6];
  assert(readMPUIndexFromMPUEntryAddr(cut6_block_MPU_entry_address) == 6);
  assert(readMPUStartFromMPUEntryAddr(cut6_block_MPU_entry_address) == block6);
  assert(readMPUEndFromMPUEntryAddr(cut6_block_MPU_entry_address) == (block5 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(cut6_block_MPU_entry_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut6_block_MPU_entry_address) == true);

  paddr cut7_block_MPU_entry_address = &ks_root->mpu[7];
  assert(readMPUIndexFromMPUEntryAddr(cut7_block_MPU_entry_address) == 7);
  assert(readMPUStartFromMPUEntryAddr(cut7_block_MPU_entry_address) == block7);
  assert(readMPUEndFromMPUEntryAddr(cut7_block_MPU_entry_address) == (block6 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(cut7_block_MPU_entry_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut7_block_MPU_entry_address) == true);

  // Test Sh1 is default
  Sh1_structure_is_default(root_kernel_structure_start);

  // Test SC
  assert(readSCOriginFromMPUEntryAddr(initial_block_MPU_entry_address) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(initial_block_MPU_entry_address) == cut7_block_MPU_entry_address);

  assert(readSCOriginFromMPUEntryAddr(cut1_block_MPU_entry_address) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut1_block_MPU_entry_address) == NULL);  // end of SC list = NULL

  assert(readSCOriginFromMPUEntryAddr(cut2_block_MPU_entry_address) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut2_block_MPU_entry_address) == cut1_block_MPU_entry_address);

  assert(readSCOriginFromMPUEntryAddr(cut3_block_MPU_entry_address) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut3_block_MPU_entry_address) == cut2_block_MPU_entry_address);

  assert(readSCOriginFromMPUEntryAddr(cut4_block_MPU_entry_address) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut4_block_MPU_entry_address) == cut3_block_MPU_entry_address);

  assert(readSCOriginFromMPUEntryAddr(cut5_block_MPU_entry_address) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut5_block_MPU_entry_address) == cut4_block_MPU_entry_address);

  assert(readSCOriginFromMPUEntryAddr(cut6_block_MPU_entry_address) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut6_block_MPU_entry_address) == cut5_block_MPU_entry_address);

  assert(readSCOriginFromMPUEntryAddr(cut7_block_MPU_entry_address) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut7_block_MPU_entry_address) == cut6_block_MPU_entry_address);
}

/*!
 * \fn void test_cut_bad_arguments()
 * \brief  Tests that bad arguments given to the cut system call fails
 * Tests that we can't cut any block not referenced in the partition kernel structure
 * Tests that a cut address should fit inside the block that is cut
 */
void test_cut_bad_arguments()
{
  // Tests don't accept not owned memory block
  assert(cutMemoryBlock((paddr) 0x100, (paddr) 0x3000, -1) == 0);
  assert(cutMemoryBlock(initial_block_root_address + 0x3000, initial_block_start + 0x4000, -1) == 0);

  // Tests don't accept a cut address outside the block
  assert(cutMemoryBlock(initial_block_root_address, 0x0, -1) == 0);
  assert(cutMemoryBlock(initial_block_root_address, initial_block_start - 32, -1) == 0);
  assert(cutMemoryBlock(initial_block_root_address, initial_block_end + 32, -1) == 0);

  // Tests can't perform cut if no free slots left
  test_cut_max_free_slots_used();
  assert(cutMemoryBlock(initial_block_root_address + 32*7, initial_block_start + 32*8, -1) == 0);
}

/*!
 * \fn void test_cut_6_cuts_in_a_row()
 * \brief Tests that when there is only one free slot left then its MPU block is correct
 * 6 cuts + initial block = 7 blocks + 1 free
 * The free slot entry should be:
 * MPU: 7 | 0 | 0 | 0 | 0
 * Sh1: 0 | 0 | 0
 * SC: 0 | 0
 */
void test_cut_6_cuts_in_a_row()
{
  paddr block1_MPU_address = cutMemoryBlock(initial_block_root_address, initial_block_start + 10*KERNELSTRUCTURETOTALLENGTH(), -1);
  paddr block2_MPU_address = cutMemoryBlock(block1_MPU_address,
                          initial_block_start + 12 * KERNELSTRUCTURETOTALLENGTH(), -1);
  paddr block3_MPU_address = cutMemoryBlock(block2_MPU_address,
                          initial_block_start + 13 * KERNELSTRUCTURETOTALLENGTH(), -1);
  paddr block4_MPU_address = cutMemoryBlock(block3_MPU_address,
                          initial_block_start + 14 * KERNELSTRUCTURETOTALLENGTH(), -1);
  paddr block5_MPU_address = cutMemoryBlock(block4_MPU_address,
                          initial_block_start + 15 * KERNELSTRUCTURETOTALLENGTH(), -1);
  paddr block6_MPU_address = cutMemoryBlock(block5_MPU_address,
                          initial_block_start + 16 * KERNELSTRUCTURETOTALLENGTH(), -1);

  dump_partition(root);

  // Check the only free slot left is as expected
  KStructure_t* ks_root = (KStructure_t*) root_kernel_structure_start;
  paddr MPU_free_slot_entry = &ks_root->mpu[7];
  assert(readMPUIndexFromMPUEntryAddr(MPU_free_slot_entry) == 7);
  assert(readMPUStartFromMPUEntryAddr(MPU_free_slot_entry) == NULL); // start = NULL (points to previous free slot)
  assert(readMPUEndFromMPUEntryAddr(MPU_free_slot_entry) == NULL); // end = NULL (points to next free slot)
  assert(readMPUAccessibleFromMPUEntryAddr(MPU_free_slot_entry) == false);
  assert(readMPUPresentFromMPUEntryAddr(MPU_free_slot_entry) == false);

  assert(readSh1PDChildFromMPUEntryAddr(MPU_free_slot_entry) == NULL);
  assert(readSh1PDFlagFromMPUEntryAddr(MPU_free_slot_entry) == false);
  assert(readSh1InChildLocationFromMPUEntryAddr(MPU_free_slot_entry) == NULL);

  assert(readSCOriginFromMPUEntryAddr(MPU_free_slot_entry) == NULL);
  assert(readSCNextFromMPUEntryAddr(MPU_free_slot_entry) == NULL);
}

/*!
 * \fn void test_cut_fails_when_block_not_accessible()
 * \brief   Test fails when trying to cut a block not accessible
  Init: 6 cuts in a row + create partition out of initial block
  Test:
      - cutting the block used to create the partition should fail
 */
void test_cut_fails_when_block_not_accessible()
{
  // Init
  test_cut_6_cuts_in_a_row();
  assert(createPartition(initial_block_root_address) != false);

  // Fails trying to cut a block not accessible
  assert(
      cutMemoryBlock(initial_block_root_address, initial_block_start + KERNELSTRUCTURETOTALLENGTH(), -1)
       == false
  );
}

/*!
 * \fn void test_cut()
 * \brief Launches the tests of the cut system call
 */
void test_cut()
{
  init_tests_only_ram();

  paddr cut_address1 = initial_block_start + 0x600;
  paddr cut_address2 = initial_block_start + 0x700;
  paddr cut_address3 = initial_block_start + 0x300;
  three_cuts_in_a_row(cut_address1, cut_address2, cut_address3);

  init_tests_only_ram();
  test_cut_max_free_slots_used();

  init_tests_only_ram();
  test_cut_bad_arguments();

  init_tests_only_ram();
  test_cut_6_cuts_in_a_row();

  init_tests_only_ram();
  test_cut_fails_when_block_not_accessible();
}

// TEST CREATE PARTITION SYSTEM CALL

/*!
 * \fn void test_create_partition()
 * \brief  Tests that a createPartition creates a new PD with the desired block and make it inaccessible to the ancestors
 */
void test_create_partition()
{
  // Check the block to become the PD of the child partition
  assert(readMPUIndexFromMPUEntryAddr(root_kernel_structure_start) == false);
  assert(readMPUStartFromMPUEntryAddr(root_kernel_structure_start) == initial_block_start);
  assert(readMPUEndFromMPUEntryAddr(root_kernel_structure_start) == initial_block_end);
  assert(readMPUAccessibleFromMPUEntryAddr(root_kernel_structure_start) == true);
  assert(readMPUPresentFromMPUEntryAddr(root_kernel_structure_start) == true);

  remaining_MPU_slots_form_a_linked_list(1, KERNELSTRUCTUREENTRIESNB - 1, root_kernel_structure_start);

  assert(createPartition(initial_block_root_address) == true);
  dump_ancestors(initial_block_start);

  // Check init of new partition's PD is correct
  assert(readPDStructurePointer(initial_block_start) == NULL);
  assert(readPDNbFreeSlots(initial_block_start) == 0);
  assert(readPDFirstFreeSlotPointer(initial_block_start) == NULL);
  assert(readPDNbPrepare(initial_block_start) == 0);
  assert(readPDParent(initial_block_start) == root);

  // MPU structure: Check the block became inaccessible in the parent partition (root) + remaining untouched
  assert(readMPUIndexFromMPUEntryAddr(root_kernel_structure_start) == 0);
  assert(readMPUStartFromMPUEntryAddr(root_kernel_structure_start) == initial_block_start);
  assert(readMPUEndFromMPUEntryAddr(root_kernel_structure_start) == initial_block_end);
  assert(readMPUAccessibleFromMPUEntryAddr(root_kernel_structure_start) == false);
  assert(readMPUPresentFromMPUEntryAddr(root_kernel_structure_start) == true);
  remaining_MPU_slots_form_a_linked_list(1, KERNELSTRUCTUREENTRIESNB - 1, root_kernel_structure_start);

  // Sh1 structure: check the block's PDflag is set + remaining untouched
  assert(readSh1PDChildFromMPUEntryAddr(root_kernel_structure_start) == false);
  assert(readSh1PDFlagFromMPUEntryAddr(root_kernel_structure_start) == 1);
  assert(readSh1InChildLocationFromMPUEntryAddr(root_kernel_structure_start) == false);
  remaining_Sh1_slots_are_default(1, KERNELSTRUCTUREENTRIESNB, root_kernel_structure_start);

  // SC structure: untouched
  assert(readSCOriginFromMPUEntryAddr(root_kernel_structure_start) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(root_kernel_structure_start) == false);
  remaining_Sh1_slots_are_default(1, KERNELSTRUCTUREENTRIESNB, root_kernel_structure_start);
}

/*!
 * \fn void test_create_partitions_bad_arguments()
 * \brief   Tests bad arguments should fail the system call
 * Tests:
 * - createPartition fails if feeded with a non existing block
 * - createPartition fails if feeded with a block that have already been used to create a partition (not accessible);
 * - createPartition fails if feeded with a block < minimum MPU region block: cut the initial block again and
 * create a block of size 12 and tries to create a partition out of it
 * - createPartition fails if feeded with a shared block
 */
void test_create_partitions_bad_arguments()
{
  KStructure_t* ks_root = (KStructure_t*) root_kernel_structure_start;
  paddr block1 = initial_block_start + 30*KERNELSTRUCTURETOTALLENGTH();
  paddr block1_MPU_address = cutMemoryBlock(initial_block_root_address, block1, -1);
  assert(block1_MPU_address == &ks_root->mpu[1]);  // 2nd entry

  // block not existing
  assert(createPartition(initial_block_root_address + 1) == false);  // Fail

  // block not accessible
  assert(createPartition(block1_MPU_address) != false); // Success
  assert(createPartition(block1_MPU_address) == false);  // Fail

  // block too small: block of size < minimum for a create
  paddr block2 = initial_block_start + 25 * KERNELSTRUCTURETOTALLENGTH();
  paddr block3 = initial_block_start + 25 * KERNELSTRUCTURETOTALLENGTH() + 12;  // too small block
  paddr block2_MPU_address = cutMemoryBlock(initial_block_root_address, block2, -1);
  assert(block2_MPU_address == &ks_root->mpu[2]);  // 3rd entry
  paddr block3_MPU_address = cutMemoryBlock(block2_MPU_address, block3, -1);
  assert(block3_MPU_address == &ks_root->mpu[3]);  // 4th entry
  assert(createPartition(block2_MPU_address) == false);  // Fail

  // block shared: prepare child partition and add a shared block
  paddr block4 = initial_block_start + 20 * KERNELSTRUCTURETOTALLENGTH();
  paddr block4_MPU_root_address = cutMemoryBlock(initial_block_root_address, block4, -1);
  assert(block4_MPU_root_address != false);  // 5th entry
  assert(prepare(block1, 8, block4_MPU_root_address) != false);
  assert(addMemoryBlock(block1, block3_MPU_address, true, true, false) != false);
  assert(createPartition(block3_MPU_address) == false);  // Fail
}

/*!
 * \fn void test_create_sister_partitions()
 * \brief Cuts 6 times = 6 created blocks + initial block + last free slot
 * Each block becomes a PD of a sister partition except initial block and last entry (free slot)
 */
void test_create_sister_partitions()
{
  KStructure_t* ks_root = (KStructure_t*) root_kernel_structure_start;
  uint32_t cut_offset = PDSTRUCTURETOTALLENGTH() + 2;
  paddr block1_MPU_address = cutMemoryBlock(initial_block_root_address, initial_block_start + cut_offset, -1);
  assert(block1_MPU_address != false);
  paddr block2_MPU_address = cutMemoryBlock(block1_MPU_address, initial_block_start + 2*cut_offset, -1) ;
  assert(block2_MPU_address != false);
  paddr block3_MPU_address = cutMemoryBlock(block2_MPU_address, initial_block_start + 3*cut_offset, -1);
  assert(block3_MPU_address != false);
  paddr block4_MPU_address = cutMemoryBlock(block3_MPU_address, initial_block_start + 4*cut_offset, -1);
  assert(block4_MPU_address != false);
  paddr block5_MPU_address = cutMemoryBlock(block4_MPU_address, initial_block_start + 5*cut_offset, -1);
  assert(block5_MPU_address != false);
  paddr block6_MPU_address = cutMemoryBlock(block5_MPU_address, initial_block_start + 6*cut_offset, -1);
  assert(block6_MPU_address != false);

  assert(createPartition(block1_MPU_address) != false);
  assert(createPartition(block2_MPU_address) != false);
  assert(createPartition(block3_MPU_address) != false);
  assert(createPartition(block4_MPU_address) != false);
  assert(createPartition(block5_MPU_address) != false);
  assert(createPartition(block6_MPU_address) != false);

  dump_partition(root);

  // Check the Sh1 structure
  assert(readSh1PDChildFromMPUEntryAddr(root_kernel_structure_start) == NULL);
  assert(readSh1PDFlagFromMPUEntryAddr(root_kernel_structure_start) == false); // untouched
  assert(readSh1InChildLocationFromMPUEntryAddr(root_kernel_structure_start) == NULL);

  paddr cut1_offset_Sh1_entry = &ks_root->mpu[1];
  assert(readSh1PDChildFromMPUEntryAddr(cut1_offset_Sh1_entry) == NULL);
  assert(readSh1PDFlagFromMPUEntryAddr(cut1_offset_Sh1_entry) == true);
  assert(readSh1InChildLocationFromMPUEntryAddr(cut1_offset_Sh1_entry) == NULL);

  paddr cut2_offset_Sh1_entry = &ks_root->mpu[2];
  assert(readSh1PDChildFromMPUEntryAddr(cut2_offset_Sh1_entry) == NULL);
  assert(readSh1PDFlagFromMPUEntryAddr(cut2_offset_Sh1_entry) == true);
  assert(readSh1InChildLocationFromMPUEntryAddr(cut2_offset_Sh1_entry) == NULL);

  paddr cut3_offset_Sh1_entry = &ks_root->mpu[3];
  assert(readSh1PDChildFromMPUEntryAddr(cut3_offset_Sh1_entry) == NULL);
  assert(readSh1PDFlagFromMPUEntryAddr(cut3_offset_Sh1_entry) == true);
  assert(readSh1InChildLocationFromMPUEntryAddr(cut3_offset_Sh1_entry) == NULL);

  paddr cut4_offset_Sh1_entry = &ks_root->mpu[4];
  assert(readSh1PDChildFromMPUEntryAddr(cut4_offset_Sh1_entry) == NULL);
  assert(readSh1PDFlagFromMPUEntryAddr(cut4_offset_Sh1_entry) == true);
  assert(readSh1InChildLocationFromMPUEntryAddr(cut4_offset_Sh1_entry) == NULL);

  paddr cut5_offset_Sh1_entry = &ks_root->mpu[5];
  assert(readSh1PDChildFromMPUEntryAddr(cut5_offset_Sh1_entry) == NULL);
  assert(readSh1PDFlagFromMPUEntryAddr(cut5_offset_Sh1_entry) == true);
  assert(readSh1InChildLocationFromMPUEntryAddr(cut5_offset_Sh1_entry) == NULL);

  paddr cut6_offset_Sh1_entry = &ks_root->mpu[6];
  assert(readSh1PDChildFromMPUEntryAddr(cut6_offset_Sh1_entry) == NULL);
  assert(readSh1PDFlagFromMPUEntryAddr(cut6_offset_Sh1_entry) == true);
  assert(readSh1InChildLocationFromMPUEntryAddr(cut6_offset_Sh1_entry) == NULL);

  paddr free_slot_Sh1_entry = &ks_root->mpu[7];
  assert(readSh1PDChildFromMPUEntryAddr(free_slot_Sh1_entry) == NULL);
  assert(readSh1PDFlagFromMPUEntryAddr(free_slot_Sh1_entry) == false); // untouched
  assert(readSh1InChildLocationFromMPUEntryAddr(free_slot_Sh1_entry) == NULL);
}

/*!
 * \fn void test_create()
 * \brief Launches the tests of the createPartition system call
 */
void test_create()
{
  init_tests_only_ram();
  test_create_partition();

  init_tests_only_ram();
  test_create_partitions_bad_arguments();

  init_tests_only_ram();
  test_create_sister_partitions();
}

// TEST PREPARE SYSTEM CALL

/*!
 * \fn void prepare_test_generic(idPD, MPUAddressBlockPrepare)
 * \brief  Generic test for prepare
 * Prepares the partition <idPD> (current partition or child partition) and checks that the concerned PD is updated
 * as expected and checks the kernel structures are all default
 */
void prepare_test_generic(paddr idPD, paddr MPUAddressBlockPrepare)
{
  paddr old_pointer_to_MPU_linked_list = readPDStructurePointer(idPD);
  paddr old_first_free_slot_address = readPDFirstFreeSlotPointer(idPD);
  uint32_t old_nb_free_slots = readPDNbFreeSlots(idPD);
  uint32_t old_nb_prepare = readPDNbPrepare(idPD);
  paddr old_parent = readPDParent(idPD);
  KStructure_t* ks_old_first = (KStructure_t*) old_pointer_to_MPU_linked_list;

  assert(prepare(idPD, -1, MPUAddressBlockPrepare) != false);

  paddr idBlockPrepare = readMPUStartFromMPUEntryAddr(MPUAddressBlockPrepare);
  KStructure_t* ks_prepare = (KStructure_t*) idBlockPrepare;

  // Check correct PD changes
  assert(readPDStructurePointer(idPD) == idBlockPrepare);
  assert(readPDNbFreeSlots(idPD) == (old_nb_free_slots + 8));  // initial free slots + prepare
  assert(readPDFirstFreeSlotPointer(idPD) == idBlockPrepare);
  assert(readPDNbPrepare(idPD) == (old_nb_prepare + 1));
  assert(readPDParent(idPD) == old_parent);

  // Check correct MPU init of prepare block
  assert(readMPUIndexFromMPUEntryAddr(idBlockPrepare) == 0);
  assert(readMPUStartFromMPUEntryAddr(idBlockPrepare) == NULL);
  assert(readMPUEndFromMPUEntryAddr(idBlockPrepare) == &ks_prepare->mpu[1]);
  assert(readMPUAccessibleFromMPUEntryAddr(idBlockPrepare) == false);
  assert(readMPUPresentFromMPUEntryAddr(idBlockPrepare) == false);

  for(int i = 1 ; i < KERNELSTRUCTUREENTRIESNB - 1 ; i++)
  {
      paddr empty_block_MPU_entry = &ks_prepare->mpu[i];
      // assert(empty_block_MPU_entry[1],
      //                  idBlockPrepare + (i - 1) * mpuentrylength);
      assert(readMPUIndexFromMPUEntryAddr(empty_block_MPU_entry) == i);
      assert(readMPUStartFromMPUEntryAddr(empty_block_MPU_entry) == NULL);
      assert(readMPUEndFromMPUEntryAddr(empty_block_MPU_entry) ==
                                         &ks_prepare->mpu[i+1]);
      assert(readMPUAccessibleFromMPUEntryAddr(empty_block_MPU_entry) == false);
      assert(readMPUPresentFromMPUEntryAddr(empty_block_MPU_entry) == false);
  }

  // Check that last (free) entry points to previous first free slot
  paddr last_entry_address =  &ks_prepare->mpu[KERNELSTRUCTUREENTRIESNB - 1];
  assert(readMPUIndexFromMPUEntryAddr(last_entry_address) == (KERNELSTRUCTUREENTRIESNB - 1));
  assert(readMPUStartFromMPUEntryAddr(last_entry_address) == NULL);
  assert(readMPUEndFromMPUEntryAddr(last_entry_address) == old_first_free_slot_address);
  assert(readMPUAccessibleFromMPUEntryAddr(last_entry_address) == false);
  assert(readMPUPresentFromMPUEntryAddr(last_entry_address) == false);

  // Check that the previous first kernel structure still holds
  if (old_first_free_slot_address !=0)
{     // if there was still at least one free slot before
      assert(readMPUIndexFromMPUEntryAddr(&ks_old_first->mpu[0]) == 0);
      assert(readMPUStartFromMPUEntryAddr(&ks_old_first->mpu[0]) != NULL);
      assert(readMPUEndFromMPUEntryAddr(&ks_old_first->mpu[0]) !=
                                        NULL);
      assert(readMPUAccessibleFromMPUEntryAddr(&ks_old_first->mpu[0]) == false);
      assert(readMPUPresentFromMPUEntryAddr(&ks_old_first->mpu[0]) == true);
      remaining_MPU_slots_form_a_linked_list(1, KERNELSTRUCTUREENTRIESNB-1, old_pointer_to_MPU_linked_list);

  }
  // Check that the new SC and Sh1 structures are default
  Sh1_structure_is_default(readPDStructurePointer(idPD));
  SC_structure_is_default(readPDStructurePointer(idPD));

  // Check next pointer points to previous kernel structure
  assert(readNextFromKernelStructureStart(idBlockPrepare) == old_pointer_to_MPU_linked_list);
}

/*!
 * \fn void test_prepare_current_partition()
 * \brief  Launches the generic test as the current partition and do a prepare on itself
 */
void test_prepare_current_partition()
{
  prepare_test_generic(getCurPartition(), initial_block_root_address);
  // Check that the block is not marked as shared in the parent
  assert(readSh1PDChildFromMPUEntryAddr(
      readPDStructurePointer(getCurPartition())) ==
                    NULL);
}

/*!
 * \fn void test_prepare_child()
 * \brief  Launches the generic test as the parent partition and do a prepare on one of its children
 * First cut the initial block to create a partition out of it and prepare the child partition from the parent
 * taking the initial block as new kernel structure for the child
 */
void test_prepare_child()
{
  // Cut initial block and create a child partition with the created block
  paddr prepare_block_MPU_address = readPDStructurePointer(getCurPartition());
  paddr id_child_pd = initial_block_start + 0x4096;
  paddr child_pd_MPU_address = cutMemoryBlock(initial_block_root_address, id_child_pd, -1);
  assert(child_pd_MPU_address != false);
  assert(createPartition(child_pd_MPU_address) != false);
  dump_partition(root);
  prepare_test_generic(id_child_pd, initial_block_root_address);
  // Check that the block is marked as shared in the parent
  assert(readSh1PDChildFromMPUEntryAddr(prepare_block_MPU_address) == id_child_pd);
  dump_partition(root);
}

/*!
 * \fn void test_prepare_planned_nb_slots_less_than_current_free_slots_nb()
 * \brief Tests if prepare fails when there are enough free slots for the projected slots
 */
void test_prepare_planned_nb_slots_less_than_current_free_slots_nb()
{
  uint32_t current_nb_free_slots = readPDNbFreeSlots(root);
  // Check a prepare fails if enough free slots
  assert(prepare(root, current_nb_free_slots - 1, initial_block_root_address) == false);
}

/*!
 * \fn void test_prepare_fails_when_reaching_max_nb_prepare()
 * \brief  Tests if prepare fails when the partition reached the maximum number of allowed prepare
 * Init: cut 8 blocks (including initial) + prepare 7 times
 * Test:
 *     - prepare should fail when reaching max number of prepare
 */
void test_prepare_fails_when_reaching_max_nb_prepare()
{
  // Init
  paddr initial_block = initial_block_start;
  paddr block1_addr = initial_block + 20 * KERNELSTRUCTURETOTALLENGTH();
  paddr block2_addr = initial_block + 18 * KERNELSTRUCTURETOTALLENGTH();
  paddr block3_addr = initial_block + 16 * KERNELSTRUCTURETOTALLENGTH();
  paddr block4_addr = initial_block + 14 * KERNELSTRUCTURETOTALLENGTH();
  paddr block5_addr = initial_block + 12 * KERNELSTRUCTURETOTALLENGTH();
  paddr block6_addr = initial_block + 10 * KERNELSTRUCTURETOTALLENGTH();
  paddr block7_addr = initial_block + 8 * KERNELSTRUCTURETOTALLENGTH();
  // cut 8 blocks
  paddr block1 = cutMemoryBlock(initial_block_root_address, block1_addr, -1);
  assert(block1 != false);
  paddr block2 = cutMemoryBlock(initial_block_root_address, block2_addr, -1);
  assert(block2 != false);
  paddr block3 = cutMemoryBlock(initial_block_root_address, block3_addr, -1);
  assert(block3 != false);
  paddr block4 = cutMemoryBlock(initial_block_root_address, block4_addr, -1);
  assert(block4 != false);
  paddr block5 = cutMemoryBlock(initial_block_root_address, block5_addr, -1);
  assert(block5 != false);
  paddr block6 = cutMemoryBlock(initial_block_root_address, block6_addr, -1);
  assert(block6 != false);
  paddr block7 = cutMemoryBlock(initial_block_root_address, block7_addr, -1);
  assert(block7 != false);
  // prepare 7 times
  assert(prepare(getCurPartition(), -1, initial_block_root_address) != false);
  assert(prepare(getCurPartition(), -1, block1) != false);
  assert(prepare(getCurPartition(), -1, block2) != false);
  assert(prepare(getCurPartition(), -1, block3) != false);
  assert(prepare(getCurPartition(), -1, block4) != false);
  assert(prepare(getCurPartition(), -1, block5) != false);
  assert(prepare(getCurPartition(), -1, block6) != false);

  // Fail because max number of prepare reached
  assert(prepare(getCurPartition(), -1, block7) == false);
}

/*!
 * \fn void test_prepare_bad_arguments()
 * \brief  Tests that providing bad arguments fail
 * Bad arguments:
 * - projectedSlotsNb: too many projected slots
 * - idPD: the provided PD is not the current partition or a child
 * - idRequisitionedBlock: the block doesn't exist or is not accessible or is too small
 */
void test_prepare_bad_arguments()
{
  // Fail because too many projected slots
  assert(prepare(root, KERNELSTRUCTUREENTRIESNB + 1, initial_block_root_address) == false);

  // Fail because PD is neither the current partition or a child
  assert(prepare((paddr) 0x1, -1, initial_block_root_address) == false);

  // Fail because the block given to hold the prepared structure doesn't exist
  assert(prepare(root, -1, initial_block_root_address - 0x100) == false);

  // cut initial block in a small block and a huge block + create child partition with huge block
  paddr huge_block = initial_block_start + KERNELSTRUCTURETOTALLENGTH() - 0x100;
  paddr huge_block_MPU_address = cutMemoryBlock(initial_block_root_address, huge_block, -1);
  assert(huge_block_MPU_address != false);
  assert(createPartition(huge_block_MPU_address) != false);
  // Fail because block used to prepare is inaccessible (PD of child partition);
  assert(prepare(getCurPartition(), -1, huge_block_MPU_address) == false);
  // Fail because block used to prepare is too small
  assert(prepare(huge_block, -1, initial_block_root_address) == false);
}

/*!
 * \fn void test_prepare()
 * \brief Launches the tests of the prepare system call
 */
void test_prepare()
{
  init_tests_only_ram();
  test_prepare_current_partition();

  init_tests_only_ram();
  test_prepare_child();

  init_tests_only_ram();
  test_prepare_planned_nb_slots_less_than_current_free_slots_nb();

  init_tests_only_ram();
  test_prepare_fails_when_reaching_max_nb_prepare();

  init_tests_only_ram();
  test_prepare_bad_arguments();
}



// TEST ADD MEMORY BLOCK SYSTEM CALL

/*!
 * \fn void add_alone()
 * \brief  Adds a block to a child and the other to share with the child
 * Tests that the add behaves according to expectations
 * init_test creates a partition and prepares it. There is one block left <block_to_share_id>
 */
void add_alone()
{
  // Init 3 blocks (create, prepare, share) + create a child partition + prepare it
  build_create_child_block_out_of_initial_block();
  build_prepare_child_block_out_of_initial_block();
  build_share_block_out_of_initial_block();
  init_test_with_create_prepare_child(false);

  // adding a block
  paddr block_to_share_in_child_address = NULL;

  block_to_share_in_child_address = addMemoryBlock(child_partition_pd,
                                                        block_to_share_MPU_root_address,
                                                        true, true, false); // RW = true, X = false
  assert(block_to_share_in_child_address != false);

  dump_ancestors(child_partition_pd);

  // Check the added block is still accessible from the current partition
  assert(readMPUStartFromMPUEntryAddr(block_to_share_MPU_root_address) == block_to_share_id);
  assert(readMPUEndFromMPUEntryAddr(block_to_share_MPU_root_address) == (block_prepare_child_id - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(block_to_share_MPU_root_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(block_to_share_MPU_root_address) == true);

  // Check the added block marked shared with the child in the current partition
  assert(readSh1PDChildFromMPUEntryAddr(block_to_share_MPU_root_address) == child_partition_pd);
  assert(readSh1PDFlagFromMPUEntryAddr(block_to_share_MPU_root_address) == false);
  assert(readSh1InChildLocationFromMPUEntryAddr(block_to_share_MPU_root_address) == block_to_share_in_child_address);

  // Check the added block is in the child partition with correct rights
  assert(readMPUStartFromMPUEntryAddr(block_to_share_in_child_address) == readMPUStartFromMPUEntryAddr(block_to_share_MPU_root_address));
  assert(readMPUEndFromMPUEntryAddr(block_to_share_in_child_address) == readMPUEndFromMPUEntryAddr(block_to_share_MPU_root_address));
  assert(readMPUAccessibleFromMPUEntryAddr(block_to_share_in_child_address) == readMPUAccessibleFromMPUEntryAddr(block_to_share_MPU_root_address));
  assert(readMPUPresentFromMPUEntryAddr(block_to_share_in_child_address) == readMPUPresentFromMPUEntryAddr(block_to_share_MPU_root_address));
  // check rights
  assert(readMPURFromMPUEntryAddr(block_to_share_in_child_address) == true);
  assert(readMPUWFromMPUEntryAddr(block_to_share_in_child_address) == true); // true
  assert(readMPUXFromMPUEntryAddr(block_to_share_in_child_address) == false);

  // Check the remaining slots are default in child
  remaining_MPU_slots_form_a_linked_list(1, KERNELSTRUCTUREENTRIESNB - 1,
                                              readPDStructurePointer(child_partition_pd));

  // Check the Sh1 structure is default in child
  Sh1_structure_is_default(readPDStructurePointer(child_partition_pd));

  // Check the SC structure: first entry not cut and initial block is hte block to share + remaining slots defaults
  assert(readSCOriginFromMPUEntryAddr(block_to_share_in_child_address) == block_to_share_id);
  assert(readSCNextFromMPUEntryAddr(block_to_share_in_child_address) == false);
  remaining_SC_slots_are_default(1, KERNELSTRUCTUREENTRIESNB - 1,
                                      readPDStructurePointer(child_partition_pd));
}

/*!
 * \fn void test_add_alone()
 * \brief Launches the add_alone test
 */
void test_add_alone()
{
  add_alone(false);
}

/*!
 * \fn void test_add_alone_Fast()
 * \brief Launches the add_alone_Fast test
 */
void test_add_alone_Fast()
{
  add_alone(true);
}

/*!
 * \fn void add_no_free_slots_left()
 * \brief  Tests that no add can be performed when no free slots are available in the child partition
 */
void add_no_free_slots_left()
{
  build_create_child_block_out_of_initial_block();
  build_prepare_child_block_out_of_initial_block();
  build_share_block_out_of_initial_block();
  init_test_with_create_without_prepare_child(false);

  assert(addMemoryBlock(child_partition_pd,
                        block_to_share_MPU_root_address,
                        true, true, false) == false);
}

/*!
 * \fn void test_add_no_free_slots_left()
 * \brief Launches the add_no_free_slots_left test
 */
void test_add_no_free_slots_left()
{
  add_no_free_slots_left(false);
}

/*!
 * \fn void test_add_no_free_slots_left_Fast()
 * \brief Launches the add_no_free_slots_left test
 */
void test_add_no_free_slots_left_Fast()
{
  add_no_free_slots_left(true);
}


/*!
 * \fn void add_bad_arguments()
 * \brief  Tests that providing bad arguments fail
 * init_test creates a partition and prepares it. There is one block left <block_to_share_id>
 * Bad arguments:
 * - idPDchild: the provided PD is not a child of the current partition
 * - MPUAddressBlockToShare: the block doesn't exist or is not accessible
 */
void add_bad_arguments()
{
  build_create_child_block_out_of_initial_block();
  build_prepare_child_block_out_of_initial_block();
  build_share_block_out_of_initial_block();
  init_test_with_create_prepare_child(false);

  // Check fail because PD is not a child
  assert(addMemoryBlock((paddr) 0x01,
                        block_to_share_MPU_root_address,
                        true, true, false) == false);
  // Check fail because block to be shared doesn't exist, invalid MPU address (with structure list length = 1)
  assert(addMemoryBlock(child_partition_pd,
                        root_kernel_structure_start - 50,
                        true, true, false) == false);
  // Prepare current partition with block to be shared -> becomes inacessible
  assert(prepare(getCurPartition(),-1, block_to_share_MPU_root_address) != false);

  // Check fail because block to be shared doesn't exist, invalid MPU address (with structure list length = 2)
  assert(addMemoryBlock(child_partition_pd,
                        root_kernel_structure_start - 50,
                        true, true, false) == false);

  // Check the block to be shared is inaccessible (block to share has been used in the previous prepare)
  assert(addMemoryBlock(child_partition_pd,
                        block_to_share_MPU_root_address,
                        true, true, false) == false);

  // Check the block's rights : must be readable and compatible to initial (RW=true, X=false)
  // Read must be set
  assert(addMemoryBlock(child_partition_pd,
                        block_to_share_MPU_root_address,
                        false, true, false) == false); // Read = false
  // Execute can't be set
  assert(addMemoryBlock(child_partition_pd,
                        block_to_share_MPU_root_address,
                        true, true, true) == false); // exec = true
}

/*!
 * \fn void test_add_bad_arguments()
 * \brief Test bad arguments on add
 */
void test_add_bad_arguments()
{
  add_bad_arguments(false);
}

/*!
 * \fn void test_add_bad_arguments_Fast()
 * \brief Test bad arguments on add Fast
 */
void test_add_bad_arguments_Fast()
{
  add_bad_arguments(true);
}

/*!
 * \fn void test_add()
 * \brief Launches the tests of the add system call
 */
void test_add()
{
  init_tests_only_ram();
  test_add_alone();

  init_tests_only_ram();
  test_add_alone_Fast();

  init_tests_only_ram();
  test_add_no_free_slots_left();

  init_tests_only_ram();
  test_add_no_free_slots_left_Fast();

  init_tests_only_ram();
  test_add_bad_arguments();

  init_tests_only_ram();
  test_add_bad_arguments_Fast();
}

// TEST REMOVE MEMORY BLOCK SYSTEM CALL

/*!
 * \fn void remove_alone(fast=false)
 * \brief  Tests that an add followed by a remove gets back to the same state as before the add
 * Tests that:
 * - addMemoryBlock changes the MPU structure
 * - PD is the same after remove
 * - MPU is default after remove
 * - Sh1 is default after remove
 * - SC is default after remove
 */
void remove_alone(int fast)
{
  // First cut the initial block
  build_create_child_block_out_of_initial_block();
  build_prepare_child_block_out_of_initial_block();
  build_share_block_out_of_initial_block();

  // create and prepare child partition
  init_test_with_create_prepare_child(false);

  // keep state of PD and check kernel structure where to add is empty
  paddr old_pointer_to_MPU_linked_list = readPDStructurePointer(child_partition_pd);
  paddr old_first_free_slot_address = readPDFirstFreeSlotPointer(child_partition_pd);
  uint32_t old_nb_free_slots = readPDNbFreeSlots(child_partition_pd);
  uint32_t old_nb_prepare = readPDNbPrepare(child_partition_pd);
  paddr old_parent = readPDParent(child_partition_pd);

  // add + remove = same as before
  assert(addMemoryBlock(child_partition_pd,
                        block_to_share_MPU_root_address,
                        true, true, false) != false);
  // check first entry is not default after add
  paddr child_kernel_structure_start = readPDStructurePointer(child_partition_pd);
  assert(readMPUStartFromMPUEntryAddr(child_kernel_structure_start) != NULL);
  assert(readMPUEndFromMPUEntryAddr(child_kernel_structure_start) != NULL);
  assert(readMPUAccessibleFromMPUEntryAddr(child_kernel_structure_start) != false);
  assert(readMPUPresentFromMPUEntryAddr(child_kernel_structure_start) != false);
  remaining_MPU_slots_form_a_linked_list(1, KERNELSTRUCTUREENTRIESNB - 1, child_kernel_structure_start);

  // REMOVE block + checks PD is same as before + MPU/Sh1/SC are default
  assert(removeMemoryBlock( child_partition_pd,
                            block_to_share_MPU_root_address) != false);
  assert(old_pointer_to_MPU_linked_list == readPDStructurePointer(child_partition_pd));
  assert(old_first_free_slot_address == readPDFirstFreeSlotPointer(child_partition_pd));
  assert(old_nb_free_slots == readPDNbFreeSlots(child_partition_pd));
  assert(old_nb_prepare == readPDNbPrepare(child_partition_pd));
  assert(old_parent == readPDParent(child_partition_pd));
  remaining_MPU_slots_form_a_linked_list(0, KERNELSTRUCTUREENTRIESNB - 1, child_kernel_structure_start);
  Sh1_structure_is_default(child_kernel_structure_start);
  SC_structure_is_default(child_kernel_structure_start);
}

/*!
 * \fn void test_remove_alone()
 * \brief Launches the remove alone test
 */
void test_remove_alone()
{
  remove_alone(false);
}

/*!
 * \fn void test_remove_alone_Fast()
 * \brief Launches the remove alone Fast test
 */
void test_remove_alone_Fast()
{
  remove_alone(true);
}


/*!
 * \fn void remove_in_grandchildren()
 * \brief  Tests that a remove of an accessible shared memory block is also removed in all grandchildren
 * This block can't be cut otherwise becomes not accessible
 *
 * Init:
 * - create + prepare a child
 * - create + prepare a grandchild
 * - add a shared memory block from the root partition to the child
 * - add the same memory block from the child to the grandchild
 *
 * Tests after remove:
 * - the shared memory block is removed in the child from the root partition and should also be removed in the
 * grandchild
 */
void remove_in_grandchildren()
{
  updateCurPartition(root);
  // First cut the initial block to create and prepare the child
  build_create_child_block_out_of_initial_block();
  build_prepare_child_block_out_of_initial_block();
  build_share_block_out_of_initial_block();

  // build 1 block later cut to create+prepare grandchild
  paddr grandchild_block_id = block_prepare_child_id + KERNELSTRUCTURETOTALLENGTH() * 4;
  paddr block_grandchild_MPU_root_address = cutMemoryBlock(block_prepare_child_MPU_root_address, grandchild_block_id, -1);
  assert(block_grandchild_MPU_root_address != false);

  // create and prepare child partition
  init_test_with_create_prepare_child(false);

  // give the block to create+prepare grandchild
  paddr block_grandchild_MPU_child_address = addMemoryBlock(child_partition_pd,
                                                            block_grandchild_MPU_root_address,
                                                            true, true, false);
  assert(block_grandchild_MPU_child_address != false);
  dump_ancestors(child_partition_pd);

  // Then move to child and create and prepare the grandchild
  updateCurPartition(child_partition_pd);
  build_create_grandchild_block(block_grandchild_MPU_child_address);
  build_prepare_grandchild_block(block_grandchild_MPU_child_address);
  assert(createPartition(block_create_grandchild_MPU_child_address) != false);
  assert(prepare(grandchild_partition_pd, 1, block_prepare_grandchild_MPU_child_address) != false);

  // Switch back to parent and add block-to-share to child
  updateCurPartition(root);
  paddr block_to_share_MPU_child_address = addMemoryBlock(child_partition_pd,
                                                          block_to_share_MPU_root_address,
                                                          true, true, false);
  assert(block_to_share_MPU_child_address != false);

  // Switch to child and add block to grandchild
  updateCurPartition(child_partition_pd);
  paddr block_to_share_MPU_grandchild_address = addMemoryBlock(grandchild_partition_pd,
                                                              block_to_share_MPU_child_address,
                                                              true, true, false);
  assert(block_to_share_MPU_grandchild_address != false);

  // Tests that block-to-share is present and accessible in child and grandchild
  assert(readMPUStartFromMPUEntryAddr(block_to_share_MPU_child_address) == block_to_share_id);
  assert(readMPUAccessibleFromMPUEntryAddr(block_to_share_MPU_child_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(block_to_share_MPU_child_address) == true);

  assert(readMPUStartFromMPUEntryAddr(block_to_share_MPU_grandchild_address) == block_to_share_id);
  assert(readMPUAccessibleFromMPUEntryAddr(block_to_share_MPU_grandchild_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(block_to_share_MPU_grandchild_address) == true);

  // REMOVE : Switch back to parent and remove block to share
  updateCurPartition(root);
  assert(removeMemoryBlock(child_partition_pd,
                          block_to_share_MPU_root_address) != false);


  // test block is not present anymore in child AND grandchild
  assert(readMPUStartFromMPUEntryAddr(block_to_share_MPU_child_address) != block_to_share_id); // NOT equal
  //assert(child_MPU_entry[2], block_to_share_id + KERNELSTRUCTURETOTALLENGTH() - 1);  // NOT equal
  assert(readMPUAccessibleFromMPUEntryAddr(block_to_share_MPU_child_address) == false);
  assert(readMPUPresentFromMPUEntryAddr(block_to_share_MPU_child_address) == false);

  assert(readMPUStartFromMPUEntryAddr(block_to_share_MPU_grandchild_address) != block_to_share_id); // NOT equal
  //assert(grandchild_MPU_entry[2], block_to_share_id + KERNELSTRUCTURETOTALLENGTH() - 1);  // NOT equal
  assert(readMPUAccessibleFromMPUEntryAddr(block_to_share_MPU_grandchild_address) == false);
  assert(readMPUPresentFromMPUEntryAddr(block_to_share_MPU_grandchild_address) == false);

  // test grandchild is empty again
  remaining_MPU_slots_form_a_linked_list(0, KERNELSTRUCTUREENTRIESNB - 1, block_prepare_grandchild_id);
}

/*!
 * \fn void test_remove_in_grandchildren()
 * \brief Launches the remove_in_grandchildren test
 */
void test_remove_in_grandchildren()
{
  remove_in_grandchildren(false);

}

/*!
 * \fn void test_remove_in_grandchildren_Fast()
 * \brief Launches the remove_in_grandchildren Fast test
 */
void test_remove_in_grandchildren_Fast()
{
  remove_in_grandchildren(true);
}

/*!
 * \fn void remove_accessible_subblocks()
 * \brief  Tests that a remove of a shared memory block succeeds when it is cut in the child with all subblocks still
 * accessible
 *
 * Init:
 * - create + prepare a child
 * - add a shared memory block from the root partition to the child
 * - cuts 3 times the shared memory block
 * Tests:
 * - the shared memory block is removed from the child
 *     - No subblocks remain in the child
 * - the PD structure of the child is the same as before the add + cuts except for the first free slot pointer
 */
void remove_accessible_subblocks()
{
  build_create_child_block_out_of_initial_block();
  build_prepare_child_block_out_of_initial_block();
  build_share_block_out_of_initial_block();
  init_test_with_create_prepare_child(false);

  // keep state of PD (except pointer to first free which changes because of the removal order of the subblocks
  // compared to a single remove) and check kernel structure where to add is empty
  paddr old_pointer_to_MPU_linked_list = readPDStructurePointer(child_partition_pd);
  uint32_t old_nb_free_slots = readPDNbFreeSlots(child_partition_pd);
  uint32_t old_nb_prepare = readPDNbPrepare(child_partition_pd);
  paddr old_parent = readPDParent(child_partition_pd);

  // ADD
  paddr block_to_share_MPU_child_address = addMemoryBlock(child_partition_pd,
                                                          block_to_share_MPU_root_address,
                                                          true, true, false);
  assert(block_to_share_MPU_child_address != false);

  // CUT Switch to child -> cut shared block 3x
  updateCurPartition(child_partition_pd);
  paddr block1_MPU_child_address = cutMemoryBlock(block_to_share_MPU_child_address,
                                                  block_to_share_id + KERNELSTRUCTURETOTALLENGTH(),
                                                  -1);
  assert(block1_MPU_child_address != false);
  paddr block2_MPU_child_address = cutMemoryBlock(block1_MPU_child_address,
                                                  block_to_share_id + 2*KERNELSTRUCTURETOTALLENGTH(),
                                                  -1);
  assert(block2_MPU_child_address != false);
  paddr block3_MPU_child_address = cutMemoryBlock(block2_MPU_child_address,
                                                  block_to_share_id + 3*KERNELSTRUCTURETOTALLENGTH(),
                                                  -1);
  assert(block3_MPU_child_address != false);
  // Check MPU structure is not empty (check first entry);
  paddr MPU_kernel_structure_start = readPDStructurePointer(child_partition_pd);
  assert(readMPUStartFromMPUEntryAddr(MPU_kernel_structure_start) != NULL); // NOT equal
  assert(readMPUEndFromMPUEntryAddr(MPU_kernel_structure_start) != NULL); // NOT equal
  assert(readMPUAccessibleFromMPUEntryAddr(MPU_kernel_structure_start) != false);
  assert(readMPUPresentFromMPUEntryAddr(MPU_kernel_structure_start) != false);

  remaining_MPU_slots_form_a_linked_list(4, KERNELSTRUCTUREENTRIESNB - 1, MPU_kernel_structure_start);

  // REMOVE switch back to parent -> remove block in child
  updateCurPartition(root);
  assert(removeMemoryBlock(child_partition_pd,
                          block_to_share_MPU_root_address) != false);

  // Test PD is same as before + MPU/Sh1/SC are default -> all cuts are removed as well
  assert(old_pointer_to_MPU_linked_list ==
                    readPDStructurePointer(child_partition_pd));
  assert(old_nb_free_slots == readPDNbFreeSlots(child_partition_pd));
  assert(old_nb_prepare == readPDNbPrepare(child_partition_pd));
  assert(old_parent == readPDParent(child_partition_pd));

  // Test the kernel structure of the child is empty again
  MPU_structure_is_empty(block_prepare_child_id);
  Sh1_structure_is_default(block_prepare_child_id);
  SC_structure_is_default(block_prepare_child_id);
}

/*!
 * \fn void test_remove_accessible_subblocks()
 * \brief Launches the remove_accessible_subblocks test
 */
void test_remove_accessible_subblocks()
{
  remove_accessible_subblocks(false);
}

/*!
 * \fn void test_remove_accessible_subblocks_Fast()
 * \brief Launches the test_remove_accessible_subblocks_Fast test
 */
void test_remove_accessible_subblocks_Fast()
{
  remove_accessible_subblocks(true);
}


/*!
 * \fn void remove_fails_with_subblocks_inaccessible()
 * \brief  Tests that a remove fails if the child cuts the shared memory block and used it so it is inaccessible
 * Init:
 * - create + prepare a child
 * - add a shared memory block from the root partition to the child
 * - cuts 3 times the shared memory block
 * - prepare the child with the last cut block (which becomes inaccessible to him and its ancestors);
 * Tests:
 * - the removeMemoryBlock operation fails
 */
void remove_fails_with_subblocks_inaccessible()
{
  build_create_child_block_out_of_initial_block();
  build_prepare_child_block_out_of_initial_block();
  build_share_block_out_of_initial_block();
  init_test_with_create_prepare_child(false);

  // ADD
  paddr block_to_share_MPU_child_address = addMemoryBlock(child_partition_pd,
                                                          block_to_share_MPU_root_address,
                                                          true, true, false);
  assert(block_to_share_MPU_child_address != false);

  // CUT Switch to child -> cut shared block 3x
  updateCurPartition(child_partition_pd);
  paddr block1_MPU_child_address = cutMemoryBlock(block_to_share_MPU_child_address,
                                                  block_to_share_id + KERNELSTRUCTURETOTALLENGTH(),
                                                  -1);
  assert(block1_MPU_child_address != false);
  paddr block2_MPU_child_address = cutMemoryBlock(block1_MPU_child_address,
                                                  block_to_share_id + 2 * KERNELSTRUCTURETOTALLENGTH(),
                                                  -1);
  assert(block2_MPU_child_address != false);
  paddr block3_MPU_child_address = cutMemoryBlock(block2_MPU_child_address,
                                                  block_to_share_id + 3 * KERNELSTRUCTURETOTALLENGTH(),
                                                  -1);
  assert(block3_MPU_child_address != false);
  // PREPARE the child prepares itself to add a kernel structure with one of the subblocks
  assert(prepare(getCurPartition(), -1, block3_MPU_child_address) != false);
  // REMOVE fails
  updateCurPartition(root);
  assert(removeMemoryBlock(child_partition_pd,
                          block_to_share_MPU_root_address) == false);
}

/*!
 * \fn void test_remove_fails_with_subblocks_inaccessible()
 * \brief Launches the test_remove_fails_with_subblocks_inaccessible test
 */
void test_remove_fails_with_subblocks_inaccessible()
{
  remove_fails_with_subblocks_inaccessible(false);
}

/*!
 * \fn void test_remove_fails_with_subblocks_inaccessible_Fast()
 * \brief Launches the remove_fails_with_subblocks_inaccessible Fast test
 */
void test_remove_fails_with_subblocks_inaccessible_Fast()
{
  remove_fails_with_subblocks_inaccessible(true);
}


/*!
 * \fn void remove_fails_with_block_in_child_not_accessible()
 * \brief  Tests that a remove fails if the child uses the block differently as a shared memory block making it
 * inaccessible
 * Init:
 * - create + prepare a child
 * - add a shared memory block from the root partition to the child
 * - prepare the child with the block (which becomes inaccessible to him and its ancestors);
 * Tests:
 * - the removeMemoryBlock operation fails
 */
void remove_fails_with_block_in_child_not_accessible()
{
  build_create_child_block_out_of_initial_block();
  build_prepare_child_block_out_of_initial_block();
  build_share_block_out_of_initial_block();
  init_test_with_create_prepare_child(false);

  // ADD
  paddr block_to_share_MPU_child_address = addMemoryBlock(child_partition_pd,
                                                          block_to_share_MPU_root_address,
                                                          true, true, false);
  assert(block_to_share_MPU_child_address != false);

  // PREPARE the child prepares itself to add a kernel structure with one of the subblocks
  updateCurPartition(child_partition_pd);
  assert(prepare(getCurPartition(), -1, block_to_share_MPU_child_address) != false);
  // REMOVE fails
  updateCurPartition(root);
      assert(removeMemoryBlock(child_partition_pd,
                              block_to_share_MPU_root_address) == false);
}

/*!
 * \fn void test_remove_fails_with_block_in_child_not_accessible()
 * \brief Launches the remove_fails_with_block_in_child_not_accessible test
 */
void test_remove_fails_with_block_in_child_not_accessible()
{
  remove_fails_with_block_in_child_not_accessible(false);
}

/*!
 * \fn void test_cut()
 * \brief Launches the test_remove_fails_with_block_in_child_not_accessible_Fast test
 */
void test_remove_fails_with_block_in_child_not_accessible_Fast()
{
  remove_fails_with_block_in_child_not_accessible(true);
}

/*!
 * \fn void remove_bad_arguments()
 * \brief  Tests that providing bad arguments fail
 *     init_test creates a partition and prepares it. There is one block left <block_to_share_id>
 *     Bad arguments:
 *     - idPDchild: the provided PD is not a child of the current partition
 *     - MPUAddressBlockToRemove: the block doesn't exist or is not accessible
 */
void remove_bad_arguments()
{
  build_create_child_block_out_of_initial_block();
  build_prepare_child_block_out_of_initial_block();
  build_share_block_out_of_initial_block();
  init_test_with_create_prepare_child(false);

  // Check fail because PD is not a child
  assert(removeMemoryBlock((paddr) 0x1,
                            block_to_share_MPU_root_address) == false);

  // Check the block to be shared doesn't exist with invalid MPU address (with kernel structure list length = 1)
  assert(removeMemoryBlock(child_partition_pd,
                          root_kernel_structure_start - 50) == false);

  // PREPARE + Check the block to be shared doesn't exist with invalid MPU address (with kernel structure list length = 2)
  assert(prepare(getCurPartition(), -1, block_to_share_MPU_root_address) != false);
  assert(removeMemoryBlock(initial_block_start,
                          root_kernel_structure_start - 50) == false);

  // Check the block to be shared is inaccessible (block to share used in previous prepare);
  assert(removeMemoryBlock(initial_block_start,
                          block_to_share_MPU_root_address) == false);
}
/*!
 * \fn void test_remove_bad_arguments()
 * \brief Launches the remove_bad_arguments test
 */
void test_remove_bad_arguments()
{
  remove_bad_arguments(false);
}

/*!
 * \fn void test_remove_bad_arguments_Fast()
 * \brief Launches the remove_bad_arguments Fast test
 */
void test_remove_bad_arguments_Fast()
{
  remove_bad_arguments(true);
}

/*!
 * \fn void test_remove()
 * \brief Launches the tests of the remove system call
 */
void test_remove()
{
  init_tests_only_ram();
  test_remove_alone();

  init_tests_only_ram();
  test_remove_alone_Fast();

  init_tests_only_ram();
  test_remove_in_grandchildren();

  init_tests_only_ram();
  test_remove_in_grandchildren_Fast();

  init_tests_only_ram();
  test_remove_accessible_subblocks();

  init_tests_only_ram();
  test_remove_accessible_subblocks_Fast();

  init_tests_only_ram();
  test_remove_fails_with_subblocks_inaccessible();

  init_tests_only_ram();
  test_remove_fails_with_subblocks_inaccessible_Fast();

  init_tests_only_ram();
  test_remove_fails_with_block_in_child_not_accessible();

  init_tests_only_ram();
  test_remove_fails_with_block_in_child_not_accessible_Fast();

  init_tests_only_ram();
  test_remove_bad_arguments();

  init_tests_only_ram();
  test_remove_bad_arguments_Fast();
}

// TEST DELETE PARTITION SYSTEM CALL

/*!
 * \fn void test_delete_partition()
 * \brief  Tests that a delete partition succeeds
 *
 * Init:
 * - create a child
 * Tests after delete:
 * - the created partition is no more referenced in the current partition
 *     - the PDflag is unset again
 *     - the block used to create the partition is accessible again
 */
void test_delete_partition()
{
  // Check the PD is referenced in the parent and block is NOT accessible anymore
  init_test_with_create_without_prepare_child(true);
  assert(readSh1PDFlagFromMPUEntryAddr(block_create_child_MPU_root_address) ==
                    true);
  assert(
      readMPUAccessibleFromMPUEntryAddr(block_create_child_MPU_root_address) ==
      false
  );
  assert(deletePartition(block_create_child_MPU_root_address) != false);
  // Check the PD is NOT referenced in the parent and block is accessible again
  assert(readSh1PDFlagFromMPUEntryAddr(block_create_child_MPU_root_address) ==
                    false);
  assert(
      readMPUAccessibleFromMPUEntryAddr(block_create_child_MPU_root_address) ==
      true
  );
}

/*!
 * \fn void test_delete_partition_with_block_shared()
 * \brief  Tests to delete a child partition after create child + prepare child + shared block with child.
 * After delete, all blocks should be accessible and not shared.
 *
 * Init:
 * - create + prepare + share a block with a child
 * Tests after delete:
 * - the created partition is no more referenced in the current partition + shared block not shared anymore
 *     - the block used to create the partition is accessible again
 *     - the block used to prepare the child partition is accessible again
 *     - the block shared is not shared anymore (or PDflag is unset);
 */
void test_delete_partition_with_block_shared()
{
  init_test_with_create_prepare_share_child(true);

  // Delete the child partition
  assert(deletePartition(block_create_child_MPU_root_address) != false);

  // check that the (create + prepare) blocks are accessible again
  assert(readMPUAccessibleFromMPUEntryAddr(block_create_child_MPU_root_address)==
                    true);
  assert(readMPUAccessibleFromMPUEntryAddr(block_prepare_child_MPU_root_address)==
                    true);
  // check the shared block is still accessible
  assert(readMPUAccessibleFromMPUEntryAddr(block_to_share_MPU_root_address)==
                    true);
  // check they are all NOT shared with anyone
  assert(readSh1PDChildFromMPUEntryAddr(block_create_child_MPU_root_address) ==
                    false);
  assert(readSh1PDFlagFromMPUEntryAddr(block_create_child_MPU_root_address)==
                    false);
  assert(
      readSh1InChildLocationFromMPUEntryAddr(block_create_child_MPU_root_address) ==
      false
  );
  assert(readSh1PDChildFromMPUEntryAddr(block_prepare_child_MPU_root_address) ==
                    false);
  assert(readSh1PDFlagFromMPUEntryAddr(block_prepare_child_MPU_root_address)==
                    false);
  assert(
      readSh1InChildLocationFromMPUEntryAddr(block_prepare_child_MPU_root_address) ==
      false
  );
  assert(readSh1PDChildFromMPUEntryAddr(block_to_share_MPU_root_address) ==
                    false);
  assert(readSh1PDFlagFromMPUEntryAddr(block_to_share_MPU_root_address)==
                    false);
  assert(
      readSh1InChildLocationFromMPUEntryAddr(block_to_share_MPU_root_address) ==
      false
  );
}

/*!
 * \fn void test_delete_partition_with_block_shared_and_grandchild()
 * \brief  Tests to delete a child partition that has a child (grandchild of root partition). After delete, all blocks
 * should be accessible again and not shared.
 *
 * Init:
 * - create a child + prepare the child + share a block
 * - create a grandchild + prepare grandchild + share a block
 * Tests after delete:
 * - the child partition is no more referenced in the current partition + shared block not shared anymore
 *     - the block used to create the partition is accessible again
 *     - the block used to prepare the child partition is accessible again
 *     - the block shared and trimmed down to grandchild is accessible again
 */
void test_delete_partition_with_block_shared_and_grandchild()
{
  init_test_with_create_prepare_child_and_create_prepare_grandchild(true);
  updateCurPartition(child_partition_pd);
  assert(addMemoryBlock(grandchild_partition_pd,
                        block_to_share_MPU_child_address,
                        true, true, false) != false);
  dump_partition(grandchild_partition_pd);
  // Delete the child partition
  updateCurPartition(root);
  assert(deletePartition(block_create_child_MPU_root_address) != false);

  // check that the (create + prepare child) blocks in root are accessible again
  assert(
      readMPUAccessibleFromMPUEntryAddr(block_create_child_MPU_root_address) ==
      true);
  assert(
      readMPUAccessibleFromMPUEntryAddr(block_prepare_child_MPU_root_address) ==
      true);
  // check the shared block is still accessible for root
  assert(readMPUAccessibleFromMPUEntryAddr(block_to_share_MPU_root_address)==
                    true);
  // check they are all NOT shared with anyone
  // for create child block
  assert(readSh1PDChildFromMPUEntryAddr(block_create_child_MPU_root_address) ==
                    false);
  assert(readSh1PDFlagFromMPUEntryAddr(block_create_child_MPU_root_address)==
                    false);
  assert(
      readSh1InChildLocationFromMPUEntryAddr(block_create_child_MPU_root_address) ==
      false
  );
  // for prepare child block
  assert(readSh1PDChildFromMPUEntryAddr(block_prepare_child_MPU_root_address) ==
                    false);
  assert(readSh1PDFlagFromMPUEntryAddr(block_prepare_child_MPU_root_address)==
                    false);
  assert(
      readSh1InChildLocationFromMPUEntryAddr(block_prepare_child_MPU_root_address) ==
      false
  );
  // for shared block (used afterwards to create grandchild);
  assert(readSh1PDChildFromMPUEntryAddr(block_to_share_MPU_root_address) ==
                    false);
  assert(readSh1PDFlagFromMPUEntryAddr(block_to_share_MPU_root_address)==
                    false);
  assert(
      readSh1InChildLocationFromMPUEntryAddr(block_to_share_MPU_root_address) ==
      false
  );
}

/*!
 * \fn void test_delete_partition_grandchild_with_blocks_not_cut()
 * \brief  Test deleting a grandchild that has cut a shared block is deleted correctly and blocks set available
 * All grandchild blocks including cut blocks and crete/prepare should be available for root partition again after
 * deletion
 * Init: cut 4 blocks in root (+ initial) + create/prepare/share child + create/prepare/share grandchild + cut
 * shared block in grandchild (no more accessible to root and child partitions);
 * Test after deletion:
 *     - all blocks used in the grandchild (create/prepare/cut share) should be available to the root partition
 *     again
 */
void test_delete_partition_grandchild_with_blocks_not_cut()
{
  KStructure_t* ks_root = (KStructure_t*) root_kernel_structure_start;
  // INIT
  paddr child_partition_pd = initial_block_start;
  paddr block_prepare_child_id = initial_block_start + KERNELSTRUCTURETOTALLENGTH() * 2;
  paddr grandchild_partition_pd = initial_block_start + KERNELSTRUCTURETOTALLENGTH() * 4;
  paddr block_prepare_grandchild_id = initial_block_start + KERNELSTRUCTURETOTALLENGTH() * 6;
  paddr block_shared_id = initial_block_start + KERNELSTRUCTURETOTALLENGTH() * 8;
  // cut all blocks in root partition
  paddr block_prepare_child_MPU_root_address = cutMemoryBlock(initial_block_root_address, block_prepare_child_id, -1);
  assert(block_prepare_child_MPU_root_address != false);
  paddr grandchild_partition_pd_MPU_address = cutMemoryBlock(block_prepare_child_MPU_root_address, grandchild_partition_pd, -1);
  assert(grandchild_partition_pd_MPU_address != false);
  paddr block_prepare_grandchild_MPU_address = cutMemoryBlock(grandchild_partition_pd_MPU_address, block_prepare_grandchild_id, -1);
  assert(block_prepare_grandchild_MPU_address != false);
  paddr block_shared_MPU_address = cutMemoryBlock(block_prepare_grandchild_MPU_address, block_shared_id, -1);
  assert(block_shared_MPU_address != false);
  // create/prepare/share child + give all blocks for grandchild
  assert(createPartition(initial_block_root_address) != false);
  assert(prepare(child_partition_pd, 8, block_prepare_child_MPU_root_address) != false);
  paddr block_shared_child_MPU_address = addMemoryBlock(child_partition_pd,
                                                        block_shared_MPU_address,
                                                        true, true, false);
  assert(block_shared_child_MPU_address != false);
  paddr grandchild_pd_MPU_child_address = addMemoryBlock(child_partition_pd,
                                                        grandchild_partition_pd_MPU_address,
                                                        true, true, false);
  assert(grandchild_pd_MPU_child_address != false);
  paddr grandchild_prepare_MPU_child_address = addMemoryBlock(child_partition_pd,
                                                        block_prepare_grandchild_MPU_address,
                                                        true, true, false);
  assert(grandchild_prepare_MPU_child_address != false);
  // create/prepare/share grandchild
  updateCurPartition(child_partition_pd);
  assert(createPartition(grandchild_pd_MPU_child_address) != false);
  assert(prepare(grandchild_partition_pd, 8, grandchild_prepare_MPU_child_address) != false);
  paddr block_shared_MPU_child_address = addMemoryBlock(grandchild_partition_pd,
                                                        block_shared_child_MPU_address,
                                                        true, true, false);
  assert(block_shared_MPU_child_address != false);
  // cut shared block in grandchild
  updateCurPartition(grandchild_partition_pd);
  assert(cutMemoryBlock(block_shared_MPU_child_address, block_shared_id + KERNELSTRUCTURETOTALLENGTH(), -1) != false);

  // Check all grandchild blocks are NOT accessible anymore to root partition
  paddr root_kernel_structure_start = readPDStructurePointer(root_partition);
  assert(
      readMPUAccessibleFromMPUEntryAddr(
          &ks_root->mpu[2]
      ) == false
  );
  assert(
      readMPUAccessibleFromMPUEntryAddr(
          &ks_root->mpu[3]
      ) == false
  );
  assert(
      readMPUAccessibleFromMPUEntryAddr(
          &ks_root->mpu[4]
      ) == false
  );
  printf("*******Before******");
  dump_ancestors(child_partition_pd);

  // DELETE grandchild from child partition
  updateCurPartition(child_partition_pd);
  assert(deletePartition(grandchild_pd_MPU_child_address) != false);
  printf("*******After******");
  dump_ancestors(child_partition_pd);

  // Test all grandchild blocks are accessible AGAIN to root partition
  root_kernel_structure_start = readPDStructurePointer(root_partition);
  assert(
      readMPUAccessibleFromMPUEntryAddr(
          &ks_root->mpu[2]
      ) == true
  );
  assert(
      readMPUAccessibleFromMPUEntryAddr(
          &ks_root->mpu[3]
      ) == true
  );
  assert(
      readMPUAccessibleFromMPUEntryAddr(
          &ks_root->mpu[4]
      ) == true
  );
}

/*!
 * \fn void test_delete_partition_bad_arguments()
 * \brief  Tests that providing bad arguments fail
 * Init: create child
 * Bad arguments:
 * - idPDchildToDelete: does not exist
 * - idPDchildToDelete: is not a child
 */
void test_delete_partition_bad_arguments()
{
  // Test fails because block doesn't exist
  assert(deletePartition(initial_block_root_address + 50) == false);

  // Test fails because initial block is not a child
  assert(deletePartition(initial_block_root_address) == false);
}

/*!
 * \fn void test_delete()
 * \brief Launches the tests of the delete system call
 */
void test_delete()
{
  init_tests_only_ram();
  test_delete_partition();

  init_tests_only_ram();
  test_delete_partition_with_block_shared();

  init_tests_only_ram();
  test_delete_partition_with_block_shared_and_grandchild();

  init_tests_only_ram();
  test_delete_partition_grandchild_with_blocks_not_cut();

  init_tests_only_ram();
  test_delete_partition_bad_arguments();
}

// TEST MERGE SYSTEM CALL
/*!
 * \fn void test_merge_two_blocks()
 * \brief  Test merging two blocks
 * Init: cut the initial block
 * Test:
 *     - PD should be the same after merge back
 *         - first free slot is the same as before
 *         - nb free slots is the same as before (only initial block);
 */
void test_merge_two_blocks()
{
  paddr block1 = initial_block_start + KERNELSTRUCTURETOTALLENGTH();

  // keep state of PD
  paddr old_pointer_to_MPU_linked_list = readPDStructurePointer(getCurPartition());
  uint32_t old_nb_free_slots = readPDNbFreeSlots(getCurPartition());
  paddr old_first_free_slot = readPDFirstFreeSlotPointer(getCurPartition());
  uint32_t old_nb_prepare = readPDNbPrepare(getCurPartition());
  paddr old_parent = readPDParent(getCurPartition());

  paddr block1_MPU_address = cutMemoryBlock(initial_block_root_address, block1, -1);
  assert(block1_MPU_address != false);

  // Test PD changed -> first free slot pointer, nb free slots
  assert(readPDNbFreeSlots(getCurPartition()) !=
                    old_nb_free_slots); // NOT
  assert(readPDFirstFreeSlotPointer(getCurPartition()) !=
                    old_first_free_slot); // NOT
  dump_partition(root);
  // MERGE
  assert(mergeMemoryBlocks(initial_block_root_address, block1_MPU_address, -1) != NULL);

  // Test PD is back in the same state
  assert(readPDStructurePointer(getCurPartition()) ==
                    old_pointer_to_MPU_linked_list);
  assert(readPDNbFreeSlots(getCurPartition()) ==
                    old_nb_free_slots);
  assert(readPDFirstFreeSlotPointer(getCurPartition()) ==
                    old_first_free_slot);
  assert(readPDNbPrepare(getCurPartition()) ==
                    old_nb_prepare);
  assert(readPDParent(getCurPartition()) ==
                    old_parent);
}

/*!
 * \fn void test_merge_full_MPU_structure()
 * \brief  Test several merges in a row
 * Init: 7 cuts in a row to fill MPU structure
 * Tests: merge all blocks
 *     - final state should be the same as initial state
 */
void test_merge_full_MPU_structure()
{
  paddr block1 = initial_block_start + KERNELSTRUCTURETOTALLENGTH();
  paddr block2 = block1 + KERNELSTRUCTURETOTALLENGTH();
  paddr block3 = block2 + KERNELSTRUCTURETOTALLENGTH();
  paddr block4 = block3 + KERNELSTRUCTURETOTALLENGTH();
  paddr block5 = block4 + KERNELSTRUCTURETOTALLENGTH();
  paddr block6 = block5 + KERNELSTRUCTURETOTALLENGTH();
  paddr block7 = block6 + KERNELSTRUCTURETOTALLENGTH();

  // Fill MPU structure
  paddr block1_MPU_address = cutMemoryBlock(initial_block_root_address, block1, -1);
  assert(block1_MPU_address != false);
  paddr block2_MPU_address = cutMemoryBlock(block1_MPU_address, block2, -1);
  assert(block2_MPU_address != false);
  paddr block3_MPU_address = cutMemoryBlock(block2_MPU_address, block3, -1);
  assert(block3_MPU_address != false);
  paddr block4_MPU_address = cutMemoryBlock(block3_MPU_address, block4, -1);
  assert(block4_MPU_address != false);
  paddr block5_MPU_address = cutMemoryBlock(block4_MPU_address, block5, -1);
  assert(block5_MPU_address != false);
  paddr block6_MPU_address = cutMemoryBlock(block5_MPU_address, block6, -1);
  assert(block6_MPU_address != false);
  paddr block7_MPU_address = cutMemoryBlock(block6_MPU_address, block7, -1);
  assert(block7_MPU_address != false);

  // Check cuts are in place
  assert(readPDNbFreeSlots(root) == 0);

  // MERGE
  assert(mergeMemoryBlocks(block6_MPU_address, block7_MPU_address, -1) != NULL);
  assert(mergeMemoryBlocks(block5_MPU_address, block6_MPU_address, -1) != NULL);
  assert(mergeMemoryBlocks(block4_MPU_address, block5_MPU_address, -1) != NULL);
  assert(mergeMemoryBlocks(block3_MPU_address, block4_MPU_address, -1) != NULL);
  assert(mergeMemoryBlocks(block2_MPU_address, block3_MPU_address, -1) != NULL);
  assert(mergeMemoryBlocks(block1_MPU_address, block2_MPU_address, -1) != NULL);
  assert(mergeMemoryBlocks(initial_block_root_address, block1_MPU_address, -1) != NULL);

  // Test structure is as initial state after merging all cut blocks -> only initial block in MPU and remainting
  // entries are free slots, Sh1 default, SC first entry is initial block
  assert(readPDNbFreeSlots(root) == 7);

  remaining_MPU_slots_form_a_linked_list(
      1,
      KERNELSTRUCTUREENTRIESNB - 1,
      readPDStructurePointer(root)
  );
  Sh1_structure_is_default(readPDStructurePointer(root));
  remaining_SC_slots_are_default(
      1,
      KERNELSTRUCTUREENTRIESNB -1,
      readPDStructurePointer(root)
  );
}

/*!
 * \fn void test_merge_subblocks_child()
 * \brief  Test that merging the last subblocks in a child gives back the initial block which becomes accessible
 * again as shared memory to ancestors
 * Init: create and prepare a child + share a block + cut the shared block (becomes inaccessible to root);
 * Test after merge:
 *     - shared block is accessible again to root
 */
void test_merge_subblocks_child()
{
  init_test_with_create_prepare_share_child(true);

  // check shared block is still accessible to root partition
  assert(
      readMPUAccessibleFromMPUEntryAddr(block_to_share_MPU_root_address) ==
      true
  );
  // cut the shared block in child
  updateCurPartition(child_partition_pd);
  paddr block_to_share_MPU_child_address_cut = cutMemoryBlock(block_to_share_MPU_child_address, block_to_share_id + KERNELSTRUCTURETOTALLENGTH(), -1);
  assert(block_to_share_MPU_child_address_cut != false);

  // check that shared block is now not accessible anymore
  assert(
      readMPUAccessibleFromMPUEntryAddr(block_to_share_MPU_root_address) ==
      false
  );

  // MERGE
  assert(
      mergeMemoryBlocks(block_to_share_MPU_child_address, block_to_share_MPU_child_address_cut, -1) !=
      NULL
  );

  // Test that shared block is accessible again to root partition after merge
  assert(
      readMPUAccessibleFromMPUEntryAddr(block_to_share_MPU_root_address) ==
      true
  );
}

/*!
 * \fn void test_merge_bad_arguments()
 * \brief  Tests that providing bad arguments fail
 * Init: create child
 * Bad arguments:
 * - MPUAddressBlockToMerge1: does not exist or is shared or is not accessible
 * - MPUAddressBlockToMerge2: does not exist or is shared or is not accessible or does not follow block 1
 */
void test_merge_bad_arguments()
{
  build_create_child_block_out_of_initial_block();
  build_prepare_child_block_out_of_initial_block();
  build_share_block_out_of_initial_block();
  paddr root_accessible_block_id = block_to_share_id + KERNELSTRUCTURETOTALLENGTH();
  paddr root_accessible_block_root_address = cutMemoryBlock(block_to_share_MPU_root_address, root_accessible_block_id, -1);
  assert(root_accessible_block_root_address != false);
  // create, prepare and share a block with a child
  init_test_with_create_prepare_share_child(false);

  dump_ancestors(child_partition_pd);

  // Check fail because do not exist
  updateCurPartition(root);
  assert(mergeMemoryBlocks((paddr) 0x1, root_accessible_block_root_address, -1) == NULL);
  assert(mergeMemoryBlocks(root_accessible_block_root_address, (paddr) 0x2, -1) == NULL);

  // Check fail because shared
  assert(mergeMemoryBlocks(root_accessible_block_root_address, block_to_share_MPU_root_address, -1) == NULL);
  assert(mergeMemoryBlocks(block_to_share_MPU_root_address, root_accessible_block_root_address, -1) == NULL);

  // Check fail because not accessible
  assert(mergeMemoryBlocks(root_accessible_block_root_address, block_create_child_MPU_root_address, -1) == NULL);
  assert(mergeMemoryBlocks(block_create_child_MPU_root_address, root_accessible_block_root_address, -1) == NULL);

  // Check block 2 follows block 1 -> cut accessible block and try to merge
  paddr block1_root_address = cutMemoryBlock(root_accessible_block_root_address, root_accessible_block_id + KERNELSTRUCTURETOTALLENGTH(), -1);
  assert(block1_root_address != false);
  assert(
      mergeMemoryBlocks(block1_root_address, root_accessible_block_root_address, -1) ==
      NULL
  );  // Fail
  assert(
      mergeMemoryBlocks(root_accessible_block_root_address, block1_root_address, -1) !=
      NULL
  );  // Success
}

/*!
 * \fn void test_merge()
 * \brief Launches the tests of the merge system call
 */
void test_merge()
{
  init_tests_only_ram();
  test_merge_two_blocks();

  init_tests_only_ram();
  test_merge_full_MPU_structure();

  init_tests_only_ram();
  test_merge_subblocks_child();

  init_tests_only_ram();
  test_merge_bad_arguments();
}

// TEST COLLECT SYSTEM CALL

/*!
 * \fn void test_collect_in_child()
 * \brief  Test collecting a child
 * Init: create and prepare a child
 * Test after collect:
 *     - the child has default values in PD (not prepared anymore);
 *     - the block collected is accessible again for the parent
 */
void test_collect_in_child()
{
  // Create and prepare a child
  init_test_with_create_prepare_child(true);

  // Check the block to collect is not accessible for the parent (since it's the child's kernel structure);
  assert(
      readMPUAccessibleFromMPUEntryAddr(block_prepare_child_MPU_root_address) ==
      false
  );

  // COLLECT
  assert(collect(child_partition_pd) != false);

  // Test that the child has no kernel structure anymore
  assert(
      readPDStructurePointer(child_partition_pd) ==
      NULL
  );
  assert(
      readPDNbFreeSlots(child_partition_pd) ==
      0
  );
  assert(
      readPDFirstFreeSlotPointer(child_partition_pd) ==
      NULL
  );
  assert(
      readPDNbPrepare(child_partition_pd) ==
      0
  );
  assert(
      readPDParent(child_partition_pd) ==
      getCurPartition()
  );

  // Test that the collected block is accessible again for the root partition
  assert(
      readMPUAccessibleFromMPUEntryAddr(block_prepare_child_MPU_root_address) ==
      true
  );
}

/*!
 * \fn void test_collect_in_current_partition()
 * \brief  Test collecting oneself
 * Init: create and prepare a child + share a child
 * + use the shared block to prepare the child again
 * Test after collect:
 *     - the child has the same values as before the prepare
 *     - the block collected is accessible again for the current partition
 */
void test_collect_in_current_partition()
{
  init_test_with_create_prepare_share_child(true);

  // switch to child partition
  updateCurPartition(child_partition_pd);

  // retain state of child PD
  paddr old_pointer_to_MPU_linked_list = readPDStructurePointer(getCurPartition());
  uint32_t old_nb_free_slots = readPDNbFreeSlots(getCurPartition());
  paddr old_first_free_slot = readPDFirstFreeSlotPointer(getCurPartition());
  uint32_t old_nb_prepare = readPDNbPrepare(getCurPartition());
  paddr old_parent = readPDParent(getCurPartition());

  // prepare itself (child partition);
  assert(
      prepare(getCurPartition(), 8, block_to_share_MPU_child_address) !=
      false
  );

  // Check number of prepare is 2 now
  assert(readPDNbPrepare(getCurPartition()) == 2);

  // Check that the block used to prepare is not accessible to the current partition
  assert(
      readMPUAccessibleFromMPUEntryAddr(block_to_share_MPU_child_address) ==
      false
  );

  // COLLECT
  assert(collect(getCurPartition()) != false);

  // Test that the PD state is back to initial values
  assert(
      readPDStructurePointer(getCurPartition()) ==
      old_pointer_to_MPU_linked_list
  );
  assert(
      readPDNbFreeSlots(getCurPartition()) ==
      old_nb_free_slots
  );
  assert(
      readPDFirstFreeSlotPointer(getCurPartition()) ==
      old_first_free_slot
  );
  assert(
      readPDNbPrepare(getCurPartition()) ==
      old_nb_prepare
  );
  assert(
      readPDParent(getCurPartition()) ==
      old_parent
  );

  // Test that the block used to prepare is accessible again to the current partition
  assert(
      readMPUAccessibleFromMPUEntryAddr(block_to_share_MPU_child_address) ==
      true
  );
}

/*!
 * \fn void test_collect_in_grandchild()
 * \brief  Test that a collect in a grandchild make the block accessible again to the ancestors
 * Init: create and prepare a child + create and prepare a grandchild + prepare the grandchild again with a shared
 * block
 * Test after collect:
 *     - the child and root partitions gain access again to the block used to the grandchild prepare
 */
void test_collect_in_grandchild()
{
  init_test_with_create_prepare_child_and_create_prepare_share_grandchild(true);

  // add initial block to child
  updateCurPartition(root);
  paddr initial_block_MPU_child_address = addMemoryBlock(child_partition_pd,
                                                        initial_block_root_address,
                                                        true, true, false);
  assert(initial_block_MPU_child_address != false);

  // add initial block to grandchild
  updateCurPartition(child_partition_pd);
  paddr initial_block_MPU_grandchild_address = addMemoryBlock(grandchild_partition_pd,
                                                              initial_block_MPU_child_address,
                                                              true, true, false);
  assert(initial_block_MPU_grandchild_address != false);

  // switch to grandchild and prepare a 2nd time
  updateCurPartition(grandchild_partition_pd);
  assert(prepare(getCurPartition(), 8, initial_block_MPU_grandchild_address) != false);

  // Test the block used to the 2nd grandchild prepare is NOT accessible in child and root partitions anymore
  assert(
      readMPUAccessibleFromMPUEntryAddr(initial_block_MPU_child_address) ==
      false
  );
  assert(
      readMPUAccessibleFromMPUEntryAddr(readPDStructurePointer(root)) ==
      false
  );

  // COLLECT
  assert(collect(getCurPartition()) != false);

  // Test the block used to the 2nd grandchild prepare is accessible in child and root partitions again
  assert(
      readMPUAccessibleFromMPUEntryAddr(initial_block_MPU_child_address) ==
      true
  );
  assert(
      readMPUAccessibleFromMPUEntryAddr(readPDStructurePointer(root)) ==
      true
  );
}

/*!
 * \fn void test_collect_with_several_structures()
 * \brief  Test collecting an empty structure in a list of structures
 * Init: create and prepare a child + prepare the child again + add a block to child (1st prepare empty/2nd prepare
 *   not empty);
 * Test after collect:
 *     - the 1st prepare empty structure (in 2nd position of the structure list) is properly collected
 */
void test_collect_with_several_structures()
{
  build_create_child_block_out_of_initial_block();
  build_prepare_child_block_out_of_initial_block();
  build_share_block_out_of_initial_block();
  init_test_with_create_prepare_child(false);

  // cut share block in three (2 cuts + original block);
  paddr block2_MPU_address = cutMemoryBlock(block_to_share_MPU_root_address, block_to_share_id + 2*KERNELSTRUCTURETOTALLENGTH(), -1);
  assert(block2_MPU_address != false);
  paddr block3_MPU_address = cutMemoryBlock(block_to_share_MPU_root_address, block_to_share_id + KERNELSTRUCTURETOTALLENGTH(), -1);
  assert(block3_MPU_address != false);

  // prepare the child again (2nd prepare) without adding a block -> 1st prepare is empty and can be collected
  assert(prepare(child_partition_pd, -1, block2_MPU_address) != false);

  // add another block to child (2nd prepare not empty anymore);
  assert(addMemoryBlock(child_partition_pd,
                        block3_MPU_address,
                        true, true, false) != false);

  // check nb of prepare is 2
  assert(readPDNbPrepare(child_partition_pd) == 2);
  dump_partition(child_partition_pd);

  // COLLECT
  assert(collect(child_partition_pd) != false);

  // check nb of prepare is 1
  assert(readPDNbPrepare(child_partition_pd) == 1);
}

/*!
 * \fn void test_collect_fails_with_no_empty_structure()
 * \brief  Test collecting a partition that has no empty structures fails
 * Test :
 *     - collecting the root partition fails (never possible since never empty);
 */
void test_collect_fails_with_no_empty_structure()
{
  updateCurPartition(root);
  // Fails because root partition is never empty
  assert(collect(getCurPartition()) == false);
}

/*!
 * \fn void test_collect_fails_trying_to_collect_a_structure_that_the_current_partition_did_not_prepare()
 * \brief  Test collecting a partition that with no empty structure prepared by its own fails
 * Init :
 *     - create + prepare + share child
 *     - prepare the child (2nd prepare empty so possible to collect by the parent only);
 * Test :
 *     - the child fails to collect itself since it didn't prepare itself (it was the parent);
 */
void test_collect_fails_trying_to_collect_a_structure_that_the_current_partition_did_not_prepare()
{
  // cut initial block several times
  child_partition_pd = initial_block_start + 20*KERNELSTRUCTURETOTALLENGTH();
  block_prepare_child_id = initial_block_start + 15*KERNELSTRUCTURETOTALLENGTH();
  block_to_share_id = initial_block_start + 10*KERNELSTRUCTURETOTALLENGTH();
  paddr block_prepare_child_2_id = initial_block_start + 5*KERNELSTRUCTURETOTALLENGTH();

  paddr child_partition_pd_address = cutMemoryBlock(initial_block_root_address, child_partition_pd, -1);
  assert(child_partition_pd_address != false);
  paddr block_prepare_child_id_address = cutMemoryBlock(initial_block_root_address, block_prepare_child_id, -1);
  assert(block_prepare_child_id_address != false);
  paddr block_to_share_id_address = cutMemoryBlock(initial_block_root_address, block_to_share_id, -1);
  assert(block_to_share_id_address != false);
  paddr block_prepare_child_2_id_address = cutMemoryBlock(initial_block_root_address, block_prepare_child_2_id, -1);
  assert(block_prepare_child_2_id_address != false);

  // Create + prepare + share child -> 1st prepare not empty
  init_test_with_create_prepare_share_child(false);

  // Prepare the child
  assert(prepare(child_partition_pd, 8, block_prepare_child_2_id_address) != false);

  // switch to child
  updateCurPartition(child_partition_pd);

  // COLLECT ITSELF fails because has not prepared itself (the parent prepared the child);
  assert(collect(getCurPartition()) == false);
}

/*!
 * \fn void test_collect_bad_arguments()
 * \brief  Tests that providing bad arguments fail
 * Bad arguments:
 * - idPD: the provided PD is not the current partition or a child
 * - idPD = current partition and nbprepare = 1
 */
void test_collect_bad_arguments()
{
  init_test_with_create_prepare_child(true);

  // Fails because initial block is not a child
  assert(collect(block_prepare_child_id) == false);

  // Fails because not possible to SELF collect the only structure prepare left (originally given by the parent);
  updateCurPartition(child_partition_pd);
  assert(collect(getCurPartition()) == false);
}

/*!
 * \fn void test_collect()
 * \brief Launches the tests of the collect system call
 */
void test_collect()
{
  init_tests_only_ram();
  test_collect_in_child();

  init_tests_only_ram();
  test_collect_in_current_partition();

  init_tests_only_ram();
  test_collect_in_grandchild();

  init_tests_only_ram();
  test_collect_with_several_structures();

  init_tests_only_ram();
  test_collect_fails_with_no_empty_structure();

  init_tests_only_ram();
  test_collect_fails_trying_to_collect_a_structure_that_the_current_partition_did_not_prepare();

  init_tests_only_ram();
  test_collect_bad_arguments();
}

// TEST MPU MAP SYSTEM CALL

/*!
 * \fn void test_mpu_physical_MemFault_without_Pip()
 * \brief  Test that the physical MPU correctly faults with PRIVDEFENA
 *         When hitting MemFault, the canary value changes -> canary region must be in MPU
 *          - Test NO MemFault whith no defined region in MPU (PRIVDEFENA set)
 *          - Test MemFault when writing in RO region
 *          - Test MemFault when writing in RO region with other defined regions around
 *          - Test MemFault when writing in RO region from userland
 */
void __attribute__((optimize(0))) test_mpu_physical_MemFault_without_Pip()
{
    enablePrivilegedMode();
  // Set MEMFAULTENA to enable MemFault Handler
  volatile uint32_t *shcsr = (void *)0xE000ED24;
  *shcsr |= (0x1 << 16);

  volatile uint32_t *mpu_ctrl = (void *)0xE000ED94;
  volatile uint32_t *mpu_rbar = (void *)0xE000ED9C;
  volatile uint32_t *mpu_rasr = (void *)0xE000EDA0;
  volatile uint32_t *mpu_rnr = (void *)0xE000ED98;

  volatile uint32_t* canary = (uint32_t*) 0x20001000; // canary value to be changed in the MemManageFault handler
  *canary = 0x0;

  // MPU init : Clear all regions
  __DMB();
  // Disable MPU
  *mpu_ctrl = 0x0;

  for (int i = 0; i < 8 ; i++){
    *mpu_rnr  = i;
    *mpu_rbar = 0;
    *mpu_rasr = 0;
  }
  __ISB();
  __DSB();

  printf("MPU config\n");

  // Define Flash region and enable MPU with PRIVDEFENA
  // REGION 0 : Flash
  *mpu_rnr = 0;
  *mpu_rbar = 0x0;
  // MPU_RASR settings for flash write protection:
  //  28 : XNbit = 0 -> Execute OK
  //  24 : AP=0b110 -> Read Only
  //  16 : TEXSCB=0b000010
  //  1 : SIZE=19 because we want to cover 1MB
  //  0 : ENABLE=1
  *mpu_rasr = (0 << 28) | (0b110 << 24) | (0b000010 << 16) | (19 << 1) | 0x1; //PRIV ROX/USER ROX

  *mpu_ctrl = 0x5; // Enable MPU with PRIVDEFENA
  __ISB();
  __DSB();

  // TESTS

  // TEST no MemFault because still PRIV and only flash is RO
  volatile uint32_t *bad_pointer = (void*)0x20000050;
  *bad_pointer = 0xdeadbeef; //-> No MemFault
  assert(*canary == 0x0);

  // TEST MemFault when adding a protected PRIV RO/USER RO region
  // Region 1 : RAM RO : 0x20000040-0x20000080
  //  24 : AP=0b110 -> Read Only
  //  1 : SIZE=5 because we want to cover 64 bytes
  //  0 : ENABLE=1
  *mpu_rnr = 1;
  *mpu_rbar = 0x20000040;
  *mpu_rasr = (1 << 28) | (0b110 << 24) | (0b001000 << 16) | (5 << 1) | 0x1; //PRIV RO/USER RO
  // Check MemFault
  bad_pointer = (void*)0x20000050;
  *bad_pointer = 0xdeadbeef; //-> MemFault, because protected RO even for PRIV
  assert(*canary == 0xdeadbeef);

  // TEST still MemFault when adding a RW region after (same address should still fault)
  *canary = 0x0;
  // Region 2 : RAM RW : 0x20001000-0x20002000
  //  24 : AP=0b011 -> R/W
  //  1 : SIZE=11 because we want to cover 0x1000 bytes
  //  0 : ENABLE=1
  *mpu_rnr = 2;
  *mpu_rbar = 0x20001000;
  *mpu_rasr = (1 << 28) | (0b011 << 24) | (0b001000 << 16) | (11 << 1) | 0x1; //PRIV RW/USER RW
  // Check MemFault
  bad_pointer = (void*)0x20000050;
  *bad_pointer = 0xdeadbeef; //-> MemFault, because protected RO even for PRIV
  assert(*canary == 0xdeadbeef);

  // TEST MemFault for userland
  *canary = 0x0;
  __set_PSP(0x20002000); // place stack in region 2 (otherwise stack outside of defined regions faults)
  __set_CONTROL(__get_CONTROL() |
                      CONTROL_SPSEL_Msk);// | // use psp
  __set_CONTROL(__get_CONTROL() |
                 CONTROL_nPRIV_Msk ); // switch to unprivileged Thread Mode
  // Check MemFault
  bad_pointer = (void*)0x20000050;
  *bad_pointer = 0xdeadbeef; //-> MemFault, because protected RO for user
  assert(*canary == 0xdeadbeef);
  enablePrivilegedMode();
}


/*!
 * \fn void test_mpu_physical_MemFault_with_Pip()
 * \brief   Test that the physical MPU correctly faults with Pip system calls
 *          Init:
 *            - cut the RO RAM block in 3
 *                - ram1 = system variables
 *                - ram1_2 = 64kB region
 *                - ram1_3 = remaining
 *            - cut the RW RAM block in 3
 *                - ram2 = function variables like the bad_pointer lies here
 *                - ram2_2 = unaligned block -> partially configured if mapped
 *                - ram2_3 = stack -> aligned, should always be mapped completely
 *                          and never touched otherwise MSTKERR or MUNSTKERR
 *            - Map the flash, the 64-kB RO ram block, the region containing function
                variables and the RW stack block
 *            - Switch to userland
 *          Test:
 *            - No MemFault for write in RW stack block
 *            - MemFault for write in RO region
 *            - MemFault for write in accessbile region not defined in MPU
 *            - map the unaligned RW region:
 *                - No MemFault when accessing the start of the block(partially configured)
 *                - MemFault catched when accessing the end of the block (block reconfigured
                    to match the legitimate faulted address)
                  - MemFault catched when accessing the start of the block again (because reconfigured
                    previously, and reconfigured now)
 */
void __attribute__((optimize(0))) test_mpu_physical_MemFault_with_Pip()
{
  dump_mpu();

  volatile uint32_t* canary = 0x20001000; // canary value to be changed in the MemManageFault handler
  *canary = 0x0;

  // Cut the first Read-Only RAM block in 3 : 0x2000000-0x20000040-0x20000080-0x20001000
  uint32_t* block_ram1_2_addr = (uint32_t*) 0x20000040;//&sram + 0x40
  paddr block_ram1_2 = cutMemoryBlock(block_ram1, block_ram1_2_addr, -1);
  assert(block_ram1_2 != NULL);
  paddr block_ram1_3 = cutMemoryBlock(block_ram1_2, 0x20000080, -1);
  assert(block_ram1_3 != NULL);

  // cut the second RW RAM block in 3: 0x20001000-0x20005000-0x20008000-0x20010000
  uint32_t* block_ram2_2_addr = (uint32_t*) 0x20005000;
  paddr block_ram2_2 = cutMemoryBlock(block_ram2, block_ram2_2_addr, -1);
  assert(block_ram2_2 != NULL);
  uint32_t* block_ram2_3_addr = (uint32_t*) 0x20008000;
  paddr block_ram2_3 = cutMemoryBlock(block_ram2_2, block_ram2_3_addr, -1);
  assert(block_ram2_3 != NULL);

  // Map 34blocks -> flash, 4 ram blocks
  assert(mapMPU(root, block_flash, 0) == true); // Flash
  assert(mapMPU(root, block_ram1_2, 1)== true); // RO region
  assert(mapMPU(root, block_ram2, 2)== true); // RW region containing the bad_pointer address
  assert(mapMPU(root, block_ram2_3, 3)== true); // Stack: never touch, should always be enabled in MPU
  dump_mpu();

  // Switch to userland, set PSP at end of RW RAM block
  __set_PSP(&user_stack_top);
  __set_CONTROL(__get_CONTROL() |
                CONTROL_SPSEL_Msk);// use psp

   // TEST NO MemFault for userland for a RW block defined in MPU
  *canary = 0x0; // defaults canary
  volatile uint32_t *bad_pointer = (void*)0x20008010;
  disablePrivilegedMode();
  *bad_pointer = 0xdeadbeef; //-> No MemFault, because in stack RW
  enablePrivilegedMode();
  assert(*canary == 0x0);


  // TEST MemFault for write in a protected RO region defined in MPU
  *canary = 0x0;
  disablePrivilegedMode();
  bad_pointer = (void*)0x20000050;
  *bad_pointer = 0xdeadbeef; //-> MemFault, because protected RO
  enablePrivilegedMode();
  assert(*canary == 0xdeadbeef);

  // TEST MemFault for write in a region not in MPU
  *canary = 0x0;
  disablePrivilegedMode();
  bad_pointer = (void*)0x20005010;
  *bad_pointer = 0xdeadbeef; //-> MemFault, because RAM RW block not in MPU
  enablePrivilegedMode();
  assert(*canary == 0xdeadbeef);

  // TEST NO MemFault for partially configured region
  *canary = 0x0;
  assert(mapMPU(root, block_ram2_2, 4) == true); // Map RW region partially configured (not aligned to cover whole region)
  dump_mpu();
  dump_partition(root);
  disablePrivilegedMode();

  bad_pointer = (void*)0x20005010;//TODO detect imprecise 0x25
  *bad_pointer = 0xdeadbeef; //-> NO MemFault anymore because MPU region should be configured
  enablePrivilegedMode();
  assert(*canary == 0x0);
  disablePrivilegedMode();

  bad_pointer = (void*)0x20007800;
  *bad_pointer = 0xdeadbeef; //-> MemFault caught because MPU region REconfigure itself
  enablePrivilegedMode();
  assert(*canary == 0x0); // MemFault does not hit the canary
  dump_mpu();
  disablePrivilegedMode();

  bad_pointer = (void*)0x20005010;
  *bad_pointer = 0xdeadbeef; //-> MemFault caught this time because MPU region REconfigure itself
  enablePrivilegedMode();
  assert(*canary == 0x0); // MemFault does not hit the canary
  dump_mpu();
}

/*!
 * \fn void test_3_mapMPU()
 * \brief  Test that mapMPU correctly configures 3 blocks in the physical MPU settings
 */
void test_3_mapMPU()
{
  // all physical MPU regions not filled at first, default values
  for (int i=0 ; i < MPU_REGIONS_NB ; i++)
  {
    assert(readPhysicalMPUStartAddr(i) == 0);
    assert(readPhysicalMPUSizeBits(i) == 0);
    assert(readPhysicalMPUSizeBytes(i) == 0);
    assert(readPhysicalMPUAP(i) == 0);
    assert(readPhysicalMPUXN(i) == 0);
    assert(readPhysicalMPURegionEnable(i) == 0);
  }

  // Map 3 blocks

  assert(mapMPU(root, block_flash, 0) == true);
  assert(mapMPU(root, block_ram1, 1)== true);
  assert(mapMPU(root, block_ram2, 2)== true);

  dump_partition(root);

  dump_mpu();

  // Check MPU Settings: flash block RX, ram block1 RO, ram block2 RW not X
  assert(readPhysicalMPUStartAddr(0) == readMPUStartFromMPUEntryAddr(block_flash));
  assert(readPhysicalMPUEndAddr(0) <= readMPUEndFromMPUEntryAddr(block_flash));
  assert(readPhysicalMPUAP(0) == 2);
  assert(!readPhysicalMPUXN(0) == readMPUXFromMPUEntryAddr(block_flash));
  assert(readPhysicalMPURegionEnable(0) == 1);

  assert(readPhysicalMPUStartAddr(1) == readMPUStartFromMPUEntryAddr(block_ram1));
  assert(readPhysicalMPUEndAddr(1) <= readMPUEndFromMPUEntryAddr(block_ram1));
  assert(readPhysicalMPUAP(1) == 2);
  assert(!readPhysicalMPUXN(1) == readMPUXFromMPUEntryAddr(block_ram1));
  assert(readPhysicalMPURegionEnable(1) == 1);

  assert(readPhysicalMPUStartAddr(2) == readMPUStartFromMPUEntryAddr(block_ram2));
  assert(readPhysicalMPUEndAddr(2) <= readMPUEndFromMPUEntryAddr(block_ram2));
  assert(readPhysicalMPUAP(2) == 3);
  assert(!readPhysicalMPUXN(2) == readMPUXFromMPUEntryAddr(block_ram2));
  assert(readPhysicalMPURegionEnable(2) == 1);

  // remaining MPU regions still not filled, default values
  for (int i=3 ; i < MPU_REGIONS_NB ; i++)
  {
    assert(readPhysicalMPUStartAddr(i) == 0);
    assert(readPhysicalMPUSizeBits(i) == 0);
    assert(readPhysicalMPUSizeBytes(i) == 0);
    assert(readPhysicalMPUAP(i) == 0);
    assert(readPhysicalMPUXN(i) == 0);
    assert(readPhysicalMPURegionEnable(i) == 0);
  }
}

/*!
 * \fn void test_mpu_in_sync_with_system_calls()
 * \brief  Test that the physical MPU mirrors the system calls changes
          createPartition: in current partition and ancestors -> the PD block in the MPU is removed
          prepare: in current partition and ancestors -> the prepare block in the MPU is removed
          add: block stays in the physical MPU
          cut: - in current partition -> the new subblock is placed at the correct position in the MPU
                - in the parent partition and ancestors -> the block is removed from the MPU
 */
void test_mpu_in_sync_with_system_calls()
{
  // build blocks and map in MPu
  build_create_child_block_out_of_initial_block();
  build_prepare_child_block_out_of_initial_block();
  build_share_block_out_of_initial_block();

  assert(mapMPU(root, initial_block_root_address, 0) == true);
  assert(mapMPU(root, block_create_child_MPU_root_address, 1) == true);
  assert(mapMPU(root, block_prepare_child_MPU_root_address, 2) == true);
  assert(mapMPU(root, block_to_share_MPU_root_address, 3) == true);

  // Check blocks are in MPU
  PDTable_t* currPart = (PDTable_t*) getCurPartition();
  assert(currPart->blocks[0] == initial_block_root_address);
  assert(currPart->blocks[1] == block_create_child_MPU_root_address);
  assert(currPart->blocks[2] == block_prepare_child_MPU_root_address);
  assert(currPart->blocks[3] == block_to_share_MPU_root_address);
  assert(currPart->blocks[4] == NULL);
  assert(currPart->blocks[5] == NULL);
  assert(currPart->blocks[6] == NULL);
  assert(currPart->blocks[7] == NULL);

  // CREATEPARTITION: block should disappear from physical mpu
  assert(createPartition(block_create_child_MPU_root_address) == 1);
  assert(currPart->blocks[1] == NULL);

  // PREPARE: block should disappear from physical mpu
  assert(prepare(child_partition_pd, 8, block_prepare_child_MPU_root_address) == 1);
  assert(currPart->blocks[2] == NULL);

  // ADD
  // in root: block still in physical MPU
  paddr shared_block_MPU_address = addMemoryBlock(child_partition_pd, block_to_share_MPU_root_address, 1, 0, 0);
  assert(shared_block_MPU_address != NULL);
  assert(currPart->blocks[3] == block_to_share_MPU_root_address);

  // in child : set the block in the MPU, shoud not be writable
  assert(mapMPU(child_partition_pd, shared_block_MPU_address, 0) == true);
  updateCurPartition(child_partition_pd);
  currPart = (PDTable_t*) getCurPartition();
  assert(currPart->blocks[0] == shared_block_MPU_address);
  assert(readPhysicalMPUAP(0) == 2);
  dump_mpu();


  // CUT in root: subblock placed correctly in MPU
  updateCurPartition(root);
  currPart = (PDTable_t*) getCurPartition();
  initial_block_start + KERNELSTRUCTURETOTALLENGTH() * 25;
  paddr subblock1_MPU_address = cutMemoryBlock(initial_block_root_address,
                                              initial_block_start + KERNELSTRUCTURETOTALLENGTH() * 5,
                                              6);
  assert(subblock1_MPU_address != NULL);
  assert(currPart->blocks[0] == initial_block_root_address);
  assert(currPart->blocks[6] == subblock1_MPU_address);

  // CUT in child: block cut in child MPU + subbblock in child not in MPU
  // + block removed from the parent's physical MPU
  assert(currPart->blocks[0] == initial_block_root_address);
  assert(currPart->blocks[1] == NULL);
  assert(currPart->blocks[2] == NULL);
  assert(currPart->blocks[3] == block_to_share_MPU_root_address);
  assert(currPart->blocks[4] == NULL);
  assert(currPart->blocks[5] == NULL);
  assert(currPart->blocks[6] == subblock1_MPU_address);
  assert(currPart->blocks[7] == NULL);
  updateCurPartition(child_partition_pd);
  currPart = (PDTable_t*) getCurPartition();
  assert(currPart->blocks[0] == shared_block_MPU_address);
  assert(currPart->blocks[1] == NULL);
  assert(currPart->blocks[2] == NULL);
  assert(currPart->blocks[3] == NULL);
  assert(currPart->blocks[4] == NULL);
  assert(currPart->blocks[5] == NULL);
  assert(currPart->blocks[6] == NULL);
  assert(currPart->blocks[7] == NULL);

  // block cut still in MPU, subblock not
  assert(cutMemoryBlock(shared_block_MPU_address,
                        block_to_share_id + KERNELSTRUCTURETOTALLENGTH(),
                        -1) != NULL);
  assert(currPart->blocks[0] == shared_block_MPU_address);
  assert(currPart->blocks[1] == NULL);
  assert(currPart->blocks[2] == NULL);
  assert(currPart->blocks[3] == NULL);
  assert(currPart->blocks[4] == NULL);
  assert(currPart->blocks[5] == NULL);
  assert(currPart->blocks[6] == NULL);
  assert(currPart->blocks[7] == NULL);

  // in root: shared block removed from physical MPU, remains the root's subblocks
  updateCurPartition(root);
  currPart = (PDTable_t*) getCurPartition();
  assert(currPart->blocks[0] == initial_block_root_address);
  assert(currPart->blocks[1] == NULL);
  assert(currPart->blocks[2] == NULL);
  assert(currPart->blocks[3] == NULL);
  assert(currPart->blocks[4] == NULL);
  assert(currPart->blocks[5] == NULL);
  assert(currPart->blocks[6] == subblock1_MPU_address);
  assert(currPart->blocks[7] == NULL);

}

/*!
 * \fn void test_mpu_remove_blocks_from_physical_mpu()
 * \brief  Tests that removing blocks from the MPU list
*          removes them from the physical MPU
 *
 * Init:
 * - build blocks to create a child
 * Tests after MPU map:
 * - all mapped blocks are configured in the physical MPU
 * - after removal of the blocks
 *    - all mapped blocks are not configured in the MPU anymore
 */
void test_mpu_remove_blocks_from_physical_mpu()
{
  // build blocks
  build_create_child_block_out_of_initial_block();
  build_prepare_child_block_out_of_initial_block();
  build_share_block_out_of_initial_block();

  assert(mapMPU(root, initial_block_root_address, 0) == true);
  assert(mapMPU(root, block_create_child_MPU_root_address, 1) == true);
  assert(mapMPU(root, block_prepare_child_MPU_root_address, 2) == true);
  assert(mapMPU(root, block_to_share_MPU_root_address, 3) == true);

  // Check blocks are in MPU
  PDTable_t* currPart = (PDTable_t*) getCurPartition();
  assert(currPart->blocks[0] == initial_block_root_address);
  assert(currPart->blocks[1] == block_create_child_MPU_root_address);
  assert(currPart->blocks[2] == block_prepare_child_MPU_root_address);
  assert(currPart->blocks[3] == block_to_share_MPU_root_address);
  assert(currPart->blocks[4] == NULL);
  assert(currPart->blocks[5] == NULL);
  assert(currPart->blocks[6] == NULL);
  assert(currPart->blocks[7] == NULL);

  // REMOVE blocks from physical MPU
  assert(mapMPU(root, NULL, 0) == true);
	assert(mapMPU(root, NULL, 1) == true);
	assert(mapMPU(root, NULL, 2) == true);
	assert(mapMPU(root, NULL, 3) == true);

  // Check blocks are NOT in MPU anymore
  assert(currPart->blocks[0] == NULL);
  assert(currPart->blocks[1] == NULL);
  assert(currPart->blocks[2] == NULL);
  assert(currPart->blocks[3] == NULL);
  assert(currPart->blocks[4] == NULL);
  assert(currPart->blocks[5] == NULL);
  assert(currPart->blocks[6] == NULL);
  assert(currPart->blocks[7] == NULL);
}

/*!
 * \fn void test_mapMPU_bad_arguments()
 * \brief  Tests that providing bad arguments fail
 * Bad arguments:
 * - idPD: the provided PD is not the current partition or a child
 * - MPUAddressBlockToEnable: the provided block is not owned by <idPD>
 * - MPURegionNb: the provided number is outside the MPU region number range
 */
void test_mapMPU_in_child()
{
  init_test_with_create_prepare_share_child(true);

  // map shared block in child MPU
  assert(mapMPU(child_partition_pd, block_to_share_MPU_child_address, 0) == true);

  // Check block is mapped in child's MPU
  updateCurPartition(child_partition_pd);
  PDTable_t* currPart = (PDTable_t*) getCurPartition();
  assert(currPart->blocks[0] == block_to_share_MPU_child_address);
  assert(currPart->blocks[1] == NULL);
  assert(currPart->blocks[2] == NULL);
  assert(currPart->blocks[3] == NULL);
  assert(currPart->blocks[4] == NULL);
  assert(currPart->blocks[5] == NULL);
  assert(currPart->blocks[6] == NULL);
  assert(currPart->blocks[7] == NULL);
}


/*!
 * \fn void test_mapMPU_bad_arguments()
 * \brief  Tests that providing bad arguments fail
 * Bad arguments:
 * - idPD: the provided PD is not the current partition or a child
 * - MPUAddressBlockToEnable: the provided block is not owned by <idPD>
 * - MPURegionNb: the provided number is outside the MPU region number range
 */
void test_mapMPU_bad_arguments()
{
  // build blocks and map in MPU
  build_create_child_block_out_of_initial_block();
  build_prepare_child_block_out_of_initial_block();
  build_share_block_out_of_initial_block();

   // Check fails when mapping in non existing child
  assert(mapMPU(0x20000500, initial_block_root_address, 0) == false);

  // Check fails when mapping a non existing block
  assert(mapMPU(root, 0x10000080, 0) == false);

  // Check fails when mapping in incorrect MPU region number
  assert(mapMPU(root, initial_block_root_address, -1) == false);
  assert(mapMPU(root, initial_block_root_address, 8) == false);
}


/*!
 * \fn void test_mapMPU()
 * \brief Launches the tests of the mapMPU system call
 */
void test_mapMPU()
{
  init_tests_only_ram();
  test_mpu_physical_MemFault_without_Pip();

  init_tests_flash_ram_w_stack();
  test_mpu_physical_MemFault_with_Pip();

  init_tests_flash_ram_w_stack();
  test_3_mapMPU();

  init_tests_only_ram();
  test_mpu_remove_blocks_from_physical_mpu();

  init_tests_only_ram();
  test_mpu_in_sync_with_system_calls();

  init_tests_only_ram();
  test_mapMPU_in_child();

  init_tests_only_ram();
  test_mapMPU_bad_arguments();
}


// TEST MPU READ SYSTEM CALL

/*!
 * \fn void test_readMPU_curr_part()
 * \brief Test read in the MPU of the current partition
 *        Init:
 *          - build blocks in current partition
 *          - map the blocks in the current partition
 *        Test: read MPU in current partition
 */
void test_readMPU_curr_part()
{
  PDTable_t* currPart = (PDTable_t*) getCurPartition();

  // Check blocks are NOT in MPU
  assert(currPart->blocks[0] == initial_block_root_address);
  assert(currPart->blocks[1] == NULL);
  assert(currPart->blocks[2] == NULL);
  assert(currPart->blocks[3] == NULL);
  assert(currPart->blocks[4] == NULL);
  assert(currPart->blocks[5] == NULL);
  assert(currPart->blocks[6] == NULL);
  assert(currPart->blocks[7] == NULL);

  // Test mpu read NULL as well
  assert(readMPU(root, 0) == initial_block_root_address);
  assert(readMPU(root, 1) == NULL);
  assert(readMPU(root, 2) == NULL);
  assert(readMPU(root, 3) == NULL);
  assert(readMPU(root, 4) == NULL);
  assert(readMPU(root, 5) == NULL);
  assert(readMPU(root, 6) == NULL);
  assert(readMPU(root, 7) == NULL);

  // build blocks and map in MPU
  build_create_child_block_out_of_initial_block();
  build_prepare_child_block_out_of_initial_block();
  build_share_block_out_of_initial_block();

  assert(mapMPU(root, initial_block_root_address, 0) == true);
  assert(mapMPU(root, block_create_child_MPU_root_address, 1) == true);
  assert(mapMPU(root, block_prepare_child_MPU_root_address, 2) == true);
  assert(mapMPU(root, block_to_share_MPU_root_address, 3) == true);

  // Check blocks are in MPU
  assert(currPart->blocks[0] == initial_block_root_address);
  assert(currPart->blocks[1] == block_create_child_MPU_root_address);
  assert(currPart->blocks[2] == block_prepare_child_MPU_root_address);
  assert(currPart->blocks[3] == block_to_share_MPU_root_address);
  assert(currPart->blocks[4] == NULL);
  assert(currPart->blocks[5] == NULL);
  assert(currPart->blocks[6] == NULL);
  assert(currPart->blocks[7] == NULL);

  // Check mpu read the same values
  assert(readMPU(root, 0) == initial_block_root_address);
  assert(readMPU(root, 1) == block_create_child_MPU_root_address);
  assert(readMPU(root, 2) == block_prepare_child_MPU_root_address);
  assert(readMPU(root, 3) == block_to_share_MPU_root_address);
  assert(readMPU(root, 4) == NULL);
  assert(readMPU(root, 5) == NULL);
  assert(readMPU(root, 6) == NULL);
  assert(readMPU(root, 7) == NULL);
}

/*!
 * \fn void test_readMPU_child_part()
 * \brief Test read in the MPU of a child of the current partition
 *        Init:
 *          - create child and share block
 *          - map the shared block in the child
 *        Test: read MPU in child
 */
void test_readMPU_child_part()
{
  init_test_with_create_prepare_share_child(true);

  // map shared block in child MPU
  assert(mapMPU(child_partition_pd, block_to_share_MPU_child_address, 0) == true);

  // Test read the shared block in the child's MPU
  assert(readMPU(child_partition_pd, 0) == block_to_share_MPU_child_address);
  assert(readMPU(child_partition_pd, 1) == NULL);
  assert(readMPU(child_partition_pd, 2) == NULL);
  assert(readMPU(child_partition_pd, 3) == NULL);
  assert(readMPU(child_partition_pd, 4) == NULL);
  assert(readMPU(child_partition_pd, 5) == NULL);
  assert(readMPU(child_partition_pd, 6) == NULL);
  assert(readMPU(child_partition_pd, 7) == NULL);
}

/*!
 * \fn void test_readMPU_bad_arguments()
 * \brief  Tests that providing bad arguments fail
 * Bad arguments:
 * - idPD: the provided PD is not the current partition or a child
 * - MPURegionNb: the provided number is outside the MPU region number range
 */
void test_readMPU_bad_arguments()
{
  // build blocks and map in MPU
  build_create_child_block_out_of_initial_block();
  build_prepare_child_block_out_of_initial_block();
  build_share_block_out_of_initial_block();

  assert(mapMPU(root, initial_block_root_address, 0) == true);
  assert(mapMPU(root, block_create_child_MPU_root_address, 1) == true);
  assert(mapMPU(root, block_prepare_child_MPU_root_address, 2) == true);
  assert(mapMPU(root, block_to_share_MPU_root_address, 3) == true);

  // Check fails when reading in non existing child
  assert(readMPU(0x20000500, 3) == NULL);

  // Check fails when reading from incorrect MPU region
  assert(readMPU(root, -1) == NULL);
  assert(readMPU(root, 8) == NULL);
}

/*!
 * \fn void test_readMPU()
 * \brief Launches the tests of the readMPU system call
 */
void test_readMPU()
{
  init_tests_only_ram();
  test_readMPU_curr_part();

  init_tests_only_ram();
  test_readMPU_child_part();

  init_tests_only_ram();
  test_readMPU_bad_arguments();
}

// FINDBLOCK SYSTEM CALL
/*!
 * \fn void test_find_initial_block()
 * \brief Test that the initial block is found
 */
void test_find_initial_block()
{
  dump_partition(root);
  blockOrError b = findBlock(root, initial_block_start);
  assert(b.error != -1);
  printf("Block found: addr=%x, s=%x, e=%x, RWX=%d%d%d, A=%d\n", b.blockAttr.mpuentryaddr,
                                                    b.blockAttr.mpublock, // displays start and end
                                                    b.blockAttr.read,
                                                    b.blockAttr.write,
                                                    b.blockAttr.exec,
                                                    b.blockAttr.accessible);
  assert(b.blockAttr.mpuentryaddr == initial_block_root_address);
  assert(b.blockAttr.mpublock.startAddr == readMPUStartFromMPUEntryAddr(initial_block_root_address));
  assert(b.blockAttr.mpublock.endAddr == readMPUEndFromMPUEntryAddr(initial_block_root_address));
  assert(b.blockAttr.read == readMPURFromMPUEntryAddr(initial_block_root_address));
  assert(b.blockAttr.write == readMPUWFromMPUEntryAddr(initial_block_root_address));
  assert(b.blockAttr.exec == readMPUXFromMPUEntryAddr(initial_block_root_address));
  assert(b.blockAttr.accessible == readMPUAccessibleFromMPUEntryAddr(initial_block_root_address));
}

/*!
 * \fn void test_find_initial_block_in_max_prepared()
 * \brief Test that the initial block is found in partition that has been prepared several times
 *        Init: prepare the root partition a maximum of times
 *        Test: check the initial block is found (test stack does not overflow)
 */
void test_find_initial_block_in_max_prepared()
{
  // Init
  paddr initial_block = initial_block_start;

  // reach max prepare
  for(int i = 30; i > 0; i=i-2)
  {
    // cut the initial block
    paddr blockaddr = cutMemoryBlock(initial_block_root_address,
                                  initial_block_start + i * KERNELSTRUCTURETOTALLENGTH(),
                                  -1);
    assert(blockaddr != false);
    int isPrepared = prepare(getCurPartition(), -1, blockaddr);
    if(!isPrepared) break;
  }
  blockOrError b = findBlock(root, initial_block_start);
  assert(b.error != -1);
  assert(b.blockAttr.mpuentryaddr == initial_block_root_address);
  assert(b.blockAttr.mpublock.startAddr == readMPUStartFromMPUEntryAddr(initial_block_root_address));
  assert(b.blockAttr.mpublock.endAddr == readMPUEndFromMPUEntryAddr(initial_block_root_address));
  assert(b.blockAttr.read == readMPURFromMPUEntryAddr(initial_block_root_address));
  assert(b.blockAttr.write == readMPUWFromMPUEntryAddr(initial_block_root_address));
  assert(b.blockAttr.exec == readMPUXFromMPUEntryAddr(initial_block_root_address));
  assert(b.blockAttr.accessible == readMPUAccessibleFromMPUEntryAddr(initial_block_root_address));

}

/*!
 * \fn void test_find_bad_arguments()
 * \brief  Tests that providing bad arguments fail
 * Bad arguments:
 * - idPD: the provided PD is not the current partition or a child
 * - addrInBlock: the provided address is not part of any block
 */
void test_find_bad_arguments()
{
  // Check fails with non existing child
  blockOrError b = findBlock(0x10000000, initial_block_start);
  printf("Block NOT found: b.null=%d, b.blockAttr=%d\n", b.error, b.blockAttr);
  assert(b.error == -1);

  // Check fails with non existing block
  blockOrError b2 = findBlock(root, 0x0);
  assert(b2.error == -1);
  printf("Block NOT found: b2.null=%d, b2.blockAttr=%d\n", b2.error, b2.blockAttr);
}

/*!
 * \fn void test_findBlock()
 * \brief Launches the tests of the findBlock system call
 */
void test_find()
{
  init_tests_only_ram();
  test_find_initial_block();

  init_tests_only_ram();
  test_find_initial_block_in_max_prepared();

  init_tests_only_ram();
  test_find_bad_arguments();
}

/**
 * Unit tests main entry point.
 * If UART_DEBUG, sends printf messages over UART
 * If -DTRACE -DOS_USE_TRACE_SEMIHOSTING_DEBUG flags are set, send printf messages on the semihosting debug channel
 */
int main_test (int argc, char* argv[])
{
  mal_init(); // initializes the global vars
    if (KERNELSTRUCTUREENTRIESNB != 8)
  {
    printf("KERNELSTRUCTUREENTRIESNB %d must be 8 for the tests, test abort.\r\n", KERNELSTRUCTUREENTRIESNB);
    while(1);
  }

  initial_block_start = (void*) &user_mem_start + PDSTRUCTURETOTALLENGTH() + KERNELSTRUCTURETOTALLENGTH(); // size in bytes
  initial_block_end = &user_mem_end - 1;

  // Test initial root partition definition
  test_initial_root();
  // Test cut system call
  test_cut();
  printf("main_test: CUT OK\r\n");
  // Test create system call
  test_create();
  printf("main_test: CREATE OK\r\n");
  // Test prepare system call
  test_prepare();
  printf("main_test: PREPARE OK\r\n");
  // Test add system call
  test_add();
  printf("main_test: ADD OK\r\n");
  // Test remove system call
  test_remove();
  printf("main_test: REMOVE OK\r\n");
  // Test delete system call
  test_delete();
  printf("main_test: DELETE OK\r\n");
  // Test merge system call
  test_merge();
  printf("main_test: MERGE OK\r\n");
  // Test collect system call
  test_collect();
  printf("main_test: COLLECT OK\r\n");
  // Test mapMPU system call
  test_mapMPU();
  printf("main_test: MPU MAP OK\r\n");
  // Test readMPU system call
  test_readMPU();
  printf("main_test: MPU READ OK\r\n");
  // Test findBlock system call
  test_find();
  printf("main_test: FINDBLOCK OK\r\n");

  printf("\r\nmain_test: All tests PASSED\r\n");

}

#endif //UNIT_TESTS
