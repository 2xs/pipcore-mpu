#include <stdio.h>
#include "Services.c"
#include "pip_debug.h"

#include <assert.h>

// End address for the user section; defined in linker script
extern uint32_t user_mem_end;
// Start address for the user section; defined in linker script
extern uint32_t user_mem_start;

// Global identifiers
paddr root = NULL;
paddr root_kernel_structure_start = NULL;
paddr initial_block_start = NULL;
paddr initial_block_end = NULL;
extern uint32_t kernelstructureentriesnb;

void init_tests(){
	/* Initialize the root partition */
	mal_init();

  root = getRootPartition();
  dump_partition(root);
  activate(root);
}


// COMMON ASSERTIONS

/*!
 * \fn void remaining_MPU_slots_form_a_linked_list(uint32_t start_index, uint32_t end_index, paddr kernel_structure_start)
 * \brief Tests that the MPU structure is well formed
          Only legitimate to a partition after one prepare and adding/removal in order
 */
void remaining_MPU_slots_form_a_linked_list(uint32_t start_index, uint32_t end_index, paddr kernel_structure_start)
{
  // test remaining empty slots: special case -> last end is 0
  for(int i = start_index ; i < end_index - 1 ; i++)
  {
      paddr empty_block_MPU_entry = (paddr) ((uint8_t*) kernel_structure_start + i * mpuentrylength);
      assert(readMPUIndexFromMPUEntryAddr(empty_block_MPU_entry) == i);
      assert(readMPUStartFromMPUEntryAddr(empty_block_MPU_entry) == 0);
      assert(readMPUEndFromMPUEntryAddr(empty_block_MPU_entry) == (paddr) ((uint8_t*) kernel_structure_start + (i + 1) * mpuentrylength));
      assert(readMPUAccessibleFromMPUEntryAddr(empty_block_MPU_entry) == false);
      assert(readMPUPresentFromMPUEntryAddr(empty_block_MPU_entry) == false);
  }

  paddr empty_block_MPU_entry = (paddr) ((uint8_t*) kernel_structure_start + end_index * mpuentrylength);
  assert(readMPUIndexFromMPUEntryAddr(empty_block_MPU_entry) == end_index);
  assert(readMPUStartFromMPUEntryAddr(empty_block_MPU_entry) == 0);
  assert(readMPUEndFromMPUEntryAddr(empty_block_MPU_entry) == 0);
  assert(readMPUAccessibleFromMPUEntryAddr(empty_block_MPU_entry) == false);
  assert(readMPUPresentFromMPUEntryAddr(empty_block_MPU_entry) == false);
}

/*!
 * \fn void remaining_MPU_slots_form_a_linked_list(uint32_t start_index, uint32_t end_index, paddr kernel_structure_start)
 * \brief Tests that the whole Sh1 structure from <start_index> to <end_index> is default
  All entries should be [PDchild=0, PDflag=False, inChildLocation=0]
 */
void remaining_Sh1_slots_are_default(uint32_t start_index, uint32_t end_index, paddr kernel_structure_start)
{
  for(int i = start_index ; i < end_index ; i++)
  {
      paddr MPU_entry = (paddr) ((uint8_t*) kernel_structure_start + i * mpuentrylength);
      assert(readSh1PDChildFromMPUEntryAddr(MPU_entry) == NULL);
      assert(readSh1PDFlagFromMPUEntryAddr(MPU_entry) == false);
      assert(readSh1InChildLocationFromMPUEntryAddr(MPU_entry) == NULL);
  }
}

/*!
 * \fn void remaining_MPU_slots_form_a_linked_list(uint32_t start_index, uint32_t end_index, paddr kernel_structure_start)
 * \brief Tests that the whole Sh1 structure is default
  All entries should be [PDchild=0, PDflag=False, inChildLocation=0]
 */
void Sh1_structure_is_default(paddr kernel_structure_start)
{
  remaining_Sh1_slots_are_default(0, kernelstructureentriesnb, kernel_structure_start);
}

/*!
 * \fn void remaining_MPU_slots_form_a_linked_list(uint32_t start_index, uint32_t end_index, paddr kernel_structure_start)
 * \brief Tests that the SC structure from <start_index> to <end_index> is default
  All entries should be [origin=0, next=0]
 */
void remaining_SC_slots_are_default(uint32_t start_index, uint32_t end_index, paddr kernel_structure_start)
{
  for(int i = start_index ; i < end_index ; i++)
  {
      paddr MPU_entry = (paddr) ((uint8_t*) kernel_structure_start + i * mpuentrylength);
      assert(readSCOriginFromMPUEntryAddr(MPU_entry) == 0);
      assert(readSCNextFromMPUEntryAddr(MPU_entry) == 0);
  }
}

/*!
 * \fn void remaining_MPU_slots_form_a_linked_list(uint32_t start_index, uint32_t end_index, paddr kernel_structure_start)
 * \brief Tests that the whole SC structure is default
  All entries should be [origin=0, next=0]
 */
void SC_structure_is_default(paddr kernel_structure_start)
{
  remaining_SC_slots_are_default(0, kernelstructureentriesnb, kernel_structure_start);
}


// INITIAL ROOT PARTITION DEFINITION

/*!
 * \fn void test_initial_root_PD_values()
 * \brief Tests that the initial values of the root PD structure are correct
 */
void test_initial_root_PD_values()
{
    assert(root == &user_mem_start);
  root_kernel_structure_start = (paddr) ((uint8_t*) &user_mem_start + (PDSTRUCTURETOTALLENGTH()));//size in bytes
  assert(readPDStructurePointer(root) == root_kernel_structure_start);
  assert(readPDFirstFreeSlotPointer(root) == (paddr) ((uint8_t*) root_kernel_structure_start + mpuentrylength));
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
  for(int i = 1 ; i < (kernelstructureentriesnb - 1) ; i++)   // 0-indexed, index nb -1 not included
  {
      assert(
          readMPUIndexFromMPUEntryAddr(
            (paddr) ((uint8_t*) root_kernel_structure_start + i * mpuentrylength)) == i
      );
      assert(
          readMPUStartFromMPUEntryAddr((paddr) ((uint8_t*) root_kernel_structure_start + i*mpuentrylength)) ==
          0);
      assert(
          readMPUEndFromMPUEntryAddr((paddr) ((uint8_t*) root_kernel_structure_start + i*mpuentrylength)) ==
          (paddr) ((uint8_t*) root_kernel_structure_start + (i+1)*mpuentrylength));
      assert(
          readMPUAccessibleFromMPUEntryAddr((paddr) ((uint8_t*) root_kernel_structure_start + i*mpuentrylength)) ==
          0);
      assert(
          readMPUPresentFromMPUEntryAddr((paddr) ((uint8_t*) root_kernel_structure_start + i*mpuentrylength))==
          0);
  }

  // last entry is special since it ends with null
  assert(readMPUIndexFromMPUEntryAddr((paddr) ((uint8_t*) root_kernel_structure_start +
                                            (kernelstructureentriesnb - 1)
                                            * mpuentrylength)
                                            )==
                    kernelstructureentriesnb - 1
  );
  assert(readMPUStartFromMPUEntryAddr(
      (paddr) ((uint8_t*) root_kernel_structure_start + (kernelstructureentriesnb - 1) * mpuentrylength)) ==
                    0);
  assert(readMPUEndFromMPUEntryAddr((paddr) ((uint8_t*) root_kernel_structure_start + (kernelstructureentriesnb-1)*mpuentrylength)) ==
                    0);
  assert(readMPUAccessibleFromMPUEntryAddr((paddr) ((uint8_t*) root_kernel_structure_start + (kernelstructureentriesnb-1)*mpuentrylength)) ==
                    0);
  assert(readMPUPresentFromMPUEntryAddr((paddr) ((uint8_t*) root_kernel_structure_start + (kernelstructureentriesnb-1)*mpuentrylength)) ==
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
  // all values are default
  for(int i = 1 ; i < kernelstructureentriesnb ; i++)   // 0-indexed
  {
      assert(
          readSh1PDChildFromMPUEntryAddr((paddr) ((uint8_t*) root_kernel_structure_start +
                                                                  i*mpuentrylength))
          == 0
      );
      assert(
          readSh1PDFlagFromMPUEntryAddr((paddr) ((uint8_t*) root_kernel_structure_start +
                                                                  i*mpuentrylength))
          == 0
      );
      assert(
          readSh1InChildLocationFromMPUEntryAddr((paddr) ((uint8_t*) root_kernel_structure_start +
                                                                          i*mpuentrylength))
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
  // first entry is special since an initial block is present
  assert(readSCOriginFromMPUEntryAddr(root_kernel_structure_start) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(root_kernel_structure_start) == 0);

  // remaining entries are default
  for(int i = 1 ; i < kernelstructureentriesnb ; i++)  // 0-indexed
  {
      assert(readSCOriginFromMPUEntryAddr((paddr) ((uint8_t*) root_kernel_structure_start + i*mpuentrylength))==
                        0);
      assert(readSCNextFromMPUEntryAddr((paddr) ((uint8_t*) root_kernel_structure_start + i*mpuentrylength)) ==
                        0);
  }
}

/*!
 * \fn void test_initial_root()
 * \brief Launches the tests of the initial root partition configuration
 */
void test_initial_root()
{
  init_tests();
  test_initial_root_PD_values();
  test_initial_root_MPU_values();
  test_initial_root_Sh1_values();
  test_initial_root_SC_values();
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
  cutMemoryBlock(initial_block_start, cut_address1);
  dump_partition(root);

  paddr initial_block_MPU_entry = root_kernel_structure_start;
  assert(readMPUIndexFromMPUEntryAddr(root_kernel_structure_start) == 0);
  assert(readMPUStartFromMPUEntryAddr(root_kernel_structure_start) == initial_block_start);
  assert(readMPUEndFromMPUEntryAddr(root_kernel_structure_start) == cut_address1 - 1);
  assert(readMPUAccessibleFromMPUEntryAddr(root_kernel_structure_start) == true);
  assert(readMPUPresentFromMPUEntryAddr(root_kernel_structure_start) == true);

  paddr cut1_block_MPU_entry = (paddr) ((uint8_t*) root_kernel_structure_start + mpuentrylength);
  assert(readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry) == 1);
  assert(readMPUStartFromMPUEntryAddr(cut1_block_MPU_entry) == cut_address1);
  assert(readMPUEndFromMPUEntryAddr(cut1_block_MPU_entry) == initial_block_end);
  assert(readMPUAccessibleFromMPUEntryAddr(cut1_block_MPU_entry) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut1_block_MPU_entry) == true);

  assert(readSCOriginFromMPUEntryAddr(initial_block_MPU_entry) == initial_block_start);
  // next is the next subblock's MPU location == not the id
  assert(readSCNextFromMPUEntryAddr(initial_block_MPU_entry) == (paddr) ((uint8_t*) root_kernel_structure_start + readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry)*mpuentrylength));

  //paddr cut1_block_SC_entry = root_kernel_structure_start + readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry)*mpuentrylength;
  assert(readSCOriginFromMPUEntryAddr(cut1_block_MPU_entry) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut1_block_MPU_entry) == 0);

  remaining_MPU_slots_form_a_linked_list(2, kernelstructureentriesnb - 1, root_kernel_structure_start);

  Sh1_structure_is_default(root_kernel_structure_start);

  remaining_SC_slots_are_default(2, kernelstructureentriesnb, root_kernel_structure_start);

  // ******2nd cut******
  // cut the created subblock
  cutMemoryBlock(cut_address1, cut_address2);

  //paddr initial_block_MPU_entry = root_kernel_structure_start;
  assert(readMPUIndexFromMPUEntryAddr(initial_block_MPU_entry) == 0);
  assert(readMPUStartFromMPUEntryAddr(initial_block_MPU_entry) == initial_block_start);
  assert(readMPUEndFromMPUEntryAddr(initial_block_MPU_entry) == cut_address1 - 1);
  assert(readMPUAccessibleFromMPUEntryAddr(initial_block_MPU_entry) == true);
  assert(readMPUPresentFromMPUEntryAddr(initial_block_MPU_entry) == true);

  //paddr cut1_block_MPU_entry = root_kernel_structure_start + mpuentrylength;
  assert(readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry) == 1);
  assert(readMPUStartFromMPUEntryAddr(cut1_block_MPU_entry) == cut_address1);
  assert(readMPUEndFromMPUEntryAddr(cut1_block_MPU_entry) == (cut_address2 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(cut1_block_MPU_entry) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut1_block_MPU_entry) == true);

  paddr cut2_block_MPU_entry = (paddr) ((uint8_t*) root_kernel_structure_start + 2*mpuentrylength);
  assert(readMPUIndexFromMPUEntryAddr(cut2_block_MPU_entry) == 2);
  assert(readMPUStartFromMPUEntryAddr(cut2_block_MPU_entry) == cut_address2);
  assert(readMPUEndFromMPUEntryAddr(cut2_block_MPU_entry) == initial_block_end);
  assert(readMPUAccessibleFromMPUEntryAddr(cut2_block_MPU_entry) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut2_block_MPU_entry) == true);

  //paddr initial_block_Sh1_entry = root_kernel_structure_start;
  assert(readSh1PDChildFromMPUEntryAddr(initial_block_MPU_entry) == 0);
  assert(readSh1PDFlagFromMPUEntryAddr(initial_block_MPU_entry) == false);
  assert(readSh1InChildLocationFromMPUEntryAddr(initial_block_MPU_entry) == 0);

  //paddr initial_block_SC_entry = root_kernel_structure_start;
  assert(readSCOriginFromMPUEntryAddr(initial_block_MPU_entry) == initial_block_start);
  // next is the next subblock's MPU location == not the id
  assert(readSCNextFromMPUEntryAddr(initial_block_MPU_entry) == (paddr) ((uint8_t*) root_kernel_structure_start + readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry)*mpuentrylength));

  //paddr cut1_block_SC_entry = root_kernel_structure_start + readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry)*mpuentrylength);
  assert(readSCOriginFromMPUEntryAddr(cut1_block_MPU_entry) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut1_block_MPU_entry) == (paddr) ((uint8_t*) root_kernel_structure_start + readMPUIndexFromMPUEntryAddr(cut2_block_MPU_entry)*mpuentrylength));

  //paddr cut2_block_SC_entry = root_kernel_structure_start + readMPUIndexFromMPUEntryAddr(cut2_block_MPU_entry)*mpuentrylength;
  assert(readSCOriginFromMPUEntryAddr(cut2_block_MPU_entry) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut2_block_MPU_entry) == 0);

  remaining_MPU_slots_form_a_linked_list(3, kernelstructureentriesnb- 1, root_kernel_structure_start);
  Sh1_structure_is_default(root_kernel_structure_start);
  remaining_SC_slots_are_default(3, kernelstructureentriesnb, root_kernel_structure_start);

  // ******3rd cut******
  // cut the initial block again -> no other blocks exist so the newly created subblock will be at index 3
  cutMemoryBlock(initial_block_start, cut_address3);

  // Test cut_address3 MPU entries
  //paddr initial_block_MPU_entry = root_kernel_structure_start;
  assert(readMPUIndexFromMPUEntryAddr(initial_block_MPU_entry) == 0);
  assert(readMPUStartFromMPUEntryAddr(initial_block_MPU_entry) == initial_block_start);
  assert(readMPUEndFromMPUEntryAddr(initial_block_MPU_entry) == (cut_address3 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(initial_block_MPU_entry) == true);
  assert(readMPUPresentFromMPUEntryAddr(initial_block_MPU_entry) == true);

  //paddr cut1_block_MPU_entry = root_kernel_structure_start + mpuentrylength;
  assert(readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry) == 1);
  assert(readMPUStartFromMPUEntryAddr(cut1_block_MPU_entry) == cut_address1);
  assert(readMPUEndFromMPUEntryAddr(cut1_block_MPU_entry) == (cut_address2 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(cut1_block_MPU_entry) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut1_block_MPU_entry) == true);

  //paddr cut2_block_MPU_entry = root_kernel_structure_start + 2 * mpuentrylength;
  assert(readMPUIndexFromMPUEntryAddr(cut2_block_MPU_entry) == 2);
  assert(readMPUStartFromMPUEntryAddr(cut2_block_MPU_entry) == cut_address2);
  assert(readMPUEndFromMPUEntryAddr(cut2_block_MPU_entry) == initial_block_end);
  assert(readMPUAccessibleFromMPUEntryAddr(cut2_block_MPU_entry) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut2_block_MPU_entry) == true);

  paddr cut3_block_MPU_entry = (paddr) ((uint8_t*) root_kernel_structure_start + 3 * mpuentrylength);
  assert(readMPUIndexFromMPUEntryAddr(cut3_block_MPU_entry) == 3);
  assert(readMPUStartFromMPUEntryAddr(cut3_block_MPU_entry) == cut_address3);
  assert(readMPUEndFromMPUEntryAddr(cut3_block_MPU_entry) == (cut_address1 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(cut3_block_MPU_entry) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut3_block_MPU_entry) == true);

  remaining_MPU_slots_form_a_linked_list(4, kernelstructureentriesnb - 1, root_kernel_structure_start);

  // Test cut_address3 Sh1 entries
  Sh1_structure_is_default(root_kernel_structure_start);

  // Test cut_address3 SC entries
  //paddr initial_block_SC_entry = root_kernel_structure_start;
  assert(readSCOriginFromMPUEntryAddr(initial_block_MPU_entry) == initial_block_start);
  // next is the next subblock's MPU location, not the id
  assert(readSCNextFromMPUEntryAddr(initial_block_MPU_entry) == (paddr) ((uint8_t*) root_kernel_structure_start + readMPUIndexFromMPUEntryAddr(cut3_block_MPU_entry) * mpuentrylength));

  //paddr cut1_block_SC_entry = root_kernel_structure_start + readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry)*mpuentrylength;
  assert(readSCOriginFromMPUEntryAddr(cut1_block_MPU_entry) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut1_block_MPU_entry) == (paddr) ((uint8_t*) root_kernel_structure_start + readMPUIndexFromMPUEntryAddr(cut2_block_MPU_entry) * mpuentrylength));

  //paddr cut2_block_SC_entry = root_kernel_structure_start + readMPUIndexFromMPUEntryAddr(cut2_block_MPU_entry)*mpuentrylength;
  assert(readSCOriginFromMPUEntryAddr(cut2_block_MPU_entry) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut2_block_MPU_entry) == 0);

  //paddr cut3_block_SC_entry = root_kernel_structure_start + readMPUIndexFromMPUEntryAddr(cut3_block_MPU_entry)*mpuentrylength;
  assert(readSCOriginFromMPUEntryAddr(cut3_block_MPU_entry) == initial_block_start);
  assert(readSCNextFromMPUEntryAddr(cut3_block_MPU_entry) == (paddr) ((uint8_t*) root_kernel_structure_start + readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry) * mpuentrylength));

  remaining_SC_slots_are_default(4, kernelstructureentriesnb, root_kernel_structure_start);

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

  paddr block1 = (paddr) ((uint8_t*) initial_block_start + KERNELSTRUCTURETOTALLENGTH()*30);
  paddr block2 = (paddr) ((uint8_t*) initial_block_start + KERNELSTRUCTURETOTALLENGTH()*29);
  paddr block3 = (paddr) ((uint8_t*) initial_block_start + KERNELSTRUCTURETOTALLENGTH()*28);
  paddr block4 = (paddr) ((uint8_t*) initial_block_start + KERNELSTRUCTURETOTALLENGTH()*27);
  paddr block5 = (paddr) ((uint8_t*) initial_block_start + KERNELSTRUCTURETOTALLENGTH()*26);
  paddr block6 = (paddr) ((uint8_t*) initial_block_start + KERNELSTRUCTURETOTALLENGTH()*25);
  paddr block7 = (paddr) ((uint8_t*) initial_block_start + KERNELSTRUCTURETOTALLENGTH()*24);

  assert(cutMemoryBlock(initial_block_start, block1) != 0);
  assert(cutMemoryBlock(initial_block_start, block2) != 0);
  assert(cutMemoryBlock(initial_block_start, block3) != 0);
  assert(cutMemoryBlock(initial_block_start, block4) != 0);
  assert(cutMemoryBlock(initial_block_start, block5) != 0);
  assert(cutMemoryBlock(initial_block_start, block6) != 0);
  assert(cutMemoryBlock(initial_block_start, block7) != 0);

  dump_partition(root);

  // Test PDS
  assert(readPDFirstFreeSlotPointer(root) == NULL);
  assert(readPDNbFreeSlots(root) == 0);
  assert(readPDNbPrepare(root) == 1);

  // Test MPU
  paddr initial_block_MPU_entry_address = root_kernel_structure_start;
  assert(readMPUIndexFromMPUEntryAddr(initial_block_MPU_entry_address) == 0);
  assert(readMPUStartFromMPUEntryAddr(initial_block_MPU_entry_address) == initial_block_start);
  assert(readMPUEndFromMPUEntryAddr(initial_block_MPU_entry_address) == (block7 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(initial_block_MPU_entry_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(initial_block_MPU_entry_address) == true);

  paddr cut1_block_MPU_entry_address = (paddr) ((uint8_t*) root_kernel_structure_start + mpuentrylength);
  assert(readMPUIndexFromMPUEntryAddr(cut1_block_MPU_entry_address) == 1);
  assert(readMPUStartFromMPUEntryAddr(cut1_block_MPU_entry_address) == block1);
  assert(readMPUEndFromMPUEntryAddr(cut1_block_MPU_entry_address) == initial_block_end);
  assert(readMPUAccessibleFromMPUEntryAddr(cut1_block_MPU_entry_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut1_block_MPU_entry_address) == true);

  paddr cut2_block_MPU_entry_address = (paddr) ((uint8_t*) root_kernel_structure_start + 2*mpuentrylength);
  assert(readMPUIndexFromMPUEntryAddr(cut2_block_MPU_entry_address) == 2);
  assert(readMPUStartFromMPUEntryAddr(cut2_block_MPU_entry_address) == block2);
  assert(readMPUEndFromMPUEntryAddr(cut2_block_MPU_entry_address) == (block1 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(cut2_block_MPU_entry_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut2_block_MPU_entry_address) == true);

  paddr cut3_block_MPU_entry_address = (paddr) ((uint8_t*) root_kernel_structure_start + 3*mpuentrylength);
  assert(readMPUIndexFromMPUEntryAddr(cut3_block_MPU_entry_address) == 3);
  assert(readMPUStartFromMPUEntryAddr(cut3_block_MPU_entry_address) == block3);
  assert(readMPUEndFromMPUEntryAddr(cut3_block_MPU_entry_address) == (block2 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(cut3_block_MPU_entry_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut3_block_MPU_entry_address) == true);

  paddr cut4_block_MPU_entry_address = (paddr) ((uint8_t*) root_kernel_structure_start + 4*mpuentrylength);
  assert(readMPUIndexFromMPUEntryAddr(cut4_block_MPU_entry_address) == 4);
  assert(readMPUStartFromMPUEntryAddr(cut4_block_MPU_entry_address) == block4);
  assert(readMPUEndFromMPUEntryAddr(cut4_block_MPU_entry_address) == (block3 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(cut4_block_MPU_entry_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut4_block_MPU_entry_address) == true);

  paddr cut5_block_MPU_entry_address = (paddr) ((uint8_t*) root_kernel_structure_start + 5*mpuentrylength);
  assert(readMPUIndexFromMPUEntryAddr(cut5_block_MPU_entry_address) == 5);
  assert(readMPUStartFromMPUEntryAddr(cut5_block_MPU_entry_address) == block5);
  assert(readMPUEndFromMPUEntryAddr(cut5_block_MPU_entry_address) == (block4 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(cut5_block_MPU_entry_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut5_block_MPU_entry_address) == true);

  paddr cut6_block_MPU_entry_address = (paddr) ((uint8_t*) root_kernel_structure_start + 6*mpuentrylength);
  assert(readMPUIndexFromMPUEntryAddr(cut6_block_MPU_entry_address) == 6);
  assert(readMPUStartFromMPUEntryAddr(cut6_block_MPU_entry_address) == block6);
  assert(readMPUEndFromMPUEntryAddr(cut6_block_MPU_entry_address) == (block5 - 1));
  assert(readMPUAccessibleFromMPUEntryAddr(cut6_block_MPU_entry_address) == true);
  assert(readMPUPresentFromMPUEntryAddr(cut6_block_MPU_entry_address) == true);

  paddr cut7_block_MPU_entry_address = (paddr) ((uint8_t*) root_kernel_structure_start + 7*mpuentrylength);
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
  assert(cutMemoryBlock((paddr) 0x100, (paddr) 0x3000) == 0);
  assert(cutMemoryBlock((paddr) ((uint8_t*) initial_block_start + 0x3000), (paddr) ((uint8_t*) initial_block_start + 0x4000)) == 0);

  // Tests don't accept a cut address outside the block
  assert(cutMemoryBlock(initial_block_start, 0) == 0);
  assert(cutMemoryBlock(initial_block_start, (paddr) ((uint8_t*) initial_block_start - 32)) == 0);
  assert(cutMemoryBlock(initial_block_start, (paddr) ((uint8_t*) initial_block_end + 32)) == 0);

  // Tests can't perform cut if no free slots left
  test_cut_max_free_slots_used();
  assert(cutMemoryBlock((paddr) ((uint8_t*) initial_block_start + 32*7), (paddr) ((uint8_t*) initial_block_start + 32*8)) == 0);
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
  cutMemoryBlock(initial_block_start, (paddr) ((uint8_t*) initial_block_start + 10*KERNELSTRUCTURETOTALLENGTH()));
  cutMemoryBlock((paddr) ((uint8_t*) initial_block_start + 10*KERNELSTRUCTURETOTALLENGTH()),
                          (paddr) ((uint8_t*) initial_block_start + 12 * KERNELSTRUCTURETOTALLENGTH()));
  cutMemoryBlock((paddr) ((uint8_t*) initial_block_start + 12 * KERNELSTRUCTURETOTALLENGTH()),
                          (paddr) ((uint8_t*) initial_block_start + 13 * KERNELSTRUCTURETOTALLENGTH()));
  cutMemoryBlock((paddr) ((uint8_t*) initial_block_start + 13 * KERNELSTRUCTURETOTALLENGTH()),
                          (paddr) ((uint8_t*) initial_block_start + 14 * KERNELSTRUCTURETOTALLENGTH()));
  cutMemoryBlock((paddr) ((uint8_t*) initial_block_start + 14 * KERNELSTRUCTURETOTALLENGTH()),
                          (paddr) ((uint8_t*) initial_block_start + 15 * KERNELSTRUCTURETOTALLENGTH()));
  cutMemoryBlock((paddr) ((uint8_t*) initial_block_start + 15 * KERNELSTRUCTURETOTALLENGTH()),
                          (paddr) ((uint8_t*) initial_block_start + 16 * KERNELSTRUCTURETOTALLENGTH()));

  dump_partition(root_partition);

  // Check the only free slot left is as expected
  paddr MPU_free_slot_entry = (paddr) ((uint8_t*) root_kernel_structure_start + 7*mpuentrylength);
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
  assert(createPartition(initial_block_start) != false);

  // Fails trying to cut a block not accessible
  assert(
      cutMemoryBlock(initial_block_start, (paddr) ((uint8_t*) initial_block_start + KERNELSTRUCTURETOTALLENGTH()))
       == false
  );
}

/*!
 * \fn void test_cut()
 * \brief Launches the tests of the cut system call
 */
void test_cut()
{
  init_tests();

  paddr cut_address1 = initial_block_start + 0x600;
  paddr cut_address2 = initial_block_start + 0x700;
  paddr cut_address3 = initial_block_start + 0x300;
  three_cuts_in_a_row(cut_address1, cut_address2, cut_address3);

  init_tests();
  test_cut_max_free_slots_used();

  init_tests();
  test_cut_bad_arguments();

  init_tests();
  test_cut_6_cuts_in_a_row();

  init_tests();
  test_cut_fails_when_block_not_accessible();
}

/**
 * Unit tests main entry point.
 * If -DDEBUG_UART flag is set, sends printf messages on UART
 * If -DTRACE -DOS_USE_TRACE_SEMIHOSTING_DEBUG flags are set, send printf messages on the semihosting debug channel
 */
int main_test (int argc, char* argv[])
{
  mal_init(); // initializes the global vars
    if (kernelstructureentriesnb != 8)
  {
    printf("kernelstructureentriesnb must be 8 for the tests, test abort.\r\n");
    while(1);
  }

  initial_block_start = &user_mem_start;
  initial_block_start = (paddr) ((uint8_t*)initial_block_start + PDSTRUCTURETOTALLENGTH()); // size in bytes
  initial_block_start = (paddr) ((uint8_t*) initial_block_start + KERNELSTRUCTURETOTALLENGTH()); // size in bytes
  initial_block_end = &user_mem_end;

  // Test initial root partition definition
  test_initial_root();
  // Test cut system call
  test_cut();
  printf("\r\nmain_test: All tests PASSED\r\n");

}


