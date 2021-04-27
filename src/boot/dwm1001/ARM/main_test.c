#include <stdio.h>
#include "maldefines.h"
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

// INITIAL ROOT PARTITION DEFINITION
/*!
 * \fn void test_initial_root_PD_values()
 * \brief Tests that the initial values of the root PD structure are correct
 */
void test_initial_root_PD_values()
{
    assert(root == &user_mem_start);
  root_kernel_structure_start = &user_mem_start + PDSTRUCTURETOTALLENGTH();
  assert(readPDStructurePointer(root) == root_kernel_structure_start);
  assert(readPDFirstFreeSlotPointer(root) == root_kernel_structure_start + mpuentrylength);
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
            root_kernel_structure_start + i * mpuentrylength) == i
      );
      assert(
          readMPUStartFromMPUEntryAddr(root_kernel_structure_start + i*mpuentrylength)==
          0);
      assert(
          readMPUEndFromMPUEntryAddr(root_kernel_structure_start + i*mpuentrylength) ==
          (root_kernel_structure_start + (i+1)*mpuentrylength));
      assert(
          readMPUAccessibleFromMPUEntryAddr(root_kernel_structure_start + i*mpuentrylength) ==
          0);
      assert(
          readMPUPresentFromMPUEntryAddr(root_kernel_structure_start + i*mpuentrylength)==
          0);
  }

  // last entry is special since it ends with null
  assert(readMPUIndexFromMPUEntryAddr(root_kernel_structure_start +
                                            (kernelstructureentriesnb - 1)
                                            * mpuentrylength
                                            )==
                    kernelstructureentriesnb - 1
  );
  assert(readMPUStartFromMPUEntryAddr(
      root_kernel_structure_start + (kernelstructureentriesnb - 1) * mpuentrylength)==
                    0);
  assert(readMPUEndFromMPUEntryAddr(root_kernel_structure_start + (kernelstructureentriesnb-1)*mpuentrylength) ==
                    0);
  assert(readMPUAccessibleFromMPUEntryAddr(root_kernel_structure_start + (kernelstructureentriesnb-1)*mpuentrylength)==
                    0);
  assert(readMPUPresentFromMPUEntryAddr(root_kernel_structure_start + (kernelstructureentriesnb-1)*mpuentrylength)==
                    0);
}

/*!
 * \fn void test_initial_root_PD_values()
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
          readSh1PDChildFromMPUEntryAddr(root_kernel_structure_start +
                                                                  i*mpuentrylength)
          == 0
      );
      assert(
          readSh1PDFlagFromMPUEntryAddr(root_kernel_structure_start +
                                                                  i*mpuentrylength)
          == 0
      );
      assert(
          readSh1InChildLocationFromMPUEntryAddr(root_kernel_structure_start +
                                                                          i*mpuentrylength)
          == 0
      );
  }
}
/*!
 * \fn void test_initial_root_PD_values()
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
      assert(readSCOriginFromMPUEntryAddr(root_kernel_structure_start + i*mpuentrylength)==
                        0);
      assert(readSCNextFromMPUEntryAddr(root_kernel_structure_start + i*mpuentrylength)==
                        0);
  }
}

/**
 * Unit tests main entry point.
 * If -DDEBUG_UART flag is set, sends printf messages on UART
 * If -DTRACE -DOS_USE_TRACE_SEMIHOSTING_DEBUG flags are set, send printf messages on the semihosting debug channel
 */
int main_test (int argc, char* argv[])
{
	/* Initialize the root partition */
	mal_init();

  root = getRootPartition();
  dump_partition(root);
  activate(root);

  initial_block_start = &user_mem_start + PDSTRUCTURETOTALLENGTH() + KERNELSTRUCTURETOTALLENGTH();
  initial_block_end = &user_mem_end;

  // Test initial root partition definition
  test_initial_root_PD_values();
  test_initial_root_MPU_values();
  test_initial_root_Sh1_values();
  test_initial_root_SC_values();
  printf("\r\nmain_test: All tests PASSED\r\n");

}


