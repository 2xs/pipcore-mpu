#include <stdio.h>
#include "maldefines.h"
#include "pip_debug.h"

#include <assert.h>

// End address for the user section; defined in linker script
extern uint32_t user_mem_end;

// Global root partition identifier
paddr root = NULL;

/*!
 * \fn void test_initial_root_PD_values()
 * \brief Tests that the initial values of the root PD structure are correct
 */
void test_initial_root_PD_values()
{
  paddr kstructure = readPDStructurePointer(root);
  assert(readPDFirstFreeSlotPointer(root) == kstructure + mpuentrylength);
  assert(readPDNbFreeSlots(root) == 7);
  assert(readPDNbPrepare(root) == 1);
  assert(readPDParent(root) == NULL);
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

  test_initial_root_PD_values();
  printf("\r\nmain_test: All tests PASSED\r\n");

}


