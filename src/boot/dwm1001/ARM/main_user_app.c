
#include <stdio.h>
#include "maldefines.h"
#include "svc.h"


#define MSG_INIT	\
	"\r\n\n"	\
	"App   :  Pip-MPU\n\r"	\
	"Built :  " __DATE__ " " __TIME__ "\n"	\
	"\r\n"

int main_user_app(int argc, char* argv[])
{
  paddr root = argv[0];
  paddr blockentryaddr_flash = argv[1];
  paddr blockentryaddr_ram0 = argv[2];
  paddr blockentryaddr_ram1 = argv[3];
  paddr blockentryaddr_ram2 = argv[4];
  paddr blockentryaddr_periph = argv[5];


  printf(MSG_INIT);

  puts("Hello World");

  int i;

  for (i = 0; i < 20; i++) {
    printf("Hello World %d!\n", i);
  }

  // cut the RW RAM block in 4: 0x20000000-0x20005000-0x20006000-0x20007900-0x20008000
  uint32_t* ram1_2_addr = (uint32_t*) 0x20005000;
  paddr blockentryaddr_ram1_2 = Pip_cutMemoryBlock(blockentryaddr_ram1, ram1_2_addr, -1);
  if(blockentryaddr_ram1_2 != NULL){
    printf("Cut done\n");
  }
  paddr blockentryaddr_ram1_3 = Pip_cutMemoryBlock(blockentryaddr_ram1_2, (uint32_t*)0x20006000, -1);
  if(blockentryaddr_ram1_3 != NULL){
    printf("Cut done\n");
  }
  uint32_t* ram1_4_addr = (uint32_t*) 0x20007900;
  paddr blockentryaddr_ram1_4 = Pip_cutMemoryBlock(blockentryaddr_ram1_3, ram1_4_addr, -1);
  if(blockentryaddr_ram1_4 != NULL){
    printf("Cut done\n");
  }

  int isCreated = Pip_createPartition(blockentryaddr_ram1_2);
  if(isCreated == true){
    printf("Create done\n");
  }

  int isPreparedChild = Pip_prepare(ram1_2_addr, 1, blockentryaddr_ram1_4);
  if(isPreparedChild == true){
    printf("Prepare done\n");
  }

  paddr blockentryaddr_flash_in_child = Pip_addMemoryBlock(ram1_2_addr, blockentryaddr_flash, true, false, true);
  if(blockentryaddr_flash_in_child != NULL){
    printf("Add done\n");
  }

  int isRemoved = Pip_removeMemoryBlock(ram1_2_addr, blockentryaddr_flash);
  if(isRemoved == true){
    printf("Remove done\n");
  }

  paddr blockentryaddr_collected = Pip_collect(ram1_2_addr);
  if(blockentryaddr_collected != NULL){ // TODO: blockentryaddr_ram1_4 == blockentryaddr_collected
    printf("Collect done\n");
  }
  int isDeleted = Pip_deletePartition(blockentryaddr_ram1_2);
  if(isDeleted == true){
    printf("Delete done\n");
  }

  int isPreparedRoot = Pip_prepare(root, 1, blockentryaddr_ram1_4);
  if(isPreparedRoot == true){
    printf("Prepare done\n");
  }

  paddr blockentryaddr_ram1_5 = Pip_cutMemoryBlock(blockentryaddr_ram1_3, (uint32_t*)0x20007000, -1);
  if(blockentryaddr_ram1_5 != NULL){
    printf("Cut done\n");
  }

  paddr blockentryaddr_merge = Pip_mergeMemoryBlocks(blockentryaddr_ram1_3, blockentryaddr_ram1_5, -1);
  if(blockentryaddr_merge != NULL){ // TODO: blockentryaddr_merge == blockentryaddr_ram1_3
    printf("Merge done\n");
  }

  int isMapped = Pip_mapMPU(root, blockentryaddr_ram1_3, 5);
  if(isMapped == true){
    printf("mapMPU done\n");
  }

  paddr blockentryaddr_entry = Pip_readMPU(root, 5);
  if(blockentryaddr_entry == blockentryaddr_ram1_3){
    printf("readMPU done\n");
  }

  while (1);
}
