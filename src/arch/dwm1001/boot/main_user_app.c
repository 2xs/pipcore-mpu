/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2021)                */
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

#include <stdio.h>
#include "user_ADT.h"
#include "svc.h"

#define MSG_INIT	\
	"\r\n\n"	\
	"App   :  Pip-MPU\n\r"	\
	"Built :  " __DATE__ " " __TIME__ "\n"	\
	"\r\n"

int main_user_app(int argc, char* argv[])
{
  uint32_t* root = (uint32_t *) argv[0];
  uint32_t* blockentryaddr_flash = (uint32_t *) argv[1];
  uint32_t* blockentryaddr_ram0 = (uint32_t *) argv[2];
  uint32_t* blockentryaddr_ram1 = (uint32_t *) argv[3];
  uint32_t* blockentryaddr_ram2 = (uint32_t *) argv[4];
  uint32_t* blockentryaddr_periph = (uint32_t *) argv[5];


  printf(MSG_INIT);

  puts("Hello World");

  int i;

  for (i = 0; i < 20; i++) {
    printf("Hello World %d!\n", i);
  }

  // cut the RW RAM block in 4: 0x20000000-0x20005000-0x20006000-0x20007900-0x20008000
  uint32_t* ram1_2_addr = (uint32_t*) 0x20005000;
  uint32_t* blockentryaddr_ram1_2 = Pip_cutMemoryBlock(blockentryaddr_ram1, ram1_2_addr, -1);
  if(blockentryaddr_ram1_2 != NULL){
    printf("Cut done\n");
  }
  uint32_t* blockentryaddr_ram1_3 = Pip_cutMemoryBlock(blockentryaddr_ram1_2, (uint32_t*)0x20006000, -1);
  if(blockentryaddr_ram1_3 != NULL){
    printf("Cut done\n");
  }
  uint32_t* ram1_4_addr = (uint32_t*) 0x20007F00;
  uint32_t* blockentryaddr_ram1_4 = Pip_cutMemoryBlock(blockentryaddr_ram1_3, ram1_4_addr, -1);
  if(blockentryaddr_ram1_4 != NULL){
    printf("Cut done\n");
  }

  int isCreated = Pip_createPartition(blockentryaddr_ram1_2);
  if(isCreated == 1){
    printf("Create done\n");
  }

  int isPreparedChild = Pip_prepare(blockentryaddr_ram1_2, 1, blockentryaddr_ram1_4);
  if(isPreparedChild == 1){
    printf("Prepare done\n");
  }

  uint32_t* blockentryaddr_flash_in_child = Pip_addMemoryBlock(blockentryaddr_ram1_2, blockentryaddr_flash, 1, 0, 1);
  if(blockentryaddr_flash_in_child != NULL){
    printf("Add done\n");
  }

  int isRemoved = Pip_removeMemoryBlock(blockentryaddr_flash);
  if(isRemoved == 1){
    printf("Remove done\n");
  }

  uint32_t* blockentryaddr_collected = Pip_collect(blockentryaddr_ram1_2);
  if(blockentryaddr_collected != NULL){
    printf("Collect done\n");
  }
  int isDeleted = Pip_deletePartition(blockentryaddr_ram1_2);
  if(isDeleted == 1){
    printf("Delete done\n");
  }

  int isPreparedRoot = Pip_prepare(root, 1, blockentryaddr_ram1_4);
  if(isPreparedRoot == 1){
    printf("Prepare done\n");
  }

  uint32_t* blockentryaddr_ram1_5 = Pip_cutMemoryBlock(blockentryaddr_ram1_3, (uint32_t*)0x20007000, -1);
  if(blockentryaddr_ram1_5 != NULL){
    printf("Cut done\n");
  }

  uint32_t* blockentryaddr_merge = Pip_mergeMemoryBlocks(blockentryaddr_ram1_3, blockentryaddr_ram1_5, -1);
  if(blockentryaddr_merge != NULL){
    printf("Merge done\n");
  }

  int isMapped = Pip_mapMPU(root, blockentryaddr_ram1_3, 5);
  if(isMapped == 1){
    printf("mapMPU done\n");
  }

  uint32_t* blockentryaddr_entry = Pip_readMPU(root, 5);
  if(blockentryaddr_entry == blockentryaddr_ram1_3){
    printf("read MPU done\n");
  }

  blockOrError block_found = Pip_findBlock(root, (uint32_t*)0x20007000);
  blockOrError block_found1 = Pip_findBlock(root, (uint32_t*)0x20000000);
  blockOrError block_found2 = Pip_findBlock(root, (uint32_t*)0x0);
  blockOrError block_found3 = Pip_findBlock(root, (uint32_t*)0x800000);
  blockOrError block_found4 = Pip_findBlock(root+1, (uint32_t*)0x20007000);
  if(block_found.error != -1
	  && block_found1.error != -1
	  && block_found2.error != -1
	  && block_found3.error == -1
	  && block_found4.error == -1){
    printf("findBlock done\n");
  }
  while (1);
}
