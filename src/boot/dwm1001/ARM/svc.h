#include "user_ADT.h"

__attribute__ ((noinline)) int Pip_createPartition(uint32_t* idBlock)
{
  __asm("SVC #0");
}

__attribute__ ((noinline)) uint32_t* Pip_cutMemoryBlock(uint32_t* idBlockToCut,
                                                    uint32_t* cutAddr,
                                                    int32_t mPURegionNb)
{
  __asm("SVC #1");
}

__attribute__ ((noinline)) uint32_t* Pip_mergeMemoryBlocks( uint32_t* idBlockToMerge1,
                                                        uint32_t* idBlockToMerge2,
                                                        int32_t mPURegionNb)
{
  __asm("SVC #2");
}


__attribute__ ((noinline)) int Pip_prepare( uint32_t* idPD,
                                            int32_t projectedSlotsNb,
                                            uint32_t* idRequisitionedBlock)
{
  __asm("SVC #3");
}

__attribute__ ((noinline)) uint32_t* Pip_addMemoryBlock(uint32_t* idPDchild,
                                                        uint32_t* idBlockToShare,
                                                        uint32_t r,
                                                        uint32_t w,
                                                        uint32_t e)
{
  __asm("SVC #4");
}

__attribute__ ((noinline)) uint32_t Pip_removeMemoryBlock(uint32_t* idPDchild,
                                                          uint32_t* idBlockToRemove)
{
  __asm("SVC #5");
}

__attribute__ ((noinline)) uint32_t Pip_deletePartition(uint32_t* idPDchildToDelete)
{
  __asm("SVC #6");
}

__attribute__ ((noinline)) uint32_t* Pip_collect(uint32_t* idPD)
{
  __asm("SVC #7");
}

__attribute__ ((noinline)) uint32_t Pip_mapMPU( uint32_t* idPD,
                                                uint32_t* idBlockToEnable,
                                                int32_t mPURegionNb)
{
  __asm("SVC #8");
}

__attribute__ ((noinline)) uint32_t* Pip_readMPU( uint32_t* idPD,
                                                  int32_t mPURegionNb)
{
  __asm("SVC #9");
}

__attribute__ ((noinline))  blockOrError Pip_findBlock(uint32_t* idPD,
                                                       uint32_t* addrInBlock)
{

  asm volatile (
      " push {r3}	\n" // compiler uses r3 so save it now...
      " SVC #10	\n"
      " mov r8, r0\n"
      " mov r9, r1\n"
      " mov r10, r2\n"
      " mov r11, r3\n"
      " pop {r3} \n"); // ...restore r3


  volatile blockOrError block_found = { .error=-1,
                                        .blockAttr.blockentryaddr=NULL,
                                        .blockAttr.blockstartaddr=NULL,
                                        .blockAttr.blockendaddr=NULL,
                                        .blockAttr.read = 0,
                                        .blockAttr.write = 0,
                                        .blockAttr.exec = 0,
                                        .blockAttr.accessible = 0
                                      }; // must be volatile
  volatile uint32_t perm = 0;
  // Fill error field
  asm  (
        " mov %[error], r0 \n"
          : [error] "=r" (block_found.error)

      );
  if(block_found.error != -1){
    // If no error, then fill the other fields
    asm  (" mov %[entryaddr], r8 \n"
          " mov %[startaddr], r9 \n"
          " mov %[endaddr], r10 \n"
          " mov %[AP], r11 \n"
          : // Outputs
          [entryaddr] "=r" (block_found.blockAttr.blockentryaddr),
          [startaddr] "=r" (block_found.blockAttr.blockstartaddr),
          [endaddr] "=r" (block_found.blockAttr.blockendaddr),
          [AP] "=r" (perm)
      );
    // Fill the bits' fields: writing bits so no need for first bit masking after shifting
    block_found.blockAttr.read = perm & (0x1);
    block_found.blockAttr.write = (perm >> 1);
    block_found.blockAttr.exec = (perm >> 2);
    block_found.blockAttr.accessible = (perm >> 3);
  }
  return block_found;
}
