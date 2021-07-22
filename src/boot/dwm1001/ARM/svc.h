__attribute__ ((noinline)) int Pip_createPartition(paddr idBlock)
{
  __asm("SVC #0");
}

__attribute__ ((noinline)) paddr Pip_cutMemoryBlock(paddr idBlockToCut,
                                                    paddr cutAddr,
                                                    Coq_index mPURegionNb)
{
  __asm("SVC #1");
}

__attribute__ ((noinline)) paddr Pip_mergeMemoryBlocks( paddr idBlockToMerge1,
                                                        paddr idBlockToMerge2,
                                                        Coq_index mPURegionNb)
{
  __asm("SVC #2");
}


__attribute__ ((noinline)) int Pip_prepare( paddr idPD,
                                            Coq_index projectedSlotsNb,
                                            paddr idRequisitionedBlock)
{
  __asm("SVC #3");
}

__attribute__ ((noinline)) paddr Pip_addMemoryBlock(paddr idPDchild,
                                                    paddr idBlockToShare,
                                                    bool r,
                                                    bool w,
                                                    bool e)
{
  __asm("SVC #4");
}

__attribute__ ((noinline)) bool Pip_removeMemoryBlock(paddr idPDchild,
                                                      paddr idBlockToRemove)
{
  __asm("SVC #5");
}

__attribute__ ((noinline)) bool Pip_deletePartition(paddr idPDchildToDelete)
{
  __asm("SVC #6");
}

__attribute__ ((noinline)) paddr Pip_collect(paddr idPD)
{
  __asm("SVC #7");
}

__attribute__ ((noinline)) bool Pip_mapMPU( paddr idPD,
                                            paddr idBlockToEnable,
                                            Coq_index mPURegionNb)
{
  __asm("SVC #8");
}

__attribute__ ((noinline)) paddr Pip_readMPU( paddr idPD,
                                              Coq_index mPURegionNb)
{
  __asm("SVC #9");
}

/*__attribute__ ((noinline)) blockOrError findBlock(paddr idPD,
                                                    paddr addrInBlock)
{
  __asm("SVC #10");
}*/

