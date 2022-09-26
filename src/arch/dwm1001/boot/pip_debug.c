#include "mal.h"
#include <stdint.h>
#include "mpu.h"
#include "stdio.h"

/*!
 * \fn void dump_PD_structure(paddr pd)
 * \brief Displays the PD structure at address <pd>.
 * \param pd The address of PD structure to display
 * \return void
 */
void dump_PD_structure(paddr pd)
{
#if defined DUMP
    PDTable_t* pdt = (PDTable_t*) pd;
    printf("\r\n----------PD %p (size: %zu/%u)------------\r\n", (void *) pdt, sizeof(PDTable_t), getPDStructureTotalLength());
    printf("%p:PD\t%p\r\n", (void *) &(pdt->structure), (void *) pdt->structure);
    printf("%p:PD\t%p\r\n", (void *) &(pdt->firstfreeslot), (void *) pdt->firstfreeslot);
    printf("%p:PD\t%u\r\n", (void *) &(pdt->nbfreeslots), pdt->nbfreeslots);
    printf("%p:PD\t%u\r\n", (void *) &(pdt->nbprepare), pdt->nbprepare);
    printf("%p:PD\t%p\r\n", (void *) &(pdt->parent), (void *) pdt->parent);
    printf("%p:PD\t", (void *) &(pdt->mpu));
    for(int i = 0 ; i < MPU_REGIONS_NB ; i++)
    {
        printf(" %p ", (void *) pdt->mpu[i]);
    }
    printf("\r\n%p:PD\t", (void *) &(pdt->LUT));
    for(int i = 0 ; i < MPU_REGIONS_NB ; i++)
    {
        printf(" %x ", (pdt->LUT[i*2]));
        printf(" %x ", (pdt->LUT[i*2+1]));
    }
    printf("\r\n");
#endif // DUMP
}

/*!
 * \fn void dump_kernel_structure(paddr kernel_structure_start_addr)
 * \brief Displays the kernel structure at <kernel_structure_start_address>.
 * \param kernel_structure_start_addr The start address of the kernel structure to display
 * \return void
 */
void dump_kernel_structure(paddr kernel_structure_start_addr)
{
#if defined DUMP
    KStructure_t* ks = (KStructure_t*) kernel_structure_start_addr;
    printf("\r\n----------Kernel structure %p (size: %u)----\r\n", kernel_structure_start_addr,
                                                                getKernelStructureTotalLength());
    printf("\r\n----------BLOCKS---------------------------\r\n");
    for (int i=0;i<KERNELSTRUCTUREENTRIESNB;i++)
    {
        paddr blockentryadddr = &ks->blocks[i];
        printf("%p:%-1u:BLK\t%-10p|%-10p\t|%-1d|%-1d|%-1d%-1d%-1d\r\n",    blockentryadddr,
                                                            readBlockIndexFromBlockEntryAddr(blockentryadddr),
                                                            readBlockStartFromBlockEntryAddr(blockentryadddr),
                                                            readBlockEndFromBlockEntryAddr(blockentryadddr),
                                                            readBlockAccessibleFromBlockEntryAddr(blockentryadddr),
                                                            readBlockPresentFromBlockEntryAddr(blockentryadddr),
                                                            readBlockRFromBlockEntryAddr(blockentryadddr),
                                                            readBlockWFromBlockEntryAddr(blockentryadddr),
                                                            readBlockXFromBlockEntryAddr(blockentryadddr)
                                                            );
    }
    printf("\r\n----------SH1---------------------------\r\n");
    for (int i=0;i<KERNELSTRUCTUREENTRIESNB;i++)
    {
        /*Sh1Entry_t* entry = (Sh1Entry_t*)(kernel_structure_start_addr + sh1offset + i*sh1entrylength);
        printf("%x:SH1\t",    entry);
        printf("%-10x|",
                                                entry->PDchild);
        printf("%-1u|",
                                                entry->PDflag);
        printf("%-10x\r\n",
                                                entry->inChildLocation);*/

        paddr blockentryadddr = &ks->blocks[i];
        paddr sh1entryadddr = &ks->sh1[i];
        printf("%p:SH1\t%-10p|%-1d|%p\r\n",  sh1entryadddr,
                                                readSh1PDChildFromBlockEntryAddr(blockentryadddr),
                                                readSh1PDFlagFromBlockEntryAddr(blockentryadddr),
                                                readSh1InChildLocationFromBlockEntryAddr(blockentryadddr));
    }
    printf("\r\n----------SC---------------------------\r\n");
    for (int i=0;i<KERNELSTRUCTUREENTRIESNB;i++)
    {
        /*SCEntry_t* entry = (SCEntry_t*)(kernel_structure_start_addr + scoffset + i*scentrylength);
        printf("%x:SC\t",    entry);
        printf("%-10x|",
                                                entry->origin);
        printf("%-10x\r\n",
                                                entry->next);*/

        paddr blockentryadddr = &ks->blocks[i];
        paddr scentryadddr = &ks->sc[i];
        printf("%p:SC\t%p|%p\r\n",  scentryadddr,
                                                readSCOriginFromBlockEntryAddr(blockentryadddr),
                                                readSCNextFromBlockEntryAddr(blockentryadddr));
    }

    printf("\r\n----------next = %p----------------------\r\n", (void *) ks->next);
#endif // DUMP
}

/*!
 * \fn void dump_partition(paddr part)
 * \brief Displays the partition by displaying the PD structure and kernel structure linked list.
 * \param part The address of the partition to display
 * \return void
 */
void dump_partition(paddr part)
{
#if defined DUMP
    dump_PD_structure(part);
    PDTable_t* pdt = (PDTable_t*) part;
    paddr kernel_structure = pdt->structure;
    while(kernel_structure != NULL)
    {
        dump_kernel_structure(kernel_structure);
        kernel_structure = readNextFromKernelStructureStart(kernel_structure);
    }
#endif // DUMP
}

/*!
 * \deprecated This function uses the old API and is no longer functional
 * \fn void dump_ancestors(paddr base_child_PD)
 * \brief Displays all ancestor partitions of <base_child_PD>.
 * \param base_child_PD The address of the base child partition to start from
 * \return void
 */
void dump_ancestors(paddr base_child_PD)
{
#if defined DUMP
    paddr root_partition = getRootPartition();
    while(base_child_PD != root_partition){
        dump_partition(base_child_PD);
        base_child_PD = readPDParent(base_child_PD);
    }
    if(base_child_PD == root_partition)
        dump_partition(root_partition);
#endif // DUMP
}

/**
 * @brief Print MPU settings
 * @return 0 on success
 * @return <0 on failure
 */
int dump_mpu()
{
#if defined DUMP
	// Printf MPU settings
    #if defined(__ARM_ARCH_7M__) || defined(__ARM_ARCH_7EM__)

    mpu_enabled() ? printf("\r\n\r\nMPU is enabled\r\n") : printf("\r\nMPU is disabled\r\n");
    ((MPU->CTRL & MPU_CTRL_PRIVDEFENA_Msk) != 0) ? printf("PRIVDEFENA set\r\n") : printf("PRIVDEFENA NOT set\r\n");
    printf("MPU settings:\r\n");
	for (uint32_t i = 0; i < MPU_NUM_REGIONS ; i++){
        MPU->RNR  = i;
        uint32_t* start = readPhysicalMPUStartAddr(i);
        uint32_t* end = readPhysicalMPUEndAddr(i);
        uint32_t AP = readPhysicalMPUAP(i);
        uint32_t XNbit = !readPhysicalMPUXN(i);
        uint32_t regionsize =  readPhysicalMPUSizeBytes(i);
        uint32_t size = readPhysicalMPUSizeBits(i);
        uint32_t enable = readPhysicalMPURegionEnable(i);

        printf("%u:MPU->RBAR =%x, start=%p\n", i, MPU->RBAR, (void *) start);// size=%d, AP=%d, X=%d,
        printf("%u:MPU->RASR =%x, end=%p, regionsize=(2^(%u+1)=%u, AP=%u, XNbit=%u, enable=%u\n",
                                                    i,
                                                    MPU->RASR,
                                                    (void *) end,
                                                    size,
                                                    regionsize,
                                                    AP,
                                                    XNbit,
                                                    enable);
    }
    printf("\r\n");
    #endif
    #if defined(__ARM_ARCH_8M_MAIN__) || defined(__ARM_ARCH_8M_BASE__)
    return -1;
    #endif
#endif // DUMP
    return 0;
}
