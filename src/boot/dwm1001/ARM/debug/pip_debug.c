#include "mal.h"
#include <stdio.h>
#include "mpu.h"

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
    printf("\r\n----------PD %x (size: %d/%d)------------\r\n", pdt, sizeof(PDTable_t), PDSTRUCTURETOTALLENGTH());
    printf("%x:PD\t%x\r\n", &(pdt->structure), pdt->structure);
    printf("%x:PD\t%x\r\n", &(pdt->firstfreeslot), pdt->firstfreeslot);
    printf("%x:PD\t%u\r\n", &(pdt->nbfreeslots), pdt->nbfreeslots);
    printf("%x:PD\t%u\r\n", &(pdt->nbprepare), pdt->nbprepare);
    printf("%x:PD\t%x\r\n", &(pdt->parent), pdt->parent);
    printf("%x:PD\t", &(pdt->mpu));
    for(int i = 0 ; i < MPU_REGIONS_NB ; i++)
    {
        printf(" %x ", (pdt->mpu[i]));
    }
    printf("\r\n%x:PD\t", &(pdt->LUT));
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
    printf("\r\n----------Kernel structure %x (size: %d)----\r\n", kernel_structure_start_addr,
                                                                KERNELSTRUCTURETOTALLENGTH());
    printf("\r\n----------BLOCKS---------------------------\r\n");
    for (int i=0;i<KERNELSTRUCTUREENTRIESNB;i++)
    {
        paddr blockentryadddr = &ks->blocks[i];
        printf("%x:%-1d:BLK\t%-10x|%-10x\t|%-1u|%-1u|%-1u%-1u%-1u\r\n",    blockentryadddr,
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
        printf("%x:SH1\t%-10x|%-1u|%-10x\r\n",  sh1entryadddr,
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
        printf("%x:SC\t%-10x|%-10x\r\n",  scentryadddr,
                                                readSCOriginFromBlockEntryAddr(blockentryadddr),
                                                readSCNextFromBlockEntryAddr(blockentryadddr));
    }

    printf("\r\n----------next = %x----------------------\r\n", ks->next);
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
	for (int i = 0; i < MPU_NUM_REGIONS ; i++){
        MPU->RNR  = i;
        uint32_t* start = readPhysicalMPUStartAddr(i);
        uint32_t* end = readPhysicalMPUEndAddr(i);
        uint32_t AP = readPhysicalMPUAP(i);
        uint32_t XNbit = !readPhysicalMPUXN(i);
        uint32_t regionsize =  readPhysicalMPUSizeBytes(i);
        uint32_t size = readPhysicalMPUSizeBits(i);
        uint32_t enable = readPhysicalMPURegionEnable(i);

        printf("%d:MPU->RBAR =%x, start=%x\n", i, MPU->RBAR, start);// size=%d, AP=%d, X=%d,
        printf("%d:MPU->RASR =%x, end=%x, regionsize=(2^(%d+1)=%d, AP=%d, XNbit=%d, enable=%d\n",
                                                    i,
                                                    MPU->RASR,
                                                    end,
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
