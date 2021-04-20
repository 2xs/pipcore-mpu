#include "mal.h"
#include <stdio.h>

/*!
 * \fn void dump_PD_structure(paddr pd)
 * \brief Displays the PD structure at address <pd>.
 * \param pd The address of PD structure to display
 * \return void
 */
void dump_PD_structure(paddr pd)
{
    PDTable_t* pdt = (PDTable_t*) pd;
    printf("\r\n----------PD %x (size: %d/%d)------------\r\n", pdt, sizeof(PDTable_t), PDSTRUCTURETOTALLENGTH());
    printf("%x:PD\t%x\r\n", &(pdt->structure), pdt->structure);
    printf("%x:PD\t%x\r\n", &(pdt->firstfreeslot), pdt->firstfreeslot);
    printf("%x:PD\t%u\r\n", &(pdt->nbfreeslots), pdt->nbfreeslots);
    printf("%x:PD\t%u\r\n", &(pdt->nbprepare), pdt->nbprepare);
    printf("%x:PD\t%x\r\n", &(pdt->parent), pdt->parent);
    printf("%x:PD\t", &(pdt->blocks));
    for(int i = 0 ; i < MPU_REGIONS_NB ; i++)
    {
        printf(" %x ", (pdt->blocks[i]));
    }
    printf("\r\n%x:PD\t", &(pdt->LUT));
    for(int i = 0 ; i < MPU_REGIONS_NB ; i++)
    {
        printf(" %x ", (pdt->LUT[i*2]));
        printf(" %x ", (pdt->LUT[i*2+1]));
    }
    printf("\r\n");
}

/*!
 * \fn vvoid dump_kernel_structure(paddr kernel_structure_start_addr)
 * \brief Displays the kernel structure at <kernel_structure_start_address>.
 * \param kernel_structure_start_addr The start address of the kernel structure to display
 * \return void
 */
void dump_kernel_structure(paddr kernel_structure_start_addr)
{
    printf("\r\n----------Kernel structure %x (size: %d)----\r\n", kernel_structure_start_addr,
                                                                KERNELSTRUCTURETOTALLENGTH());
    printf("\r\n----------MPU---------------------------\r\n");
    for (int i=0;i<kernelstructureentriesnb;i++)
    {
        /*MPUEntry_t* entry = (MPUEntry_t*)(kernel_structure_start_addr + i*mpuentrylength);
        printf("%x:",    entry);
        printf("%-1d:MPU\t",
                                                (entry->mpuindex).MPUi);
        printf("%-10x|",
                                                (entry->mpublock).startAddr);
        printf("%-10x|",
                                                (entry->mpublock).endAddr);
        printf("%-1u|",
                                                entry->accessible);
        printf("%-1u\r\n",
                                                entry->present);*/
        paddr mpuentryadddr = kernel_structure_start_addr + i*mpuentrylength;
        printf("%x:%-1d:MPU\t%-10x|%-10x|%-1u|%-1u\r\n",    mpuentryadddr,
                                                            readMPUIndexFromMPUEntryAddr(mpuentryadddr),
                                                            readMPUStartFromMPUEntryAddr(mpuentryadddr),
                                                            readMPUEndFromMPUEntryAddr(mpuentryadddr),
                                                            readMPUAccessibleFromMPUEntryAddr(mpuentryadddr),
                                                            readMPUPresentFromMPUEntryAddr(mpuentryadddr));
    }
    printf("\r\n----------SH1---------------------------\r\n");
    for (int i=0;i<kernelstructureentriesnb;i++)
    {
        /*Sh1Entry_t* entry = (Sh1Entry_t*)(kernel_structure_start_addr + sh1offset + i*sh1entrylength);
        printf("%x:SH1\t",    entry);
        printf("%-10x|",
                                                entry->PDchild);
        printf("%-1u|",
                                                entry->PDflag);
        printf("%-10x\r\n",
                                                entry->inChildLocation);*/

        paddr sh1entryadddr = kernel_structure_start_addr + sh1offset + i*sh1entrylength;
        printf("%x:SH1\t%-10x|%-1u|%-10x\r\n",  sh1entryadddr,
                                                readSh1PDChildFromMPUEntryAddr(sh1entryadddr),
                                                readSh1PDFlagFromMPUEntryAddr(sh1entryadddr),
                                                readSh1InChildLocationFromMPUEntryAddr(sh1entryadddr));
    }
    printf("\r\n----------SC---------------------------\r\n");
    for (int i=0;i<kernelstructureentriesnb;i++)
    {
        /*SCEntry_t* entry = (SCEntry_t*)(kernel_structure_start_addr + scoffset + i*scentrylength);
        printf("%x:SC\t",    entry);
        printf("%-10x|",
                                                entry->origin);
        printf("%-10x\r\n",
                                                entry->next);*/
        paddr scentryadddr = kernel_structure_start_addr + scoffset + i*scentrylength;
        printf("%x:SC\t%-10x|%-1u|%-10x\r\n",  scentryadddr,
                                                readSCOriginFromMPUEntryAddr(scentryadddr),
                                                readSCNextFromMPUEntryAddr(scentryadddr));
    }

    printf("\r\n----------next = %x----------------------\r\n", *(kernel_structure_start_addr + nextoffset));

}

/*!
 * \fn void dump_partition(paddr part)
 * \brief Displays the partition by displaying the PD structure and kernel structure linked list.
 * \param part The address of the partition to display
 * \return void
 */
void dump_partition(paddr part)
{
    dump_PD_structure(part);
    PDTable_t* pdt = (PDTable_t*) part;
    paddr kernel_structure = pdt->structure;
    while(kernel_structure != NULL)
    {
        dump_kernel_structure(kernel_structure);
        kernel_structure = readNextFromKernelStructureStart(kernel_structure);
    }
}

/*!
 * \fn void dump_ancestors(paddr base_child_PD)
 * \brief Displays all ancestor partitions of <base_child_PD>.
 * \param base_child_PD The address of the base child partition to start from
 * \return void
 */
void dump_ancestors(paddr base_child_PD)
{
    paddr root_partition = getRootPartition();
    while(base_child_PD != root_partition){
        dump_partition(base_child_PD);
        base_child_PD = readPDParent(base_child_PD);
    }
    if(base_child_PD == root_partition)
        dump_partition(root_partition);
}
