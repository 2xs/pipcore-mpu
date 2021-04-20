#include <stdio.h>

void dump_PD_structure(paddr pd);
void dump_kernel_structure(paddr kernel_structure_start_addr);
void dump_partition(paddr part);
void dump_ancestors(paddr base_child_PD_address);
