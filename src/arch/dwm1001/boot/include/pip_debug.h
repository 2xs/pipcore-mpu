#ifndef __PIP_DEBUG__
#define __PIP_DEBUG__

void dump_PD_structure(paddr pd);
void dump_kernel_structure(paddr kernel_structure_start_addr);
void dump_partition(paddr part);
void dump_ancestors(paddr base_child_PD_address);
int dump_mpu();


#if defined DUMP
#define debug_printf(fmt, ...) do {printf(fmt, __VA_ARGS__); } while (0)
//#define debug_puts(...) do {puts(__VA_ARGS__); } while (0) // TODO: fix no output -> triggers HardFault
#else
#define debug_printf(fmt, ...) (void)0
//#define debug_puts(X) (void) 0
#endif

#endif // __PIP_DEBUG__
