#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
#include "maldefines.h"
#include "nrf52.h"
#include "core_cm4.h"
#include "pip_debug.h"

#if defined(DEBUG_UART)
#include "uart_debug_init.h"
#endif // DEBUG_UART

#if defined(TRACE)
#include "Trace.h"
#endif // TRACE

#define MSG_INIT	\
	"\r\n\n"	\
	"App   :  Pip-MPU\n\r"	\
	"Built :  " __DATE__ " " __TIME__ "\n"	\
	"\r\n"

// End address for the user section; defined in linker script
extern uint32_t user_mem_end;

/**
 * Main entry point.
 * If -DDEBUG_UART flag is set, sends printf messages on UART
 * If -DTRACE -DOS_USE_TRACE_SEMIHOSTING_DEBUG flags are set, send printf messages on the semihosting debug channel
 */
int main (int argc, char* argv[])
{
  // Check the MPU
  if (checkMPU()<0)
  {
    // the check doesn't pass, panic since Pip relies on the MPU
    printf("DEBUG: (kernel) MPU ERROR");
    while(1);
  }

	/* Initialize the root partition */
	mal_init();

  paddr root = getRootPartition();
  dump_partition(root);
  activate(root);

  // set PSP to root stack and switch to unprivileged mode
  __set_PSP(&user_mem_end);
  __set_CONTROL(__get_CONTROL() |
                CONTROL_SPSEL_Msk | // use psp
                CONTROL_nPRIV_Msk ); // switch to unprivileged Thread Mode
  __ISB();

	/*
	// At this point, mmu is still not enabled.
	ial_get_ctx_addr(0, getRootPartition(), &ctx_p, &ctx_v);

	return ial_prepare_yield(getRootPartition(), ctx_v);*/

	// cpu_switch_context_exit(); -> Yield, switch to root partition

  // yield partition 0
  #if defined(DEBUG_UART)
  init_uart();
  #endif // DEBUG_UART

  #if defined(TRACE)
  const char* trace_msg = "Trace is on\r\n";
  trace_printf((uint8_t const *)trace_msg);
  #endif // TRACE

  printf(MSG_INIT);

  puts("Hello World");

  int i;

  for (i = 0; i < 20; i++) {
    printf("Hello World %d!\n", i);
  }
  do {
    i++;
  } while (1);
}

