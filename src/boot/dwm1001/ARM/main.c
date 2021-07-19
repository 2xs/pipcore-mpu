#include <stdio.h>
#include "maldefines.h"
#include "nrf52.h"
#include "pip_debug.h"

#if defined(UART_DEBUG)
#include "uart_debug_init.h"
#endif // UART_DEBUG

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
 * If UART_DEBUG, sends printf messages on UART
 * If -DTRACE -DOS_USE_TRACE_SEMIHOSTING_DEBUG flags are set, send printf messages on the semihosting debug channel
 */
int main (int argc, char* argv[])
{


	/*
	// At this point, mmu is still not enabled.
	ial_get_ctx_addr(0, getRootPartition(), &ctx_p, &ctx_v);

	return ial_prepare_yield(getRootPartition(), ctx_v);*/

	// cpu_switch_context_exit(); -> Yield, switch to root partition

  // yield partition 0
#if defined(UART_DEBUG)
  init_uart();
#endif // UART_DEBUG

#if defined(TRACE)
  const char* trace_msg = "Trace is on\r\n";
  trace_printf((uint8_t const *)trace_msg);
#endif // TRACE

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

  printf(MSG_INIT);

  puts("Hello World");

  int i;

  for (i = 0; i < 20; i++) {
    printf("Hello World %d!\n", i);
  }
  while (1);
}

