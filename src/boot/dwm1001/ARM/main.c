#include <stdio.h>
#include "maldefines.h"
#include "nrf52.h"
#include "pip_debug.h"
#include "main_user_app.h"

#if defined(UART_DEBUG)
#include "uart_debug_init.h"
#endif // UART_DEBUG

#if defined(TRACE)
#include "Trace.h"
#endif // TRACE

// Stack end address for the user section; defined in linker script
extern uint32_t user_stack_top;

extern paddr blockentryaddr_flash;
extern paddr blockentryaddr_ram0;
extern paddr blockentryaddr_ram1;
extern paddr blockentryaddr_ram2;
extern paddr blockentryaddr_periph;

void main_user_app_trampoline(int argc, char* argv[]);

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

  // Initialize the root partition
  mal_init();

  paddr root = getRootPartition();
  dump_partition(root);
  activate(root);

  // set PSP to root stack and switch to unprivileged mode
  uint32_t psp = (uint32_t) &user_stack_top; // stack starts one address down to match the stack MPU region
  __set_PSP(psp);

  __set_CONTROL(__get_CONTROL() |
                CONTROL_SPSEL_Msk);// use psp

  uint32_t* initial_blocks[6] = { root,
                                  blockentryaddr_flash,
                                  blockentryaddr_ram0,
                                  blockentryaddr_ram1,
                                  blockentryaddr_ram2,
                                  blockentryaddr_periph};

  main_user_app_trampoline(6, (char**)initial_blocks);

  while(1);
}

void main_user_app_trampoline(int argc, char* argv[])
{
  __set_CONTROL(__get_CONTROL() |
                CONTROL_nPRIV_Msk ); // switch to unprivileged Thread Mode
  __DMB();
  __ISB();
  __DSB();

  /********************** Start of user application ************************/
  main_user_app(argc, argv);
  printf("App ended\n\r");
}
