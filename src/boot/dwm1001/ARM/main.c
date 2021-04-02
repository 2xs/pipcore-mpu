#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>

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


/**
 * Main entry point.
 * If -DDEBUG_UART flag is set, sends printf messages on UART
 * If -DTRACE -DOS_USE_TRACE_SEMIHOSTING_DEBUG flags are set, send printf messages on the semihosting debug channel
 */
void main(void)
{
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

