#include <stdio.h>

#if defined(UART_DEBUG)
#include "uart_debug_init.h"
#endif // UART_DEBUG

#if defined(TRACE)
#include "Trace.h"
#endif // TRACE

// Override the 'write' clib method to implement 'printf' over UART.
int _write( int handle, char* data, int size ) {
    const char * nl = "\r\n";

    #if defined(TRACE)
    // Trace message
    trace_write (data, size);
    #endif // TRACE

    #if defined(UART_DEBUG)
    // Message by UART
    nrf_drv_uart_tx(&uart_instance, (const char *)data, strlen(data));
    while (nrf_drv_uart_tx_in_progress(&uart_instance)){} // Wait end of TX
    #endif // UART_DEBUG

    return size;
}
