/**
 * LEAPS - Low Energy Accurate Positioning System.
 *
 * UART example.
 *
 * Copyright (c) 2016-2019, LEAPS. All rights reserved.
 *
 */
#include <stdio.h>

#if defined(UART_DEBUG)
#include "uart_debug_init.h"

#define APP_ERR(err_code)	\
do {							\
	printf("\r\nerr: line(%u) code(%u)\r\n", __LINE__, (err_code));\
} while (0)						\

/* UART event handler */
void nrf_uart_event_handler(nrf_drv_uart_event_t * p_event, void * p_context)
{
	switch (p_event->type) {

		case NRF_DRV_UART_EVT_ERROR:
			nrf_drv_uart_rx_abort(&uart_instance);
			nrf_drv_uart_tx_abort(&uart_instance);
			break;
		case NRF_DRV_UART_EVT_RX_DONE:
		default:
			break;
	}
}

void init_uart()
{
    uint32_t err_code = NRF_SUCCESS;
    const char *ok_msg = "\n\rUART ready!\r\n";
    const char *err_msg = "ERROR! Already initialised ?\r\n";

    // Configure UART GPIOS
    config.pselrxd = 11;
    config.pseltxd = 5;
    config.use_easy_dma = false;

    // Init UART
    err_code = nrf_drv_uart_init(&uart_instance, &config, nrf_uart_event_handler);
    if (err_code == NRF_SUCCESS)
            nrf_drv_uart_tx(&uart_instance, (uint8_t const *)ok_msg, strlen(ok_msg)); //INIT SUCCESS
    else
            nrf_drv_uart_tx(&uart_instance, (uint8_t const *)err_msg, strlen(err_msg)); // INIT FAILED

    while (nrf_drv_uart_tx_in_progress(&uart_instance)) {}// wait for end of transmission

    // Initial message: printf is now sending through UART (message doubled if Trace is on)
    //printf("\r\nHello World!\r\n");
}
#endif // UART_DEBUG



