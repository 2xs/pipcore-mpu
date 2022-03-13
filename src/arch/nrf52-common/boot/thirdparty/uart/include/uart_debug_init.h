#include "nrf_drv_uart.h"
#include "sdk_common.h"

static nrf_drv_uart_t uart_instance = NRF_DRV_UART_INSTANCE(0);
static nrf_drv_uart_config_t config = NRF_DRV_UART_DEFAULT_CONFIG;

/**
 * @brief Function for initializing  the UART driver and sends a greeting message through UART.
 */
void init_uart();
