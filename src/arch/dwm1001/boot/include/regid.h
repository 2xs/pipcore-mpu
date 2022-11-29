/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2022)                */
/*                                                                             */
/*  This software is a computer program whose purpose is to run a minimal,     */
/*  hypervisor relying on proven properties such as memory isolation.          */
/*                                                                             */
/*  This software is governed by the CeCILL license under French law and       */
/*  abiding by the rules of distribution of free software.  You can  use,      */
/*  modify and/ or redistribute the software under the terms of the CeCILL     */
/*  license as circulated by CEA, CNRS and INRIA at the following URL          */
/*  "http://www.cecill.info".                                                  */
/*                                                                             */
/*  As a counterpart to the access to the source code and  rights to copy,     */
/*  modify and redistribute granted by the license, users are provided only    */
/*  with a limited warranty  and the software's author,  the holder of the     */
/*  economic rights,  and the successive licensors  have only  limited         */
/*  liability.                                                                 */
/*                                                                             */
/*  In this respect, the user's attention is drawn to the risks associated     */
/*  with loading,  using,  modifying and/or developing or reproducing the      */
/*  software by the user in light of its specific status of free software,     */
/*  that may mean  that it is complicated to manipulate,  and  that  also      */
/*  therefore means  that it is reserved for developers  and  experienced      */
/*  professionals having in-depth computer knowledge. Users are therefore      */
/*  encouraged to load and test the software's suitability as regards their    */
/*  requirements in conditions enabling the security of their systems and/or   */
/*  data to be ensured and,  more generally, to use and operate it in the      */
/*  same conditions as regards security.                                       */
/*                                                                             */
/*  The fact that you are presently reading this means that you have had       */
/*  knowledge of the CeCILL license and that you accept its terms.             */
/*******************************************************************************/

#ifndef __REGID_H__
#define __REGID_H__

#define EXPAND_AS_INDEX(id, reg, ...) \
	PIP_##id##_##reg##_INDEX

#define EXPAND_AS_INDEX_BASE(id, reg, ...) \
	PIP_##id##_##reg##_INDEX = 0

#define EXPAND_AS_REGISTER(id, reg, ...) \
	PIP_##id##_##reg

#define EXPAND_AS_REGISTER_BASE(id, reg, ...) \
	PIP_##id##_BASE, \
	PIP_##id##_##reg = PIP_##id##_BASE

#define EXPAND_INSTANCE_AS_INDEX(inst, base) \
	inst(base, EXPAND_AS_INDEX_BASE, EXPAND_AS_INDEX)

#define EXPAND_INSTANCE_AS_REGISTER(inst, base) \
	inst(base, EXPAND_AS_REGISTER_BASE, EXPAND_AS_REGISTER)

// =========================================================================
// =========================================================================
// =========================================================================

#define NRF_FICR_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_FICR_FICR, DEVICEID_0, registerAccessReadWrite, base, 0x060), \
	macro_b(NRF_FICR_FICR, DEVICEADDRTYPE, registerAccessReadWrite, base, 0x0A0), \
	macro_b(NRF_FICR_FICR, DEVICEADDR_0, registerAccessReadWrite, base, 0x0A4), \
	macro_b(NRF_FICR_FICR, DEVICEADDR_1, registerAccessReadWrite, base, 0x0A8)

#define NRF_POWER_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_POWER_POWER, SYSTEMOFF, registerAccessReadWrite, base, 0x500), \
	macro_b(NRF_POWER_POWER, RAMON, registerAccessReadWrite, base, 0x524), \
	macro_b(NRF_POWER_POWER, DCDCEN, registerAccessReadWrite, base, 0x578), \
	macro_b(NRF_POWER_POWER, RAM_0_POWERCLR, registerAccessReadWrite, base, 0x908), \
	macro_b(NRF_POWER_POWER, RAM_1_POWERCLR, registerAccessReadWrite, base, 0x918), \
	macro_b(NRF_POWER_POWER, RAM_2_POWERCLR, registerAccessReadWrite, base, 0x928), \
	macro_b(NRF_POWER_POWER, RAM_3_POWERCLR, registerAccessReadWrite, base, 0x938), \
	macro_b(NRF_POWER_POWER, RAM_4_POWERCLR, registerAccessReadWrite, base, 0x948), \
	macro_b(NRF_POWER_POWER, RAM_5_POWERCLR, registerAccessReadWrite, base, 0x958), \
	macro_b(NRF_POWER_POWER, RAM_6_POWERCLR, registerAccessReadWrite, base, 0x968), \
	macro_b(NRF_POWER_POWER, RAM_7_POWERCLR, registerAccessReadWrite, base, 0x978)

#define NRF_CLOCK_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_CLOCK_CLOCK, TASKS_HFCLKSTART, registerAccessReadWrite, base, 0x000), \
	macro_b(NRF_CLOCK_CLOCK, TASKS_HFCLKSTOP, registerAccessReadWrite, base, 0x004), \
	macro_b(NRF_CLOCK_CLOCK, TASKS_LFCLKSTART, registerAccessReadWrite, base, 0x008), \
	macro_b(NRF_CLOCK_CLOCK, TASKS_LFCLKSTOP, registerAccessReadWrite, base, 0x00C), \
	macro_b(NRF_CLOCK_CLOCK, TASKS_CAL, registerAccessReadWrite, base, 0x010), \
	macro_b(NRF_CLOCK_CLOCK, EVENTS_HFCLKSTARTED, registerAccessReadWrite, base, 0x100), \
	macro_b(NRF_CLOCK_CLOCK, EVENTS_LFCLKSTARTED, registerAccessReadWrite, base, 0x104), \
	macro_b(NRF_CLOCK_CLOCK, EVENTS_DONE, registerAccessReadWrite, base, 0x10C), \
	macro_b(NRF_CLOCK_CLOCK, EVENTS_CTTO, registerAccessReadWrite, base, 0x110), \
	macro_b(NRF_CLOCK_CLOCK, LFCLKSTAT, registerAccessReadWrite, base, 0x418), \
	macro_b(NRF_CLOCK_CLOCK, LFCLKSRC, registerAccessReadWrite, base, 0x518)

#define NRF_RADIO_ERRATA_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_RADIO_ERRATA, ERRATA_32, registerAccessReadWrite, base, 0x5A0)

#define NRF_RADIO_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_RADIO_RADIO, TASKS_TXEN, registerAccessReadWrite, base, 0x000), \
	macro_b(NRF_RADIO_RADIO, TASKS_RXEN, registerAccessReadWrite, base, 0x004), \
	macro_b(NRF_RADIO_RADIO, TASKS_START, registerAccessReadWrite, base, 0x008), \
	macro_b(NRF_RADIO_RADIO, TASKS_DISABLE, registerAccessReadWrite, base, 0x010), \
	macro_b(NRF_RADIO_RADIO, EVENTS_READY, registerAccessReadWrite, base, 0x100), \
	macro_b(NRF_RADIO_RADIO, EVENTS_ADDRESS, registerAccessReadWrite, base, 0x104), \
	macro_b(NRF_RADIO_RADIO, EVENTS_END, registerAccessReadWrite, base, 0x10C), \
	macro_b(NRF_RADIO_RADIO, EVENTS_DISABLED, registerAccessReadWrite, base, 0x110), \
	macro_b(NRF_RADIO_RADIO, EVENTS_DEVMATCH, registerAccessReadWrite, base, 0x114), \
	macro_b(NRF_RADIO_RADIO, EVENTS_RSSIEND, registerAccessReadWrite, base, 0x11C), \
	macro_b(NRF_RADIO_RADIO, EVENTS_BCMATCH, registerAccessReadWrite, base, 0x128), \
	macro_b(NRF_RADIO_RADIO, EVENTS_CRCOK, registerAccessReadWrite, base, 0x130), \
	macro_b(NRF_RADIO_RADIO, SHORTS, registerAccessReadWrite, base, 0x200), \
	macro_b(NRF_RADIO_RADIO, INTENSET, registerAccessReadWrite, base, 0x304), \
	macro_b(NRF_RADIO_RADIO, INTENCLR, registerAccessReadWrite, base, 0x308), \
	macro_b(NRF_RADIO_RADIO, CRCSTATUS, registerAccessReadWrite, base, 0x400), \
	macro_b(NRF_RADIO_RADIO, PACKETPTR, registerAccessReadWrite, base, 0x504), \
	macro_b(NRF_RADIO_RADIO, FREQUENCY, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_RADIO_RADIO, TXPOWER, registerAccessReadWrite, base, 0x50C), \
	macro_b(NRF_RADIO_RADIO, MODE, registerAccessReadWrite, base, 0x510), \
	macro_b(NRF_RADIO_RADIO, PCNF0, registerAccessReadWrite, base, 0x514), \
	macro_b(NRF_RADIO_RADIO, PCNF1, registerAccessReadWrite, base, 0x518), \
	macro_b(NRF_RADIO_RADIO, BASE0, registerAccessReadWrite, base, 0x51C), \
	macro_b(NRF_RADIO_RADIO, BASE1, registerAccessReadWrite, base, 0x520), \
	macro_b(NRF_RADIO_RADIO, PREFIX0, registerAccessReadWrite, base, 0x524), \
	macro_b(NRF_RADIO_RADIO, TXADDRESS, registerAccessReadWrite, base, 0x52C), \
	macro_b(NRF_RADIO_RADIO, RXADDRESSES, registerAccessReadWrite, base, 0x530), \
	macro_b(NRF_RADIO_RADIO, CRCCNF, registerAccessReadWrite, base, 0x534), \
	macro_b(NRF_RADIO_RADIO, CRCPOLY, registerAccessReadWrite, base, 0x538), \
	macro_b(NRF_RADIO_RADIO, CRCINIT, registerAccessReadWrite, base, 0x53C), \
	macro_b(NRF_RADIO_RADIO, TIFS, registerAccessReadWrite, base, 0x544), \
	macro_b(NRF_RADIO_RADIO, RSSISAMPLE, registerAccessReadWrite, base, 0x548), \
	macro_b(NRF_RADIO_RADIO, STATE, registerAccessReadWrite, base, 0x550), \
	macro_b(NRF_RADIO_RADIO, DATAWHITEIV, registerAccessReadWrite, base, 0x554), \
	macro_b(NRF_RADIO_RADIO, BCC, registerAccessReadWrite, base, 0x560), \
	macro_b(NRF_RADIO_RADIO, DAB_0, registerAccessReadWrite, base, 0x600), \
	macro_b(NRF_RADIO_RADIO, DAB_1, registerAccessReadWrite, base, 0x604), \
	macro_b(NRF_RADIO_RADIO, DAB_2, registerAccessReadWrite, base, 0x608), \
	macro_b(NRF_RADIO_RADIO, DAB_3, registerAccessReadWrite, base, 0x60c), \
	macro_b(NRF_RADIO_RADIO, DAB_4, registerAccessReadWrite, base, 0x610), \
	macro_b(NRF_RADIO_RADIO, DAB_5, registerAccessReadWrite, base, 0x614), \
	macro_b(NRF_RADIO_RADIO, DAB_6, registerAccessReadWrite, base, 0x618), \
	macro_b(NRF_RADIO_RADIO, DAB_7, registerAccessReadWrite, base, 0x61c), \
	macro_b(NRF_RADIO_RADIO, DAP_0, registerAccessReadWrite, base, 0x620), \
	macro_b(NRF_RADIO_RADIO, DAP_1, registerAccessReadWrite, base, 0x624), \
	macro_b(NRF_RADIO_RADIO, DAP_2, registerAccessReadWrite, base, 0x628), \
	macro_b(NRF_RADIO_RADIO, DAP_3, registerAccessReadWrite, base, 0x62c), \
	macro_b(NRF_RADIO_RADIO, DAP_4, registerAccessReadWrite, base, 0x630), \
	macro_b(NRF_RADIO_RADIO, DAP_5, registerAccessReadWrite, base, 0x634), \
	macro_b(NRF_RADIO_RADIO, DAP_6, registerAccessReadWrite, base, 0x638), \
	macro_b(NRF_RADIO_RADIO, DAP_7, registerAccessReadWrite, base, 0x63c), \
	macro_b(NRF_RADIO_RADIO, DACNF, registerAccessReadWrite, base, 0x640), \
	macro_b(NRF_RADIO_RADIO, MODECNF0, registerAccessReadWrite, base, 0x650), \
	macro_b(NRF_RADIO_RADIO, ERRATA_102_106_107, registerAccessReadWrite, base, 0x774), \
	macro_b(NRF_RADIO_RADIO, POWER, registerAccessReadWrite, base, 0xFFC)

#define NRF_PPI_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_PPI_PPI, CHEN, registerAccessReadWrite, base, 0x500), \
	macro_b(NRF_PPI_PPI, CHENSET, registerAccessReadWrite, base, 0x504), \
	macro_b(NRF_PPI_PPI, CHENCLR, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_PPI_PPI, CH_0_EEP, registerAccessReadWrite, base, 0x510), \
	macro_b(NRF_PPI_PPI, CH_0_TEP, registerAccessReadWrite, base, 0x514), \
	macro_b(NRF_PPI_PPI, CH_1_EEP, registerAccessReadWrite, base, 0x518), \
	macro_b(NRF_PPI_PPI, CH_1_TEP, registerAccessReadWrite, base, 0x51C), \
	macro_b(NRF_PPI_PPI, CH_2_EEP, registerAccessReadWrite, base, 0x520), \
	macro_b(NRF_PPI_PPI, CH_2_TEP, registerAccessReadWrite, base, 0x524), \
	macro_b(NRF_PPI_PPI, CH_3_EEP, registerAccessReadWrite, base, 0x528), \
	macro_b(NRF_PPI_PPI, CH_3_TEP, registerAccessReadWrite, base, 0x52C), \
	macro_b(NRF_PPI_PPI, CH_4_EEP, registerAccessReadWrite, base, 0x530), \
	macro_b(NRF_PPI_PPI, CH_4_TEP, registerAccessReadWrite, base, 0x534), \
	macro_b(NRF_PPI_PPI, CH_5_EEP, registerAccessReadWrite, base, 0x538), \
	macro_b(NRF_PPI_PPI, CH_5_TEP, registerAccessReadWrite, base, 0x53C), \
	macro_b(NRF_PPI_PPI, CH_6_EEP, registerAccessReadWrite, base, 0x540), \
	macro_b(NRF_PPI_PPI, CH_6_TEP, registerAccessReadWrite, base, 0x544), \
	macro_b(NRF_PPI_PPI, CH_7_EEP, registerAccessReadWrite, base, 0x548), \
	macro_b(NRF_PPI_PPI, CH_7_TEP, registerAccessReadWrite, base, 0x54C), \
	macro_b(NRF_PPI_PPI, CH_8_EEP, registerAccessReadWrite, base, 0x550), \
	macro_b(NRF_PPI_PPI, CH_8_TEP, registerAccessReadWrite, base, 0x554), \
	macro_b(NRF_PPI_PPI, CH_9_EEP, registerAccessReadWrite, base, 0x558), \
	macro_b(NRF_PPI_PPI, CH_9_TEP, registerAccessReadWrite, base, 0x55C), \
	macro_b(NRF_PPI_PPI, CH_10_EEP, registerAccessReadWrite, base, 0x560), \
	macro_b(NRF_PPI_PPI, CH_10_TEP, registerAccessReadWrite, base, 0x564), \
	macro_b(NRF_PPI_PPI, CH_11_EEP, registerAccessReadWrite, base, 0x568), \
	macro_b(NRF_PPI_PPI, CH_11_TEP, registerAccessReadWrite, base, 0x56C), \
	macro_b(NRF_PPI_PPI, CH_12_EEP, registerAccessReadWrite, base, 0x570), \
	macro_b(NRF_PPI_PPI, CH_12_TEP, registerAccessReadWrite, base, 0x574), \
	macro_b(NRF_PPI_PPI, CH_13_EEP, registerAccessReadWrite, base, 0x578), \
	macro_b(NRF_PPI_PPI, CH_13_TEP, registerAccessReadWrite, base, 0x57C), \
	macro_b(NRF_PPI_PPI, CH_14_EEP, registerAccessReadWrite, base, 0x580), \
	macro_b(NRF_PPI_PPI, CH_14_TEP, registerAccessReadWrite, base, 0x584), \
	macro_b(NRF_PPI_PPI, CH_15_EEP, registerAccessReadWrite, base, 0x588), \
	macro_b(NRF_PPI_PPI, CH_15_TEP, registerAccessReadWrite, base, 0x58C), \
	macro_b(NRF_PPI_PPI, CH_16_EEP, registerAccessReadWrite, base, 0x590), \
	macro_b(NRF_PPI_PPI, CH_16_TEP, registerAccessReadWrite, base, 0x594), \
	macro_b(NRF_PPI_PPI, CH_17_EEP, registerAccessReadWrite, base, 0x598), \
	macro_b(NRF_PPI_PPI, CH_17_TEP, registerAccessReadWrite, base, 0x59C), \
	macro_b(NRF_PPI_PPI, CH_18_EEP, registerAccessReadWrite, base, 0x5A0), \
	macro_b(NRF_PPI_PPI, CH_18_TEP, registerAccessReadWrite, base, 0x5A4), \
	macro_b(NRF_PPI_PPI, CH_19_EEP, registerAccessReadWrite, base, 0x5A8), \
	macro_b(NRF_PPI_PPI, CH_19_TEP, registerAccessReadWrite, base, 0x5AC)

#define NRF_UART0_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_UART_UART0, TASKS_STARTRX, registerAccessReadWrite, base, 0x000), \
	macro_b(NRF_UART_UART0, TASKS_STARTTX, registerAccessReadWrite, base, 0x008), \
	macro_b(NRF_UART_UART0, TASKS_SUSPEND, registerAccessReadWrite, base, 0x01C), \
	macro_b(NRF_UART_UART0, EVENTS_RXDRDY, registerAccessReadWrite, base, 0x108), \
	macro_b(NRF_UART_UART0, EVENTS_TXDRDY, registerAccessReadWrite, base, 0x11C), \
	macro_b(NRF_UART_UART0, INTENSET, registerAccessReadWrite, base, 0x304), \
	macro_b(NRF_UART_UART0, ENABLE, registerAccessReadWrite, base, 0x500), \
	macro_b(NRF_UART_UART0, PSELRTS, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_UART_UART0, PSELTXD, registerAccessReadWrite, base, 0x50C), \
	macro_b(NRF_UART_UART0, PSELCTS, registerAccessReadWrite, base, 0x510), \
	macro_b(NRF_UART_UART0, PSELRXD, registerAccessReadWrite, base, 0x514), \
	macro_b(NRF_UART_UART0, RXD, registerAccessReadWrite, base, 0x518), \
	macro_b(NRF_UART_UART0, TXD, registerAccessReadWrite, base, 0x51C), \
	macro_b(NRF_UART_UART0, BAUDRATE, registerAccessReadWrite, base, 0x524), \
	macro_b(NRF_UART_UART0, CONFIG, registerAccessReadWrite, base, 0x56C)

#define NRF_SPIM0_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_SPIM_SPIM0, TASKS_START, registerAccessReadWrite, base, 0x010), \
	macro_b(NRF_SPIM_SPIM0, TASKS_STOP, registerAccessReadWrite, base, 0x014), \
	macro_b(NRF_SPIM_SPIM0, EVENTS_END, registerAccessReadWrite, base, 0x118), \
	macro_b(NRF_SPIM_SPIM0, INTENSET, registerAccessReadWrite, base, 0x304), \
	macro_b(NRF_SPIM_SPIM0, INTENCLR, registerAccessReadWrite, base, 0x308), \
	macro_b(NRF_SPIM_SPIM0, ENABLE, registerAccessReadWrite, base, 0x500), \
	macro_b(NRF_SPIM_SPIM0, PSEL_SCK, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_SPIM_SPIM0, PSEL_MOSI, registerAccessReadWrite, base, 0x50C), \
	macro_b(NRF_SPIM_SPIM0, PSEL_MISO, registerAccessReadWrite, base, 0x510), \
	macro_b(NRF_SPIM_SPIM0, FREQUENCY, registerAccessReadWrite, base, 0x524), \
	macro_b(NRF_SPIM_SPIM0, RXD_PTR, registerAccessReadWrite, base, 0x534), \
	macro_b(NRF_SPIM_SPIM0, RXD_MAXCNT, registerAccessReadWrite, base, 0x538), \
	macro_b(NRF_SPIM_SPIM0, TXD_PTR, registerAccessReadWrite, base, 0x544), \
	macro_b(NRF_SPIM_SPIM0, TXD_MAXCNT, registerAccessReadWrite, base, 0x548), \
	macro_b(NRF_SPIM_SPIM0, CONFIG, registerAccessReadWrite, base, 0x554)

#define NRF_TWIM0_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_TWIM_TWIM0, TASKS_STARTRX, registerAccessReadWrite, base, 0x000), \
	macro_b(NRF_TWIM_TWIM0, TASKS_STARTTX, registerAccessReadWrite, base, 0x008), \
	macro_b(NRF_TWIM_TWIM0, EVENTS_STOPPED, registerAccessReadWrite, base, 0x104), \
	macro_b(NRF_TWIM_TWIM0, EVENTS_ERROR, registerAccessReadWrite, base, 0x124), \
	macro_b(NRF_TWIM_TWIM0, SHORTS, registerAccessReadWrite, base, 0x200), \
	macro_b(NRF_TWIM_TWIM0, INTENSET, registerAccessReadWrite, base, 0x304), \
	macro_b(NRF_TWIM_TWIM0, INTENCLR, registerAccessReadWrite, base, 0x308), \
	macro_b(NRF_TWIM_TWIM0, ERRORSRC, registerAccessReadWrite, base, 0x4C4), \
	macro_b(NRF_TWIM_TWIM0, ENABLE, registerAccessReadWrite, base, 0x500), \
	macro_b(NRF_TWIM_TWIM0, PSEL_SCL, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_TWIM_TWIM0, PSEL_SDA, registerAccessReadWrite, base, 0x50C), \
	macro_b(NRF_TWIM_TWIM0, FREQUENCY, registerAccessReadWrite, base, 0x524), \
	macro_b(NRF_TWIM_TWIM0, RXD_PTR, registerAccessReadWrite, base, 0x534), \
	macro_b(NRF_TWIM_TWIM0, RXD_MAXCNT, registerAccessReadWrite, base, 0x538), \
	macro_b(NRF_TWIM_TWIM0, TXD_PTR, registerAccessReadWrite, base, 0x544), \
	macro_b(NRF_TWIM_TWIM0, TXD_MAXCNT, registerAccessReadWrite, base, 0x548), \
	macro_b(NRF_TWIM_TWIM0, ADDRESS, registerAccessReadWrite, base, 0x588)

#define NRF_SPIM1_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_SPIM_SPIM1, TASKS_START, registerAccessReadWrite, base, 0x010), \
	macro_b(NRF_SPIM_SPIM1, TASKS_STOP, registerAccessReadWrite, base, 0x014), \
	macro_b(NRF_SPIM_SPIM1, EVENTS_END, registerAccessReadWrite, base, 0x118), \
	macro_b(NRF_SPIM_SPIM1, INTENSET, registerAccessReadWrite, base, 0x304), \
	macro_b(NRF_SPIM_SPIM1, INTENCLR, registerAccessReadWrite, base, 0x308), \
	macro_b(NRF_SPIM_SPIM1, ENABLE, registerAccessReadWrite, base, 0x500), \
	macro_b(NRF_SPIM_SPIM1, PSEL_SCK, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_SPIM_SPIM1, PSEL_MOSI, registerAccessReadWrite, base, 0x50C), \
	macro_b(NRF_SPIM_SPIM1, PSEL_MISO, registerAccessReadWrite, base, 0x510), \
	macro_b(NRF_SPIM_SPIM1, FREQUENCY, registerAccessReadWrite, base, 0x524), \
	macro_b(NRF_SPIM_SPIM1, RXD_PTR, registerAccessReadWrite, base, 0x534), \
	macro_b(NRF_SPIM_SPIM1, RXD_MAXCNT, registerAccessReadWrite, base, 0x538), \
	macro_b(NRF_SPIM_SPIM1, TXD_PTR, registerAccessReadWrite, base, 0x544), \
	macro_b(NRF_SPIM_SPIM1, TXD_MAXCNT, registerAccessReadWrite, base, 0x548), \
	macro_b(NRF_SPIM_SPIM1, CONFIG, registerAccessReadWrite, base, 0x554)

#define NRF_TWIM1_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_TWIM_TWIM1, TASKS_STARTRX, registerAccessReadWrite, base, 0x000), \
	macro_b(NRF_TWIM_TWIM1, TASKS_STARTTX, registerAccessReadWrite, base, 0x008), \
	macro_b(NRF_TWIM_TWIM1, EVENTS_STOPPED, registerAccessReadWrite, base, 0x104), \
	macro_b(NRF_TWIM_TWIM1, EVENTS_ERROR, registerAccessReadWrite, base, 0x124), \
	macro_b(NRF_TWIM_TWIM1, SHORTS, registerAccessReadWrite, base, 0x200), \
	macro_b(NRF_TWIM_TWIM1, INTENSET, registerAccessReadWrite, base, 0x304), \
	macro_b(NRF_TWIM_TWIM1, INTENCLR, registerAccessReadWrite, base, 0x308), \
	macro_b(NRF_TWIM_TWIM1, ERRORSRC, registerAccessReadWrite, base, 0x4C4), \
	macro_b(NRF_TWIM_TWIM1, ENABLE, registerAccessReadWrite, base, 0x500), \
	macro_b(NRF_TWIM_TWIM1, PSEL_SCL, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_TWIM_TWIM1, PSEL_SDA, registerAccessReadWrite, base, 0x50C), \
	macro_b(NRF_TWIM_TWIM1, FREQUENCY, registerAccessReadWrite, base, 0x524), \
	macro_b(NRF_TWIM_TWIM1, RXD_PTR, registerAccessReadWrite, base, 0x534), \
	macro_b(NRF_TWIM_TWIM1, RXD_MAXCNT, registerAccessReadWrite, base, 0x538), \
	macro_b(NRF_TWIM_TWIM1, TXD_PTR, registerAccessReadWrite, base, 0x544), \
	macro_b(NRF_TWIM_TWIM1, TXD_MAXCNT, registerAccessReadWrite, base, 0x548), \
	macro_b(NRF_TWIM_TWIM1, ADDRESS, registerAccessReadWrite, base, 0x588)

#define NRF_GPIOTE_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_GPIOTE_GPIOTE, EVENTS_IN_0, registerAccessReadWrite, base, 0x100), \
	macro_b(NRF_GPIOTE_GPIOTE, EVENTS_IN_1, registerAccessReadWrite, base, 0x104), \
	macro_b(NRF_GPIOTE_GPIOTE, EVENTS_IN_2, registerAccessReadWrite, base, 0x108), \
	macro_b(NRF_GPIOTE_GPIOTE, EVENTS_IN_3, registerAccessReadWrite, base, 0x10c), \
	macro_b(NRF_GPIOTE_GPIOTE, EVENTS_IN_4, registerAccessReadWrite, base, 0x110), \
	macro_b(NRF_GPIOTE_GPIOTE, EVENTS_IN_5, registerAccessReadWrite, base, 0x114), \
	macro_b(NRF_GPIOTE_GPIOTE, EVENTS_IN_6, registerAccessReadWrite, base, 0x118), \
	macro_b(NRF_GPIOTE_GPIOTE, EVENTS_IN_7, registerAccessReadWrite, base, 0x11c), \
	macro_b(NRF_GPIOTE_GPIOTE, INTENSET, registerAccessReadWrite, base, 0x304), \
	macro_b(NRF_GPIOTE_GPIOTE, INTENCLR, registerAccessReadWrite, base, 0x308), \
	macro_b(NRF_GPIOTE_GPIOTE, CONFIG_0, registerAccessReadWrite, base, 0x510), \
	macro_b(NRF_GPIOTE_GPIOTE, CONFIG_1, registerAccessReadWrite, base, 0x514), \
	macro_b(NRF_GPIOTE_GPIOTE, CONFIG_2, registerAccessReadWrite, base, 0x518), \
	macro_b(NRF_GPIOTE_GPIOTE, CONFIG_3, registerAccessReadWrite, base, 0x51c), \
	macro_b(NRF_GPIOTE_GPIOTE, CONFIG_4, registerAccessReadWrite, base, 0x520), \
	macro_b(NRF_GPIOTE_GPIOTE, CONFIG_5, registerAccessReadWrite, base, 0x524), \
	macro_b(NRF_GPIOTE_GPIOTE, CONFIG_6, registerAccessReadWrite, base, 0x528), \
	macro_b(NRF_GPIOTE_GPIOTE, CONFIG_7, registerAccessReadWrite, base, 0x52c)

#define NRF_SAADC_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_SAADC_SAADC, TASKS_START, registerAccessReadWrite, base, 0x000), \
	macro_b(NRF_SAADC_SAADC, TASKS_SAMPLE, registerAccessReadWrite, base, 0x004), \
	macro_b(NRF_SAADC_SAADC, TASKS_STOP, registerAccessReadWrite, base, 0x008), \
	macro_b(NRF_SAADC_SAADC, TASKS_CALIBRATEOFFSET, registerAccessReadWrite, base, 0x00C), \
	macro_b(NRF_SAADC_SAADC, EVENTS_STARTED, registerAccessReadWrite, base, 0x100), \
	macro_b(NRF_SAADC_SAADC, EVENTS_END, registerAccessReadWrite, base, 0x104), \
	macro_b(NRF_SAADC_SAADC, EVENTS_CALIBRATEDONE, registerAccessReadWrite, base, 0x110), \
	macro_b(NRF_SAADC_SAADC, EVENTS_STOPPED, registerAccessReadWrite, base, 0x114), \
	macro_b(NRF_SAADC_SAADC, ENABLE, registerAccessReadWrite, base, 0x500), \
	macro_b(NRF_SAADC_SAADC, CH_0_PSELP, registerAccessReadWrite, base, 0x510), \
	macro_b(NRF_SAADC_SAADC, CH_0_PSELN, registerAccessReadWrite, base, 0x514), \
	macro_b(NRF_SAADC_SAADC, CH_0_CONFIG, registerAccessReadWrite, base, 0x518), \
	macro_b(NRF_SAADC_SAADC, RESOLUTION, registerAccessReadWrite, base, 0x5F0), \
	macro_b(NRF_SAADC_SAADC, OVERSAMPLE, registerAccessReadWrite, base, 0x5F4), \
	macro_b(NRF_SAADC_SAADC, RESULT_PTR, registerAccessReadWrite, base, 0x62C), \
	macro_b(NRF_SAADC_SAADC, RESULT_MAXCNT, registerAccessReadWrite, base, 0x630)

#define NRF_TIMER0_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_TIMER_TIMER0, TASKS_STOP, registerAccessReadWrite, base, 0x004), \
	macro_b(NRF_TIMER_TIMER0, TASKS_CLEAR, registerAccessReadWrite, base, 0x00C), \
	macro_b(NRF_TIMER_TIMER0, TASKS_SHUTDOWN, registerAccessReadWrite, base, 0x010), \
	macro_b(NRF_TIMER_TIMER0, TASKS_CAPTURE_0, registerAccessReadWrite, base, 0x040), \
	macro_b(NRF_TIMER_TIMER0, TASKS_CAPTURE_1, registerAccessReadWrite, base, 0x044), \
	macro_b(NRF_TIMER_TIMER0, TASKS_CAPTURE_2, registerAccessReadWrite, base, 0x048), \
	macro_b(NRF_TIMER_TIMER0, TASKS_CAPTURE_3, registerAccessReadWrite, base, 0x04C), \
	macro_b(NRF_TIMER_TIMER0, TASKS_CAPTURE_4, registerAccessReadWrite, base, 0x050), \
	macro_b(NRF_TIMER_TIMER0, TASKS_CAPTURE_5, registerAccessReadWrite, base, 0x054), \
	macro_b(NRF_TIMER_TIMER0, EVENTS_COMPARE_0, registerAccessReadWrite, base, 0x140), \
	macro_b(NRF_TIMER_TIMER0, EVENTS_COMPARE_1, registerAccessReadWrite, base, 0x144), \
	macro_b(NRF_TIMER_TIMER0, EVENTS_COMPARE_2, registerAccessReadWrite, base, 0x148), \
	macro_b(NRF_TIMER_TIMER0, EVENTS_COMPARE_3, registerAccessReadWrite, base, 0x14C), \
	macro_b(NRF_TIMER_TIMER0, EVENTS_COMPARE_4, registerAccessReadWrite, base, 0x150), \
	macro_b(NRF_TIMER_TIMER0, EVENTS_COMPARE_5, registerAccessReadWrite, base, 0x154), \
	macro_b(NRF_TIMER_TIMER0, MODE, registerAccessReadWrite, base, 0x504), \
	macro_b(NRF_TIMER_TIMER0, BITMODE, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_TIMER_TIMER0, PRESCALER, registerAccessReadWrite, base, 0x510), \
	macro_b(NRF_TIMER_TIMER0, CC_0, registerAccessReadWrite, base, 0x540), \
	macro_b(NRF_TIMER_TIMER0, CC_1, registerAccessReadWrite, base, 0x544), \
	macro_b(NRF_TIMER_TIMER0, CC_2, registerAccessReadWrite, base, 0x548), \
	macro_b(NRF_TIMER_TIMER0, CC_3, registerAccessReadWrite, base, 0x54C)

#define NRF_TIMER1_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_TIMER_TIMER1, TASKS_START, registerAccessReadWrite, base, 0x000), \
	macro_b(NRF_TIMER_TIMER1, TASKS_STOP, registerAccessReadWrite, base, 0x004), \
	macro_b(NRF_TIMER_TIMER1, TASKS_CLEAR, registerAccessReadWrite, base, 0x00C), \
	macro_b(NRF_TIMER_TIMER1, TASKS_SHUTDOWN, registerAccessReadWrite, base, 0x010), \
	macro_b(NRF_TIMER_TIMER1, TASKS_CAPTURE_0, registerAccessReadWrite, base, 0x040), \
	macro_b(NRF_TIMER_TIMER1, TASKS_CAPTURE_1, registerAccessReadWrite, base, 0x044), \
	macro_b(NRF_TIMER_TIMER1, TASKS_CAPTURE_2, registerAccessReadWrite, base, 0x048), \
	macro_b(NRF_TIMER_TIMER1, TASKS_CAPTURE_3, registerAccessReadWrite, base, 0x04C), \
	macro_b(NRF_TIMER_TIMER1, TASKS_CAPTURE_4, registerAccessReadWrite, base, 0x050), \
	macro_b(NRF_TIMER_TIMER1, TASKS_CAPTURE_5, registerAccessReadWrite, base, 0x054), \
	macro_b(NRF_TIMER_TIMER1, EVENTS_COMPARE_0, registerAccessReadWrite, base, 0x140), \
	macro_b(NRF_TIMER_TIMER1, EVENTS_COMPARE_1, registerAccessReadWrite, base, 0x144), \
	macro_b(NRF_TIMER_TIMER1, EVENTS_COMPARE_2, registerAccessReadWrite, base, 0x148), \
	macro_b(NRF_TIMER_TIMER1, EVENTS_COMPARE_3, registerAccessReadWrite, base, 0x14C), \
	macro_b(NRF_TIMER_TIMER1, EVENTS_COMPARE_4, registerAccessReadWrite, base, 0x150), \
	macro_b(NRF_TIMER_TIMER1, EVENTS_COMPARE_5, registerAccessReadWrite, base, 0x154), \
	macro_b(NRF_TIMER_TIMER1, SHORTS, registerAccessReadWrite, base, 0x200), \
	macro_b(NRF_TIMER_TIMER1, INTENSET, registerAccessReadWrite, base, 0x304), \
	macro_b(NRF_TIMER_TIMER1, INTENCLR, registerAccessReadWrite, base, 0x308), \
	macro_b(NRF_TIMER_TIMER1, MODE, registerAccessReadWrite, base, 0x504), \
	macro_b(NRF_TIMER_TIMER1, BITMODE, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_TIMER_TIMER1, PRESCALER, registerAccessReadWrite, base, 0x510), \
	macro_b(NRF_TIMER_TIMER1, CC_0, registerAccessReadWrite, base, 0x540), \
	macro_b(NRF_TIMER_TIMER1, CC_1, registerAccessReadWrite, base, 0x544), \
	macro_b(NRF_TIMER_TIMER1, CC_2, registerAccessReadWrite, base, 0x548), \
	macro_b(NRF_TIMER_TIMER1, CC_3, registerAccessReadWrite, base, 0x54C), \
	macro_b(NRF_TIMER_TIMER1, CC_4, registerAccessReadWrite, base, 0x550), \
	macro_b(NRF_TIMER_TIMER1, CC_5, registerAccessReadWrite, base, 0x554)

#define NRF_TIMER2_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_TIMER_TIMER2, TASKS_STOP, registerAccessReadWrite, base, 0x004), \
	macro_b(NRF_TIMER_TIMER2, TASKS_SHUTDOWN, registerAccessReadWrite, base, 0x010), \
	macro_b(NRF_TIMER_TIMER2, TASKS_CAPTURE_0, registerAccessReadWrite, base, 0x040), \
	macro_b(NRF_TIMER_TIMER2, TASKS_CAPTURE_1, registerAccessReadWrite, base, 0x044), \
	macro_b(NRF_TIMER_TIMER2, TASKS_CAPTURE_2, registerAccessReadWrite, base, 0x048), \
	macro_b(NRF_TIMER_TIMER2, TASKS_CAPTURE_3, registerAccessReadWrite, base, 0x04C), \
	macro_b(NRF_TIMER_TIMER2, TASKS_CAPTURE_4, registerAccessReadWrite, base, 0x050), \
	macro_b(NRF_TIMER_TIMER2, TASKS_CAPTURE_5, registerAccessReadWrite, base, 0x054), \
	macro_b(NRF_TIMER_TIMER2, EVENTS_COMPARE_0, registerAccessReadWrite, base, 0x140), \
	macro_b(NRF_TIMER_TIMER2, EVENTS_COMPARE_1, registerAccessReadWrite, base, 0x144), \
	macro_b(NRF_TIMER_TIMER2, EVENTS_COMPARE_2, registerAccessReadWrite, base, 0x148), \
	macro_b(NRF_TIMER_TIMER2, EVENTS_COMPARE_3, registerAccessReadWrite, base, 0x14C), \
	macro_b(NRF_TIMER_TIMER2, EVENTS_COMPARE_4, registerAccessReadWrite, base, 0x150), \
	macro_b(NRF_TIMER_TIMER2, EVENTS_COMPARE_5, registerAccessReadWrite, base, 0x154), \
	macro_b(NRF_TIMER_TIMER2, MODE, registerAccessReadWrite, base, 0x504), \
	macro_b(NRF_TIMER_TIMER2, BITMODE, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_TIMER_TIMER2, PRESCALER, registerAccessReadWrite, base, 0x510)

#define NRF_RTC0_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_RTC_RTC0, TASKS_START, registerAccessReadWrite, base, 0x000), \
	macro_b(NRF_RTC_RTC0, TASKS_STOP, registerAccessReadWrite, base, 0x004), \
	macro_b(NRF_RTC_RTC0, TASKS_CLEAR, registerAccessReadWrite, base, 0x008), \
	macro_b(NRF_RTC_RTC0, EVENTS_TICK, registerAccessReadWrite, base, 0x100), \
	macro_b(NRF_RTC_RTC0, EVENTS_OVRFLW, registerAccessReadWrite, base, 0x104), \
	macro_b(NRF_RTC_RTC0, EVENTS_COMPARE_0, registerAccessReadWrite, base, 0x140), \
	macro_b(NRF_RTC_RTC0, EVENTS_COMPARE_1, registerAccessReadWrite, base, 0x144), \
	macro_b(NRF_RTC_RTC0, EVENTS_COMPARE_2, registerAccessReadWrite, base, 0x148), \
	macro_b(NRF_RTC_RTC0, EVENTS_COMPARE_3, registerAccessReadWrite, base, 0x14c), \
	macro_b(NRF_RTC_RTC0, INTENSET, registerAccessReadWrite, base, 0x304), \
	macro_b(NRF_RTC_RTC0, INTENCLR, registerAccessReadWrite, base, 0x308), \
	macro_b(NRF_RTC_RTC0, EVTENSET, registerAccessReadWrite, base, 0x344), \
	macro_b(NRF_RTC_RTC0, EVTENCLR, registerAccessReadWrite, base, 0x348), \
	macro_b(NRF_RTC_RTC0, COUNTER, registerAccessReadWrite, base, 0x504), \
	macro_b(NRF_RTC_RTC0, PRESCALER, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_RTC_RTC0, CC_0, registerAccessReadWrite, base, 0x540), \
	macro_b(NRF_RTC_RTC0, CC_1, registerAccessReadWrite, base, 0x544), \
	macro_b(NRF_RTC_RTC0, CC_2, registerAccessReadWrite, base, 0x548), \
	macro_b(NRF_RTC_RTC0, CC_3, registerAccessReadWrite, base, 0x54c)

#define NRF_TEMP_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_TEMP_TEMP, TASKS_START, registerAccessReadWrite, base, 0x000), \
	macro_b(NRF_TEMP_TEMP, TASKS_STOP, registerAccessReadWrite, base, 0x004), \
	macro_b(NRF_TEMP_TEMP, EVENTS_DATARDY, registerAccessReadWrite, base, 0x100), \
	macro_b(NRF_TEMP_TEMP, TEMP, registerAccessReadWrite, base, 0x508)

#define NRF_RNG_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_RNG_RNG, TASKS_START, registerAccessReadWrite, base, 0x000), \
	macro_b(NRF_RNG_RNG, TASKS_STOP, registerAccessReadWrite, base, 0x004), \
	macro_b(NRF_RNG_RNG, EVENTS_VALRDY, registerAccessReadWrite, base, 0x100), \
	macro_b(NRF_RNG_RNG, SHORTS, registerAccessReadWrite, base, 0x200), \
	macro_b(NRF_RNG_RNG, INTENSET, registerAccessReadWrite, base, 0x304), \
	macro_b(NRF_RNG_RNG, INTENCLR, registerAccessReadWrite, base, 0x308), \
	macro_b(NRF_RNG_RNG, CONFIG, registerAccessReadWrite, base, 0x504), \
	macro_b(NRF_RNG_RNG, VALUE, registerAccessReadWrite, base, 0x508)

#define NRF_ECB_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_ECB_ECB, TASKS_STARTECB, registerAccessReadWrite, base, 0x000), \
	macro_b(NRF_ECB_ECB, TASKS_STOPECB, registerAccessReadWrite, base, 0x004), \
	macro_b(NRF_ECB_ECB, EVENTS_ENDECB, registerAccessReadWrite, base, 0x100), \
	macro_b(NRF_ECB_ECB, EVENTS_ERRORECB, registerAccessReadWrite, base, 0x104), \
	macro_b(NRF_ECB_ECB, ECBDATAPTR, registerAccessReadWrite, base, 0x504)

#define NRF_WDT_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_WDT_WDT, TASKS_START, registerAccessReadWrite, base, 0x000), \
	macro_b(NRF_WDT_WDT, INTENSET, registerAccessReadWrite, base, 0x304), \
	macro_b(NRF_WDT_WDT, RUNSTATUS, registerAccessReadWrite, base, 0x400), \
	macro_b(NRF_WDT_WDT, CRV, registerAccessReadWrite, base, 0x504), \
	macro_b(NRF_WDT_WDT, RREN, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_WDT_WDT, CONFIG, registerAccessReadWrite, base, 0x50C), \
	macro_b(NRF_WDT_WDT, RR_0, registerAccessReadWrite, base, 0x600)

#define NRF_RTC1_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_RTC_RTC1, TASKS_START, registerAccessReadWrite, base, 0x000), \
	macro_b(NRF_RTC_RTC1, TASKS_STOP, registerAccessReadWrite, base, 0x004), \
	macro_b(NRF_RTC_RTC1, EVENTS_OVRFLW, registerAccessReadWrite, base, 0x104), \
	macro_b(NRF_RTC_RTC1, EVENTS_COMPARE_0, registerAccessReadWrite, base, 0x140), \
	macro_b(NRF_RTC_RTC1, INTENSET, registerAccessReadWrite, base, 0x304), \
	macro_b(NRF_RTC_RTC1, INTENCLR, registerAccessReadWrite, base, 0x308), \
	macro_b(NRF_RTC_RTC1, COUNTER, registerAccessReadWrite, base, 0x504), \
	macro_b(NRF_RTC_RTC1, PRESCALER, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_RTC_RTC1, CC_0, registerAccessReadWrite, base, 0x540)

#define NRF_QDEC_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_QDEC_QDEC, TASKS_START, registerAccessReadWrite, base, 0x000), \
	macro_b(NRF_QDEC_QDEC, TASKS_STOP, registerAccessReadWrite, base, 0x004), \
	macro_b(NRF_QDEC_QDEC, TASKS_RDCLRACC, registerAccessReadWrite, base, 0x00C), \
	macro_b(NRF_QDEC_QDEC, EVENTS_ACCOF, registerAccessReadWrite, base, 0x108), \
	macro_b(NRF_QDEC_QDEC, EVENTS_STOPPED, registerAccessReadWrite, base, 0x110), \
	macro_b(NRF_QDEC_QDEC, INTENSET, registerAccessReadWrite, base, 0x304), \
	macro_b(NRF_QDEC_QDEC, INTENCLR, registerAccessReadWrite, base, 0x308), \
	macro_b(NRF_QDEC_QDEC, ENABLE, registerAccessReadWrite, base, 0x500), \
	macro_b(NRF_QDEC_QDEC, ACC, registerAccessReadWrite, base, 0x514), \
	macro_b(NRF_QDEC_QDEC, ACCREAD, registerAccessReadWrite, base, 0x518), \
	macro_b(NRF_QDEC_QDEC, PSEL_LED, registerAccessReadWrite, base, 0x51C), \
	macro_b(NRF_QDEC_QDEC, PSEL_A, registerAccessReadWrite, base, 0x520), \
	macro_b(NRF_QDEC_QDEC, PSEL_B, registerAccessReadWrite, base, 0x524), \
	macro_b(NRF_QDEC_QDEC, DBFEN, registerAccessReadWrite, base, 0x528)

#define NRF_TIMER3_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_TIMER_TIMER3, TASKS_STOP, registerAccessReadWrite, base, 0x004), \
	macro_b(NRF_TIMER_TIMER3, TASKS_SHUTDOWN, registerAccessReadWrite, base, 0x010), \
	macro_b(NRF_TIMER_TIMER3, TASKS_CAPTURE_0, registerAccessReadWrite, base, 0x040), \
	macro_b(NRF_TIMER_TIMER3, TASKS_CAPTURE_1, registerAccessReadWrite, base, 0x044), \
	macro_b(NRF_TIMER_TIMER3, TASKS_CAPTURE_2, registerAccessReadWrite, base, 0x048), \
	macro_b(NRF_TIMER_TIMER3, TASKS_CAPTURE_3, registerAccessReadWrite, base, 0x04C), \
	macro_b(NRF_TIMER_TIMER3, TASKS_CAPTURE_4, registerAccessReadWrite, base, 0x050), \
	macro_b(NRF_TIMER_TIMER3, TASKS_CAPTURE_5, registerAccessReadWrite, base, 0x054), \
	macro_b(NRF_TIMER_TIMER3, EVENTS_COMPARE_0, registerAccessReadWrite, base, 0x140), \
	macro_b(NRF_TIMER_TIMER3, EVENTS_COMPARE_1, registerAccessReadWrite, base, 0x144), \
	macro_b(NRF_TIMER_TIMER3, EVENTS_COMPARE_2, registerAccessReadWrite, base, 0x148), \
	macro_b(NRF_TIMER_TIMER3, EVENTS_COMPARE_3, registerAccessReadWrite, base, 0x14C), \
	macro_b(NRF_TIMER_TIMER3, EVENTS_COMPARE_4, registerAccessReadWrite, base, 0x150), \
	macro_b(NRF_TIMER_TIMER3, EVENTS_COMPARE_5, registerAccessReadWrite, base, 0x154), \
	macro_b(NRF_TIMER_TIMER3, MODE, registerAccessReadWrite, base, 0x504), \
	macro_b(NRF_TIMER_TIMER3, BITMODE, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_TIMER_TIMER3, PRESCALER, registerAccessReadWrite, base, 0x510)

#define NRF_TIMER4_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_TIMER_TIMER4, TASKS_STOP, registerAccessReadWrite, base, 0x004), \
	macro_b(NRF_TIMER_TIMER4, TASKS_SHUTDOWN, registerAccessReadWrite, base, 0x010), \
	macro_b(NRF_TIMER_TIMER4, TASKS_CAPTURE_0, registerAccessReadWrite, base, 0x040), \
	macro_b(NRF_TIMER_TIMER4, TASKS_CAPTURE_1, registerAccessReadWrite, base, 0x044), \
	macro_b(NRF_TIMER_TIMER4, TASKS_CAPTURE_2, registerAccessReadWrite, base, 0x048), \
	macro_b(NRF_TIMER_TIMER4, TASKS_CAPTURE_3, registerAccessReadWrite, base, 0x04C), \
	macro_b(NRF_TIMER_TIMER4, TASKS_CAPTURE_4, registerAccessReadWrite, base, 0x050), \
	macro_b(NRF_TIMER_TIMER4, TASKS_CAPTURE_5, registerAccessReadWrite, base, 0x054), \
	macro_b(NRF_TIMER_TIMER4, EVENTS_COMPARE_0, registerAccessReadWrite, base, 0x140), \
	macro_b(NRF_TIMER_TIMER4, EVENTS_COMPARE_1, registerAccessReadWrite, base, 0x144), \
	macro_b(NRF_TIMER_TIMER4, EVENTS_COMPARE_2, registerAccessReadWrite, base, 0x148), \
	macro_b(NRF_TIMER_TIMER4, EVENTS_COMPARE_3, registerAccessReadWrite, base, 0x14C), \
	macro_b(NRF_TIMER_TIMER4, EVENTS_COMPARE_4, registerAccessReadWrite, base, 0x150), \
	macro_b(NRF_TIMER_TIMER4, EVENTS_COMPARE_5, registerAccessReadWrite, base, 0x154), \
	macro_b(NRF_TIMER_TIMER4, MODE, registerAccessReadWrite, base, 0x504), \
	macro_b(NRF_TIMER_TIMER4, BITMODE, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_TIMER_TIMER4, PRESCALER, registerAccessReadWrite, base, 0x510)

#define NRF_NVMC_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_NVMC_NVMC, READY, registerAccessReadWrite, base, 0x400), \
	macro_b(NRF_NVMC_NVMC, CONFIG, registerAccessReadWrite, base, 0x504), \
	macro_b(NRF_NVMC_NVMC, ERASEPAGE, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_NVMC_NVMC, ICACHECNF, registerAccessReadWrite, base, 0x540)

#define NRF_SPIM2_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_SPIM_SPIM2, TASKS_START, registerAccessReadWrite, base, 0x010), \
	macro_b(NRF_SPIM_SPIM2, TASKS_STOP, registerAccessReadWrite, base, 0x014), \
	macro_b(NRF_SPIM_SPIM2, EVENTS_END, registerAccessReadWrite, base, 0x118), \
	macro_b(NRF_SPIM_SPIM2, INTENSET, registerAccessReadWrite, base, 0x304), \
	macro_b(NRF_SPIM_SPIM2, INTENCLR, registerAccessReadWrite, base, 0x308), \
	macro_b(NRF_SPIM_SPIM2, ENABLE, registerAccessReadWrite, base, 0x500), \
	macro_b(NRF_SPIM_SPIM2, PSEL_SCK, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_SPIM_SPIM2, PSEL_MOSI, registerAccessReadWrite, base, 0x50C), \
	macro_b(NRF_SPIM_SPIM2, PSEL_MISO, registerAccessReadWrite, base, 0x510), \
	macro_b(NRF_SPIM_SPIM2, FREQUENCY, registerAccessReadWrite, base, 0x524), \
	macro_b(NRF_SPIM_SPIM2, RXD_PTR, registerAccessReadWrite, base, 0x534), \
	macro_b(NRF_SPIM_SPIM2, RXD_MAXCNT, registerAccessReadWrite, base, 0x538), \
	macro_b(NRF_SPIM_SPIM2, TXD_PTR, registerAccessReadWrite, base, 0x544), \
	macro_b(NRF_SPIM_SPIM2, TXD_MAXCNT, registerAccessReadWrite, base, 0x548), \
	macro_b(NRF_SPIM_SPIM2, CONFIG, registerAccessReadWrite, base, 0x554)

#define NRF_RTC2_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_RTC_RTC2, TASKS_START, registerAccessReadWrite, base, 0x000), \
	macro_b(NRF_RTC_RTC2, TASKS_STOP, registerAccessReadWrite, base, 0x004), \
	macro_b(NRF_RTC_RTC2, EVENTS_OVRFLW, registerAccessReadWrite, base, 0x104), \
	macro_b(NRF_RTC_RTC2, EVENTS_COMPARE_0, registerAccessReadWrite, base, 0x140), \
	macro_b(NRF_RTC_RTC2, INTENSET, registerAccessReadWrite, base, 0x304), \
	macro_b(NRF_RTC_RTC2, INTENCLR, registerAccessReadWrite, base, 0x308), \
	macro_b(NRF_RTC_RTC2, COUNTER, registerAccessReadWrite, base, 0x504), \
	macro_b(NRF_RTC_RTC2, PRESCALER, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_RTC_RTC2, CC_0, registerAccessReadWrite, base, 0x540)

#define NRF_P0_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_GPIO_P0, OUT, registerAccessReadWrite, base, 0x504), \
	macro_b(NRF_GPIO_P0, OUTSET, registerAccessReadWrite, base, 0x508), \
	macro_b(NRF_GPIO_P0, OUTCLR, registerAccessReadWrite, base, 0x50C), \
	macro_b(NRF_GPIO_P0, IN, registerAccessReadWrite, base, 0x510), \
	macro_b(NRF_GPIO_P0, DIR, registerAccessReadWrite, base, 0x514), \
	macro_b(NRF_GPIO_P0, PIN_CNF_0, registerAccessReadWrite, base, 0x700), \
	macro_b(NRF_GPIO_P0, PIN_CNF_1, registerAccessReadWrite, base, 0x704), \
	macro_b(NRF_GPIO_P0, PIN_CNF_2, registerAccessReadWrite, base, 0x708), \
	macro_b(NRF_GPIO_P0, PIN_CNF_3, registerAccessReadWrite, base, 0x70c), \
	macro_b(NRF_GPIO_P0, PIN_CNF_4, registerAccessReadWrite, base, 0x710), \
	macro_b(NRF_GPIO_P0, PIN_CNF_5, registerAccessReadWrite, base, 0x714), \
	macro_b(NRF_GPIO_P0, PIN_CNF_6, registerAccessReadWrite, base, 0x718), \
	macro_b(NRF_GPIO_P0, PIN_CNF_7, registerAccessReadWrite, base, 0x71c), \
	macro_b(NRF_GPIO_P0, PIN_CNF_8, registerAccessReadWrite, base, 0x720), \
	macro_b(NRF_GPIO_P0, PIN_CNF_9, registerAccessReadWrite, base, 0x724), \
	macro_b(NRF_GPIO_P0, PIN_CNF_10, registerAccessReadWrite, base, 0x728), \
	macro_b(NRF_GPIO_P0, PIN_CNF_11, registerAccessReadWrite, base, 0x72c), \
	macro_b(NRF_GPIO_P0, PIN_CNF_12, registerAccessReadWrite, base, 0x730), \
	macro_b(NRF_GPIO_P0, PIN_CNF_13, registerAccessReadWrite, base, 0x734), \
	macro_b(NRF_GPIO_P0, PIN_CNF_14, registerAccessReadWrite, base, 0x738), \
	macro_b(NRF_GPIO_P0, PIN_CNF_15, registerAccessReadWrite, base, 0x73c), \
	macro_b(NRF_GPIO_P0, PIN_CNF_16, registerAccessReadWrite, base, 0x740), \
	macro_b(NRF_GPIO_P0, PIN_CNF_17, registerAccessReadWrite, base, 0x744), \
	macro_b(NRF_GPIO_P0, PIN_CNF_18, registerAccessReadWrite, base, 0x748), \
	macro_b(NRF_GPIO_P0, PIN_CNF_19, registerAccessReadWrite, base, 0x74c), \
	macro_b(NRF_GPIO_P0, PIN_CNF_20, registerAccessReadWrite, base, 0x750), \
	macro_b(NRF_GPIO_P0, PIN_CNF_21, registerAccessReadWrite, base, 0x754), \
	macro_b(NRF_GPIO_P0, PIN_CNF_22, registerAccessReadWrite, base, 0x758), \
	macro_b(NRF_GPIO_P0, PIN_CNF_23, registerAccessReadWrite, base, 0x75c), \
	macro_b(NRF_GPIO_P0, PIN_CNF_24, registerAccessReadWrite, base, 0x760), \
	macro_b(NRF_GPIO_P0, PIN_CNF_25, registerAccessReadWrite, base, 0x764), \
	macro_b(NRF_GPIO_P0, PIN_CNF_26, registerAccessReadWrite, base, 0x768), \
	macro_b(NRF_GPIO_P0, PIN_CNF_27, registerAccessReadWrite, base, 0x76c), \
	macro_b(NRF_GPIO_P0, PIN_CNF_28, registerAccessReadWrite, base, 0x770), \
	macro_b(NRF_GPIO_P0, PIN_CNF_29, registerAccessReadWrite, base, 0x774), \
	macro_b(NRF_GPIO_P0, PIN_CNF_30, registerAccessReadWrite, base, 0x778), \
	macro_b(NRF_GPIO_P0, PIN_CNF_31, registerAccessReadWrite, base, 0x77c)

#define ARMV7M_NVIC_INSTANCE(base, macro_a, macro_b) \
	macro_a(ARMV7M_SCS_NVIC, ISER0, registerAccessReadWrite, base, 0x100), \
	macro_b(ARMV7M_SCS_NVIC, ISER1, registerAccessReadWrite, base, 0x104), \
	macro_b(ARMV7M_SCS_NVIC, ISER2, registerAccessReadWrite, base, 0x108), \
	macro_b(ARMV7M_SCS_NVIC, ISER3, registerAccessReadWrite, base, 0x10c), \
	macro_b(ARMV7M_SCS_NVIC, ISER4, registerAccessReadWrite, base, 0x110), \
	macro_b(ARMV7M_SCS_NVIC, ISER5, registerAccessReadWrite, base, 0x114), \
	macro_b(ARMV7M_SCS_NVIC, ISER6, registerAccessReadWrite, base, 0x118), \
	macro_b(ARMV7M_SCS_NVIC, ISER7, registerAccessReadWrite, base, 0x11c), \
	macro_b(ARMV7M_SCS_NVIC, ISER8, registerAccessReadWrite, base, 0x120), \
	macro_b(ARMV7M_SCS_NVIC, ISER9, registerAccessReadWrite, base, 0x124), \
	macro_b(ARMV7M_SCS_NVIC, ISER10, registerAccessReadWrite, base, 0x128), \
	macro_b(ARMV7M_SCS_NVIC, ISER11, registerAccessReadWrite, base, 0x12c), \
	macro_b(ARMV7M_SCS_NVIC, ISER12, registerAccessReadWrite, base, 0x130), \
	macro_b(ARMV7M_SCS_NVIC, ISER13, registerAccessReadWrite, base, 0x134), \
	macro_b(ARMV7M_SCS_NVIC, ISER14, registerAccessReadWrite, base, 0x138), \
	macro_b(ARMV7M_SCS_NVIC, ISER15, registerAccessReadWrite, base, 0x13c), \
	macro_b(ARMV7M_SCS_NVIC, ICER0, registerAccessReadWrite, base, 0x180), \
	macro_b(ARMV7M_SCS_NVIC, ICER1, registerAccessReadWrite, base, 0x184), \
	macro_b(ARMV7M_SCS_NVIC, ICER2, registerAccessReadWrite, base, 0x188), \
	macro_b(ARMV7M_SCS_NVIC, ICER3, registerAccessReadWrite, base, 0x18c), \
	macro_b(ARMV7M_SCS_NVIC, ICER4, registerAccessReadWrite, base, 0x190), \
	macro_b(ARMV7M_SCS_NVIC, ICER5, registerAccessReadWrite, base, 0x194), \
	macro_b(ARMV7M_SCS_NVIC, ICER6, registerAccessReadWrite, base, 0x198), \
	macro_b(ARMV7M_SCS_NVIC, ICER7, registerAccessReadWrite, base, 0x19c), \
	macro_b(ARMV7M_SCS_NVIC, ICER8, registerAccessReadWrite, base, 0x1a0), \
	macro_b(ARMV7M_SCS_NVIC, ICER9, registerAccessReadWrite, base, 0x1a4), \
	macro_b(ARMV7M_SCS_NVIC, ICER10, registerAccessReadWrite, base, 0x1a8), \
	macro_b(ARMV7M_SCS_NVIC, ICER11, registerAccessReadWrite, base, 0x1ac), \
	macro_b(ARMV7M_SCS_NVIC, ICER12, registerAccessReadWrite, base, 0x1b0), \
	macro_b(ARMV7M_SCS_NVIC, ICER13, registerAccessReadWrite, base, 0x1b4), \
	macro_b(ARMV7M_SCS_NVIC, ICER14, registerAccessReadWrite, base, 0x1b8), \
	macro_b(ARMV7M_SCS_NVIC, ICER15, registerAccessReadWrite, base, 0x1bc), \
	macro_b(ARMV7M_SCS_NVIC, ISPR0, registerAccessReadWrite, base, 0x200), \
	macro_b(ARMV7M_SCS_NVIC, ISPR1, registerAccessReadWrite, base, 0x204), \
	macro_b(ARMV7M_SCS_NVIC, ISPR2, registerAccessReadWrite, base, 0x208), \
	macro_b(ARMV7M_SCS_NVIC, ISPR3, registerAccessReadWrite, base, 0x20c), \
	macro_b(ARMV7M_SCS_NVIC, ISPR4, registerAccessReadWrite, base, 0x210), \
	macro_b(ARMV7M_SCS_NVIC, ISPR5, registerAccessReadWrite, base, 0x214), \
	macro_b(ARMV7M_SCS_NVIC, ISPR6, registerAccessReadWrite, base, 0x218), \
	macro_b(ARMV7M_SCS_NVIC, ISPR7, registerAccessReadWrite, base, 0x21c), \
	macro_b(ARMV7M_SCS_NVIC, ISPR8, registerAccessReadWrite, base, 0x220), \
	macro_b(ARMV7M_SCS_NVIC, ISPR9, registerAccessReadWrite, base, 0x224), \
	macro_b(ARMV7M_SCS_NVIC, ISPR10, registerAccessReadWrite, base, 0x228), \
	macro_b(ARMV7M_SCS_NVIC, ISPR11, registerAccessReadWrite, base, 0x22c), \
	macro_b(ARMV7M_SCS_NVIC, ISPR12, registerAccessReadWrite, base, 0x230), \
	macro_b(ARMV7M_SCS_NVIC, ISPR13, registerAccessReadWrite, base, 0x234), \
	macro_b(ARMV7M_SCS_NVIC, ISPR14, registerAccessReadWrite, base, 0x238), \
	macro_b(ARMV7M_SCS_NVIC, ISPR15, registerAccessReadWrite, base, 0x23c), \
	macro_b(ARMV7M_SCS_NVIC, ICPR0, registerAccessReadWrite, base, 0x280), \
	macro_b(ARMV7M_SCS_NVIC, ICPR1, registerAccessReadWrite, base, 0x284), \
	macro_b(ARMV7M_SCS_NVIC, ICPR2, registerAccessReadWrite, base, 0x288), \
	macro_b(ARMV7M_SCS_NVIC, ICPR3, registerAccessReadWrite, base, 0x28c), \
	macro_b(ARMV7M_SCS_NVIC, ICPR4, registerAccessReadWrite, base, 0x290), \
	macro_b(ARMV7M_SCS_NVIC, ICPR5, registerAccessReadWrite, base, 0x294), \
	macro_b(ARMV7M_SCS_NVIC, ICPR6, registerAccessReadWrite, base, 0x298), \
	macro_b(ARMV7M_SCS_NVIC, ICPR7, registerAccessReadWrite, base, 0x29c), \
	macro_b(ARMV7M_SCS_NVIC, ICPR8, registerAccessReadWrite, base, 0x2a0), \
	macro_b(ARMV7M_SCS_NVIC, ICPR9, registerAccessReadWrite, base, 0x2a4), \
	macro_b(ARMV7M_SCS_NVIC, ICPR10, registerAccessReadWrite, base, 0x2a8), \
	macro_b(ARMV7M_SCS_NVIC, ICPR11, registerAccessReadWrite, base, 0x2ac), \
	macro_b(ARMV7M_SCS_NVIC, ICPR12, registerAccessReadWrite, base, 0x2b0), \
	macro_b(ARMV7M_SCS_NVIC, ICPR13, registerAccessReadWrite, base, 0x2b4), \
	macro_b(ARMV7M_SCS_NVIC, ICPR14, registerAccessReadWrite, base, 0x2b8), \
	macro_b(ARMV7M_SCS_NVIC, ICPR15, registerAccessReadWrite, base, 0x2bc), \
	macro_b(ARMV7M_SCS_NVIC, IPR0, registerAccessReadWrite, base, 0x400), \
	macro_b(ARMV7M_SCS_NVIC, IPR1, registerAccessReadWrite, base, 0x404), \
	macro_b(ARMV7M_SCS_NVIC, IPR2, registerAccessReadWrite, base, 0x408), \
	macro_b(ARMV7M_SCS_NVIC, IPR3, registerAccessReadWrite, base, 0x40c), \
	macro_b(ARMV7M_SCS_NVIC, IPR4, registerAccessReadWrite, base, 0x410), \
	macro_b(ARMV7M_SCS_NVIC, IPR5, registerAccessReadWrite, base, 0x414), \
	macro_b(ARMV7M_SCS_NVIC, IPR6, registerAccessReadWrite, base, 0x418), \
	macro_b(ARMV7M_SCS_NVIC, IPR7, registerAccessReadWrite, base, 0x41c), \
	macro_b(ARMV7M_SCS_NVIC, IPR8, registerAccessReadWrite, base, 0x420), \
	macro_b(ARMV7M_SCS_NVIC, IPR9, registerAccessReadWrite, base, 0x424), \
	macro_b(ARMV7M_SCS_NVIC, IPR10, registerAccessReadWrite, base, 0x428), \
	macro_b(ARMV7M_SCS_NVIC, IPR11, registerAccessReadWrite, base, 0x42c), \
	macro_b(ARMV7M_SCS_NVIC, IPR12, registerAccessReadWrite, base, 0x430), \
	macro_b(ARMV7M_SCS_NVIC, IPR13, registerAccessReadWrite, base, 0x434), \
	macro_b(ARMV7M_SCS_NVIC, IPR14, registerAccessReadWrite, base, 0x438), \
	macro_b(ARMV7M_SCS_NVIC, IPR15, registerAccessReadWrite, base, 0x43c), \
	macro_b(ARMV7M_SCS_NVIC, IPR16, registerAccessReadWrite, base, 0x440), \
	macro_b(ARMV7M_SCS_NVIC, IPR17, registerAccessReadWrite, base, 0x444), \
	macro_b(ARMV7M_SCS_NVIC, IPR18, registerAccessReadWrite, base, 0x448), \
	macro_b(ARMV7M_SCS_NVIC, IPR19, registerAccessReadWrite, base, 0x44c), \
	macro_b(ARMV7M_SCS_NVIC, IPR20, registerAccessReadWrite, base, 0x450), \
	macro_b(ARMV7M_SCS_NVIC, IPR21, registerAccessReadWrite, base, 0x454), \
	macro_b(ARMV7M_SCS_NVIC, IPR22, registerAccessReadWrite, base, 0x458), \
	macro_b(ARMV7M_SCS_NVIC, IPR23, registerAccessReadWrite, base, 0x45c), \
	macro_b(ARMV7M_SCS_NVIC, IPR24, registerAccessReadWrite, base, 0x460), \
	macro_b(ARMV7M_SCS_NVIC, IPR25, registerAccessReadWrite, base, 0x464), \
	macro_b(ARMV7M_SCS_NVIC, IPR26, registerAccessReadWrite, base, 0x468), \
	macro_b(ARMV7M_SCS_NVIC, IPR27, registerAccessReadWrite, base, 0x46c), \
	macro_b(ARMV7M_SCS_NVIC, IPR28, registerAccessReadWrite, base, 0x470), \
	macro_b(ARMV7M_SCS_NVIC, IPR29, registerAccessReadWrite, base, 0x474), \
	macro_b(ARMV7M_SCS_NVIC, IPR30, registerAccessReadWrite, base, 0x478), \
	macro_b(ARMV7M_SCS_NVIC, IPR31, registerAccessReadWrite, base, 0x47c), \
	macro_b(ARMV7M_SCS_NVIC, IPR32, registerAccessReadWrite, base, 0x480), \
	macro_b(ARMV7M_SCS_NVIC, IPR33, registerAccessReadWrite, base, 0x484), \
	macro_b(ARMV7M_SCS_NVIC, IPR34, registerAccessReadWrite, base, 0x488), \
	macro_b(ARMV7M_SCS_NVIC, IPR35, registerAccessReadWrite, base, 0x48c), \
	macro_b(ARMV7M_SCS_NVIC, IPR36, registerAccessReadWrite, base, 0x490), \
	macro_b(ARMV7M_SCS_NVIC, IPR37, registerAccessReadWrite, base, 0x494), \
	macro_b(ARMV7M_SCS_NVIC, IPR38, registerAccessReadWrite, base, 0x498), \
	macro_b(ARMV7M_SCS_NVIC, IPR39, registerAccessReadWrite, base, 0x49c), \
	macro_b(ARMV7M_SCS_NVIC, IPR40, registerAccessReadWrite, base, 0x4a0), \
	macro_b(ARMV7M_SCS_NVIC, IPR41, registerAccessReadWrite, base, 0x4a4), \
	macro_b(ARMV7M_SCS_NVIC, IPR42, registerAccessReadWrite, base, 0x4a8), \
	macro_b(ARMV7M_SCS_NVIC, IPR43, registerAccessReadWrite, base, 0x4ac), \
	macro_b(ARMV7M_SCS_NVIC, IPR44, registerAccessReadWrite, base, 0x4b0), \
	macro_b(ARMV7M_SCS_NVIC, IPR45, registerAccessReadWrite, base, 0x4b4), \
	macro_b(ARMV7M_SCS_NVIC, IPR46, registerAccessReadWrite, base, 0x4b8), \
	macro_b(ARMV7M_SCS_NVIC, IPR47, registerAccessReadWrite, base, 0x4bc), \
	macro_b(ARMV7M_SCS_NVIC, IPR48, registerAccessReadWrite, base, 0x4c0), \
	macro_b(ARMV7M_SCS_NVIC, IPR49, registerAccessReadWrite, base, 0x4c4), \
	macro_b(ARMV7M_SCS_NVIC, IPR50, registerAccessReadWrite, base, 0x4c8), \
	macro_b(ARMV7M_SCS_NVIC, IPR51, registerAccessReadWrite, base, 0x4cc), \
	macro_b(ARMV7M_SCS_NVIC, IPR52, registerAccessReadWrite, base, 0x4d0), \
	macro_b(ARMV7M_SCS_NVIC, IPR53, registerAccessReadWrite, base, 0x4d4), \
	macro_b(ARMV7M_SCS_NVIC, IPR54, registerAccessReadWrite, base, 0x4d8), \
	macro_b(ARMV7M_SCS_NVIC, IPR55, registerAccessReadWrite, base, 0x4dc), \
	macro_b(ARMV7M_SCS_NVIC, IPR56, registerAccessReadWrite, base, 0x4e0), \
	macro_b(ARMV7M_SCS_NVIC, IPR57, registerAccessReadWrite, base, 0x4e4), \
	macro_b(ARMV7M_SCS_NVIC, IPR58, registerAccessReadWrite, base, 0x4e8), \
	macro_b(ARMV7M_SCS_NVIC, IPR59, registerAccessReadWrite, base, 0x4ec), \
	macro_b(ARMV7M_SCS_NVIC, IPR60, registerAccessReadWrite, base, 0x4f0), \
	macro_b(ARMV7M_SCS_NVIC, IPR61, registerAccessReadWrite, base, 0x4f4), \
	macro_b(ARMV7M_SCS_NVIC, IPR62, registerAccessReadWrite, base, 0x4f8), \
	macro_b(ARMV7M_SCS_NVIC, IPR63, registerAccessReadWrite, base, 0x4fc), \
	macro_b(ARMV7M_SCS_NVIC, IPR64, registerAccessReadWrite, base, 0x500), \
	macro_b(ARMV7M_SCS_NVIC, IPR65, registerAccessReadWrite, base, 0x504), \
	macro_b(ARMV7M_SCS_NVIC, IPR66, registerAccessReadWrite, base, 0x508), \
	macro_b(ARMV7M_SCS_NVIC, IPR67, registerAccessReadWrite, base, 0x50c), \
	macro_b(ARMV7M_SCS_NVIC, IPR68, registerAccessReadWrite, base, 0x510), \
	macro_b(ARMV7M_SCS_NVIC, IPR69, registerAccessReadWrite, base, 0x514), \
	macro_b(ARMV7M_SCS_NVIC, IPR70, registerAccessReadWrite, base, 0x518), \
	macro_b(ARMV7M_SCS_NVIC, IPR71, registerAccessReadWrite, base, 0x51c), \
	macro_b(ARMV7M_SCS_NVIC, IPR72, registerAccessReadWrite, base, 0x520), \
	macro_b(ARMV7M_SCS_NVIC, IPR73, registerAccessReadWrite, base, 0x524), \
	macro_b(ARMV7M_SCS_NVIC, IPR74, registerAccessReadWrite, base, 0x528), \
	macro_b(ARMV7M_SCS_NVIC, IPR75, registerAccessReadWrite, base, 0x52c), \
	macro_b(ARMV7M_SCS_NVIC, IPR76, registerAccessReadWrite, base, 0x530), \
	macro_b(ARMV7M_SCS_NVIC, IPR77, registerAccessReadWrite, base, 0x534), \
	macro_b(ARMV7M_SCS_NVIC, IPR78, registerAccessReadWrite, base, 0x538), \
	macro_b(ARMV7M_SCS_NVIC, IPR79, registerAccessReadWrite, base, 0x53c), \
	macro_b(ARMV7M_SCS_NVIC, IPR80, registerAccessReadWrite, base, 0x540), \
	macro_b(ARMV7M_SCS_NVIC, IPR81, registerAccessReadWrite, base, 0x544), \
	macro_b(ARMV7M_SCS_NVIC, IPR82, registerAccessReadWrite, base, 0x548), \
	macro_b(ARMV7M_SCS_NVIC, IPR83, registerAccessReadWrite, base, 0x54c), \
	macro_b(ARMV7M_SCS_NVIC, IPR84, registerAccessReadWrite, base, 0x550), \
	macro_b(ARMV7M_SCS_NVIC, IPR85, registerAccessReadWrite, base, 0x554), \
	macro_b(ARMV7M_SCS_NVIC, IPR86, registerAccessReadWrite, base, 0x558), \
	macro_b(ARMV7M_SCS_NVIC, IPR87, registerAccessReadWrite, base, 0x55c), \
	macro_b(ARMV7M_SCS_NVIC, IPR88, registerAccessReadWrite, base, 0x560), \
	macro_b(ARMV7M_SCS_NVIC, IPR89, registerAccessReadWrite, base, 0x564), \
	macro_b(ARMV7M_SCS_NVIC, IPR90, registerAccessReadWrite, base, 0x568), \
	macro_b(ARMV7M_SCS_NVIC, IPR91, registerAccessReadWrite, base, 0x56c), \
	macro_b(ARMV7M_SCS_NVIC, IPR92, registerAccessReadWrite, base, 0x570), \
	macro_b(ARMV7M_SCS_NVIC, IPR93, registerAccessReadWrite, base, 0x574), \
	macro_b(ARMV7M_SCS_NVIC, IPR94, registerAccessReadWrite, base, 0x578), \
	macro_b(ARMV7M_SCS_NVIC, IPR95, registerAccessReadWrite, base, 0x57c), \
	macro_b(ARMV7M_SCS_NVIC, IPR96, registerAccessReadWrite, base, 0x580), \
	macro_b(ARMV7M_SCS_NVIC, IPR97, registerAccessReadWrite, base, 0x584), \
	macro_b(ARMV7M_SCS_NVIC, IPR98, registerAccessReadWrite, base, 0x588), \
	macro_b(ARMV7M_SCS_NVIC, IPR99, registerAccessReadWrite, base, 0x58c), \
	macro_b(ARMV7M_SCS_NVIC, IPR100, registerAccessReadWrite, base, 0x590), \
	macro_b(ARMV7M_SCS_NVIC, IPR101, registerAccessReadWrite, base, 0x594), \
	macro_b(ARMV7M_SCS_NVIC, IPR102, registerAccessReadWrite, base, 0x598), \
	macro_b(ARMV7M_SCS_NVIC, IPR103, registerAccessReadWrite, base, 0x59c), \
	macro_b(ARMV7M_SCS_NVIC, IPR104, registerAccessReadWrite, base, 0x5a0), \
	macro_b(ARMV7M_SCS_NVIC, IPR105, registerAccessReadWrite, base, 0x5a4), \
	macro_b(ARMV7M_SCS_NVIC, IPR106, registerAccessReadWrite, base, 0x5a8), \
	macro_b(ARMV7M_SCS_NVIC, IPR107, registerAccessReadWrite, base, 0x5ac), \
	macro_b(ARMV7M_SCS_NVIC, IPR108, registerAccessReadWrite, base, 0x5b0), \
	macro_b(ARMV7M_SCS_NVIC, IPR109, registerAccessReadWrite, base, 0x5b4), \
	macro_b(ARMV7M_SCS_NVIC, IPR110, registerAccessReadWrite, base, 0x5b8), \
	macro_b(ARMV7M_SCS_NVIC, IPR111, registerAccessReadWrite, base, 0x5bc), \
	macro_b(ARMV7M_SCS_NVIC, IPR112, registerAccessReadWrite, base, 0x5c0), \
	macro_b(ARMV7M_SCS_NVIC, IPR113, registerAccessReadWrite, base, 0x5c4), \
	macro_b(ARMV7M_SCS_NVIC, IPR114, registerAccessReadWrite, base, 0x5c8), \
	macro_b(ARMV7M_SCS_NVIC, IPR115, registerAccessReadWrite, base, 0x5cc), \
	macro_b(ARMV7M_SCS_NVIC, IPR116, registerAccessReadWrite, base, 0x5d0), \
	macro_b(ARMV7M_SCS_NVIC, IPR117, registerAccessReadWrite, base, 0x5d4), \
	macro_b(ARMV7M_SCS_NVIC, IPR118, registerAccessReadWrite, base, 0x5d8), \
	macro_b(ARMV7M_SCS_NVIC, IPR119, registerAccessReadWrite, base, 0x5dc), \
	macro_b(ARMV7M_SCS_NVIC, IPR120, registerAccessReadWrite, base, 0x5e0), \
	macro_b(ARMV7M_SCS_NVIC, IPR121, registerAccessReadWrite, base, 0x5e4), \
	macro_b(ARMV7M_SCS_NVIC, IPR122, registerAccessReadWrite, base, 0x5e8), \
	macro_b(ARMV7M_SCS_NVIC, IPR123, registerAccessReadWrite, base, 0x5ec)

#define ARMV7M_SCID_INSTANCE(base, macro_a, macro_b) \
	macro_a(ARMV7M_SCS_SCID, ICSR, registerAccessReadWrite, base, 0xD04), \
	macro_b(ARMV7M_SCS_SCID, AIRCR, registerAccessReadWrite, base, 0xD0C), \
	macro_b(ARMV7M_SCS_SCID, SCR, registerAccessReadWrite, base, 0xD10), \
	macro_b(ARMV7M_SCS_SCID, CCR, registerAccessReadWrite, base, 0xD14), \
	macro_b(ARMV7M_SCS_SCID, SHPR1, registerAccessReadWrite, base, 0xD18), \
	macro_b(ARMV7M_SCS_SCID, SHPR2, registerAccessReadWrite, base, 0xD1C), \
	macro_b(ARMV7M_SCS_SCID, SHPR3, registerAccessReadWrite, base, 0xD20), \
	macro_b(ARMV7M_SCS_SCID, CFSR, registerAccessReadWrite, base, 0xD28), \
	macro_b(ARMV7M_SCS_SCID, CPACR, registerAccessReadWrite, base, 0xD88), \
	macro_b(ARMV7M_SCS_SCID, DEMCR, registerAccessReadWrite, base, 0xDFC)

#define NRF_ERRATA_INSTANCE(base, macro_a, macro_b) \
	macro_a(NRF_ERRATA, REG0, registerAccessReadWrite, base, 0xFE0), \
	macro_b(NRF_ERRATA, REG1, registerAccessReadWrite, base, 0xFE4), \
	macro_b(NRF_ERRATA, REG2, registerAccessReadWrite, base, 0xFE8), \
	macro_b(NRF_ERRATA, REG3, registerAccessReadWrite, base, 0xFEc)

#define EXPAND_INSTANCE_LIST_AS(macro)                                                                   \
	macro( NRF_FICR_INSTANCE, 0x10000000 ),                                                            \
	macro( NRF_POWER_INSTANCE, 0x40000000 ),                                                           \
	macro( NRF_CLOCK_INSTANCE, 0x40000000 ),                                                           \
	macro( NRF_RADIO_ERRATA_INSTANCE, 0x40000000 ),                                                    \
	macro( NRF_RADIO_INSTANCE, 0x40001000 ),                                                           \
	macro( NRF_PPI_INSTANCE, 0x4001F000 ),                                                             \
	macro( NRF_UART0_INSTANCE, 0x40002000 ),                                                           \
	macro( NRF_SPIM0_INSTANCE, 0x40003000 ),                                                           \
	macro( NRF_TWIM0_INSTANCE, 0x40003000 ),                                                           \
	macro( NRF_SPIM1_INSTANCE, 0x40004000 ),                                                           \
	macro( NRF_TWIM1_INSTANCE, 0x40004000 ),                                                           \
	macro( NRF_GPIOTE_INSTANCE, 0x40006000 ),                                                          \
	macro( NRF_SAADC_INSTANCE, 0x40007000 ),                                                           \
	macro( NRF_TIMER0_INSTANCE, 0x40008000 ),                                                          \
	macro( NRF_TIMER1_INSTANCE, 0x40009000 ),                                                          \
	macro( NRF_TIMER2_INSTANCE, 0x4000A000 ),                                                          \
	macro( NRF_RTC0_INSTANCE, 0x4000B000 ),                                                            \
	macro( NRF_TEMP_INSTANCE, 0x4000C000 ),                                                            \
	macro( NRF_RNG_INSTANCE, 0x4000D000 ),                                                             \
	macro( NRF_ECB_INSTANCE, 0x4000E000 ),                                                             \
	macro( NRF_WDT_INSTANCE, 0x40010000 ),                                                             \
	macro( NRF_RTC1_INSTANCE, 0x40011000 ),                                                            \
	macro( NRF_QDEC_INSTANCE, 0x40012000 ),                                                            \
	macro( NRF_TIMER3_INSTANCE, 0x4001A000 ),                                                          \
	macro( NRF_TIMER4_INSTANCE, 0x4001B000 ),                                                          \
	macro( NRF_NVMC_INSTANCE, 0x4001E000 ),                                                            \
	macro( NRF_SPIM2_INSTANCE, 0x40004000 ),                                                           \
	macro( NRF_RTC2_INSTANCE, 0x40024000 ),                                                            \
	macro( NRF_P0_INSTANCE, 0x50000000 ),                                                              \
	macro( ARMV7M_NVIC_INSTANCE, 0xE000E000 ),                                                         \
	macro( ARMV7M_SCID_INSTANCE, 0xE000E000 ),                                                         \
	macro( NRF_ERRATA_INSTANCE, 0xF0000000 )

/*
 *
 */
enum {
	EXPAND_INSTANCE_LIST_AS(EXPAND_INSTANCE_AS_REGISTER),
	ARRAY_SIZE,
	EXPAND_INSTANCE_LIST_AS(EXPAND_INSTANCE_AS_INDEX),
};

#endif /* __REGID_H__ */
