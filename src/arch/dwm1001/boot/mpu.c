/*
 * Copyright (C) 2016 Loci Controls Inc.
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

/**
 * @ingroup     cpu_cortexm_common
 * @{
 *
 * @file        mpu.c
 * @brief       Cortex-M Memory Protection Unit (MPU) Driver
 *
 * @author      Ian Martin <ian@locicontrols.com>
 *
 * @}
 */


#include "mpu.h"
#include <string.h> // include memcpy
#include <stdint.h>
#include "pip_debug.h"
#include "stdio.h"

/*!
 * \fn int mpu_disable(void)
 * \brief Disable the physical MPU
 * \return 0:Yes/-1:No
 */
int mpu_disable(void) {
#if __MPU_PRESENT
    MPU->CTRL &= ~MPU_CTRL_ENABLE_Msk;
    return 0;
#else
    return -1;
#endif
}

/*!
 * \fn int mpu_enable(void)
 * \brief Enable the physical MPU with the PRIVDEFENA flag
 * \return 0:Yes/-1:No
 */
int mpu_enable(void) {
#if __MPU_PRESENT
    MPU->CTRL |= MPU_CTRL_PRIVDEFENA_Msk | MPU_CTRL_ENABLE_Msk;

#ifdef SCB_SHCSR_MEMFAULTENA_Msk
    /* Enable the memory fault exception if SCB SHCSR (System Handler Control
     * and State Register) has a separate bit for mem faults. That is the case
     * on ARMv7-M. ARMv6-M does not support separate exception enable for mem
     * faults and all fault conditions cause a HardFault. */
    SCB->SHCSR |= SCB_SHCSR_MEMFAULTENA_Msk;
#else
    return -1; // the Memory Management fault handler must be enabled
#endif

    return 0;
#else
    return -1;
#endif
}

/*!
 * \fn int mpu_enabled(void)
 * \brief Check if MPU is enabled
 * \return 1:Yes/0:No
 */
int mpu_enabled(void) {
#if __MPU_PRESENT
    return (MPU->CTRL & MPU_CTRL_ENABLE_Msk) != 0;
#else
    return 0;
#endif
}

/*!
 * \fn int mpu_init(void)
 * \brief Resets the physical MPU
 * \return 0:Success/-1:Error
 */
int mpu_init(void) {
	__DMB();
    // Disable MPU
	mpu_disable();
#if __MPU_PRESENT && !defined(__ARM_ARCH_8M_MAIN__) && !defined(__ARM_ARCH_8M_BASE__)
    for (uint32_t i = 0; i < MPU_NUM_REGIONS ; i++){
        MPU->RNR  = i; // no need if VALID bit with REGION bits are set in RBAR
        MPU->RBAR = 0;
        MPU->RASR = 0;
    }
    // Enable MPU
    mpu_enable();
    __ISB();
	__DSB();
    return 0;
#else
    return -1;
#endif
}

int mpu_configure_region(uint_fast8_t region, uintptr_t base, uint_fast32_t attr) {
    /* Todo enable MPU support for Cortex-M23/M33 */
#if __MPU_PRESENT && !defined(__ARM_ARCH_8M_MAIN__) && !defined(__ARM_ARCH_8M_BASE__)
    MPU->RNR  = region;
    MPU->RBAR = base & MPU_RBAR_ADDR_Msk;
    MPU->RASR = attr | MPU_RASR_ENABLE_Msk;

    return 0;
#else
    (void)region;
    (void)base;
    (void)attr;
    return -1;
#endif
}

/** Memcopy with strictly ordered memory access, e.g. for register targets.
*   Replaces memcpy of string.h
* \param dst Destination data is copied to.
* \param src Source data is copied from.
* \param len Amount of data words to be copied.
*/
__STATIC_INLINE void orderedCpy(volatile uint32_t* dst, const uint32_t* src, uint32_t len)
{
  uint32_t i;
  for (i = 0U; i < len; ++i)
  {
    dst[i] = src[i];
  }
}

/**
 * @brief configure the MPU based on a lookup table (LUT)
 *
 * @param[in]   LUT     MPU regions to configure
 *
 * @return 0 on success
 * @return <0 on failure
 */
int mpu_configure_from_LUT(uint32_t* LUT)
{
    __DMB();
    // Disable MPU
	mpu_disable();

	// Configure MPU
#if defined(__ARM_ARCH_7M__) || defined(__ARM_ARCH_7EM__)
	// ARM warning: You can normally use the memcpy() function in a C/C++ compiler for this sequence. However, you must verify that the compiler uses word transfers.
	/*for (int i = 0; i < MPU_NUM_REGIONS ; i = i+MPU_ALIAS_REG_NB)
	{
		// Copy a subset of the LUT into the alias registers -> MPU_ALIAS_REG_NB regions configuration
		orderedCpy((void*)&( MPU->RBAR), LUT+i*2*sizeof(uint32_t), MPU_ALIAS_REG_NB*2*sizeof(uint32_t));

	}*/
    for (uint32_t i = 0; i < MPU_NUM_REGIONS ; i++){
        //MPU->RNR  = i; // no need if VALID bit with REGION bits are set in RBAR
        MPU->RBAR = LUT[i*2];
        MPU->RASR = LUT[i*2+1];
    }
    // Enable MPU with PRIVDEFENA
	mpu_enable();
#endif
#if defined(__ARM_ARCH_8M_MAIN__) || defined(__ARM_ARCH_8M_BASE__)
    return -1;
#endif
	// Enable MPU with PRIVDEFENA
	mpu_enable();
	__ISB();
	__DSB();
    return 0;
}

/*!
 * \fn uint32_t readPhysicalMPUSizeBits(uint32_t MPURegionNb)
 * \brief Reads the given physical MPU region's size (in bits)
 * \param MPURegionNb the physical MPU region to read from
 * \return the physical MPU region's size in bits (region size = 2^(size in bits+1))
 */
uint32_t readPhysicalMPUSizeBits(uint32_t MPURegionNb)
{
    MPU->RNR  = MPURegionNb;
    return (MPU->RASR & MPU_RASR_SIZE_Msk) >> MPU_RASR_SIZE_Pos;
}

/*!
 * \fn uint32_t readPhysicalMPUSizeBytes(uint32_t MPURegionNb)
 * \brief Reads the given physical MPU region's size (in bytes)
 * \param MPURegionNb the physical MPU region to read from
 * \return the physical MPU region's size in bytes (region size = 2^(size in bits+1))
 */
uint32_t readPhysicalMPUSizeBytes(uint32_t MPURegionNb)
{
    MPU->RNR  = MPURegionNb;
    uint32_t size = (MPU->RASR & MPU_RASR_SIZE_Msk) >> MPU_RASR_SIZE_Pos;
    return (size == 0) ? 0 : 1 << (size+1);
}

/*!
 * \fn uint32_t* readPhysicalMPUStartAddr(uint32_t MPURegionNb)
 * \brief Reads the given physical MPU region's start address
 * \param MPURegionNb the physical MPU region to read from
 * \return the physical MPU region's start address
 */
uint32_t* readPhysicalMPUStartAddr(uint32_t MPURegionNb)
{
    MPU->RNR  = MPURegionNb;
    return (uint32_t*)((MPU->RBAR & MPU_RBAR_ADDR_Msk));
}

/*!
 * \fn uint32_t* readPhysicalMPUEndAddr(uint32_t MPURegionNb)
 * \brief Reads the given physical MPU region's end address
 * \param MPURegionNb the physical MPU region to read from
 * \return the physical MPU region's end address
 */
uint32_t* readPhysicalMPUEndAddr(uint32_t MPURegionNb)
{
    // Cast in order to offset the start address in bytes not in addresses
    uint32_t start = (uint32_t) readPhysicalMPUStartAddr(MPURegionNb);
    uint32_t size = readPhysicalMPUSizeBytes(MPURegionNb);
    return (uint32_t*) (start + size - 1);
}

/*!
 * \fn uint32_t readPhysicalMPUAP(uint32_t MPURegionNb)
 * \brief Reads the given physical MPU region's RW permissions
 * \param MPURegionNb the physical MPU region to read from
 * \return the physical MPU region's RW permissions
 */
uint32_t readPhysicalMPUAP(uint32_t MPURegionNb)
{
    MPU->RNR  = MPURegionNb;
    return (MPU->RASR & MPU_RASR_AP_Msk) >> MPU_RASR_AP_Pos;
}


/*!
 * \fn uint32_t readPhysicalMPUXN(uint32_t MPURegionNb)
 * \brief Reads the given physical MPU region's X permission
 * \param MPURegionNb the physical MPU region to read from
 * \return the physical MPU region's X permission (XN = 0 -> execute right)
 */
uint32_t readPhysicalMPUXN(uint32_t MPURegionNb)
{
    MPU->RNR  = MPURegionNb;
    return (MPU->RASR & MPU_RASR_XN_Msk) >> MPU_RASR_XN_Pos;
}

/*!
 * \fn uint32_t readPhysicalMPURegionEnable(uint32_t MPURegionNb)
 * \brief Reads the given physical MPU region's enable bit
 * \param MPURegionNb the physical MPU region to read from
 * \return the physical MPU region's enable bit
 */
uint32_t readPhysicalMPURegionEnable(uint32_t MPURegionNb)
{
    MPU->RNR  = MPURegionNb;
    return (MPU->RASR & MPU_RASR_ENABLE_Msk);
}
