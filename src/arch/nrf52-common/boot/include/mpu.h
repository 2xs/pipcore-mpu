/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2022)                */
/*  Copyright (C) 2020-2022 Orange                                             */
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
 * @file        mpu.h
 * @brief       Cortex-M Memory Protection Unit (MPU) Driver Header File
 *
 * @author      Ian Martin <ian@locicontrols.com>
 *
 * @}
 */

#ifndef MPU_H
#define MPU_H

#if defined(NRF52840_XXAA)
#include "nrf52840.h"
#else
#include "nrf52.h"
#endif
#include "core_cm4.h"
#include "trace.h"
#include "mal.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Number of MPU regions available (will vary depending on the Cortex-M version)
 */
#define MPU_NUM_REGIONS ( (MPU->TYPE & MPU_TYPE_DREGION_Msk) >> MPU_TYPE_DREGION_Pos )

/**
 * @brief Number of MPU register aliases available
 */
#define MPU_ALIAS_REG_NB 4

extern void
  MemoryManagement_Handler (void);

/**
 * @brief Access Permission words
 */
enum {
    AP_NO_NO = 0, /**< no access for all levels */
    AP_RW_NO = 1, /**< read/write for privileged level, no access from user level */
    AP_RW_RO = 2, /**< read/write for privileged level, read-only for user level */
    AP_RW_RW = 3, /**< read/write for all levels */
    AP_RO_NO = 5, /**< read-only for privileged level, no access from user level */
    AP_RO_RO = 6, /**< read-only for all levels */
};

/**
 * @brief MPU region sizes
 */
enum {
    MPU_SIZE_32B  =  4, /**<  32 bytes     */
    MPU_SIZE_64B  =  5, /**<  64 bytes     */
    MPU_SIZE_128B =  6, /**< 128 bytes     */
    MPU_SIZE_256B =  7, /**< 256 bytes     */
    MPU_SIZE_512B =  8, /**< 512 bytes     */
    MPU_SIZE_1K   =  9, /**<   1 kilobytes */
    MPU_SIZE_2K   = 10, /**<   2 kilobytes */
    MPU_SIZE_4K   = 11, /**<   4 kilobytes */
    MPU_SIZE_8K   = 12, /**<   8 kilobytes */
    MPU_SIZE_16K  = 13, /**<  16 kilobytes */
    MPU_SIZE_32K  = 14, /**<  32 kilobytes */
    MPU_SIZE_64K  = 15, /**<  64 kilobytes */
    MPU_SIZE_128K = 16, /**< 128 kilobytes */
    MPU_SIZE_256K = 17, /**< 256 kilobytes */
    MPU_SIZE_512K = 18, /**< 512 kilobytes */
    MPU_SIZE_1M   = 19, /**<   1 megabytes */
    MPU_SIZE_2M   = 20, /**<   2 megabytes */
    MPU_SIZE_4M   = 21, /**<   4 megabytes */
    MPU_SIZE_8M   = 22, /**<   8 megabytes */
    MPU_SIZE_16M  = 23, /**<  16 megabytes */
    MPU_SIZE_32M  = 24, /**<  32 megabytes */
    MPU_SIZE_64M  = 25, /**<  64 megabytes */
    MPU_SIZE_128M = 26, /**< 128 megabytes */
    MPU_SIZE_256M = 27, /**< 256 megabytes */
    MPU_SIZE_512M = 28, /**< 512 megabytes */
    MPU_SIZE_1G   = 29, /**<   1 gigabytes */
    MPU_SIZE_2G   = 30, /**<   2 gigabytes */
    MPU_SIZE_4G   = 31, /**<   4 gigabytes */
};

/**
 * @brief convert a region size code to a size in bytes
 *
 * @param[in]   size    region size code, e.g. MPU_SIZE_32B
 *
 * @return region size in bytes
 */
#define MPU_SIZE_TO_BYTES(size) ( (uintptr_t)1 << ((size) + 1) )

/**
 * @brief generate an MPU attribute word suitable for writing to the RASR register
 *
 * @param[in]   xn      eXecute Never flag (forbids instruction fetches)
 * @param[in]   ap      Access Permission word, e.g. AP_RO_RO
 * @param[in]   tex     Type Extension Field
 * @param[in]   c       Cacheable bit
 * @param[in]   b       Bufferable bit
 * @param[in]   s       Sub-Region Disable (SRD) field
 * @param[in]   size    region size code, e.g. MPU_SIZE_32B
 *
 * @return combined region attribute word
 */
static inline uint32_t MPU_ATTR(
    uint32_t xn,
    uint32_t ap,
    uint32_t tex,
    uint32_t c,
    uint32_t b,
    uint32_t s,
    uint32_t size)
{
    return
        (xn   << 28) |
        (ap   << 24) |
        (tex  << 19) |
        (s    << 18) |
        (c    << 17) |
        (b    << 16) |
        (size <<  1);
}

/**
 * @brief disable the MPU
 *
 * @return 0 on success
 * @return <0 on failure or no MPU present
 */
int __attribute__((section(".text_pip_mal"))) mpu_disable(void);

/**
 * @brief enable the MPU
 *
 * @return 0 on success
 * @return <0 on failure or no MPU present
 */
int __attribute__((section(".text_pip_mal"))) mpu_enable(void);

/**
 * @brief test if the MPU is enabled
 *
 * @return true if enabled
 * @return false if disabled
 */
int __attribute__((section(".text_pip_mal"))) mpu_enabled(void);

/*!
 * \fn int mpu_init(void)
 * \brief Resets the physical MPU
 * \return 0:Success/-1:Error
 */
int __attribute__((section(".text_pip_mal"))) mpu_init(void);

/**
 * @brief configure the base address and attributes for an MPU region
 *
 * @param[in]   region  MPU region to configure (0 <= @p region < MPU_NUM_REGIONS)
 * @param[in]   base    base address in RAM (aligned to the size specified within @p attr)
 * @param[in]   attr    attribute word generated by MPU_ATTR()
 *
 * @return 0 on success
 * @return <0 on failure or no MPU present
 */
int __attribute__((section(".text_pip_mal"))) mpu_configure(uint_fast8_t region, uintptr_t base, uint_fast32_t attr);

/**
 * @brief configure the MPU based on a lookup table (LUT)
 *
 * @param[in]   LUT     MPU regions to configure
 *
 * @return 0 on success
 * @return <0 on failure
 */
int __attribute__((section(".text_pip_mal"))) mpu_configure_from_LUT(uint32_t* LUT);

uint32_t*__attribute__((section(".text_pip_mal"))) readPhysicalMPUStartAddr(uint32_t MPURegionNb); //!< the physical MPU region's start address
uint32_t*__attribute__((section(".text_pip_mal"))) readPhysicalMPUEndAddr(uint32_t MPURegionNb); //!< the physical MPU region's end address
uint32_t __attribute__((section(".text_pip_mal"))) readPhysicalMPUAP(uint32_t MPURegionNb); //!< the physical MPU region's RW bit
uint32_t __attribute__((section(".text_pip_mal"))) readPhysicalMPUXN(uint32_t MPURegionNb); //!< the physical MPU region's X bit
uint32_t __attribute__((section(".text_pip_mal"))) readPhysicalMPUSizeBits(uint32_t MPURegionNb); //!< the physical MPU region's region bits (size in log2)
uint32_t __attribute__((section(".text_pip_mal"))) readPhysicalMPUSizeBytes(uint32_t MPURegionNb); //!< the physical MPU region's region size in bytes
uint32_t __attribute__((section(".text_pip_mal"))) readPhysicalMPURegionEnable(uint32_t MPURegionNb); //!< the physical MPU region's enable bit


#ifdef __cplusplus
}
#endif


#endif /* MPU_H */
