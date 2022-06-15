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

#include "register_range.h"
#include "register_accessor.h"

#define RANGE0_NUMBER 16
#define RANGE1_NUMBER 124
#define RANGE2_NUMBER 1
#define RANGE3_NUMBER 5
#define RANGE4_NUMBER 1
#define RANGE5_NUMBER 4

static const registerAccessor_t
range0[RANGE0_NUMBER]
__attribute__((section(".rodata"))) =
{
	/* 0xE000E100: NVIC_ISER0 */
	registerAccessReadWrite,
	/* 0xE000E104: NVIC_ISER1 */
	registerAccessReadWrite,
	/* 0xE000E108: NVIC_ISER2 */
	registerAccessReadWrite,
	/* 0xE000E10C: NVIC_ISER3 */
	registerAccessReadWrite,
	/* 0xE000E110: NVIC_ISER4 */
	registerAccessReadWrite,
	/* 0xE000E114: NVIC_ISER5 */
	registerAccessReadWrite,
	/* 0xE000E118: NVIC_ISER6 */
	registerAccessReadWrite,
	/* 0xE000E11C: NVIC_ISER7 */
	registerAccessReadWrite,
	/* 0xE000E120: NVIC_ISER8 */
	registerAccessReadWrite,
	/* 0xE000E124: NVIC_ISER9 */
	registerAccessReadWrite,
	/* 0xE000E128: NVIC_ISER10 */
	registerAccessReadWrite,
	/* 0xE000E12C: NVIC_ISER11 */
	registerAccessReadWrite,
	/* 0xE000E130: NVIC_ISER12 */
	registerAccessReadWrite,
	/* 0xE000E134: NVIC_ISER13 */
	registerAccessReadWrite,
	/* 0xE000E138: NVIC_ISER14 */
	registerAccessReadWrite,
	/* 0xE000E13C: NVIC_ISER15 */
	registerAccessReadWrite,
};

static const registerAccessor_t
range1[RANGE1_NUMBER]
__attribute__((section(".rodata"))) =
{
	/* 0xE000E400: NVIC_IPR0 */
	registerAccessReadWrite,
	/* 0xE000E404: NVIC_IPR1 */
	registerAccessReadWrite,
	/* 0xE000E408: NVIC_IPR2 */
	registerAccessReadWrite,
	/* 0xE000E40C: NVIC_IPR3 */
	registerAccessReadWrite,
	/* 0xE000E410: NVIC_IPR4 */
	registerAccessReadWrite,
	/* 0xE000E414: NVIC_IPR5 */
	registerAccessReadWrite,
	/* 0xE000E418: NVIC_IPR6 */
	registerAccessReadWrite,
	/* 0xE000E41C: NVIC_IPR7 */
	registerAccessReadWrite,
	/* 0xE000E420: NVIC_IPR8 */
	registerAccessReadWrite,
	/* 0xE000E424: NVIC_IPR9 */
	registerAccessReadWrite,
	/* 0xE000E428: NVIC_IPR10 */
	registerAccessReadWrite,
	/* 0xE000E42C: NVIC_IPR11 */
	registerAccessReadWrite,
	/* 0xE000E430: NVIC_IPR12 */
	registerAccessReadWrite,
	/* 0xE000E434: NVIC_IPR13 */
	registerAccessReadWrite,
	/* 0xE000E438: NVIC_IPR14 */
	registerAccessReadWrite,
	/* 0xE000E43C: NVIC_IPR15 */
	registerAccessReadWrite,
	/* 0xE000E440: NVIC_IPR16 */
	registerAccessReadWrite,
	/* 0xE000E444: NVIC_IPR17 */
	registerAccessReadWrite,
	/* 0xE000E448: NVIC_IPR18 */
	registerAccessReadWrite,
	/* 0xE000E44C: NVIC_IPR19 */
	registerAccessReadWrite,
	/* 0xE000E450: NVIC_IPR20 */
	registerAccessReadWrite,
	/* 0xE000E454: NVIC_IPR21 */
	registerAccessReadWrite,
	/* 0xE000E458: NVIC_IPR22 */
	registerAccessReadWrite,
	/* 0xE000E45C: NVIC_IPR23 */
	registerAccessReadWrite,
	/* 0xE000E460: NVIC_IPR24 */
	registerAccessReadWrite,
	/* 0xE000E464: NVIC_IPR25 */
	registerAccessReadWrite,
	/* 0xE000E468: NVIC_IPR26 */
	registerAccessReadWrite,
	/* 0xE000E46C: NVIC_IPR27 */
	registerAccessReadWrite,
	/* 0xE000E470: NVIC_IPR28 */
	registerAccessReadWrite,
	/* 0xE000E474: NVIC_IPR29 */
	registerAccessReadWrite,
	/* 0xE000E478: NVIC_IPR30 */
	registerAccessReadWrite,
	/* 0xE000E47C: NVIC_IPR31 */
	registerAccessReadWrite,
	/* 0xE000E480: NVIC_IPR32 */
	registerAccessReadWrite,
	/* 0xE000E484: NVIC_IPR33 */
	registerAccessReadWrite,
	/* 0xE000E488: NVIC_IPR34 */
	registerAccessReadWrite,
	/* 0xE000E48C: NVIC_IPR35 */
	registerAccessReadWrite,
	/* 0xE000E490: NVIC_IPR36 */
	registerAccessReadWrite,
	/* 0xE000E494: NVIC_IPR37 */
	registerAccessReadWrite,
	/* 0xE000E498: NVIC_IPR38 */
	registerAccessReadWrite,
	/* 0xE000E49C: NVIC_IPR39 */
	registerAccessReadWrite,
	/* 0xE000E4A0: NVIC_IPR40 */
	registerAccessReadWrite,
	/* 0xE000E4A4: NVIC_IPR41 */
	registerAccessReadWrite,
	/* 0xE000E4A8: NVIC_IPR42 */
	registerAccessReadWrite,
	/* 0xE000E4AC: NVIC_IPR43 */
	registerAccessReadWrite,
	/* 0xE000E4B0: NVIC_IPR44 */
	registerAccessReadWrite,
	/* 0xE000E4B4: NVIC_IPR45 */
	registerAccessReadWrite,
	/* 0xE000E4B8: NVIC_IPR46 */
	registerAccessReadWrite,
	/* 0xE000E4BC: NVIC_IPR47 */
	registerAccessReadWrite,
	/* 0xE000E4C0: NVIC_IPR48 */
	registerAccessReadWrite,
	/* 0xE000E4C4: NVIC_IPR49 */
	registerAccessReadWrite,
	/* 0xE000E4C8: NVIC_IPR50 */
	registerAccessReadWrite,
	/* 0xE000E4CC: NVIC_IPR51 */
	registerAccessReadWrite,
	/* 0xE000E4D0: NVIC_IPR52 */
	registerAccessReadWrite,
	/* 0xE000E4D4: NVIC_IPR53 */
	registerAccessReadWrite,
	/* 0xE000E4D8: NVIC_IPR54 */
	registerAccessReadWrite,
	/* 0xE000E4DC: NVIC_IPR55 */
	registerAccessReadWrite,
	/* 0xE000E4E0: NVIC_IPR56 */
	registerAccessReadWrite,
	/* 0xE000E4E4: NVIC_IPR57 */
	registerAccessReadWrite,
	/* 0xE000E4E8: NVIC_IPR58 */
	registerAccessReadWrite,
	/* 0xE000E4EC: NVIC_IPR59 */
	registerAccessReadWrite,
	/* 0xE000E4F0: NVIC_IPR60 */
	registerAccessReadWrite,
	/* 0xE000E4F4: NVIC_IPR61 */
	registerAccessReadWrite,
	/* 0xE000E4F8: NVIC_IPR62 */
	registerAccessReadWrite,
	/* 0xE000E4FC: NVIC_IPR63 */
	registerAccessReadWrite,
	/* 0xE000E500: NVIC_IPR64 */
	registerAccessReadWrite,
	/* 0xE000E504: NVIC_IPR65 */
	registerAccessReadWrite,
	/* 0xE000E508: NVIC_IPR66 */
	registerAccessReadWrite,
	/* 0xE000E50C: NVIC_IPR67 */
	registerAccessReadWrite,
	/* 0xE000E510: NVIC_IPR68 */
	registerAccessReadWrite,
	/* 0xE000E514: NVIC_IPR69 */
	registerAccessReadWrite,
	/* 0xE000E518: NVIC_IPR70 */
	registerAccessReadWrite,
	/* 0xE000E51C: NVIC_IPR71 */
	registerAccessReadWrite,
	/* 0xE000E520: NVIC_IPR72 */
	registerAccessReadWrite,
	/* 0xE000E524: NVIC_IPR73 */
	registerAccessReadWrite,
	/* 0xE000E528: NVIC_IPR74 */
	registerAccessReadWrite,
	/* 0xE000E52C: NVIC_IPR75 */
	registerAccessReadWrite,
	/* 0xE000E530: NVIC_IPR76 */
	registerAccessReadWrite,
	/* 0xE000E534: NVIC_IPR77 */
	registerAccessReadWrite,
	/* 0xE000E538: NVIC_IPR78 */
	registerAccessReadWrite,
	/* 0xE000E53C: NVIC_IPR79 */
	registerAccessReadWrite,
	/* 0xE000E540: NVIC_IPR80 */
	registerAccessReadWrite,
	/* 0xE000E544: NVIC_IPR81 */
	registerAccessReadWrite,
	/* 0xE000E548: NVIC_IPR82 */
	registerAccessReadWrite,
	/* 0xE000E54C: NVIC_IPR83 */
	registerAccessReadWrite,
	/* 0xE000E550: NVIC_IPR84 */
	registerAccessReadWrite,
	/* 0xE000E554: NVIC_IPR85 */
	registerAccessReadWrite,
	/* 0xE000E558: NVIC_IPR86 */
	registerAccessReadWrite,
	/* 0xE000E55C: NVIC_IPR87 */
	registerAccessReadWrite,
	/* 0xE000E560: NVIC_IPR88 */
	registerAccessReadWrite,
	/* 0xE000E564: NVIC_IPR89 */
	registerAccessReadWrite,
	/* 0xE000E568: NVIC_IPR90 */
	registerAccessReadWrite,
	/* 0xE000E56C: NVIC_IPR91 */
	registerAccessReadWrite,
	/* 0xE000E570: NVIC_IPR92 */
	registerAccessReadWrite,
	/* 0xE000E574: NVIC_IPR93 */
	registerAccessReadWrite,
	/* 0xE000E578: NVIC_IPR94 */
	registerAccessReadWrite,
	/* 0xE000E57C: NVIC_IPR95 */
	registerAccessReadWrite,
	/* 0xE000E580: NVIC_IPR96 */
	registerAccessReadWrite,
	/* 0xE000E584: NVIC_IPR97 */
	registerAccessReadWrite,
	/* 0xE000E588: NVIC_IPR98 */
	registerAccessReadWrite,
	/* 0xE000E58C: NVIC_IPR99 */
	registerAccessReadWrite,
	/* 0xE000E590: NVIC_IPR100 */
	registerAccessReadWrite,
	/* 0xE000E594: NVIC_IPR101 */
	registerAccessReadWrite,
	/* 0xE000E598: NVIC_IPR102 */
	registerAccessReadWrite,
	/* 0xE000E59C: NVIC_IPR103 */
	registerAccessReadWrite,
	/* 0xE000E5A0: NVIC_IPR104 */
	registerAccessReadWrite,
	/* 0xE000E5A4: NVIC_IPR105 */
	registerAccessReadWrite,
	/* 0xE000E5A8: NVIC_IPR106 */
	registerAccessReadWrite,
	/* 0xE000E5AC: NVIC_IPR107 */
	registerAccessReadWrite,
	/* 0xE000E5B0: NVIC_IPR108 */
	registerAccessReadWrite,
	/* 0xE000E5B4: NVIC_IPR109 */
	registerAccessReadWrite,
	/* 0xE000E5B8: NVIC_IPR110 */
	registerAccessReadWrite,
	/* 0xE000E5BC: NVIC_IPR111 */
	registerAccessReadWrite,
	/* 0xE000E5C0: NVIC_IPR112 */
	registerAccessReadWrite,
	/* 0xE000E5C4: NVIC_IPR113 */
	registerAccessReadWrite,
	/* 0xE000E5C8: NVIC_IPR114 */
	registerAccessReadWrite,
	/* 0xE000E5CC: NVIC_IPR115 */
	registerAccessReadWrite,
	/* 0xE000E5D0: NVIC_IPR116 */
	registerAccessReadWrite,
	/* 0xE000E5D4: NVIC_IPR117 */
	registerAccessReadWrite,
	/* 0xE000E5D8: NVIC_IPR118 */
	registerAccessReadWrite,
	/* 0xE000E5DC: NVIC_IPR119 */
	registerAccessReadWrite,
	/* 0xE000E5E0: NVIC_IPR120 */
	registerAccessReadWrite,
	/* 0xE000E5E4: NVIC_IPR121 */
	registerAccessReadWrite,
	/* 0xE000E5E8: NVIC_IPR122 */
	registerAccessReadWrite,
	/* 0xE000E5EC: NVIC_IPR123 */
	registerAccessReadWrite,
};

static const registerAccessor_t
range2[RANGE2_NUMBER]
__attribute__((section(".rodata"))) =
{
	/* 0xE000ED04: ICSR */
	registerAccessReadWrite,
};

static const registerAccessor_t
range3[RANGE3_NUMBER]
__attribute__((section(".rodata"))) =
{
	/* 0xE000ED10: SCR */
	registerAccessReadWrite,
	/* 0xE000ED14: CCR */
	registerAccessReadWrite,
	/* 0xE000ED18: SHPR1 */
	registerAccessReadWrite,
	/* 0xE000ED1C: SHPR2 */
	registerAccessReadWrite,
	/* 0xE000ED20: SHPR3 */
	registerAccessReadWrite,
};

static const registerAccessor_t
range4[RANGE4_NUMBER]
__attribute__((section(".rodata"))) =
{
	/* 0xE000ED88: CPACR */
	registerAccessReadWrite,
};

static const registerAccessor_t
range5[RANGE5_NUMBER]
__attribute__((section(".rodata"))) =
{
	/* 0xF0000FE0: FTPANR0 */
	registerAccessRead,
	/* 0xF0000FE4: FTPANR1 */
	registerAccessRead,
	/* 0xF0000FE8: FTPANR2 */
	registerAccessRead,
	/* 0xF0000FEC: FTPANR3 */
	registerAccessRead,
};

const registerAccessorRange_t
registerAccessorRanges[REGISTER_RANGE_NUMBER]
__attribute__((section(".rodata"))) =
{
	/* 0xE000E100-0xE000E13C */
	{
		.registerAccessors    = range0,
		.registerAccessorSize = RANGE0_NUMBER,
		.baseAddress          = 0xE000E100,
	},
	/* 0xE000E400-0xE000E5EC */
	{
		.registerAccessors    = range1,
		.registerAccessorSize = RANGE1_NUMBER,
		.baseAddress          = 0xE000E400,
	},
	/* 0xE000ED04-0xE000ED04 */
	{
		.registerAccessors    = range2,
		.registerAccessorSize = RANGE2_NUMBER,
		.baseAddress          = 0xE000ED04,
	},
	/* 0xE000ED10-0xE000ED20 */
	{
		.registerAccessors    = range3,
		.registerAccessorSize = RANGE3_NUMBER,
		.baseAddress          = 0xE000ED10,
	},
	/* 0xE000ED88-0xE000ED88 */
	{
		.registerAccessors    = range4,
		.registerAccessorSize = RANGE4_NUMBER,
		.baseAddress          = 0xE000ED88,
	},
	/* 0xF0000FE0-0xF0000FEC */
	{
		.registerAccessors    = range5,
		.registerAccessorSize = RANGE5_NUMBER,
		.baseAddress          = 0xF0000FE0,
	},
};
