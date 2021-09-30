###############################################################################
#  © Université de Lille, The Pip Development Team (2015-2021)                #
#                                                                             #
#  This software is a computer program whose purpose is to run a minimal,     #
#  hypervisor relying on proven properties such as memory isolation.          #
#                                                                             #
#  This software is governed by the CeCILL license under French law and       #
#  abiding by the rules of distribution of free software.  You can  use,      #
#  modify and/ or redistribute the software under the terms of the CeCILL     #
#  license as circulated by CEA, CNRS and INRIA at the following URL          #
#  "http://www.cecill.info".                                                  #
#                                                                             #
#  As a counterpart to the access to the source code and  rights to copy,     #
#  modify and redistribute granted by the license, users are provided only    #
#  with a limited warranty  and the software's author,  the holder of the     #
#  economic rights,  and the successive licensors  have only  limited         #
#  liability.                                                                 #
#                                                                             #
#  In this respect, the user's attention is drawn to the risks associated     #
#  with loading,  using,  modifying and/or developing or reproducing the      #
#  software by the user in light of its specific status of free software,     #
#  that may mean  that it is complicated to manipulate,  and  that  also      #
#  therefore means  that it is reserved for developers  and  experienced      #
#  professionals having in-depth computer knowledge. Users are therefore      #
#  encouraged to load and test the software's suitability as regards their    #
#  requirements in conditions enabling the security of their systems and/or   #
#  data to be ensured and,  more generally, to use and operate it in the      #
#  same conditions as regards security.                                       #
#                                                                             #
#  The fact that you are presently reading this means that you have had       #
#  knowledge of the CeCILL license and that you accept its terms.             #
###############################################################################

# Tool to convert Coq code into C code
DIGGER_DIR  = tools/digger
DIGGER     := $(DIGGER_DIR)/digger

# Coq Proof Assistant
COQC   := coqc -q
COQDEP := coqdep -c
COQDOC := coqdoc -toc -interpolate -utf8 -html

# GNU C Compiler
CC  := arm-none-eabi-gcc

# Netwide assembler
AS  := arm-none-eabi-as

# GNU Linker
LD  := arm-none-eabi-ld

# GNU Objcopy
BI  := arm-none-eabi-objcopy

# GNU Debugger
GDB :=

################# Compilation options #################

TARGET    = dwm1001
PARTITION =

# Check the unit tests
UNIT_TESTS   ?=
UNIT_CFLAGS   = -DUNIT_TESTS

# Semihosting DEBUG (to enable for unit testing), default
# printf has bug, using trace_printf instead
SEMI_DEBUG   ?= yes
SEMI_CFLAGS   = -DTRACE
SEMI_CFLAGS  += -Dprintf=trace_printf
SEMI_CFLAGS  += -DOS_USE_TRACE_SEMIHOSTING_DEBUG

# UART DEBUG (to disable for unit testing)
UART_DEBUG   ?=
UART_CFLAGS  += -DUART_DEBUG

# Dump outputs allowed
DUMP         ?=
DUMP_CFLAGS   = -DDUMP

# Check debugging mode
ifdef SEMI_DEBUG
  ifdef UART_DEBUG
    $(error [Error] Choose either semihosting or UART for debugging)
  endif
endif

# Check boot sequence
ifdef UNIT_TESTS
  ifdef UART_DEBUG
    $(error [Error] Unit tests only run in semihosting not UART)
  endif
endif

# Arch related options
ARCH_CFLAGS   = -mthumb
ARCH_CFLAGS  += -mcpu=cortex-m4
ARCH_CFLAGS  += -Isrc/arch/$(TARGET)/boot/thirdparty/cmsis/include
ARCH_CFLAGS  += -Isrc/arch/$(TARGET)/boot/include
ARCH_CFLAGS  += -Isrc/arch/$(TARGET)/boot/thirdparty/mdk/include
ARCH_CFLAGS  += -Isrc/arch/$(TARGET)/boot/thirdparty/debug/include
ARCH_CFLAGS  += -Isrc/arch/$(TARGET)/boot/thirdparty/uart/include
ARCH_CFLAGS  += -Isrc/interface
ARCH_CFLAGS  += -Isrc/arch/$(TARGET)/MAL/include
ARCH_CFLAGS  += -Ibuild/$(TARGET)/pipcore
ARCH_CFLAGS  += $(if $(UNIT_TESTS), $(UNIT_CFLAGS))
ARCH_CFLAGS  += $(if $(SEMI_DEBUG), $(SEMI_CFLAGS))
ARCH_CFLAGS  += $(if $(UART_DEBUG), $(UART_CFLAGS))
ARCH_CFLAGS  += $(if $(DUMP),       $(DUMP_CFLAGS))
ARCH_CFLAGS  += -DNRF52832_XXAA

ARCH_LDFLAGS  = -nostartfiles
ARCH_LDFLAGS += -lc
ARCH_LDFLAGS += -lgcc
ARCH_LDFLAGS += -lm
ARCH_LDFLAGS += -std=gnu11
ARCH_LDFLAGS += -Wall
ARCH_LDFLAGS += -ffreestanding
ARCH_LDFLAGS += -mthumb
ARCH_LDFLAGS += -mcpu=cortex-m4

ARCH_ASFLAGS  =

# Debug related options
DEBUG_CFLAGS  = -g
DEBUG_CFLAGS += -Og

# If the DEBUG variable is set, the output binary will
# be in debug mode. Otherwise, if the DEBUG variable is
# not set, the output binary will be in released mode.
DEBUG = yes

################## Execution options ##################

GDBARGS =
