CC = arm-none-eabi-gcc
AS = arm-none-eabi-as
#LD = arm-none-eabi-ld
BI = arm-none-eabi-objcopy

# UART DEBUG (to disable for unit testing)
UART_DEBUG ?= no
# Semihosting DEBUG (to enable for unit testing)
SEMI_DEBUG ?= yes

# UNIT TESTS
UNIT_TESTS ?= no

# DUMP OUTPUTS ALLOWED
DUMP ?= no

# LINKER VARIABLES
TARGET = dwm1001
BUILD_DIR=build
SRC_DIR=src

TARGET_SRC_DIR=$(SRC_DIR)/arch/$(TARGET)
TARGET_SRC_BOOT_DIR=$(TARGET_SRC_DIR)/boot
TARGET_SRC_MAL_DIR=$(TARGET_SRC_DIR)/MAL

TARGET_DIR=$(BUILD_DIR)/$(TARGET)
KERNEL_BASENAME=pip
#KERNEL_ELF=$(KERNEL_BASENAME).elf
#KERNEL_BIN=$(KERNEL_BASENAME).bin
LINKSCRIPT := $(TARGET_SRC_DIR)/link.ld

DIGGER_DIR=tools/digger
DIGGER=$(DIGGER_DIR)/digger

COQDEP=coqdep -c
COQC=coqc -q
COQDOC=coqdoc -toc -interpolate -utf8 -html

## COMPILER FLAGS
CFLAGS  = -mthumb
CFLAGS += -mcpu=cortex-m4
CFLAGS += -I$(TARGET_SRC_BOOT_DIR)/thirdparty/cmsis/include
CFLAGS += -I$(TARGET_SRC_BOOT_DIR)
#CFLAGS += -I$(TARGET_SRC_BOOT_DIR)/thirdparty/newlib
#CFLAGS += -lc
#CFLAGS += -I/usr/arm-none-eabi/include
#CFLAGS += -nostdinc
#CFLAGS += --specs=nano.specs
#CFLAGS += --specs=nosys.specs
CFLAGS += -I$(TARGET_SRC_BOOT_DIR)/thirdparty/mdk
CFLAGS += -I$(SRC_DIR)/interface
CFLAGS += -I$(TARGET_SRC_MAL_DIR)/include
CFLAGS += -I$(TARGET_DIR)/pipcore
# include debug symbols
CFLAGS += -g # debug symbols for GDB -DDEBUG
CFLAGS += -Og # optimize debugging experience more than -O0

ifeq ($(UNIT_TESTS), yes)
  # check the unit tests
  CFLAGS += -DUNIT_TESTS
endif

ifeq ($(SEMI_DEBUG), yes)
  # debug through semihosting, default printf has bug, using trace_printf instead
  CFLAGS += -DTRACE
  CFLAGS += -Dprintf=trace_printf
  CFLAGS += -DOS_USE_TRACE_SEMIHOSTING_DEBUG
  CFLAGS += -I$(TARGET_SRC_BOOT_DIR)/thirdparty/debug # debug on semihosting debug channel and trace API
endif

ifeq ($(UART_DEBUG), yes)
  # debug through UART
  CFLAGS += -I$(TARGET_SRC_BOOT_DIR)/thirdparty/debug
  CFLAGS += -DUART_DEBUG
  CFLAGS += -I$(TARGET_SRC_BOOT_DIR)/thirdparty/uart
endif

ifeq ($(DUMP), yes)
  # dump outputs allowed
  CFLAGS += -DDUMP
endif

#CFLAGS += -fmessage-length=0
#CFLAGS += -ffunction-sections
#CFLAGS += -fdata-sections
#CFLAGS += --specs=nosys.specs
CFLAGS += -DNRF52832_XXAA

# LINKER FLAGS
LDFLAGS += -nostartfiles  # do not include start files but keep default libs: -nostdlib = -nostartfiles + -nodefaultlibs
LDFLAGS += -lc
LDFLAGS += -lgcc
LDFLAGS += -lm
LDFLAGS += -std=gnu11
LDFLAGS += -Wall # recommended compiler warnings
LDFLAGS += -ffreestanding # remove printf to puts optimizations
LDFLAGS += -mthumb
LDFLAGS += -mcpu=cortex-m4

#LDFLAGS  = -lgcc
#LDFLAGS += -lc
#LDFLAGS += -lm
#LDFLAGS += -lrdimon
#LDFLAGS += -std=gnu11
#LDFLAGS += -Og
#LDFLAGS += -fmessage-length=0
#LDFLAGS += -fsigned-char
#LDFLAGS += -ffunction-sections
#LDFLAGS += -fdata-sections
#LDFLAGS += -ffreestanding
#LDFLAGS += -fno-move-loop-invariants
#LDFLAGS += -Wall
#LDFLAGS += -Wextra
#LDFLAGS += --specs=nosys.specs
#LDFLAGS += --specs=rdimon.specs
#LDFLAGS += -lrdimon

# Coq Sources
COQCODEDIRS=$(SRC_DIR)/extraction $(SRC_DIR)/core $(SRC_DIR)/model
COQPROOFDIRS=$(PROOF_DIR) $(PROOF_DIR)/invariants
VCODESOURCES=$(foreach dir, ${COQCODEDIRS}, $(wildcard $(dir)/*.v))
VPROOFSOURCES=$(foreach dir, ${COQPROOFDIRS}, $(wildcard $(dir)/*.v))
VSOURCES=$(VCODESOURCES) $(VPROOFSOURCES)
VOBJECTS=$(VSOURCES:.v=.vo)

# JSON files extracted from Coq
JSONS=Internal.json Services.json
EXTRACTEDCSOURCES=$(addprefix $(TARGET_DIR)/pipcore/, $(JSONS:.json=.c))

# .c & .S FILES
C_FILES           = $(wildcard $(TARGET_SRC_BOOT_DIR)/*.c)
C_FILES_MAL       = $(wildcard $(TARGET_SRC_MAL_DIR)/*.c)
C_FILES_UART      = $(wildcard $(TARGET_SRC_BOOT_DIR)/thirdparty/uart/*.c)
C_FILES_UART_UTIL = $(wildcard $(TARGET_SRC_BOOT_DIR)/thirdparty/uart/util/*.c)
C_FILES_MDK       = $(wildcard $(TARGET_SRC_BOOT_DIR)/thirdparty/mdk/*.c)
C_FILES_DEBUG     = $(wildcard $(TARGET_SRC_BOOT_DIR)/thirdparty/debug/*.c)
C_FILES_NEWLIB    = $(wildcard $(TARGET_SRC_BOOT_DIR)/thirdparty/newlib/*.c)
C_FILES_PIPCORE   = $(wildcard $(TARGET_DIR)/pipcore/*.c)
S_FILES           = $(wildcard $(TARGET_SRC_BOOT_DIR)/*.S)

# OBJECT FILES
# String substitution for every C/C++ file.
OBJS = $(patsubst %.c, $(TARGET_DIR)/%.o, $(notdir $(C_FILES))) # .c -> .o but do not include the name of the directory
OBJS_MAL = $(patsubst %.c, $(TARGET_DIR)/MAL/%.o, $(notdir $(C_FILES_MAL)))
OBJS += $(OBJS_MAL)
OBJS_PIPCORE = $(patsubst %.c, $(TARGET_DIR)/pipcore/%.o, $(notdir $(C_FILES_PIPCORE)))
OBJS += $(OBJS_PIPCORE)
OBJS_MDK = $(patsubst %.c, $(TARGET_DIR)/mdk/%.o, $(notdir $(C_FILES_MDK)))
OBJS += $(OBJS_MDK)
OBJS_NEWLIB = $(patsubst %.c, $(TARGET_DIR)/newlib/%.o, $(notdir $(C_FILES_NEWLIB)))
OBJS += $(OBJS_NEWLIB)
OBJS += $(patsubst %.S, $(TARGET_DIR)/%.o, $(notdir $(S_FILES)))

ifeq ($(UART_DEBUG), yes)
OBJS_DEBUG = $(patsubst %.c, $(TARGET_DIR)/debug/%.o, $(notdir $(C_FILES_DEBUG)))
OBJS += $(OBJS_DEBUG)
OBJS_UART = $(patsubst %.c, $(TARGET_DIR)/uart/%.o, $(notdir $(C_FILES_UART)))
OBJS += $(OBJS_UART)
OBJS_UART_UTIL = $(patsubst %.c, $(TARGET_DIR)/uart/util/%.o, $(notdir $(C_FILES_UART_UTIL)))
OBJS += $(OBJS_UART_UTIL)
endif

ifeq ($(SEMI_DEBUG), yes)
OBJS_DEBUG = $(patsubst %.c, $(TARGET_DIR)/debug/%.o, $(notdir $(C_FILES_DEBUG)))
OBJS += $(OBJS_DEBUG)
endif


# RULES
ifeq ($(UNIT_TESTS), yes)
ifeq ($(UART_DEBUG), yes)
$(info [Error] unit tests only run in semihosting not UART, try with: make all UNIT_TESTS=yes SEMI_DEBUG=yes UART_DEBUG=no )
all:
else
all: app.bin
endif
else
all: app.bin
endif


$(DIGGER):
	make -C $(DIGGER_DIR)

# Coq options
COQOPTS=$(shell cat _CoqProject)

# Implicit rules for Coq source files
$(addsuffix .d,$(filter-out $(SRC_DIR)/extraction/Extraction.v,$(VSOURCES))): %.v.d: %.v
	$(COQDEP) $(COQOPTS) "$<" > "$@"

$(SRC_DIR)/extraction/Extraction.v.d: $(SRC_DIR)/extraction/Extraction.v
	$(COQDEP) $(COQOPTS) "$<" | $(SED) 's/Extraction.vo/Extraction.vo Internal.json Services.json/' > "$@"

%.vo: %.v
	$(COQC) $(COQOPTS) $<

$(VSOURCES:.v=.glob): %.glob: %.vo

# Extract C code from Coq source
$(SRC_DIR)/extraction/Extraction.vo $(JSONS): $(SRC_DIR)/extraction/Extraction.v
	#coq_makefile -f _CoqProject src/model/*.v src/core/*.v -o MakefileCoq # if MakefileCoq doesn't exist yet
	make -f MakefileCoq $(SRC_DIR)/extraction/Extraction.vo
	# compile all .v into .vo
	#$(COQC) $(COQOPTS) -w all $<

extract: $(TARGET_DIR) $(EXTRACTEDCSOURCES)

DIGGERFLAGS := -m Monad -M coq_LLI
DIGGERFLAGS += -m Datatypes -r Coq_true:true -r Coq_false:false -r Coq_tt:tt -r index:Coq_index
DIGGERFLAGS += -m MALInternal -d :MALInternal.json
DIGGERFLAGS += -m MAL -d :MAL.json
DIGGERFLAGS += -m ADT -m Nat
DIGGERFLAGS += -q maldefines.h
DIGGERFLAGS += -c true -c false -c tt -c Coq_error

$(TARGET_DIR)/pipcore/Internal.c: Internal.json $(DIGGER)
	$(DIGGER) $(DIGGERFLAGS) --ignore coq_N $< -o $@

$(TARGET_DIR)/pipcore/Internal.h: Internal.json $(DIGGER)
	$(DIGGER) $(DIGGERFLAGS) --ignore coq_N --header $< -o $@

$(TARGET_DIR)/pipcore/Services.c: Services.json $(DIGGER) $(TARGET_DIR)/pipcore/Internal.h $(TARGET_DIR)/pipcore/Services.h
	$(DIGGER) $(DIGGERFLAGS) -m Internal -d :Internal.json -q Internal.h $< -o $@

$(TARGET_DIR)/pipcore/Services.h: Services.json $(DIGGER)
	$(DIGGER) $(DIGGERFLAGS) --ignore coq_N --header $< -o $@

#%.o: %.S
$(TARGET_DIR)/%.o: $(TARGET_SRC_BOOT_DIR)/%.S
	$(AS) -o $@ $^ $(ASFLAGS)

#%.o: %.c
$(TARGET_DIR)/newlib/%.o: $(TARGET_SRC_BOOT_DIR)/thirdparty/newlib/%.c
	$(CC) -o $@ $^ -c $(CFLAGS)

$(TARGET_DIR)/uart/%.o: $(TARGET_SRC_BOOT_DIR)/thirdparty/uart/%.c
	$(CC) -o $@ $^ -c $(CFLAGS)

$(TARGET_DIR)/uart/util/%.o: $(TARGET_SRC_BOOT_DIR)/thirdparty/uart/util/%.c
	$(CC) -o $@ $^ -c $(CFLAGS)

$(TARGET_DIR)/mdk/%.o: $(TARGET_SRC_BOOT_DIR)/thirdparty/mdk/%.c
	$(CC) -o $@ $^ -c $(CFLAGS)

$(TARGET_DIR)/debug/%.o: $(TARGET_SRC_BOOT_DIR)/thirdparty/debug/%.c
	$(CC) -o $@ $^ -c $(CFLAGS)

$(TARGET_DIR)/MAL/%.o: $(TARGET_SRC_MAL_DIR)/%.c
	$(CC) -o $@ $^ -c $(CFLAGS)

$(TARGET_DIR)/%.o: $(TARGET_SRC_BOOT_DIR)/%.c
	$(CC) -o $@ $^ -c $(CFLAGS)

$(TARGET_DIR)/pipcore/%.o: $(TARGET_DIR)/pipcore/%.c
	$(CC) -o $@ $^ -c $(CFLAGS)

app.elf: $(OBJS)
	$(CC) $(LDFLAGS) -T$(LINKSCRIPT) $^ -o $(TARGET_DIR)/app.elf

app.bin: $(TARGET_DIR) app.elf
	$(BI) -O binary $(TARGET_DIR)/app.elf $(TARGET_DIR)/app.bin

clean: clean-c clean-coq
	rm -rf $(TARGET_DIR)/

clean-coq:
	rm -f $(TARGET_DIR)/pipcore/* *.json
	rm -f $(VOBJECTS) $(VSOURCES:.v=.v.d) $(VSOURCES:.v=.glob)

clean-c:
	find $(TARGET_DIR) ! \( -name "*.c" -o -name "*.h" \) -type f -exec rm -f {} +

# Generate build directory
$(TARGET_DIR):
	mkdir -p $@
	mkdir -p $@/pipcore
	mkdir -p $@/newlib
	mkdir -p $@/uart
	mkdir -p $@/uart/util
	mkdir -p $@/mdk
	mkdir -p $@/debug
	mkdir -p $@/MAL
