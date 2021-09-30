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

include toolchain.mk

CFLAGS   = -Wall
CFLAGS  += -Wextra
CFLAGS  += -std=gnu99

CFLAGS  += $(ARCH_CFLAGS)
ASFLAGS  = $(ARCH_ASFLAGS)
LDFLAGS  = $(ARCH_LDFLAGS)

# Enable debug symbols and logs
CFLAGS  += $(if $(DEBUG), $(DEBUG_CFLAGS))

# LINKER VARIABLES
BUILD_DIR=build
SRC_DIR=src

TARGET_SRC_DIR=$(SRC_DIR)/arch/$(TARGET)
TARGET_SRC_BOOT_DIR=$(TARGET_SRC_DIR)/boot
TARGET_SRC_THIRDPARTY_DIR=$(TARGET_SRC_BOOT_DIR)/thirdparty
TARGET_SRC_MAL_DIR=$(TARGET_SRC_DIR)/MAL

TARGET_DIR=$(BUILD_DIR)/$(TARGET)
KERNEL_BASENAME=pip
LINKSCRIPT := $(TARGET_SRC_DIR)/link.ld

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
C_FILES_MDK       = $(wildcard $(TARGET_SRC_THIRDPARTY_DIR)/mdk/*.c)
C_FILES_NEWLIB    = $(wildcard $(TARGET_SRC_THIRDPARTY_DIR)/newlib/*.c)
C_FILES_DEBUG     = $(wildcard $(TARGET_SRC_THIRDPARTY_DIR)/debug/*.c)
C_FILES_UART      = $(wildcard $(TARGET_SRC_THIRDPARTY_DIR)/uart/*.c)
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
OBJS_DEBUG = $(patsubst %.c, $(TARGET_DIR)/debug/%.o, $(notdir $(C_FILES_DEBUG)))
OBJS += $(OBJS_DEBUG)
OBJS_UART = $(patsubst %.c, $(TARGET_DIR)/uart/%.o, $(notdir $(C_FILES_UART)))
OBJS += $(OBJS_UART)

all: app.bin

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
$(TARGET_DIR)/newlib/%.o: $(TARGET_SRC_THIRDPARTY_DIR)/newlib/%.c
	$(CC) -o $@ $^ -c $(CFLAGS)

$(TARGET_DIR)/uart/%.o: $(TARGET_SRC_THIRDPARTY_DIR)/uart/%.c
	$(CC) -o $@ $^ -c $(CFLAGS)

$(TARGET_DIR)/mdk/%.o: $(TARGET_SRC_BOOT_DIR)/thirdparty/mdk/%.c
	$(CC) -o $@ $^ -c $(CFLAGS)

$(TARGET_DIR)/debug/%.o: $(TARGET_SRC_THIRDPARTY_DIR)/debug/%.c
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
	mkdir -p $@/mdk
	mkdir -p $@/debug
	mkdir -p $@/MAL

.PHONY: all extract clean clean-coq clean-c
