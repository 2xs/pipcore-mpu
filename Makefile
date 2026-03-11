###############################################################################
#  © Université de Lille, The Pip Development Team (2015-2024)                #
#  Copyright (C) 2020-2024 Orange                                             #
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

ifeq ("$(wildcard toolchain.mk)","")
    $(error Run the configuration script first: ./configure.sh)
endif

include toolchain.mk

# Default tools
CAT := cat
SED := sed

OCAMLOPT := ocamlopt

# GALLINA_C should be either digger or dx
# if DXDIR is set, use dx
ifeq ($(strip $(DXDIR)),)
GALLINA_C := digger
else
GALLINA_C := dx
endif

CFLAGS=-Wall -Wextra
CFLAGS+=-std=gnu99

CFLAGS+=$(ARCH_CFLAGS)
CFLAGS+=$(FAE_INCLUDE_DIRECTORY_CFLAGS)
ASFLAGS=$(ARCH_ASFLAGS)
LDFLAGS=$(ARCH_LDFLAGS)

# Enable debug symbols and logs
CFLAGS+=$(if $(DEBUG), $(DEBUG_CFLAGS))

ROCQFLAGS := $(shell $(CAT) _CoqProject)
# Enable all warnings except for those triggered by the standard lib
ROCQ_COMPILER_FLAGS := $(ROCQFLAGS) -w all,-nonprimitive-projection-syntax,-disj-pattern-notation
ROCQ_COMPILER_EXTR_FLAGS := $(shell $(SED) 's/-[RQ]  */&..\//g' _CoqProject) -w all,-extraction

BIFLAGS=$(ARCH_BIFLAGS)

#####################################################################
##                      Directory variables                        ##
#####################################################################

SRC_DIR=src
GENERATED_FILES_DIR=generated
DOC_DIR=doc
C_DOC_DIR=$(DOC_DIR)/c
ROCQ_DOC_DIR=$(DOC_DIR)/rocq

######################### Rocq related dirs #########################

ROCQ_CORE_DIR=$(SRC_DIR)/core
ROCQ_MODEL_DIR=$(SRC_DIR)/model
ROCQ_EXTRACTION_DIR=$(SRC_DIR)/extraction
ROCQ_DX_DIR=$(SRC_DIR)/dx

ROCQ_PROOF_DIR=proof
ROCQ_INVARIANTS_DIR=$(ROCQ_PROOF_DIR)/invariants


########################### C related dirs ##########################

# Architecture agnostic C dirs
C_MODEL_INTERFACE_INCLUDE_DIR=$(SRC_DIR)/interface

# CRT0 related directory
CRT0_DIR=$(SRC_DIR)/partition_crt0

# Architecture dependent C dirs
ARCH_DEPENDENT_DIR=$(SRC_DIR)/arch
C_SRC_TARGET_DIR=$(ARCH_DEPENDENT_DIR)/$(TARGET)

C_TARGET_MAL_DIR=$(C_SRC_TARGET_DIR)/MAL
C_TARGET_MAL_INCLUDE_DIR=$(C_TARGET_MAL_DIR)/include

C_TARGET_BOOT_DIR=$(C_SRC_TARGET_DIR)/boot
C_TARGET_BOOT_INCLUDE_DIR=$(C_TARGET_BOOT_DIR)/include

C_TARGET_THIRDPARTY_DIR=$(C_TARGET_BOOT_DIR)/thirdparty

C_TARGET_CMSIS_DIR=$(C_TARGET_THIRDPARTY_DIR)/cmsis
C_TARGET_CMSIS_INCLUDE_DIR=$(C_TARGET_CMSIS_DIR)/include

C_TARGET_MDK_DIR=$(C_TARGET_THIRDPARTY_DIR)/mdk
C_TARGET_MDK_INCLUDE_DIR=$(C_TARGET_MDK_DIR)/include

C_TARGET_UART_DIR=$(C_TARGET_THIRDPARTY_DIR)/uart
C_TARGET_UART_INCLUDE_DIR=$(C_TARGET_UART_DIR)/include

C_GENERATED_SRC_DIR=$(GENERATED_FILES_DIR)
C_GENERATED_HEADERS_DIR=$(GENERATED_FILES_DIR)

#####################################################################
##                        Files variables                          ##
#####################################################################

############################ C files ################################

C_GENERATED_SRC=$(C_GENERATED_SRC_DIR)/Services.c $(C_GENERATED_SRC_DIR)/Internal.c
C_TARGET_BOOT_SRC=$(wildcard $(C_TARGET_BOOT_DIR)/*.c)
C_TARGET_CMSIS_SRC=$(wildcard $(C_TARGET_CMSIS_DIR)/*.c)
C_TARGET_MDK_SRC=$(wildcard $(C_TARGET_MDK_DIR)/*.c)
C_TARGET_UART_SRC=$(wildcard $(C_TARGET_UART_DIR)/*.c)
C_TARGET_MAL_SRC=$(wildcard $(C_TARGET_MAL_DIR)/*.c)
AS_TARGET_BOOT_SRC=$(wildcard $(C_TARGET_BOOT_DIR)/*.s)
GAS_TARGET_BOOT_SRC=$(wildcard $(C_TARGET_BOOT_DIR)/*.S)

C_GENERATED_HEADERS=$(C_GENERATED_HEADERS_DIR)/Internal.h $(C_GENERATED_HEADERS_DIR)/Services.h
C_MODEL_INTERFACE_HEADERS=$(wildcard $(C_MODEL_INTERFACE_INCLUDE_DIR)/*.h)
C_TARGET_MAL_HEADERS=$(wildcard $(C_TARGET_MAL_INCLUDE_DIR)/*.h)
C_TARGET_BOOT_HEADERS=$(wildcard $(C_TARGET_BOOT_INCLUDE_DIR)/*.h)
C_TARGET_CMSIS_HEADERS=$(wildcard $(C_TARGET_CMSIS_INCLUDE_DIR)/*.h)
C_TARGET_MDK_HEADERS=$(wildcard $(C_TARGET_MDK_INCLUDE_DIR)/*.h)
C_TARGET_UART_HEADERS=$(wildcard $(C_TARGET_UART_INCLUDE_DIR)/*.h)

C_GENERATED_OBJ=$(C_GENERATED_SRC:.c=.o)
C_TARGET_BOOT_OBJ=$(C_TARGET_BOOT_SRC:.c=.o)
C_TARGET_MAL_OBJ=$(C_TARGET_MAL_SRC:.c=.o)
AS_TARGET_BOOT_OBJ=$(AS_TARGET_BOOT_SRC:.s=.o)
GAS_TARGET_BOOT_OBJ=$(GAS_TARGET_BOOT_SRC:.S=.o)
C_TARGET_CMSIS_OBJ=$(C_TARGET_CMSIS_SRC:.c=.o)
C_TARGET_MDK_OBJ=$(C_TARGET_MDK_SRC:.c=.o)
C_TARGET_UART_OBJ=$(C_TARGET_UART_SRC:.c=.o)

############################## Rocq files ##############################

# Rocq source files
ROCQ_SRC_FILES=$(foreach dir, $(ROCQ_CORE_DIR)\
                              $(ROCQ_MODEL_DIR)\
                            , $(wildcard $(dir)/*.v)\
               )

# Rocq file needed for extraction
ROCQ_EXTRACTION_FILES=$(wildcard $(ROCQ_EXTRACTION_DIR)/*.v)

# TODO: Uncomment the following lines once the proofs are done
# Rocq proof files
#ROCQ_PROOF_FILES=$(foreach dir, $(ROCQ_PROOF_DIR)\
#                               $(ROCQ_INVARIANTS_DIR)\
#                             , $(wildcard $(dir)/*.v)\
#                 )
ROCQ_PROOF_FILES=$(foreach dir, $(ROCQ_PROOF_DIR)\
                              , $(wildcard $(dir)/*.v)\
                 )
ROCQ_PROOF_FILES+=$(ROCQ_INVARIANTS_DIR)/Invariants.v
ROCQ_PROOF_FILES+=$(ROCQ_INVARIANTS_DIR)/findBlockInKSWithAddr.v
ROCQ_PROOF_FILES+=$(ROCQ_INVARIANTS_DIR)/checkChildOfCurrPart.v
ROCQ_PROOF_FILES+=$(ROCQ_INVARIANTS_DIR)/getGlobalIdPDCurrentOrChild.v
ROCQ_PROOF_FILES+=$(ROCQ_INVARIANTS_DIR)/findBlockInKS.v
ROCQ_PROOF_FILES+=$(ROCQ_INVARIANTS_DIR)/FindBlock.v
ROCQ_PROOF_FILES+=$(ROCQ_INVARIANTS_DIR)/ReadMPU.v
ROCQ_PROOF_FILES+=$(ROCQ_INVARIANTS_DIR)/insertNewEntry.v
ROCQ_PROOF_FILES+=$(ROCQ_INVARIANTS_DIR)/AddMemoryBlockSecProps.v
ROCQ_PROOF_FILES+=$(ROCQ_INVARIANTS_DIR)/AddMemoryBlock.v

# TODO: Uncomment the following lines once the proofs are done
# Group of Rocq files written by humans
ROCQ_VFILES=$(ROCQ_PROOF_FILES) $(ROCQ_SRC_FILES)
#ROCQ_VFILES=$(ROCQ_SRC_FILES)

# Rocq dependency files (generated by rocq dep and included in this makefile)
ROCQ_DEPFILES=$(ROCQ_VFILES:.v=.v.d)
# Rocq compiled sources
ROCQ_VOFILES=$(ROCQ_VFILES:.v=.vo)
# Rocq glob files (needed for html generation)
ROCQ_GLOBFILES=$(ROCQ_VFILES:.v=.glob)
# Unused but still produced by Rocq sources compilation
# and thus need to be tracked and cleaned
ROCQ_VOSFILES=$(ROCQ_VFILES:.v=.vos)
ROCQ_VOKFILES=$(ROCQ_VFILES:.v=.vok)
ROCQ_AUXFILES=$(ROCQ_VFILES:.v=.aux)
# Prepends a '.' to .aux file names (dir/.name.aux)
ROCQ_AUXFILES:=$(join\
                   $(dir $(ROCQ_AUXFILES)),\
                   $(addprefix ., $(notdir $(ROCQ_AUXFILES)))\
                )

# Rocq extraction "compilation" files
ROCQ_EXTR_DEPFILES=$(ROCQ_EXTRACTION_FILES:.v=.v.d)
ROCQ_EXTR_VOFILES=$(ROCQ_EXTRACTION_FILES:.v=.vo)
ROCQ_EXTR_GLOBFILES=$(ROCQ_EXTRACTION_FILES:.v=.glob)
ROCQ_EXTR_VOSFILES=$(ROCQ_EXTRACTION_FILES:.v=.vos)
ROCQ_EXTR_VOKFILES=$(ROCQ_EXTRACTION_FILES:.v=.vok)
ROCQ_EXTR_AUXFILES=$(ROCQ_EXTRACTION_FILES:.v=.aux)
ROCQ_EXTR_AUXFILES:=$(addprefix $(dir $(ROCQ_EXTR_AUXFILES))., $(notdir $(ROCQ_EXTR_AUXFILES)))

ROCQ_EXTR_COMPILED_FILES:=$(ROCQ_EXTR_VOFILES) $(ROCQ_EXTR_GLOBFILES)\
	$(ROCQ_EXTR_VOSFILES) $(ROCQ_EXTR_VOKFILES) $(ROCQ_EXTR_AUXFILES)

# Rocq dx files
ROCQ_DX_VFILES=$(wildcard $(ROCQ_DX_DIR)/*.v)
ROCQ_DX_DEPFILES=$(ROCQ_DX_VFILES:.v=.v.d)
ROCQ_DX_GLOBFILES=$(ROCQ_DX_FILES:.v=.glob)
ROCQ_DX_VOSFILES=$(ROCQ_DX_FILES:.v=.vos)
ROCQ_DX_VOKFILES=$(ROCQ_DX_FILES:.v=.vok)
ROCQ_DX_AUXFILES=$(ROCQ_DX_FILES:.v=.aux)
ROCQ_DX_AUXFILES:=$(addprefix $(dir $(ROCQ_DX_AUXFILES))., $(notdir $(ROCQ_DX_AUXFILES)))

ROCQ_DX_COMPILED_FILES:=$(ROCQ_DX_VOFILES) $(ROCQ_DX_GLOBFILES)\
	$(ROCQ_DX_VOSFILES) $(ROCQ_DX_VOKFILES) $(ROCQ_DX_AUXFILES)

# Group of Rocq files produced by the compilation process
ROCQ_COMPILED_FILES=$(ROCQ_VOFILES) $(ROCQ_VOKFILES) $(ROCQ_VOSFILES)\
                    $(ROCQ_GLOBFILES) $(ROCQ_AUXFILES)\
                    $(ROCQ_EXTR_COMPILED_FILES)

ROCQ_DEPENDENCY_FILES=$(ROCQ_DEPFILES) $(ROCQ_EXTR_DEPFILES)

ifeq ($(GALLINA_C),dx)
ROCQ_DEPENDENCY_FILES += $(ROCQ_DX_DEPFILES)
ROCQ_COMPILED_FILES += $(ROCQ_DX_COMPILED_FILES)
endif

######################## Miscellaneous files ########################

OBJECT_FILES=$(C_TARGET_MAL_OBJ) $(C_TARGET_BOOT_OBJ)\
             $(C_TARGET_CMSIS_OBJ) $(C_TARGET_MDK_OBJ)\
             $(C_TARGET_UART_OBJ) $(C_GENERATED_OBJ)\
             $(AS_TARGET_BOOT_OBJ) $(GAS_TARGET_BOOT_OBJ)

# Jsons (Rocq extracted AST)
JSONS=Internal.json MAL.json MALInternal.json Services.json
JSONS:=$(addprefix $(GENERATED_FILES_DIR)/, $(JSONS))

#####################################################################
##                    Default Makefile target                      ##
#####################################################################

all: pip.bin

#####################################################################
##                    Code compilation targets                     ##
#####################################################################

##################### Generation from Rocq to C #####################

DIGGERFLAGS := -m Monad -M coq_LLI
DIGGERFLAGS += -m Datatypes -r Coq_true:true -r Coq_false:false -r Coq_tt:tt -r index:Coq_index -r coq_N:N
DIGGERFLAGS += -m MALInternal -d :$(GENERATED_FILES_DIR)/MALInternal.json
DIGGERFLAGS += -m MAL -d :$(GENERATED_FILES_DIR)/MAL.json
DIGGERFLAGS += -m ADT -m Nat
DIGGERFLAGS += -q maldefines.h
DIGGERFLAGS += -c true -c false -c tt -c Coq_error

ifeq ($(GALLINA_C),digger)

$(GENERATED_FILES_DIR)/Internal.h: $(GENERATED_FILES_DIR)/Internal.json $(JSONS)\
                                 | $(GENERATED_FILES_DIR) $(DIGGER)
	$(DIGGER) $(DIGGERFLAGS) --header\
		                 $< -o $@

$(GENERATED_FILES_DIR)/Internal.c: $(GENERATED_FILES_DIR)/Internal.json $(JSONS)\
	                           $(GENERATED_FILES_DIR)/Internal.h\
                                 | $(GENERATED_FILES_DIR) $(DIGGER)
	$(DIGGER) $(DIGGERFLAGS) -q Internal.h -q mal.h\
	                         $< -o $@

$(GENERATED_FILES_DIR)/Services.h: $(GENERATED_FILES_DIR)/Services.json $(JSONS)\
                                 | $(GENERATED_FILES_DIR) $(DIGGER)
	$(DIGGER) $(DIGGERFLAGS) --header\
		                 $< -o $@
$(GENERATED_FILES_DIR)/Services.c: $(GENERATED_FILES_DIR)/Services.json $(JSONS)\
	                           $(GENERATED_FILES_DIR)/Services.h\
	                           $(GENERATED_FILES_DIR)/Internal.json\
	                           $(GENERATED_FILES_DIR)/Internal.h\
                                 | $(GENERATED_FILES_DIR) $(DIGGER)
	$(DIGGER) $(DIGGERFLAGS) -m Internal -d :$(GENERATED_FILES_DIR)/Internal.json\
	                         -q Services.h -q Internal.h -q mal.h\
				 $< -o $@

endif

############################ Rocq rules ############################

# Rule to generate dependency files
$(ROCQ_DEPENDENCY_FILES):\
	%.v.d : %.v
	@$(ROCQ) dep $(ROCQFLAGS) $< > $@

-include $(ROCQ_DEPENDENCY_FILES)

%.cmi: %.mli
	$(OCAMLOPT) -args $(DXDIR)/cprinter-inc-args -c $<

%.cmx: %.ml %.cmi
	$(OCAMLOPT) -args $(DXDIR)/cprinter-inc-args -I generated -c $<

generated/cprinter: generated/Main.cmx
	$(OCAMLOPT) -args $(DXDIR)/cprinter-inc-args -args $(DXDIR)/cprinter-link-args $< -o $@

generated/compcert.ini: $(DXDIR)/compcertcprinter/compcert.ini
	cp $< $@

ifneq (,$(findstring grouped-target,$(.FEATURES)))
$(JSONS) $(ROCQ_EXTR_COMPILED_FILES) &:\
		$(ROCQ_EXTRACTION_FILES) $(ROCQ_EXTR_DEPFILES)\
		| $(GENERATED_FILES_DIR)
	cd $(GENERATED_FILES_DIR) && $(ROCQ) compile $(ROCQ_COMPILER_EXTR_FLAGS) ../$<

# FIXME .aux files are difficult to match ; previous rule was wrong. Omit them for now
# %.vo %.vok %.vos %.glob .%.aux &: %.v %.v.d
%.vo %.vok %.vos %.glob &: %.v %.v.d
	$(ROCQ) compile $(ROCQ_COMPILER_FLAGS) $<

$(GENERATED_FILES_DIR)/Main.ml $(GENERATED_FILES_DIR)/Main.mli src/dx/Extr.vo &: src/dx/Extr.v | $(GENERATED_FILES_DIR)
	cd $(GENERATED_FILES_DIR) && $(ROCQ) compile $(ROCQ_COMPILER_EXTR_FLAGS) ../$<

ifeq ($(GALLINA_C),dx)
$(C_GENERATED_SRC) $(C_GENERATED_HEADERS) \
		&: $(GENERATED_FILES_DIR)/cprinter $(GENERATED_FILES_DIR)/compcert.ini
	cd $(GENERATED_FILES_DIR) && ./cprinter
# Fix duplicate definitions of structs in Services.h
#$(SED) '/^struct .*{/,/^};/d' < $(GENERATED_FILES_DIR)/Services.h > $(GENERATED_FILES_DIR)/Services.h.tmp
#mv $(GENERATED_FILES_DIR)/Services.h.tmp $(GENERATED_FILES_DIR)/Services.h
endif

# if make doesn't support grouped targets
else
# Unfortunately, without grouped-target we cannot inherit dependencies
# computed by rocq dep, so we must mv files after the fact
$(JSONS): src/extraction/Extraction.vo | $(GENERATED_FILES_DIR)
	mv $(notdir $@) $(GENERATED_FILES_DIR)

# FIXME .aux files are difficult to match ; previous rule was wrong. Omit them for now
# %.vo %.vok %.vos %.glob .%.aux : %.v %.v.d
%.vo %.vok %.vos %.glob : %.v %.v.d
	$(ROCQ) compile $(ROCQ_COMPILER_FLAGS) $<

$(GENERATED_FILES_DIR)/Main.ml $(GENERATED_FILES_DIR)/Main.mli src/dx/Extr.vo: src/dx/Extr.v src/dx/Main.vo | $(GENERATED_FILES_DIR)
	cd $(GENERATED_FILES_DIR) && $(ROCQ) compile $(ROCQ_COMPILER_EXTR_FLAGS) ../$<

ifeq ($(GALLINA_C),dx)
# The files will be generated multiple times...
$(C_GENERATED_SRC) $(C_GENERATED_HEADERS) \
		: $(GENERATED_FILES_DIR)/cprinter $(GENERATED_FILES_DIR)/compcert.ini
	cd $(GENERATED_FILES_DIR) && ./cprinter
# Fix duplicate definitions of structs in Services.h
#$(SED) '/^struct .*{/,/^};/d' < $(GENERATED_FILES_DIR)/Services.h > $(GENERATED_FILES_DIR)/Services.h.tmp
#mv $(GENERATED_FILES_DIR)/Services.h.tmp $(GENERATED_FILES_DIR)/Services.h
endif

endif

########################### C object rules ##########################

# Static pattern rule for constructing object files from generated C files
$(C_GENERATED_OBJ):\
    %.o : %.c $(C_GENERATED_HEADERS) $(C_MODEL_INTERFACE_HEADERS)\
              $(C_TARGET_MAL_HEADERS) $(C_TARGET_BOOT_HEADERS)\
              $(C_TARGET_CMSIS_HEADERS) $(C_TARGET_MDK_HEADERS)\
              $(C_TARGET_UART_HEADERS)
	$(CC) $(CFLAGS) -I $(C_GENERATED_HEADERS_DIR)\
                        -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -I $(C_TARGET_CMSIS_INCLUDE_DIR)\
                        -I $(C_TARGET_MDK_INCLUDE_DIR)\
                        -I $(C_TARGET_UART_INCLUDE_DIR)\
                        -c -o $@ $<

# Static pattern rule for constructing object files from target boot C files
$(C_TARGET_BOOT_OBJ):\
    %.o : %.c $(C_GENERATED_HEADERS) $(C_MODEL_INTERFACE_HEADERS)\
              $(C_TARGET_MAL_HEADERS) $(C_TARGET_BOOT_HEADERS)\
              $(C_TARGET_CMSIS_HEADERS) $(C_TARGET_MDK_HEADERS)\
              $(C_TARGET_UART_HEADERS)
	$(CC) $(CFLAGS) -I $(C_GENERATED_HEADERS_DIR)\
                        -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -I $(C_TARGET_CMSIS_INCLUDE_DIR)\
                        -I $(C_TARGET_MDK_INCLUDE_DIR)\
                        -I $(C_TARGET_UART_INCLUDE_DIR)\
                        -I $(CRT0_DIR)\
                        -c -o $@ $<

$(C_TARGET_CMSIS_OBJ):\
    %.o : %.c $(C_GENERATED_HEADERS) $(C_MODEL_INTERFACE_HEADERS)\
              $(C_TARGET_MAL_HEADERS) $(C_TARGET_BOOT_HEADERS)\
              $(C_TARGET_CMSIS_HEADERS) $(C_TARGET_MDK_HEADERS)\
              $(C_TARGET_UART_HEADERS)
	$(CC) $(CFLAGS) -I $(C_GENERATED_HEADERS_DIR)\
                        -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -I $(C_TARGET_CMSIS_INCLUDE_DIR)\
                        -I $(C_TARGET_MDK_INCLUDE_DIR)\
                        -I $(C_TARGET_UART_INCLUDE_DIR)\
                        -c -o $@ $<

$(C_TARGET_MDK_OBJ):\
    %.o : %.c $(C_GENERATED_HEADERS) $(C_MODEL_INTERFACE_HEADERS)\
              $(C_TARGET_MAL_HEADERS) $(C_TARGET_BOOT_HEADERS)\
              $(C_TARGET_CMSIS_HEADERS) $(C_TARGET_MDK_HEADERS)\
              $(C_TARGET_UART_HEADERS)
	$(CC) $(CFLAGS) -I $(C_GENERATED_HEADERS_DIR)\
                        -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -I $(C_TARGET_CMSIS_INCLUDE_DIR)\
                        -I $(C_TARGET_MDK_INCLUDE_DIR)\
                        -I $(C_TARGET_UART_INCLUDE_DIR)\
                        -c -o $@ $<

$(C_TARGET_UART_OBJ):\
    %.o : %.c $(C_GENERATED_HEADERS) $(C_MODEL_INTERFACE_HEADERS)\
              $(C_TARGET_MAL_HEADERS) $(C_TARGET_BOOT_HEADERS)\
              $(C_TARGET_CMSIS_HEADERS) $(C_TARGET_MDK_HEADERS)\
              $(C_TARGET_UART_HEADERS)
	$(CC) $(CFLAGS) -I $(C_GENERATED_HEADERS_DIR)\
                        -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -I $(C_TARGET_CMSIS_INCLUDE_DIR)\
                        -I $(C_TARGET_MDK_INCLUDE_DIR)\
                        -I $(C_TARGET_UART_INCLUDE_DIR)\
                        -c -o $@ $<

# Static pattern rule for constructing object files from target boot assembly files
$(AS_TARGET_BOOT_OBJ):\
    %.o : %.s
	$(AS) $(ASFLAGS) -o $@ $<

$(GAS_TARGET_BOOT_OBJ):\
    %.o : %.S
	$(AS) $(ASFLAGS) -o $@ $<

# Static pattern rule for constructing object files from target MAL C files
$(C_TARGET_MAL_OBJ):\
    %.o : %.c $(C_GENERATED_HEADERS) $(C_MODEL_INTERFACE_HEADERS)\
              $(C_TARGET_MAL_HEADERS) $(C_TARGET_BOOT_HEADERS)\
              $(C_TARGET_CMSIS_HEADERS) $(C_TARGET_MDK_HEADERS)\
              $(C_TARGET_UART_HEADERS)
	$(CC) $(CFLAGS) -I $(C_GENERATED_HEADERS_DIR)\
                        -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -I $(C_TARGET_CMSIS_INCLUDE_DIR)\
                        -I $(C_TARGET_MDK_INCLUDE_DIR)\
                        -I $(C_TARGET_UART_INCLUDE_DIR)\
                        -c -o $@ $<

######################### Pip + Partition ELF #######################


pip.bin: pip.elf
	$(BI) $(BIFLAGS) $< $@
	$(BI) $(BIFLAGS)\
          --pad-to=$$((($$(wc -c < $@) + $(PADDING_POW2) - 1) & ~($(PADDING_POW2) - 1)))\
          --gap-fill=$(PADDING_VALUE)\
        $< $@

# $(AS_TARGET_BOOT_OBJ) must be the first object file arg to the linker
pip.elf: $(C_SRC_TARGET_DIR)/link.ld\
         $(C_TARGET_BOOT_OBJ) $(AS_TARGET_BOOT_OBJ)\
         $(GAS_TARGET_BOOT_OBJ) $(C_TARGET_CMSIS_OBJ)\
         $(C_TARGET_MDK_OBJ) $(C_TARGET_UART_OBJ)\
         $(C_TARGET_MAL_OBJ) $(C_GENERATED_OBJ)
	$(LD)\
         $(C_TARGET_BOOT_OBJ) $(AS_TARGET_BOOT_OBJ)\
         $(GAS_TARGET_BOOT_OBJ) $(C_TARGET_CMSIS_OBJ)\
         $(C_TARGET_MDK_OBJ) $(C_TARGET_UART_OBJ)\
         $(C_TARGET_MAL_OBJ) $(C_GENERATED_OBJ)\
         -T $< -o $@ $(LDFLAGS)

#####################################################################
##                      Proof related targets                      ##
#####################################################################

# TODO: Uncomment the following lines once the proofs are done
#       Don't forget to add this target to the .PHONY target
proofs: $(ROCQ_PROOF_FILES:.v=.vo)

####################################################################
##                        Utility targets                         ##
####################################################################

####################### Documentation targets ######################

doc: doc-c doc-rocq gettingstarted developer-guide

doc-c: | $(C_DOC_DIR)
	cd doc && doxygen doxygen.conf

doc-rocq: $(ROCQ_VFILES) $(ROCQ_GLOBFILES) | $(ROCQ_DOC_DIR)
	$(ROCQ) doc\
		-toc -interpolate -utf8 -html -g $(ROCQFLAGS) -d $(ROCQ_DOC_DIR)\
		$(ROCQ_VFILES)

gettingstarted:
	cd doc/getting-started/ &&\
        pdflatex getting-started.tex &&\
        pdflatex getting-started.tex

developer-guide:
	cd doc/developer-guide/ &&\
        pdflatex developer-guide.tex &&\
        pdflatex developer-guide.tex

####################################################################

$(GENERATED_FILES_DIR) $(C_DOC_DIR) $(ROCQ_DOC_DIR):
	mkdir -p $@

realclean: clean
	rm -rf $(ROCQ_DOC_DIR) $(C_DOC_DIR)
	rm -f $(DOC_DIR)/getting-started/getting-started.aux\
              $(DOC_DIR)/getting-started/getting-started.out\
              $(DOC_DIR)/getting-started/getting-started.toc\
              $(DOC_DIR)/getting-started/getting-started.log\
              $(DOC_DIR)/getting-started/getting-started.pdf
	rm -f $(DOC_DIR)/developer-guide/developer-guide.aux\
              $(DOC_DIR)/developer-guide/developer-guide.out\
              $(DOC_DIR)/developer-guide/developer-guide.toc\
              $(DOC_DIR)/developer-guide/developer-guide.log\
              $(DOC_DIR)/developer-guide/developer-guide.pdf

clean:
	rm -f .lia.cache $(ROCQ_DEPENDENCY_FILES)
	rm -rf $(ROCQ_COMPILED_FILES)
	rm -rf $(GENERATED_FILES_DIR)
	rm -f $(OBJECT_FILES)
	rm -f pip.elf pip.bin

.PHONY: all doc doc-c doc-rocq gettingstarted realclean clean
