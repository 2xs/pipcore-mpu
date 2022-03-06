###############################################################################
#  © Université de Lille, The Pip Development Team (2015-2022)                #
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

#ifeq ("$(wildcard toolchain.mk)","")
#    $(error Run the configuration script first: ./configure.sh)
#endif

#ifeq ("$(wildcard toolchain.mk)","")
#    $(error Run the configuration script first: ./configure.sh)
#endif

include toolchain.mk

# Default tools
CAT := cat
SED := sed

CFLAGS=-Wall -Wextra
CFLAGS+=-std=gnu99

CFLAGS+=$(ARCH_CFLAGS)
ASFLAGS=$(ARCH_ASFLAGS)
LDFLAGS=$(ARCH_LDFLAGS)

# Enable debug symbols and logs
CFLAGS+=$(if $(RELEASE), $(DEBUG_CFLAGS))
COQFLAGS := $(shell $(CAT) _CoqProject)
COQCFLAGS := $(COQFLAGS) -w all,-nonprimitive-projection-syntax
COQCEXTRFLAGS := $(shell $(SED) 's/-[RQ]  */&..\//g' _CoqProject) -w all,-extraction

#####################################################################
##                      Directory variables                        ##
#####################################################################

SRC_DIR=src
GENERATED_FILES_DIR=generated
DOC_DIR=doc
C_DOC_DIR=$(DOC_DIR)/c
COQ_DOC_DIR=$(DOC_DIR)/coq

########################## Coq related dirs #########################

COQ_CORE_DIR=$(SRC_DIR)/core
COQ_MODEL_DIR=$(SRC_DIR)/model
COQ_EXTRACTION_DIR=$(SRC_DIR)/extraction

COQ_PROOF_DIR=proof
COQ_INVARIANTS_DIR=$(COQ_PROOF_DIR)/invariants

########################### C related dirs ##########################

# Architecture agnostic C dirs
C_MODEL_INTERFACE_INCLUDE_DIR=$(SRC_DIR)/interface

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

C_TARGET_DEBUG_DIR=$(C_TARGET_THIRDPARTY_DIR)/debug
C_TARGET_DEBUG_INCLUDE_DIR=$(C_TARGET_DEBUG_DIR)/include

C_TARGET_MDK_DIR=$(C_TARGET_THIRDPARTY_DIR)/mdk
C_TARGET_MDK_INCLUDE_DIR=$(C_TARGET_MDK_DIR)/include

C_TARGET_NEWLIB_DIR=$(C_TARGET_THIRDPARTY_DIR)/newlib
C_TARGET_NEWLIB_INCLUDE_DIR=$(C_TARGET_NEWLIB_DIR)/include

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
C_TARGET_DEBUG_SRC=$(wildcard $(C_TARGET_DEBUG_DIR)/*.c)
C_TARGET_MDK_SRC=$(wildcard $(C_TARGET_MDK_DIR)/*.c)
C_TARGET_NEWLIB_SRC=$(wildcard $(C_TARGET_NEWLIB_DIR)/*.c)
C_TARGET_UART_SRC=$(wildcard $(C_TARGET_UART_DIR)/*.c)
C_TARGET_MAL_SRC=$(wildcard $(C_TARGET_MAL_DIR)/*.c)
AS_TARGET_BOOT_SRC=$(wildcard $(C_TARGET_BOOT_DIR)/*.s)
GAS_TARGET_BOOT_SRC=$(wildcard $(C_TARGET_BOOT_DIR)/*.S)

C_GENERATED_HEADERS=$(C_GENERATED_HEADERS_DIR)/Internal.h $(C_GENERATED_HEADERS_DIR)/Services.h
C_MODEL_INTERFACE_HEADERS=$(wildcard $(C_MODEL_INTERFACE_INCLUDE_DIR)/*.h)
C_TARGET_MAL_HEADERS=$(wildcard $(C_TARGET_MAL_INCLUDE_DIR)/*.h)
C_TARGET_BOOT_HEADERS=$(wildcard $(C_TARGET_BOOT_INCLUDE_DIR)/*.h)
C_TARGET_CMSIS_HEADERS=$(wildcard $(C_TARGET_CMSIS_INCLUDE_DIR)/*.h)
C_TARGET_DEBUG_HEADERS=$(wildcard $(C_TARGET_DEBUG_INCLUDE_DIR)/*.h)
C_TARGET_MDK_HEADERS=$(wildcard $(C_TARGET_MDK_INCLUDE_DIR)/*.h)
C_TARGET_NEWLIB_HEADERS=$(wildcard $(C_TARGET_NEWLIB_INCLUDE_DIR)/*.h)
C_TARGET_UART_HEADERS=$(wildcard $(C_TARGET_UART_INCLUDE_DIR)/*.h)

C_GENERATED_OBJ=$(C_GENERATED_SRC:.c=.o)
C_TARGET_BOOT_OBJ=$(C_TARGET_BOOT_SRC:.c=.o)
C_TARGET_MAL_OBJ=$(C_TARGET_MAL_SRC:.c=.o)
AS_TARGET_BOOT_OBJ=$(AS_TARGET_BOOT_SRC:.s=.o)
GAS_TARGET_BOOT_OBJ=$(GAS_TARGET_BOOT_SRC:.S=.o)
C_TARGET_CMSIS_OBJ=$(C_TARGET_CMSIS_SRC:.c=.o)
C_TARGET_DEBUG_OBJ=$(C_TARGET_DEBUG_SRC:.c=.o)
C_TARGET_MDK_OBJ=$(C_TARGET_MDK_SRC:.c=.o)
C_TARGET_NEWLIB_OBJ=$(C_TARGET_NEWLIB_SRC:.c=.o)
C_TARGET_UART_OBJ=$(C_TARGET_UART_SRC:.c=.o)

########################### Coq files ###############################

# Coq source files
COQ_SRC_FILES=$(foreach dir, $(COQ_CORE_DIR)\
	                     $(COQ_MODEL_DIR)\
	                   , $(wildcard $(dir)/*.v)\
               )

# Coq file needed for extraction
COQ_EXTRACTION_FILES=$(wildcard $(COQ_EXTRACTION_DIR)/*.v)

# TODO: Uncomment the following lines once the proofs are done
# Coq proof files
#COQ_PROOF_FILES=$(foreach dir, $(COQ_PROOF_DIR)\
#                               $(COQ_INVARIANTS_DIR)\
#                             , $(wildcard $(dir)/*.v)\
#                 )
COQ_PROOF_FILES=$(foreach dir, $(COQ_PROOF_DIR)\
                             , $(wildcard $(dir)/*.v)\
                 )
COQ_PROOF_FILES+=$(COQ_INVARIANTS_DIR)/Invariants.v
COQ_PROOF_FILES+=$(COQ_INVARIANTS_DIR)/findBlockInKSWithAddr.v
COQ_PROOF_FILES+=$(COQ_INVARIANTS_DIR)/checkChildOfCurrPart.v
COQ_PROOF_FILES+=$(COQ_INVARIANTS_DIR)/getGlobalIdPDCurrentOrChild.v
COQ_PROOF_FILES+=$(COQ_INVARIANTS_DIR)/findBlockInKS.v

# TODO: Uncomment the following lines once the proofs are done
# Group of Coq files written by humans
COQ_VFILES=$(COQ_PROOF_FILES) $(COQ_SRC_FILES)
#COQ_VFILES=$(COQ_SRC_FILES)

# Coq dependency files (generated by coqdep and included in this makefile)
COQ_DEPFILES=$(COQ_VFILES:.v=.v.d)
# Coq compiled sources
COQ_VOFILES=$(COQ_VFILES:.v=.vo)
# Coq glob files (needed for html generation)
COQ_GLOBFILES=$(COQ_VFILES:.v=.glob)
# Unused but still produced by Coq sources compilation
# and thus need to be tracked and cleaned
COQ_VOSFILES=$(COQ_VFILES:.v=.vos)
COQ_VOKFILES=$(COQ_VFILES:.v=.vok)
COQ_AUXFILES=$(COQ_VFILES:.v=.aux)
# Prepends a '.' to .aux file names (dir/.name.aux)
COQ_AUXFILES:=$(join\
		$(dir $(COQ_AUXFILES)),\
		$(addprefix ., $(notdir $(COQ_AUXFILES)))\
	      )

# Coq extraction "compilation" files
COQ_EXTR_DEPFILE=$(COQ_EXTRACTION_FILES:.v=.v.d)
COQ_EXTR_VOFILE=$(COQ_EXTRACTION_FILES:.v=.vo)
COQ_EXTR_GLOBFILE=$(COQ_EXTRACTION_FILES:.v=.glob)
COQ_EXTR_VOSFILE=$(COQ_EXTRACTION_FILES:.v=.vos)
COQ_EXTR_VOKFILE=$(COQ_EXTRACTION_FILES:.v=.vok)
COQ_EXTR_AUXFILE=$(COQ_EXTRACTION_FILES:.v=.aux)
COQ_EXTR_AUXFILE:=$(addprefix $(dir $(COQ_EXTR_AUXFILE))., $(notdir $(COQ_EXTR_AUXFILE)))

COQ_EXTR_COMPILED_FILES:=$(COQ_EXTR_VOFILE) $(COQ_EXTR_GLOBFILE)\
	$(COQ_EXTR_VOSFILE) $(COQ_EXTR_VOKFILE) $(COQ_EXTR_AUXFILE)

# Group of Coq files produced by the compilation process
COQ_COMPILED_FILES=$(COQ_VOFILES) $(COQ_VOKFILES) $(COQ_VOSFILES)\
		   $(COQ_GLOBFILES) $(COQ_AUXFILES)\
		   $(COQ_EXTR_COMPILED_FILES)

COQ_DEPENDENCY_FILES=$(COQ_DEPFILES) $(COQ_EXTR_DEPFILE)

######################## Miscellaneous files ########################

OBJECT_FILES=$(C_TARGET_MAL_OBJ) $(C_TARGET_BOOT_OBJ)\
             $(C_TARGET_CMSIS_OBJ) $(C_TARGET_DEBUG_OBJ)\
             $(C_TARGET_MDK_OBJ) $(C_TARGET_NEWLIB_OBJ)\
             $(C_TARGET_UART_OBJ) $(C_GENERATED_OBJ)\
	     	 $(AS_TARGET_BOOT_OBJ) $(GAS_TARGET_BOOT_OBJ)

# Jsons (Coq extracted AST)
JSONS=Internal.json MAL.json MALInternal.json Services.json
JSONS:=$(addprefix $(GENERATED_FILES_DIR)/, $(JSONS))


######################## Include benchmarks ########################

ifneq (,$(filter -DBENCHMARK,$(CFLAGS)))
### Benchmarks makefile prevails
	include benchmarks/Makefile
endif
#####################################################################
##                    Default Makefile target                      ##
#####################################################################

all: pip.bin

#####################################################################
##                    Code compilation targets                     ##
#####################################################################

###################### Generation from Coq to C #####################

DIGGERFLAGS := -m Monad -M coq_LLI
DIGGERFLAGS += -m Datatypes -r Coq_true:true -r Coq_false:false -r Coq_tt:tt -r index:Coq_index
DIGGERFLAGS += -m MALInternal -d :$(GENERATED_FILES_DIR)/MALInternal.json
DIGGERFLAGS += -m MAL -d :$(GENERATED_FILES_DIR)/MAL.json
DIGGERFLAGS += -m ADT -m Nat
DIGGERFLAGS += -q maldefines.h
DIGGERFLAGS += -c true -c false -c tt -c Coq_error
DIGGERFLAGS += --ignore coq_N

$(GENERATED_FILES_DIR)/Internal.h: $(GENERATED_FILES_DIR)/Internal.json $(JSONS)\
                                 | $(GENERATED_FILES_DIR) $(DIGGER)
	$(DIGGER) $(DIGGERFLAGS) --header\
		                 $< -o $@ && sed -i 's/extern/extern __attribute__((section(".text_pipcore")))/g' generated/Internal.h

$(GENERATED_FILES_DIR)/Internal.c: $(GENERATED_FILES_DIR)/Internal.json $(JSONS)\
	                           $(GENERATED_FILES_DIR)/Internal.h\
                                 | $(GENERATED_FILES_DIR) $(DIGGER)
	$(DIGGER) $(DIGGERFLAGS) -q Internal.h -q mal.h\
	                         $< -o $@

$(GENERATED_FILES_DIR)/Services.h: $(GENERATED_FILES_DIR)/Services.json $(JSONS)\
                                 | $(GENERATED_FILES_DIR) $(DIGGER)
	$(DIGGER) $(DIGGERFLAGS) --header\
		                 $< -o $@ && sed -i 's/extern/extern __attribute__((section(".text_pipcore")))/g' generated/Services.h

$(GENERATED_FILES_DIR)/Services.c: $(GENERATED_FILES_DIR)/Services.json $(JSONS)\
	                           $(GENERATED_FILES_DIR)/Services.h\
	                           $(GENERATED_FILES_DIR)/Internal.json\
	                           $(GENERATED_FILES_DIR)/Internal.h\
                                 | $(GENERATED_FILES_DIR) $(DIGGER)
	$(DIGGER) $(DIGGERFLAGS) -m Internal -d :$(GENERATED_FILES_DIR)/Internal.json\
	                         -q Services.h -q Internal.h -q mal.h\
				 $< -o $@

############################## Coq rules ############################

# Rule to generate dependency files
$(COQ_DEPENDENCY_FILES):\
	%.v.d : %.v
	@$(COQDEP) $(COQFLAGS) $< > $@

-include $(COQ_DEPENDENCY_FILES)

ifneq (,$(findstring grouped-target,$(.FEATURES)))
$(JSONS) $(COQ_EXTR_COMPILED_FILES) &:\
		$(COQ_EXTRACTION_FILES) $(COQ_EXTR_DEPFILE)\
		| $(GENERATED_FILES_DIR)
	cd $(GENERATED_FILES_DIR) && $(COQC) $(COQCEXTRFLAGS) ../$<

%.vo %.vok %.vos %.glob .%.aux &: %.v %.v.d
	$(COQC) $(COQCFLAGS) $<
else
# Unfortunately, without grouped-target we cannot inherit dependencies
# computed by coqdep, so we must mv files after the fact
$(JSONS): src/extraction/Extraction.vo | $(GENERATED_FILES_DIR)
	mv $(notdir $@) $(GENERATED_FILES_DIR)

%.vo %.vok %.vos %.glob .%.aux : %.v %.v.d
	$(COQC) $(COQCFLAGS) $<
endif

########################### C object rules ##########################

# Static pattern rule for constructing object files from generated C files
$(C_GENERATED_OBJ):\
    %.o : %.c $(C_GENERATED_HEADERS) $(C_MODEL_INTERFACE_HEADERS)\
              $(C_TARGET_MAL_HEADERS) $(C_TARGET_BOOT_HEADERS)\
              $(C_TARGET_CMSIS_HEADERS) $(C_TARGET_DEBUG_HEADERS)\
              $(C_TARGET_MDK_HEADERS) $(C_TARGET_NEWLIB_HEADERS)\
              $(C_TARGET_UART_HEADERS)
	$(CC) $(CFLAGS) -I $(C_GENERATED_HEADERS_DIR)\
                        -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -I $(C_TARGET_CMSIS_INCLUDE_DIR)\
                        -I $(C_TARGET_DEBUG_INCLUDE_DIR)\
                        -I $(C_TARGET_MDK_INCLUDE_DIR)\
                        -I $(C_TARGET_NEWLIB_INCLUDE_DIR)\
                        -I $(C_TARGET_UART_INCLUDE_DIR)\
                        -c -o $@ $<

# Static pattern rule for constructing object files from target boot C files
$(C_TARGET_BOOT_OBJ):\
    %.o : %.c $(C_GENERATED_HEADERS) $(C_MODEL_INTERFACE_HEADERS)\
              $(C_TARGET_MAL_HEADERS) $(C_TARGET_BOOT_HEADERS)\
              $(C_TARGET_CMSIS_HEADERS) $(C_TARGET_DEBUG_HEADERS)\
              $(C_TARGET_MDK_HEADERS) $(C_TARGET_NEWLIB_HEADERS)\
              $(C_TARGET_UART_HEADERS)
	$(CC) $(CFLAGS) -I $(C_GENERATED_HEADERS_DIR)\
                        -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -I $(C_TARGET_CMSIS_INCLUDE_DIR)\
                        -I $(C_TARGET_DEBUG_INCLUDE_DIR)\
                        -I $(C_TARGET_MDK_INCLUDE_DIR)\
                        -I $(C_TARGET_NEWLIB_INCLUDE_DIR)\
                        -I $(C_TARGET_UART_INCLUDE_DIR)\
                        -c -o $@ $<

$(C_TARGET_CMSIS_OBJ):\
    %.o : %.c $(C_GENERATED_HEADERS) $(C_MODEL_INTERFACE_HEADERS)\
              $(C_TARGET_MAL_HEADERS) $(C_TARGET_BOOT_HEADERS)\
              $(C_TARGET_CMSIS_HEADERS) $(C_TARGET_DEBUG_HEADERS)\
              $(C_TARGET_MDK_HEADERS) $(C_TARGET_NEWLIB_HEADERS)\
              $(C_TARGET_UART_HEADERS)
	$(CC) $(CFLAGS) -I $(C_GENERATED_HEADERS_DIR)\
                        -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -I $(C_TARGET_CMSIS_INCLUDE_DIR)\
                        -I $(C_TARGET_DEBUG_INCLUDE_DIR)\
                        -I $(C_TARGET_MDK_INCLUDE_DIR)\
                        -I $(C_TARGET_NEWLIB_INCLUDE_DIR)\
                        -I $(C_TARGET_UART_INCLUDE_DIR)\
                        -c -o $@ $<

$(C_TARGET_DEBUG_OBJ):\
    %.o : %.c $(C_GENERATED_HEADERS) $(C_MODEL_INTERFACE_HEADERS)\
              $(C_TARGET_MAL_HEADERS) $(C_TARGET_BOOT_HEADERS)\
              $(C_TARGET_CMSIS_HEADERS) $(C_TARGET_DEBUG_HEADERS)\
              $(C_TARGET_MDK_HEADERS) $(C_TARGET_NEWLIB_HEADERS)\
              $(C_TARGET_UART_HEADERS)
	$(CC) $(CFLAGS) -I $(C_GENERATED_HEADERS_DIR)\
                        -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -I $(C_TARGET_CMSIS_INCLUDE_DIR)\
                        -I $(C_TARGET_DEBUG_INCLUDE_DIR)\
                        -I $(C_TARGET_MDK_INCLUDE_DIR)\
                        -I $(C_TARGET_NEWLIB_INCLUDE_DIR)\
                        -I $(C_TARGET_UART_INCLUDE_DIR)\
                        -c -o $@ $<

$(C_TARGET_MDK_OBJ):\
    %.o : %.c $(C_GENERATED_HEADERS) $(C_MODEL_INTERFACE_HEADERS)\
              $(C_TARGET_MAL_HEADERS) $(C_TARGET_BOOT_HEADERS)\
              $(C_TARGET_CMSIS_HEADERS) $(C_TARGET_DEBUG_HEADERS)\
              $(C_TARGET_MDK_HEADERS) $(C_TARGET_NEWLIB_HEADERS)\
              $(C_TARGET_UART_HEADERS)
	$(CC) $(CFLAGS) -I $(C_GENERATED_HEADERS_DIR)\
                        -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -I $(C_TARGET_CMSIS_INCLUDE_DIR)\
                        -I $(C_TARGET_DEBUG_INCLUDE_DIR)\
                        -I $(C_TARGET_MDK_INCLUDE_DIR)\
                        -I $(C_TARGET_NEWLIB_INCLUDE_DIR)\
                        -I $(C_TARGET_UART_INCLUDE_DIR)\
                        -c -o $@ $<

$(C_TARGET_NEWLIB_OBJ):\
    %.o : %.c $(C_GENERATED_HEADERS) $(C_MODEL_INTERFACE_HEADERS)\
              $(C_TARGET_MAL_HEADERS) $(C_TARGET_BOOT_HEADERS)\
              $(C_TARGET_CMSIS_HEADERS) $(C_TARGET_DEBUG_HEADERS)\
              $(C_TARGET_MDK_HEADERS) $(C_TARGET_NEWLIB_HEADERS)\
              $(C_TARGET_UART_HEADERS)
	$(CC) $(CFLAGS) -I $(C_GENERATED_HEADERS_DIR)\
                        -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -I $(C_TARGET_CMSIS_INCLUDE_DIR)\
                        -I $(C_TARGET_DEBUG_INCLUDE_DIR)\
                        -I $(C_TARGET_MDK_INCLUDE_DIR)\
                        -I $(C_TARGET_NEWLIB_INCLUDE_DIR)\
                        -I $(C_TARGET_UART_INCLUDE_DIR)\
                        -c -o $@ $<

$(C_TARGET_UART_OBJ):\
    %.o : %.c $(C_GENERATED_HEADERS) $(C_MODEL_INTERFACE_HEADERS)\
              $(C_TARGET_MAL_HEADERS) $(C_TARGET_BOOT_HEADERS)\
              $(C_TARGET_CMSIS_HEADERS) $(C_TARGET_DEBUG_HEADERS)\
              $(C_TARGET_MDK_HEADERS) $(C_TARGET_NEWLIB_HEADERS)\
              $(C_TARGET_UART_HEADERS)
	$(CC) $(CFLAGS) -I $(C_GENERATED_HEADERS_DIR)\
                        -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -I $(C_TARGET_CMSIS_INCLUDE_DIR)\
                        -I $(C_TARGET_DEBUG_INCLUDE_DIR)\
                        -I $(C_TARGET_MDK_INCLUDE_DIR)\
                        -I $(C_TARGET_NEWLIB_INCLUDE_DIR)\
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
              $(C_TARGET_CMSIS_HEADERS) $(C_TARGET_DEBUG_HEADERS)\
              $(C_TARGET_MDK_HEADERS) $(C_TARGET_NEWLIB_HEADERS)\
              $(C_TARGET_UART_HEADERS)
	$(CC) $(CFLAGS) -I $(C_GENERATED_HEADERS_DIR)\
                        -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -I $(C_TARGET_CMSIS_INCLUDE_DIR)\
                        -I $(C_TARGET_DEBUG_INCLUDE_DIR)\
                        -I $(C_TARGET_MDK_INCLUDE_DIR)\
                        -I $(C_TARGET_NEWLIB_INCLUDE_DIR)\
                        -I $(C_TARGET_UART_INCLUDE_DIR)\
                        -c -o $@ $<

######################### Pip + Partition ELF #######################

# $(AS_TARGET_BOOT_OBJ) must be the first object file arg to the linker
pip.bin: $(C_SRC_TARGET_DIR)/link.ld\
         $(C_TARGET_BOOT_OBJ) $(AS_TARGET_BOOT_OBJ)\
         $(GAS_TARGET_BOOT_OBJ) $(C_TARGET_CMSIS_OBJ)\
         $(C_TARGET_DEBUG_OBJ) $(C_TARGET_MDK_OBJ)\
         $(C_TARGET_NEWLIB_OBJ) $(C_TARGET_UART_OBJ)\
         $(C_TARGET_MAL_OBJ) $(C_GENERATED_OBJ)
	$(LD) -r \
         $(C_TARGET_BOOT_OBJ) $(AS_TARGET_BOOT_OBJ)\
         $(GAS_TARGET_BOOT_OBJ) $(C_TARGET_CMSIS_OBJ)\
         $(C_TARGET_DEBUG_OBJ) $(C_TARGET_MDK_OBJ)\
         $(C_TARGET_NEWLIB_OBJ) $(C_TARGET_UART_OBJ)\
         $(C_TARGET_MAL_OBJ) $(C_GENERATED_OBJ)\
         -T $< -o $@ $(LDFLAGS)

#####################################################################
##                      Proof related targets                      ##
#####################################################################

# TODO: Uncomment the following lines once the proofs are done
#       Don't forget to add this target to the .PHONY target
proofs: $(COQ_PROOF_FILES:.v=.vo)

####################################################################
##                        Utility targets                         ##
####################################################################

####################### Documentation targets ######################

doc: doc-c doc-coq gettingstarted

doc-c: | $(C_DOC_DIR)
	cd doc && doxygen doxygen.conf

doc-coq: $(COQ_VFILES) $(COQ_GLOBFILES) | $(COQ_DOC_DIR)
	$(COQDOC)\
		-toc -interpolate -utf8 -html -g $(COQFLAGS) -d $(COQ_DOC_DIR)\
		$(COQ_VFILES)

gettingstarted:
	cd doc/getting-started/ &&\
        pdflatex getting-started.tex &&\
        pdflatex getting-started.tex

####################################################################

$(GENERATED_FILES_DIR) $(C_DOC_DIR) $(COQ_DOC_DIR):
	mkdir -p $@

######################## Clean ########################
realclean: clean
	rm -rf $(COQ_DOC_DIR) $(C_DOC_DIR)
	rm -f $(DOC_DIR)/getting-started/getting-started.aux\
              $(DOC_DIR)/getting-started/getting-started.out\
              $(DOC_DIR)/getting-started/getting-started.toc\
              $(DOC_DIR)/getting-started/getting-started.log\
              $(DOC_DIR)/getting-started/getting-started.pdf

clean:
	rm -f .lia.cache $(COQ_DEPENDENCY_FILES)
	rm -rf $(COQ_COMPILED_FILES)
	rm -rf $(GENERATED_FILES_DIR)
	rm -f $(OBJECT_FILES)
	rm -f pip.elf
	rm -f pip.bin

.PHONY: all doc doc-c doc-coq gettingstarted realclean clean
