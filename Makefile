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

# Per-target build fragment. It must define TARGET_THIRDPARTY_NAMES, the list
# of vendored subdirectories under $(C_TARGET_THIRDPARTY_DIR), which may be
# empty. The include is deliberately not a "-include": a target that forgot
# its fragment would otherwise build and link silently without its vendor code.
ifeq ("$(wildcard $(C_SRC_TARGET_DIR)/target.mk)","")
    $(error Target '$(TARGET)' has no build fragment: $(C_SRC_TARGET_DIR)/target.mk)
endif
include $(C_SRC_TARGET_DIR)/target.mk

C_TARGET_THIRDPARTY_DIRS=$(addprefix $(C_TARGET_THIRDPARTY_DIR)/,$(TARGET_THIRDPARTY_NAMES))
C_TARGET_THIRDPARTY_INCLUDE_DIRS=$(addsuffix /include,$(C_TARGET_THIRDPARTY_DIRS))

C_GENERATED_SRC_DIR=$(GENERATED_FILES_DIR)
C_GENERATED_HEADERS_DIR=$(GENERATED_FILES_DIR)

# Rocq generated C is target-independent, but objects compiled from it are not
C_GENERATED_OBJ_DIR=$(GENERATED_FILES_DIR)/$(TARGET)

#####################################################################
##                        Files variables                          ##
#####################################################################

############################ C files ################################

C_GENERATED_SRC=$(C_GENERATED_SRC_DIR)/Services.c $(C_GENERATED_SRC_DIR)/Internal.c
C_TARGET_BOOT_SRC=$(wildcard $(C_TARGET_BOOT_DIR)/*.c)
C_TARGET_THIRDPARTY_SRC=$(foreach d,$(C_TARGET_THIRDPARTY_DIRS),$(wildcard $(d)/*.c))
C_TARGET_MAL_SRC=$(wildcard $(C_TARGET_MAL_DIR)/*.c)
AS_TARGET_BOOT_SRC=$(wildcard $(C_TARGET_BOOT_DIR)/*.s)
GAS_TARGET_BOOT_SRC=$(wildcard $(C_TARGET_BOOT_DIR)/*.S)

C_GENERATED_HEADERS=$(C_GENERATED_HEADERS_DIR)/Internal.h $(C_GENERATED_HEADERS_DIR)/Services.h
C_MODEL_INTERFACE_HEADERS=$(wildcard $(C_MODEL_INTERFACE_INCLUDE_DIR)/*.h)
C_TARGET_MAL_HEADERS=$(wildcard $(C_TARGET_MAL_INCLUDE_DIR)/*.h)
C_TARGET_BOOT_HEADERS=$(wildcard $(C_TARGET_BOOT_INCLUDE_DIR)/*.h)
C_TARGET_THIRDPARTY_HEADERS=$(foreach d,$(C_TARGET_THIRDPARTY_INCLUDE_DIRS),$(wildcard $(d)/*.h))

C_GENERATED_OBJ=$(addprefix $(C_GENERATED_OBJ_DIR)/,$(notdir $(C_GENERATED_SRC:.c=.o)))
C_TARGET_BOOT_OBJ=$(C_TARGET_BOOT_SRC:.c=.o)
C_TARGET_MAL_OBJ=$(C_TARGET_MAL_SRC:.c=.o)
AS_TARGET_BOOT_OBJ=$(AS_TARGET_BOOT_SRC:.s=.o)
GAS_TARGET_BOOT_OBJ=$(GAS_TARGET_BOOT_SRC:.S=.o)
C_TARGET_THIRDPARTY_OBJ=$(C_TARGET_THIRDPARTY_SRC:.c=.o)

# Include path and header dependencies for the C translated from Rocq. That
# code is architecture-independent: it reaches the hardware only through the
# contract declared in $(C_MODEL_INTERFACE_INCLUDE_DIR), and deliberately does
# not see the target's own headers. Keeping the two sets apart means a change
# to an arch header does not rebuild the generated objects.
C_GENERATED_INCLUDES=-I $(C_GENERATED_HEADERS_DIR)\
                     -I $(C_MODEL_INTERFACE_INCLUDE_DIR)

C_GENERATED_DEP_HEADERS=$(C_GENERATED_HEADERS) $(C_MODEL_INTERFACE_HEADERS)

# Include path and header dependencies for the architecture-dependent C: the
# MAL, the boot layer and the target's vendored third-party code. These do see
# the generated headers, since the boot layer calls the services.
C_TARGET_INCLUDES=$(C_GENERATED_INCLUDES)\
                  -I $(C_TARGET_MAL_INCLUDE_DIR)\
                  -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                  $(foreach d,$(C_TARGET_THIRDPARTY_INCLUDE_DIRS),-I $(d))

C_TARGET_DEP_HEADERS=$(C_GENERATED_DEP_HEADERS)\
                     $(C_TARGET_MAL_HEADERS) $(C_TARGET_BOOT_HEADERS)\
                     $(C_TARGET_THIRDPARTY_HEADERS)

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

# Rocq writes the aux file for d/f.v as d/.f.aux: the dot goes before the
# basename, not before the path. $(1) is a single .v file.
rocq_auxfile = $(dir $(1)).$(notdir $(1:.v=.aux))

ROCQ_AUXFILES=$(foreach v,$(ROCQ_VFILES),$(call rocq_auxfile,$(v)))

# Rocq extraction "compilation" files
ROCQ_EXTR_DEPFILES=$(ROCQ_EXTRACTION_FILES:.v=.v.d)
ROCQ_EXTR_VOFILES=$(ROCQ_EXTRACTION_FILES:.v=.vo)
ROCQ_EXTR_GLOBFILES=$(ROCQ_EXTRACTION_FILES:.v=.glob)
ROCQ_EXTR_VOSFILES=$(ROCQ_EXTRACTION_FILES:.v=.vos)
ROCQ_EXTR_VOKFILES=$(ROCQ_EXTRACTION_FILES:.v=.vok)
ROCQ_EXTR_AUXFILES=$(foreach v,$(ROCQ_EXTRACTION_FILES),$(call rocq_auxfile,$(v)))

ROCQ_EXTR_COMPILED_FILES:=$(ROCQ_EXTR_VOFILES) $(ROCQ_EXTR_GLOBFILES)\
	$(ROCQ_EXTR_VOSFILES) $(ROCQ_EXTR_VOKFILES) $(ROCQ_EXTR_AUXFILES)

# Rocq dx files
ROCQ_DX_VFILES=$(wildcard $(ROCQ_DX_DIR)/*.v)
ROCQ_DX_DEPFILES=$(ROCQ_DX_VFILES:.v=.v.d)
ROCQ_DX_VOFILES=$(ROCQ_DX_VFILES:.v=.vo)
ROCQ_DX_GLOBFILES=$(ROCQ_DX_VFILES:.v=.glob)
ROCQ_DX_VOSFILES=$(ROCQ_DX_VFILES:.v=.vos)
ROCQ_DX_VOKFILES=$(ROCQ_DX_VFILES:.v=.vok)
ROCQ_DX_AUXFILES=$(foreach v,$(ROCQ_DX_VFILES),$(call rocq_auxfile,$(v)))

ROCQ_DX_COMPILED_FILES:=$(ROCQ_DX_VOFILES) $(ROCQ_DX_GLOBFILES)\
	$(ROCQ_DX_VOSFILES) $(ROCQ_DX_VOKFILES) $(ROCQ_DX_AUXFILES)

# Files served by the generic rocq compile rule. This is every .v in the tree,
# not just the ones $(ROCQ_VFILES) builds: a rule that is never invoked costs
# nothing, whereas a missing one breaks a dependency pulled in by rocq dep.
# src/dx/Extr.v is excluded because it has a dedicated rule below, which would
# otherwise be reported as an overriding recipe.
ROCQ_RULE_VFILES:=$(filter-out $(ROCQ_DX_DIR)/Extr.v,\
                      $(wildcard $(ROCQ_CORE_DIR)/*.v)\
                      $(wildcard $(ROCQ_MODEL_DIR)/*.v)\
                      $(wildcard $(ROCQ_PROOF_DIR)/*.v)\
                      $(wildcard $(ROCQ_INVARIANTS_DIR)/*.v)\
                      $(wildcard $(ROCQ_DX_DIR)/*.v)\
                  )

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
             $(C_TARGET_THIRDPARTY_OBJ) $(C_GENERATED_OBJ)\
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

# Skipped when SKIP_ROCQ_DEPS is set, which the compile_commands.json target
# does when it re-invokes make. These are *included* makefiles, and make
# remakes those for real even under --dry-run -- being able to read them is
# what tells make what to do, so -n cannot apply. Combined with
# --always-make that regenerates every one of them, which leaves each .vo
# looking out of date and costs a full Rocq rebuild on the next build. The
# C compilation recipes the database is after do not depend on these at all.
ifndef SKIP_ROCQ_DEPS
-include $(ROCQ_DEPENDENCY_FILES)
endif

%.cmi: %.mli
	$(OCAMLOPT) -args $(DXDIR)/cprinter-inc-args -c $<

%.cmx: %.ml %.cmi
	$(OCAMLOPT) -args $(DXDIR)/cprinter-inc-args -I generated -c $<

generated/cprinter: generated/Main.cmx
	$(OCAMLOPT) -args $(DXDIR)/cprinter-inc-args -args $(DXDIR)/cprinter-link-args $< -o $@

generated/compcert.ini: $(DXDIR)/compcertcprinter/compcert.ini
	cp $< $@

# One compile rule per .v file. A pattern rule cannot be used here because the
# aux file is $(dir)/.$(notdir), and a pattern rule's stem spans the directory
# too: ".%.aux" would ask for ".src/model/MAL.aux".
# $(1) is the .v file, $(2) the target separator ("&:" when make supports
# grouped targets, ":" otherwise).
define rocq_compile_rule
$(1:.v=.vo) $(1:.v=.vok) $(1:.v=.vos) $(1:.v=.glob) $(call rocq_auxfile,$(1)) $(2) $(1) $(1).d
	$$(ROCQ) compile $$(ROCQ_COMPILER_FLAGS) $$<
endef

ifneq (,$(findstring grouped-target,$(.FEATURES)))
$(JSONS) $(ROCQ_EXTR_COMPILED_FILES) &:\
		$(ROCQ_EXTRACTION_FILES) $(ROCQ_EXTR_DEPFILES)\
		| $(GENERATED_FILES_DIR)
	cd $(GENERATED_FILES_DIR) && $(ROCQ) compile $(ROCQ_COMPILER_EXTR_FLAGS) ../$<

$(foreach v,$(ROCQ_RULE_VFILES),$(eval $(call rocq_compile_rule,$(v),&:)))

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

# Unlike the grouped-target branch above, nothing else here builds the
# extraction objects, so they need the generic rule too.
$(foreach v,$(ROCQ_RULE_VFILES) $(ROCQ_EXTRACTION_FILES),\
    $(eval $(call rocq_compile_rule,$(v),:)))

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

# Static pattern rule for constructing object files from the generated C files.
# These are the only objects whose source and object directories differ, hence
# a rule of their own: see $(C_GENERATED_OBJ_DIR) above.
$(C_GENERATED_OBJ):\
    $(C_GENERATED_OBJ_DIR)/%.o : $(C_GENERATED_SRC_DIR)/%.c $(C_GENERATED_DEP_HEADERS)\
                                 | $(C_GENERATED_OBJ_DIR)
	$(CC) $(CFLAGS) $(C_GENERATED_INCLUDES) -c -o $@ $<

# Static pattern rule for constructing object files from the target MAL and the
# target's vendored third-party code. These two share one recipe; only the
# target boot sources need an extra include directory.
$(C_TARGET_MAL_OBJ) $(C_TARGET_THIRDPARTY_OBJ):\
    %.o : %.c $(C_TARGET_DEP_HEADERS)
	$(CC) $(CFLAGS) $(C_TARGET_INCLUDES) -c -o $@ $<

# Static pattern rule for constructing object files from target boot C files
$(C_TARGET_BOOT_OBJ):\
    %.o : %.c $(C_TARGET_DEP_HEADERS)
	$(CC) $(CFLAGS) $(C_TARGET_INCLUDES) -I $(CRT0_DIR) -c -o $@ $<

# Static pattern rule for constructing object files from target boot assembly files
$(AS_TARGET_BOOT_OBJ):\
    %.o : %.s
	$(AS) $(ASFLAGS) -o $@ $<

# The .S sources go through the C preprocessor, so they can share the boot
# layer's headers. They get only that include directory: assembly has no
# business seeing the C translated from Rocq, and the generated headers are
# not assembler-safe anyway.
$(GAS_TARGET_BOOT_OBJ):\
    %.o : %.S $(C_TARGET_BOOT_HEADERS)
	$(AS) $(ASFLAGS) -I $(C_TARGET_BOOT_INCLUDE_DIR) -o $@ $<

######################### Pip + Partition ELF #######################


# Pad the image out to __root, the address link.ld aligns the root partition
# binary to, so that "cat pip.bin root.fae" puts the root exactly where Pip's
# own linker symbols say it is. objcopy's --pad-to takes an address, and
# __root is one.
#
# This replaces an arithmetic that rounded the file size up to
# $(PADDING_POW2). The two agree only when link.ld aligns __root to
# PADDING_POW2 and the ROM starts at address zero, which holds for dwm1001
# and not for rp2350, whose root region is 64K-aligned in flash at
# 0x10000000. $(PADDING_POW2) remains the alignment the FAE concatenation
# needs, now asserted by link.ld rather than imposed here.
pip.bin: pip.elf
	$(BI) $(BIFLAGS)\
          --pad-to=0x$$($(TOOL_PREFIX)nm $< | $(SED) -n 's/^\([0-9a-fA-F]*\) . __root$$/\1/p')\
          --gap-fill=$(PADDING_VALUE)\
        $< $@

# $(AS_TARGET_BOOT_OBJ) must be the first object file arg to the linker
pip.elf: $(C_SRC_TARGET_DIR)/link.ld\
         $(C_TARGET_BOOT_OBJ) $(AS_TARGET_BOOT_OBJ)\
         $(GAS_TARGET_BOOT_OBJ) $(C_TARGET_THIRDPARTY_OBJ)\
         $(C_TARGET_MAL_OBJ) $(C_GENERATED_OBJ)
	$(LD)\
         $(C_TARGET_BOOT_OBJ) $(AS_TARGET_BOOT_OBJ)\
         $(GAS_TARGET_BOOT_OBJ) $(C_TARGET_THIRDPARTY_OBJ)\
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

$(GENERATED_FILES_DIR) $(C_GENERATED_OBJ_DIR) $(C_DOC_DIR) $(ROCQ_DOC_DIR):
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

################################################################
### Compilation database
################################################################

# The compilation database clang tooling reads: clangd, clang-tidy, and
# anything else that needs to know a file's real compiler flags. Without it
# an editor guesses, which on this tree means every arch header looks like a
# missing include.
COMPILE_DB=compile_commands.json

# The target's self-contained builds, which the root Makefile deliberately
# does not drive: the host unit tests and, while it exists, the bring-up
# harness. Wildcarded, so a target that has neither contributes nothing.
COMPILE_DB_SUBDIRS=$(wildcard $(C_SRC_TARGET_DIR)/test $(C_SRC_TARGET_DIR)/bringup)

# Built from make's dry-run output rather than by intercepting a real build.
# Nothing is compiled and no object is touched, so this costs a second and
# works even while pip.elf does not link. --always-make is what makes make
# print every recipe rather than only the out-of-date ones; without it an
# up-to-date tree yields an empty database.
#
# The root build goes in first and the sub-builds append. That order is the
# one that matters: the bring-up harness compiles the same boot sources
# through ../boot/ paths, so each of them appears twice, and clang tooling
# takes the first entry for a given file -- which should be the real build's.
#
# PHONY because it is cheap and because its true dependency is every recipe
# in every one of these Makefiles, which make cannot express.
$(COMPILE_DB):
	@command -v bear > /dev/null || { \
		echo 'bear is not installed: cannot build $(COMPILE_DB)' >&2; \
		exit 2; }
	@# The 'cd generated && ...' recipes, which build the dx printer, are
	@# dropped before bear sees them. bear parse-sh reads its input as one
	@# script and tracks every cd, whereas make runs each recipe line in
	@# its own shell from here -- so those two lines would otherwise push
	@# the recorded directory to generated/generated for every entry after
	@# them, and the root build's include flags are relative to here.
	@# Neither dropped line is a C compilation, which the entry count
	@# below is what confirms.
	$(MAKE) SKIP_ROCQ_DEPS=1 --always-make --keep-going --dry-run \
	    | grep -v '^cd ' | bear parse-sh --output $@
	for dir in $(COMPILE_DB_SUBDIRS) ; do \
		$(MAKE) -C $$dir --always-make --keep-going --dry-run \
		    | grep -v '^cd ' \
		    | bear parse-sh --append --output $@ --directory $$dir ; \
	done
	@# Give every cross-compiled entry an explicit target triple. clangd
	@# takes its target from the driver name and never passes --target
	@# itself, so without this it rejects -mabi= and -march= outright and
	@# falls back to guessed flags. The host entries, which are the unit
	@# tests, are left alone: those really are host builds.
	$(SED) -i 's|^\( *\)"$(CC)",$$|\1"$(CC)",\n\1"--target=$(TARGET_CLANG_TRIPLE)",|' $@
	@# bear's layout is what the substitution above matches, so check it
	@# landed rather than trusting it: a formatting change upstream would
	@# otherwise leave a database that silently does not work.
	@cross=`grep -c '"$(CC)",' $@` ; \
	 tagged=`grep -c -- '"--target=$(TARGET_CLANG_TRIPLE)",' $@` ; \
	 if [ "$$cross" -ne "$$tagged" ] || [ "$$tagged" -eq 0 ] ; then \
		echo "$@: $$tagged of $$cross cross entries got a target triple" >&2 ; \
		exit 2 ; \
	 fi ; \
	 echo "$@: $$tagged entries for $(TARGET_CLANG_TRIPLE), `grep -c '"cc",' $@` for the host"
	@# Every recorded directory must exist, and every recorded file must be
	@# in it. A wrong directory is the failure mode that does not announce
	@# itself: the database parses, clangd loads it, and then resolves the
	@# build's relative include flags against the wrong base.
	@bad=`grep '"directory":' $@ | $(SED) 's|.*: "||; s|".*||' | sort -u \
	      | while read -r d ; do [ -d "$$d" ] || echo "$$d" ; done` ; \
	 if [ -n "$$bad" ] ; then \
		echo "$@: recorded directory does not exist: $$bad" >&2 ; exit 2 ; \
	 fi
	@bad=`grep '"file":' $@ | $(SED) 's|.*: "||; s|".*||' \
	      | while read -r f ; do [ -f "$$f" ] || echo "$$f" ; done` ; \
	 if [ -n "$$bad" ] ; then \
		echo "$@: recorded file does not exist: $$bad" >&2 ; exit 2 ; \
	 fi

clean:
	rm -f .lia.cache $(ROCQ_DEPENDENCY_FILES)
	rm -rf $(ROCQ_COMPILED_FILES)
	rm -rf $(GENERATED_FILES_DIR)
	rm -f $(OBJECT_FILES)
	rm -f pip.elf pip.bin

.PHONY: all doc doc-c doc-rocq gettingstarted realclean clean $(COMPILE_DB)
