###############################################################################
#  © Université de Lille, The Pip Development Team (2015-2021)                #
#  Copyright (C) 2020-2022 Orange                                             #
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

# For debug purposes, add the following as rules
#	@echo $<
#	$(info $$C_BENCHMARK_OBJ is [${C_BENCHMARK_OBJ}])
# like
#print: $(C_BENCHMARK_HELPERS_OBJ)
#	$(info $$C_BENCHMARK_HELPERS_OBJ is [${C_BENCHMARK_HELPERS_OBJ}])

# Important notice: this Makefile is included in the main Makefile.
# The base repository is thus the main repository.

#####################################################################
##                      Directory variables                        ##
#####################################################################

BENCH_DIR=generated/benchmarks

########################### C related dirs ##########################

# Architecture agnostic C dirs
C_BENCHMARK_DIR=../embench-iot/src/$(BENCH_NAME)
C_TARGET_BENCHMARK_INCLUDE_DIR=../embench-iot/support
C_MAIN_BENCHMARK_DIR=../pip-mpu-benchmark

ALLOCATOR_DIR   = $(C_MAIN_BENCHMARK_DIR)/allocator
SEMIHOSTING_DIR = $(C_MAIN_BENCHMARK_DIR)/semihosting
STDIO_DIR       = $(C_MAIN_BENCHMARK_DIR)/stdio
SVC_DIR         = $(C_MAIN_BENCHMARK_DIR)/svc

INCLUDE_DIRS = -I $(C_MAIN_BENCHMARK_DIR)/include
INCLUDE_DIRS += -I $(ALLOCATOR_DIR)
INCLUDE_DIRS += -I $(SEMIHOSTING_DIR)
INCLUDE_DIRS += -I $(STDIO_DIR)
INCLUDE_DIRS += -I $(SVC_DIR)


#####################################################################
##                        Files variables                          ##
#####################################################################

############################ C files ################################

C_BENCHMARK_SRC=$(wildcard $(C_BENCHMARK_DIR)/*.c)

C_MAIN_BENCHMARK_SRC := $(filter-out $(C_MAIN_BENCHMARK_DIR)/crt0.c, $(wildcard $(C_MAIN_BENCHMARK_DIR)/*.c))
C_MAIN_BENCHMARK_OBJ  = $(addprefix $(BENCH_DIR)/$(BENCH_NAME)/,$(notdir $(C_MAIN_BENCHMARK_SRC:.c=.o)))

C_ALLOCATOR_SRC = $(wildcard $(ALLOCATOR_DIR)/*.c)
#C_MAIN_BENCHMARK_OBJ += $(addprefix $(BENCH_DIR)/$(BENCH_NAME)/allocator/,$(notdir $(C_SRC:.c=.o)))
C_SEMIHOSTING_SRC = $(wildcard $(SEMIHOSTING_DIR)/*.c)
#C_MAIN_BENCHMARK_OBJ += $(addprefix $(BENCH_DIR)/$(BENCH_NAME)/semihosting/,$(notdir $(C_SRC:.c=.o)))
C_STDIO_SRC = $(wildcard $(STDIO_DIR)/*.c)
#C_MAIN_BENCHMARK_OBJ += $(addprefix $(BENCH_DIR)/$(BENCH_NAME)/stdio/,$(notdir $(C_SRC:.c=.o)))
C_SVC_SRC = $(wildcard $(SVC_DIR)/*.c)
#C_MAIN_BENCHMARK_OBJ += $(addprefix $(BENCH_DIR)/$(BENCH_NAME)/svc/,$(notdir $(C_SRC:.c=.o)))

C_BENCHMARK_COMMON_SRC=$(C_TARGET_BENCHMARK_INCLUDE_DIR)/beebsc.c

C_BENCHMARK_OBJ  = $(addprefix $(BENCH_DIR)/$(BENCH_NAME)/,$(notdir $(C_BENCHMARK_SRC:.c=.o)))
C_OTHER_BENCHMARK_OBJ  = $(C_ALLOCATOR_SRC:.c=.o)
C_OTHER_BENCHMARK_OBJ += $(C_SEMIHOSTING_SRC:.c=.o)
C_OTHER_BENCHMARK_OBJ += $(C_STDIO_SRC:.c=.o)
C_OTHER_BENCHMARK_OBJ += $(C_SVC_SRC:.c=.o)



#C_OTHER_BENCHMARK_OBJ  = $(addprefix $(BENCH_DIR)/$(BENCH_NAME)/allocator/,$(notdir $(C_ALLOCATOR_SRC:.c=.o)))
#C_OTHER_BENCHMARK_OBJ += $(addprefix $(BENCH_DIR)/$(BENCH_NAME)/semihosting/,$(notdir $(C_SEMIHOSTING_SRC:.c=.o)))
#C_OTHER_BENCHMARK_OBJ += $(addprefix $(BENCH_DIR)/$(BENCH_NAME)/stdio/,$(notdir $(C_STDIO_SRC:.c=.o)))
#C_OTHER_BENCHMARK_OBJ += $(addprefix $(BENCH_DIR)/$(BENCH_NAME)/svc/,$(notdir $(C_SVC_SRC:.c=.o)))

C_BENCHMARK_COMMON_OBJ=$(addprefix $(BENCH_DIR)/$(BENCH_NAME)/, $(notdir $(C_BENCHMARK_COMMON_SRC:.c=.o)))

OBJECT_FILES += $(C_BENCHMARK_OBJ)
OBJECT_FILES += $(C_MAIN_BENCHMARK_OBJ)
OBJECT_FILES += $(C_OTHER_BENCHMARK_OBJ)
OBJECT_FILES+=$(C_BENCHMARK_COMMON_OBJ)

#####################################################################
##                    Code compilation targets                     ##
#####################################################################
$(C_BENCHMARK_COMMON_OBJ): \
    $(BENCH_DIR)/$(BENCH_NAME)/%.o : $(C_TARGET_BENCHMARK_INCLUDE_DIR)/%.c \
                                    $(BENCH_DIR)/$(BENCH_NAME)
	$(CC) $(CFLAGS) \
                    -I $(C_TARGET_BENCHMARK_INCLUDE_DIR)\
                        -c -o $@ $<
$(C_BENCHMARK_OBJ): \
    $(BENCH_DIR)/$(BENCH_NAME)/%.o : $(C_BENCHMARK_DIR)/%.c \
              $(BENCH_DIR)/$(BENCH_NAME)
	$(CC) $(CFLAGS) \
                    $(INCLUDE_DIRS)\
                    -I $(C_TARGET_BENCHMARK_INCLUDE_DIR)\
                    -c -o $@ $<


$(C_MAIN_BENCHMARK_OBJ): \
    $(BENCH_DIR)/$(BENCH_NAME)/%.o : $(C_MAIN_BENCHMARK_DIR)/%.c\
              $(BENCH_DIR)/$(BENCH_NAME)
	@echo $<
	$(info $$C_MAIN_BENCHMARK_OBJ is [${C_MAIN_BENCHMARK_OBJ}])
	$(info $$C_MAIN_BENCHMARK_SRC is [${C_MAIN_BENCHMARK_SRC}])
	$(info $$C_SRC is [${C_SRC}])
	$(CC) $(CFLAGS) -I .\
                    $(INCLUDE_DIRS)\
                    -I $(C_TARGET_BENCHMARK_INCLUDE_DIR)\
                        -c -o $@ $<

%.o: %.c
	$(info $$C_OTHER_BENCHMARK_OBJ is [${C_OTHER_BENCHMARK_OBJ}])
	$(CC) $(CFLAGS)\
	    $(INCLUDE_DIRS)\
	    -c $< -o $@

######################### ELF #######################

ifndef BENCH_NAME
all:
	$(error BENCH_NAME not set)
else
all: $(BENCH_DIR)/$(BENCH_NAME)/$(BENCH_NAME).elf print_elf
endif

$(BENCH_DIR)/$(BENCH_NAME)/$(BENCH_NAME).elf: $(ARCH_DEPENDENT_DIR)/$(BOARD)/link.ld\
         $(C_TARGET_BOOT_OBJ) $(AS_TARGET_BOOT_OBJ)\
         $(GAS_TARGET_BOOT_OBJ) $(C_TARGET_CMSIS_OBJ)\
         $(C_TARGET_DEBUG_OBJ) $(C_TARGET_MDK_OBJ)\
         $(C_TARGET_NEWLIB_OBJ) $(C_TARGET_UART_OBJ)\
         $(C_TARGET_MAL_OBJ) $(C_GENERATED_OBJ)\
         $(C_BENCHMARK_COMMON_OBJ) $(C_BENCHMARK_OBJ)\
         $(C_MAIN_BENCHMARK_OBJ) $(C_BENCHMARK_HELPERS_OBJ)\
         $(C_OTHER_BENCHMARK_OBJ)
	$(LD) -L $(C_SRC_TARGET_DIR)\
         $(C_TARGET_BOOT_OBJ) $(AS_TARGET_BOOT_OBJ)\
         $(GAS_TARGET_BOOT_OBJ) $(C_TARGET_CMSIS_OBJ)\
         $(C_TARGET_DEBUG_OBJ) $(C_TARGET_MDK_OBJ)\
         $(C_TARGET_NEWLIB_OBJ) $(C_TARGET_UART_OBJ)\
         $(C_TARGET_MAL_OBJ) $(C_GENERATED_OBJ)\
         $(C_BENCHMARK_COMMON_OBJ) $(C_BENCHMARK_OBJ)\
         $(C_MAIN_BENCHMARK_OBJ) $(C_BENCHMARK_HELPERS_OBJ)\
         $(C_OTHER_BENCHMARK_OBJ)\
         -T $< -o $@ $(LDFLAGS)

print_elf: $(BENCH_DIR)/$(BENCH_NAME)/$(BENCH_NAME).elf
	@echo '-> Created' $<

####################################################################

$(BENCH_DIR)/$(BENCH_NAME):
	mkdir -p $@

cleanbench-soft:
	rm -f $(OBJECT_FILES)

cleanbench-hard:
	rm -rf $(BENCH_DIR)
