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

#####################################################################
##                        Files variables                          ##
#####################################################################

############################ C files ################################

C_BENCHMARK_SRC=$(wildcard $(C_BENCHMARK_DIR)/*.c)
C_MAIN_BENCHMARK_SRC := $(filter-out $(C_MAIN_BENCHMARK_DIR)/crt0.c, $(wildcard $(C_MAIN_BENCHMARK_DIR)/*.c))
C_BENCHMARK_COMMON_SRC=$(C_TARGET_BENCHMARK_INCLUDE_DIR)/beebsc.c

C_BENCHMARK_OBJ=$(addprefix $(BENCH_DIR)/$(BENCH_NAME)/,$(notdir $(C_BENCHMARK_SRC:.c=.o)))
C_MAIN_BENCHMARK_OBJ=$(addprefix $(BENCH_DIR)/$(BENCH_NAME)/,$(notdir $(C_MAIN_BENCHMARK_SRC:.c=.o)))
C_BENCHMARK_COMMON_OBJ=$(addprefix $(BENCH_DIR)/$(BENCH_NAME)/, $(notdir $(C_BENCHMARK_COMMON_SRC:.c=.o)))

OBJECT_FILES+=$(C_BENCHMARK_OBJ)
OBJECT_FILES+=$(C_MAIN_BENCHMARK_OBJ)

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
                    -I $(C_TARGET_BENCHMARK_INCLUDE_DIR)\
                    -c -o $@ $<


$(C_MAIN_BENCHMARK_OBJ): \
    $(BENCH_DIR)/$(BENCH_NAME)/%.o : $(C_MAIN_BENCHMARK_DIR)/%.c\
              $(BENCH_DIR)/$(BENCH_NAME)
	$(CC) $(CFLAGS) -I.\
                    -I $(C_MAIN_BENCHMARK_DIR)\
                    -I $(C_TARGET_BENCHMARK_INCLUDE_DIR)\
                        -c -o $@ $<

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
         $(C_MAIN_BENCHMARK_OBJ) $(C_BENCHMARK_HELPERS_OBJ)
	$(LD) -L $(C_SRC_TARGET_DIR)\
         $(C_TARGET_BOOT_OBJ) $(AS_TARGET_BOOT_OBJ)\
         $(GAS_TARGET_BOOT_OBJ) $(C_TARGET_CMSIS_OBJ)\
         $(C_TARGET_DEBUG_OBJ) $(C_TARGET_MDK_OBJ)\
         $(C_TARGET_NEWLIB_OBJ) $(C_TARGET_UART_OBJ)\
         $(C_TARGET_MAL_OBJ) $(C_GENERATED_OBJ)\
         $(C_BENCHMARK_COMMON_OBJ) $(C_BENCHMARK_OBJ)\
         $(C_MAIN_BENCHMARK_OBJ) $(C_BENCHMARK_HELPERS_OBJ)\
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
