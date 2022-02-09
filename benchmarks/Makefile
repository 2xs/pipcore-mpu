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

#####################################################################
##                      Directory variables                        ##
#####################################################################

BENCH_DIR=generated/benchmarks

########################### C related dirs ##########################

# Architecture agnostic C dirs
C_BENCHMARK_DIR=../embench-iot/src/$(BENCH_NAME)
C_TARGET_BENCHMARK_INCLUDE_DIR=../embench-iot/support

#####################################################################
##                        Files variables                          ##
#####################################################################

############################ C files ################################

C_BENCHMARK_SRC=$(wildcard $(C_BENCHMARK_DIR)/*.c)
C_BENCHMARK_COMMON_SRC=$(C_TARGET_BENCHMARK_INCLUDE_DIR)/beebsc.c

C_BENCHMARK_OBJ=$(addprefix $(BENCH_DIR)/$(BENCH_NAME)/,$(notdir $(C_BENCHMARK_SRC:.c=.o)))
C_BENCHMARK_COMMON_OBJ=$(addprefix $(BENCH_DIR)/$(BENCH_NAME)/, $(notdir $(C_BENCHMARK_COMMON_SRC:.c=.o)))

OBJECT_FILES+=$(C_BENCHMARK_OBJ)

#####################################################################
##                    Code compilation targets                     ##
#####################################################################

$(C_BENCHMARK_COMMON_OBJ): \
    $(BENCH_DIR)/$(BENCH_NAME)/%.o : $(C_TARGET_BENCHMARK_INCLUDE_DIR)/%.c $(C_GENERATED_HEADERS) $(C_MODEL_INTERFACE_HEADERS)\
              $(C_TARGET_MAL_HEADERS) $(C_TARGET_BOOT_HEADERS)\
              $(C_TARGET_CMSIS_HEADERS) $(C_TARGET_DEBUG_HEADERS)\
              $(C_TARGET_MDK_HEADERS) $(C_TARGET_NEWLIB_HEADERS)\
              $(C_TARGET_UART_HEADERS)\
              $(BENCH_DIR)/$(BENCH_NAME)
	$(CC) $(CFLAGS) -I $(C_GENERATED_HEADERS_DIR)\
                        -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -I $(C_TARGET_CMSIS_INCLUDE_DIR)\
                        -I $(C_TARGET_DEBUG_INCLUDE_DIR)\
                        -I $(C_TARGET_MDK_INCLUDE_DIR)\
                        -I $(C_TARGET_NEWLIB_INCLUDE_DIR)\
                        -I $(C_TARGET_UART_INCLUDE_DIR)\
                        -I $(C_TARGET_BENCHMARK_INCLUDE_DIR)\
                        -c -o $@ $<

$(C_BENCHMARK_OBJ): \
    $(BENCH_DIR)/$(BENCH_NAME)/%.o : $(C_BENCHMARK_DIR)/%.c   $(C_GENERATED_HEADERS) $(C_MODEL_INTERFACE_HEADERS)\
              $(C_TARGET_MAL_HEADERS) $(C_TARGET_BOOT_HEADERS)\
              $(C_TARGET_CMSIS_HEADERS) $(C_TARGET_DEBUG_HEADERS)\
              $(C_TARGET_MDK_HEADERS) $(C_TARGET_NEWLIB_HEADERS)\
              $(C_TARGET_UART_HEADERS)\
              $(BENCH_DIR)/$(BENCH_NAME)
	$(CC) $(CFLAGS) -I $(C_GENERATED_HEADERS_DIR)\
                        -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -I $(C_TARGET_CMSIS_INCLUDE_DIR)\
                        -I $(C_TARGET_DEBUG_INCLUDE_DIR)\
                        -I $(C_TARGET_MDK_INCLUDE_DIR)\
                        -I $(C_TARGET_NEWLIB_INCLUDE_DIR)\
                        -I $(C_TARGET_UART_INCLUDE_DIR)\
                        -I $(C_TARGET_BENCHMARK_INCLUDE_DIR)\
                        -c -o $@ $<

######################### ELF #######################

all:
	$(error No rule named "all", use "bench" instead)

ifndef BENCH_NAME
bench:
	$(error BENCH_NAME not set)
else
bench: $(BENCH_DIR)/$(BENCH_NAME)/$(BENCH_NAME).bin
endif

$(BENCH_DIR)/$(BENCH_NAME)/$(BENCH_NAME).bin: $(BENCH_DIR)/$(BENCH_NAME)/$(BENCH_NAME).elf
	$(BI) -O binary $< $@

$(BENCH_DIR)/$(BENCH_NAME)/$(BENCH_NAME).elf: $(C_SRC_TARGET_DIR)/link.ld\
         $(C_TARGET_BOOT_OBJ) $(AS_TARGET_BOOT_OBJ)\
         $(GAS_TARGET_BOOT_OBJ) $(C_TARGET_CMSIS_OBJ)\
         $(C_TARGET_DEBUG_OBJ) $(C_TARGET_MDK_OBJ)\
         $(C_TARGET_NEWLIB_OBJ) $(C_TARGET_UART_OBJ)\
         $(C_TARGET_MAL_OBJ) $(C_GENERATED_OBJ)\
         $(C_BENCHMARK_COMMON_OBJ) $(C_BENCHMARK_OBJ)
	$(LD) \
         $(C_TARGET_BOOT_OBJ) $(AS_TARGET_BOOT_OBJ)\
         $(GAS_TARGET_BOOT_OBJ) $(C_TARGET_CMSIS_OBJ)\
         $(C_TARGET_DEBUG_OBJ) $(C_TARGET_MDK_OBJ)\
         $(C_TARGET_NEWLIB_OBJ) $(C_TARGET_UART_OBJ)\
         $(C_TARGET_MAL_OBJ) $(C_GENERATED_OBJ)\
         $(C_BENCHMARK_COMMON_OBJ) $(C_BENCHMARK_OBJ)\
         -T $< -o $@ $(LDFLAGS)

####################################################################

$(BENCH_DIR)/$(BENCH_NAME):
	mkdir -p $@
