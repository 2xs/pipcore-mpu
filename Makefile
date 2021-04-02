CC = arm-none-eabi-gcc
AS = arm-none-eabi-as
#LD = arm-none-eabi-ld
BI = arm-none-eabi-objcopy

## COMPILER FLAGS
CFLAGS = -mthumb -mcpu=cortex-m4  #
CFLAGS += -Isrc/boot/dwm1001/ARM/cmsis/include -Isrc/boot/dwm1001/ARM #-Isrc/boot/dwm1001/ARM/newlib #-lc #-I/usr/arm-none-eabi/include #-nostdinc --specs=nano.specs --specs=nosys.specs
CFLAGS += -Isrc/boot/dwm1001/ARM/mdk -Isrc/boot/dwm1001/ARM/mdk/headers
CFLAGS += -Isrc/boot/dwm1001/ARM/mdk/util -Isrc/boot/dwm1001/ARM/mdk/common -Isrc/boot/dwm1001/ARM/mdk/hal
# include debug symbols
CFLAGS += -g -DDEBUG # debug symbols for GDB
CFLAGS += -Og # optimize debugging experience more than -O0
# debug through semihosting TODO: set as commandline var
CFLAGS += -DTRACE -DOS_USE_TRACE_SEMIHOSTING_DEBUG -Isrc/boot/dwm1001/ARM/debug # debug on semihosting debug channel and trace API
# debug through UART TODO: set as commandline var
CFLAGS += -DDEBUG_UART -Isrc/boot/dwm1001/ARM/uart # debug through UART
#CFLAGS += -fmessage-length=0
#CFLAGS += -ffunction-sections
#CFLAGS += -fdata-sections
#CFLAGS += --specs=nosys.specs
CFLAGS += -DNRF52832_XXAA
BIN = $(CURDIR)
OBJ = $(CURDIR)

# LINKER FLAGS
LDFLAGS += -nostartfiles  # do not include start files but keep default libs: -nostdlib = -nostartfiles + -nodefaultlibs
LDFLAGS += -lc -lgcc -lm -std=gnu11
LDFLAGS += -Wall # recommended compiler warnings
LDFLAGS += -ffreestanding # remove printf to puts optimizations
LDFLAGS += -mthumb -mcpu=cortex-m4
#LDFLAGS = -lgcc -lc -lm -lrdimon -std=gnu11 -Og -fmessage-length=0 -fsigned-char -ffunction-sections -fdata-sections -ffreestanding -fno-move-loop-invariants -Wall -Wextra
#LDFLAGS += --specs=nosys.specs --specs=rdimon.specs -lrdimon

# LINKER VARIABLES
TARGET = dwm1001
BUILD_DIR=build
SRC_DIR=src
TARGET_DIR=$(BUILD_DIR)/$(TARGET)
KERNEL_BASENAME=pip
#KERNEL_ELF=$(KERNEL_BASENAME).elf
#KERNEL_BIN=$(KERNEL_BASENAME).bin
LINKSCRIPT := $(SRC_DIR)/boot/$(TARGET)/ARM/link.ld

# .c & .S FILES
C_FILES = $(wildcard $(SRC_DIR)/boot/$(TARGET)/ARM/*.c)
C_FILES_UART = $(wildcard $(SRC_DIR)/boot/$(TARGET)/ARM/uart/*.c)
C_FILES_MDK = $(wildcard $(SRC_DIR)/boot/$(TARGET)/ARM/mdk/*.c)
C_FILES_MDK_COM = $(wildcard $(SRC_DIR)/boot/$(TARGET)/ARM/mdk/common/*.c)
C_FILES_DEBUG = $(wildcard $(SRC_DIR)/boot/$(TARGET)/ARM/debug/*.c)
C_FILES_NEWLIB = $(wildcard $(SRC_DIR)/boot/$(TARGET)/ARM/newlib/*.c)
S_FILES = $(wildcard $(SRC_DIR)/boot/$(TARGET)/ARM/*.S)

# OBJECT FILES
# String substitution for every C/C++ file.
#OBJS := $(C_FILES:%=$(TARGET_DIR)/%.o)
#OBJS := $(patsubst %.c, $(TARGET_DIR)/%.o, $(C_FILES))
OBJS = $(patsubst %.c, $(TARGET_DIR)/%.o, $(notdir $(C_FILES))) # .c -> .o but do not include the name of the directory
#OBJS = $(patsubst %.c, %.o, $(C_FILES))

OBJS_UART = $(patsubst %.c, $(TARGET_DIR)/uart/%.o, $(notdir $(C_FILES_UART)))
OBJS += $(OBJS_UART)
OBJS_MDK = $(patsubst %.c, $(TARGET_DIR)/mdk/%.o, $(notdir $(C_FILES_MDK)))
OBJS += $(OBJS_MDK)
OBJS_MDK_COM = $(patsubst %.c, $(TARGET_DIR)/mdk/common/%.o, $(notdir $(C_FILES_MDK_COM)))
OBJS += $(OBJS_MDK_COM)
OBJS_DEBUG = $(patsubst %.c, $(TARGET_DIR)/debug/%.o, $(notdir $(C_FILES_DEBUG)))
OBJS += $(OBJS_DEBUG)
OBJS_NEWLIB = $(patsubst %.c, $(TARGET_DIR)/newlib/%.o, $(notdir $(C_FILES_NEWLIB)))
OBJS += $(OBJS_NEWLIB)
OBJS += $(patsubst %.S, $(TARGET_DIR)/%.o, $(notdir $(S_FILES)))

# RULES
all: app.bin

#%.o: %.S
$(TARGET_DIR)/%.o: $(SRC_DIR)/boot/$(TARGET)/ARM/%.S
	$(AS) -o $@ $^ $(ASFLAGS)

#%.o: %.c
$(TARGET_DIR)/newlib/%.o: $(SRC_DIR)/boot/$(TARGET)/ARM/newlib/%.c
	$(CC) -o $@ $^ -c $(CFLAGS)

$(TARGET_DIR)/uart/%.o: $(SRC_DIR)/boot/$(TARGET)/ARM/uart/%.c
	$(CC) -o $@ $^ -c $(CFLAGS)

$(TARGET_DIR)/mdk/%.o: $(SRC_DIR)/boot/$(TARGET)/ARM/mdk/%.c
	$(CC) -o $@ $^ -c $(CFLAGS)

$(TARGET_DIR)/mdk/common/%.o: $(SRC_DIR)/boot/$(TARGET)/ARM/mdk/common/%.c
	$(CC) -o $@ $^ -c $(CFLAGS)

$(TARGET_DIR)/debug/%.o: $(SRC_DIR)/boot/$(TARGET)/ARM/debug/%.c
	$(CC) -o $@ $^ -c $(CFLAGS)

$(TARGET_DIR)/%.o: $(SRC_DIR)/boot/$(TARGET)/ARM/%.c
	$(CC) -o $@ $^ -c $(CFLAGS)

app.elf: $(OBJS)
	$(CC) $(LDFLAGS) -T$(LINKSCRIPT) $^ -o $(TARGET_DIR)/app.elf

app.bin: $(TARGET_DIR) app.elf
	$(BI) -O binary $(TARGET_DIR)/app.elf $(TARGET_DIR)/app.bin

clean:
	rm -rf $(TARGET_DIR)/

# Generate build directory
$(TARGET_DIR):
	mkdir -p $@
	mkdir -p $@/newlib
	mkdir -p $@/uart
	mkdir -p $@/mdk
	mkdir -p $@/mdk/common
	mkdir -p $@/debug
