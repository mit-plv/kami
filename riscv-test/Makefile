default_target: hexdump

.PHONY: build objdump hexdump clean

RISCV_COMPLIANCE_PATH ?= ./riscv-compliance
TEST_TARGET ?= I-ADD-01

RISCV_GCC ?= riscv64-unknown-elf-gcc
RISCV_GCC_ARGS_BASIS:=\
 -I ./ -I $(RISCV_COMPLIANCE_PATH)/riscv-test-env \
 -O0 \
 -nostartfiles -nodefaultlibs -nostdlib -s -static \
 -T config.ld \
 -march=rv32i -mabi=ilp32

RISCV_GCC_OUT:=$(TEST_TARGET).o
RISCV_GCC_ARGS_OUT:=-o $(RISCV_GCC_OUT)

RISCV_OBJDUMP ?= riscv64-unknown-elf-objdump
RISCV_OBJDUMP_ARGS:=-d
RISCV_OBJDUMP_OUT:=$(TEST_TARGET).objdump

RISCV_OBJCOPY ?= riscv64-unknown-elf-objcopy
RISCV_OBJCOPY_ARGS:=-O binary -j .text
RISCV_HEX_BIN_OUT:=$(TEST_TARGET).hex.o
RISCV_HEXDUMP_OUT:=$(TEST_TARGET).hex

build: compliance_io.h compliance_test.h
	$(RISCV_GCC) $(RISCV_GCC_ARGS_BASIS) $(RISCV_GCC_ARGS_OUT) $(RISCV_COMPLIANCE_PATH)/riscv-test-suite/rv32i/src/$(TEST_TARGET).S

objdump: build
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_ARGS) $(RISCV_GCC_OUT) > $(RISCV_OBJDUMP_OUT)

hexdump: build
	$(RISCV_OBJCOPY) $(RISCV_OBJCOPY_ARGS) $(RISCV_GCC_OUT) $(RISCV_HEX_BIN_OUT)
	od -An -t x1 $(RISCV_HEX_BIN_OUT) > $(RISCV_HEXDUMP_OUT)

clean:
	rm -rf $(RISCV_GCC_OUT) $(RISCV_OBJDUMP_OUT) $(RISCV_HEX_BIN_OUT) $(RISCV_HEXDUMP_OUT)
