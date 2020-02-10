default_target: all

.PHONY: all test

RISCV_GCC ?= riscv64-unknown-elf-gcc
RISCV_GCC_ARGS:=-I ./ -I ./riscv-compliance/riscv-test-env -O0 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld -march=rv32i -mabi=ilp32

RISCV_OBJDUMP ?= riscv64-unknown-elf-objdump
RISCV_OBJDUMP_ARGS:=-d

test:
	$(RISCV_GCC) $(RISCV_GCC_ARGS) riscv-compliance/riscv-test-suite/rv32i/src/I-ADD-01.S

all: test
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_ARGS) a.out > a.objdump

clean:
	rm -rf a.out a.objdump
