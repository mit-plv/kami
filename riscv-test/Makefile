default_target: test

.PHONY: test clean

RISCV_COMPLIANCE_PATH ?= ./riscv-compliance
TEST_TARGET ?= I-ADD-01

RISCV_GCC ?= riscv64-unknown-elf-gcc
RISCV_GCC_ARGS_BASIS:=\
 -I ./ -I $(RISCV_COMPLIANCE_PATH)/riscv-test-env \
 -O0 -Og \
 -nostartfiles -nodefaultlibs -nostdlib -s -static \
 -T config.ld \
 -march=rv32i -mabi=ilp32

RISCV_GCC_OUT:=$(TEST_TARGET).o
RISCV_GCC_ARGS_OUT:=-o $(RISCV_GCC_OUT)

RISCV_OBJDUMP ?= riscv64-unknown-elf-objdump
RISCV_OBJDUMP_ARGS:=-d
RISCV_OBJDUMP_OUT:=$(TEST_TARGET).objdump

RISCV_OBJCOPY ?= riscv64-unknown-elf-objcopy
RISCV_OBJCOPY_ARGS:=-O binary -j .text -j .data
RISCV_HEX_BIN_OUT:=$(TEST_TARGET).hex.o
RISCV_HEXDUMP_OUT:=$(TEST_TARGET).hex

build: compliance_io.h compliance_test.h
	$(RISCV_GCC) $(RISCV_GCC_ARGS_BASIS) $(RISCV_GCC_ARGS_OUT) $(RISCV_COMPLIANCE_PATH)/riscv-test-suite/rv32i/src/$(TEST_TARGET).S

objdump: build
	$(RISCV_OBJDUMP) $(RISCV_OBJDUMP_ARGS) $(RISCV_GCC_OUT) > $(RISCV_OBJDUMP_OUT)

$(RISCV_OBJDUMP_OUT): objdump

$(RISCV_HEXDUMP_OUT): build
	$(RISCV_OBJCOPY) $(RISCV_OBJCOPY_ARGS) $(RISCV_GCC_OUT) $(RISCV_HEX_BIN_OUT)
	hexdump -v $(RISCV_HEX_BIN_OUT) | cut -c 9- > $(RISCV_HEXDUMP_OUT)

program0.hex: $(RISCV_HEXDUMP_OUT)
	< $< tr ' ' '\n' | grep . | awk 'NR % 4 == 1' > $@
program1.hex: $(RISCV_HEXDUMP_OUT)
	< $< tr ' ' '\n' | grep . | awk 'NR % 4 == 2' > $@
program2.hex: $(RISCV_HEXDUMP_OUT)
	< $< tr ' ' '\n' | grep . | awk 'NR % 4 == 3' > $@
program3.hex: $(RISCV_HEXDUMP_OUT)
	< $< tr ' ' '\n' | grep . | awk 'NR % 4 == 0' > $@

IVERILOG ?= iverilog

debug: system.v mkTop.v objdump program0.hex program1.hex program2.hex program3.hex
	$(IVERILOG) -DDEBUG -y ../Kami/Ext/BluespecFrontEnd/verilog/build/ -y. -g2005-sv -o debug.vvp system.v
	vvp debug.vvp

$(TEST_TARGET).vvp: system.v mkTop.v 
	$(IVERILOG) -y ../Kami/Ext/BluespecFrontEnd/verilog/build/ -y. -g2005-sv -o $(TEST_TARGET).vvp system.v

$(TEST_TARGET).vcd: $(TEST_TARGET).vvp program0.hex program1.hex program2.hex program3.hex
	vvp $(TEST_TARGET).vvp >/dev/null
	mv system.vcd $(TEST_TARGET).vcd
	rm -rf program0.hex program1.hex program2.hex program3.hex

test: $(RISCV_OBJDUMP_OUT) $(TEST_TARGET).vcd
	./test_one.sh $^

clean:
	rm -rf *.o *.objdump *.hex *.vvp *.vcd
