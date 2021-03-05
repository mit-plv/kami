default_target: verilog

.PHONY: clean

TARGET ?= Top
TARGET_VM ?= mkTop
TARGET_VM_FRAM ?= mkTopM

PROC_DIR ?= ../../Ocaml/
PROC ?= $(PROC_DIR)Proc.bsv

BUILD_DIR ?= build

BSC ?= bsc \
	-bdir $(BUILD_DIR) \
	-info-dir $(BUILD_DIR) \
	-simdir $(BUILD_DIR) \
	-vdir $(BUILD_DIR)
BSC_LIB_PATH := $(dir $(realpath $(shell which bsc)))../lib/Verilog

verilog_comp: $(TARGET).bsv $(PROC) SimpleBRAM.bsv MulDiv.bsv
	mkdir -p $(BUILD_DIR)
	$(BSC) -verilog -p +:$(PROC_DIR) +RTS -K100M -RTS -g $(TARGET_VM) -steps 2000000000 -u $(TARGET).bsv

verilog_lib_copy:
	cp $(BSC_LIB_PATH)/FIFO2.v $(BUILD_DIR)/
	cp $(BSC_LIB_PATH)/RegFile.v $(BUILD_DIR)/
	cp $(BSC_LIB_PATH)/SizedFIFO.v $(BUILD_DIR)/

verilog: verilog_comp verilog_lib_copy

sim: $(TARGET).bsv $(PROC) SimpleBRAM.bsv MulDiv.bsv
	mkdir -p $(BUILD_DIR)
	$(BSC) -sim -p +:$(PROC_DIR) -u +RTS -K100M -RTS -steps 2000000000 $(TARGET).bsv
	$(BSC) -sim -p +:$(PROC_DIR) -e $(TARGET_VM) -steps 2000000000 -o $(TARGET_VM) *.ba

sim_with_fram: $(TARGET).bsv $(PROC) FRAM.bsv SimpleBRAM.bsv MulDiv.bsv
	mkdir -p $(BUILD_DIR)
	$(BSC) -sim -p +:$(PROC_DIR) -u +RTS -K100M -RTS -steps 2000000000 $(TARGET).bsv
	$(BSC) -sim -p +:$(PROC_DIR) -e $(TARGET_VM_FRAM) -steps 2000000000 -o $(TARGET_VM_FRAM) *.ba

clean:
	rm -rf $(BUILD_DIR)
	rm -rf $(TARGET) $(TARGET).so
# rm -rf *.bo *.ba *.cxx *.h *.o
# rm -rf $(TARGET_VM) $(TARGET_VM).so $(TARGET_VM_FRAM) $(TARGET_VM_FRAM).so
# rm -rf mkBramInst.v $(TARGET_VM).v $(TARGET_VM_FRAM).v
