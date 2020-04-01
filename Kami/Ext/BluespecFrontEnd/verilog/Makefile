default_target: verilog

.PHONY: clean

BSC ?= bsc

verilog: Top.bsv Proc.bsv SimpleBRAM.bsv MulDiv.bsv
	$(BSC) -verilog +RTS -K100M -RTS -g mkTop -steps 2000000000 -u Top.bsv

sim: Top.bsv Proc.bsv SimpleBRAM.bsv MulDiv.bsv
	$(BSC) -sim -u +RTS -K100M -RTS -steps 2000000000 Top.bsv
	$(BSC) -sim -e mkTop -steps 2000000000 -o mkTop *.ba

sim_with_fram: Top.bsv Proc.bsv FRAM.bsv SimpleBRAM.bsv MulDiv.bsv
	$(BSC) -sim -u +RTS -K100M -RTS -steps 2000000000 Top.bsv
	$(BSC) -sim -e mkTopM -steps 2000000000 -o mkTopM *.ba

clean:
	rm -rf *.bo *.ba *.cxx *.h *.o
	rm -rf mkTop mkTop.so mkTopM mkTopM.so
	rm -rf mkBramInst.v mkTop.v mkTopM.v
