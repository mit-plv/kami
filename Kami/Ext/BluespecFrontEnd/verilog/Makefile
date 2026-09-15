default_target: verilog

.PHONY: default_target verilog sim sim_with_fram clean

BSC ?= bsc
BSCFLAGS := +RTS -K100M -RTS -steps 2000000000 -bdir gen -vdir gen -info-dir gen -simdir gen

# The processor extracted from Kami (see ../../Extraction.v and ../../Ocaml).
../../Ocaml/Proc.bsv:
	$(MAKE) -C ../../Ocaml Proc.bsv

Proc.bsv: ../../Ocaml/Proc.bsv
	cp $< $@

gen:
	mkdir -p gen

gen/mkTop.v: Top.bsv Proc.bsv SimpleBRAM.bsv MulDiv.bsv FRAM.bsv RegFileZero.bsv | gen
	$(BSC) -verilog $(BSCFLAGS) -g mkTop -u Top.bsv

verilog: gen/mkTop.v

sim: Top.bsv Proc.bsv SimpleBRAM.bsv MulDiv.bsv | gen
	$(BSC) -sim $(BSCFLAGS) -u Top.bsv
	$(BSC) -sim $(BSCFLAGS) -e mkTop -o mkTop gen/*.ba

sim_with_fram: Top.bsv Proc.bsv FRAM.bsv SimpleBRAM.bsv MulDiv.bsv | gen
	$(BSC) -sim $(BSCFLAGS) -u Top.bsv
	$(BSC) -sim $(BSCFLAGS) -e mkTopM -o mkTopM gen/*.ba

clean:
	rm -rf gen
	rm -f Proc.bsv mkTop mkTop.so mkTopM mkTopM.so
