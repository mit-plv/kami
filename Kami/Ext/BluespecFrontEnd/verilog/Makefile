all: Top.bsv Proc.bsv
	bsc -verilog +RTS -K100M -RTS -g mkTop -steps 2000000000 -u Top.bsv

clean:
	rm -rf *.bo *.ba *.v
