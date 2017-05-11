all: HostSim.bsv Proc.bsv
	bsc -verilog -elab -u -steps 2000000000 HostSim.bsv
	bsc -sim -e mkHost -steps 2000000000 -o ProcSim *.ba

clean:
	rm -rf *.v *.bo *.ba *.cxx *.h *.o ProcSim ProcSim.so
