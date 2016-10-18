all: HostSim.bsv Proc.bsv
	bsc -sim -u HostSim.bsv
	bsc -sim -e mkHost -o ProcSim *.ba

clean:
	rm -rf *.bo *.ba *.cxx *.h *.o ProcSim ProcSim.so
