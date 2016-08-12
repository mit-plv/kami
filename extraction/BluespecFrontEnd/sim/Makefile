EXEC_NAME=ProcExec

.PHONY: sim clean 

sim: FrontEnd.bsv Proc.bsv
	bsc -sim -u ToHostFrontEnd.bsv
	bsc -sim -e mkProcHost -o $(EXEC_NAME) *.ba

clean:
	rm -rf *.bo *.ba *.cxx *.h *.o $(EXEC_NAME) "$(EXEC_NAME).so"
