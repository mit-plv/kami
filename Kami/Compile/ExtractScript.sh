#!/bin/bash

sed -i -e 's/import qualified Prelude/import qualified Prelude\rimport qualified Data.Bits\rimport qualified Data.Char\rimport Vtor\r/g' ../../Target.hs
ln -sf ../../Target.hs
ghc --make ./PrettyPrintVerilog.hs
time ./PrettyPrintVerilog > ./top.sv

time verilator --cc top.sv --trace --trace-structs --trace-underscore --exe sim_main.cpp
make -j -C obj_dir -f Vtop.mk Vtop
file obj_dir/Vtop
