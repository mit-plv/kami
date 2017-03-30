#!/bin/bash

sed -i -e "s/import qualified Prelude/import qualified Prelude\nimport qualified Data.Bits\nimport qualified Data.Char\n/g" ../Target.hs
ln -s ../Target.hs
ghc --make ./PrettyPrintVerilog.hs
time ./PrettyPrintVerilog > ./top.ver

time verilator --cc top.ver --exe sim_main.cpp
make -j -C obj_dir -f Vtop.mk Vtop
file obj_dir/Vtop
