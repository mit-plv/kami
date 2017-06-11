#!/bin/bash

cp ../top.sv ./
cp ../*.mem ./
sed -i -e "s/\\\$/_/g" ./top.sv
rename -f "s/\\\$/_/g" *.mem
sed -i -e "s/_readmemb/\\\$readmemb/g" ./top.sv
make build.vc707g2
