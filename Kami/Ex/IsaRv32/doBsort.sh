#!/bin/bash

COMP=riscv32-unknown-elf-gcc

$COMP -O1 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld bsort.c
riscv32-unknown-elf-objdump -d a.out > bsort.dmp
./BinaryToKamiPgm.native bsort.dmp > PgmBsort.v
rm bsort.dmp a.out
