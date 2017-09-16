#!/bin/bash

COMP=riscv32-unknown-elf-gcc

$COMP -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld fact.c
riscv32-unknown-elf-objdump -d a.out > fact.dmp
./BinaryToKamiPgm.native fact.dmp > PgmFact.v
rm fact.dmp a.out
