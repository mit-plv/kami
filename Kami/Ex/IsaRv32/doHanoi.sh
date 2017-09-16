#!/bin/bash

COMP=riscv32-unknown-elf-gcc

$COMP -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld hanoi.c
riscv32-unknown-elf-objdump -d a.out > hanoi.dmp
./BinaryToKamiPgm.native hanoi.dmp > PgmHanoi.v
rm hanoi.dmp a.out
