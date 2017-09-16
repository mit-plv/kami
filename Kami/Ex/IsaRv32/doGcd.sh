#!/bin/bash

COMP=riscv32-unknown-elf-gcc

$COMP -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld gcd.c
riscv32-unknown-elf-objdump -d a.out > gcd.dmp
./BinaryToKamiPgm.native gcd.dmp > PgmGcd.v
rm gcd.dmp a.out
