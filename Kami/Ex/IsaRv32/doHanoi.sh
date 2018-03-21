#!/bin/bash
set -e

COMP=riscv32-unknown-elf-gcc
OBJDUMP=riscv32-unknown-elf-objdump

$COMP -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld hanoi.c
$OBJDUMP -d a.out > hanoi.dmp
./BinaryToKamiPgm.native hanoi.dmp > PgmHanoi.v
rm hanoi.dmp a.out
