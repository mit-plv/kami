#!/bin/bash
set -e

COMP=riscv32-unknown-elf-gcc
OBJDUMP=riscv32-unknown-elf-objdump

$COMP -O1 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld bsort.c
$OBJDUMP -d a.out > bsort.dmp
./BinaryToKamiPgm.native bsort.dmp > PgmBsort.v
rm a.out
