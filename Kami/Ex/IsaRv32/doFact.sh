#!/bin/bash
set -e

COMP=riscv32-unknown-elf-gcc
OBJDUMP=riscv32-unknown-elf-objdump

$COMP -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld fact.c
$OBJDUMP -d a.out > fact.dmp
./BinaryToKamiPgm.native fact.dmp > PgmFact.v
rm fact.dmp a.out
