#!/bin/bash
set -e

COMP=riscv32-unknown-elf-gcc
OBJDUMP=riscv32-unknown-elf-objdump

$COMP -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld gcd.c
$OBJDUMP -d a.out > gcd.dmp
./BinaryToKamiPgm.native gcd.dmp > PgmGcd.v
rm gcd.dmp a.out
