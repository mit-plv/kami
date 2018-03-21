#!/bin/bash
set -e

COMP=riscv32-unknown-elf-gcc
OBJDUMP=riscv32-unknown-elf-objdump

$COMP -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld peterson1.c
$OBJDUMP -d a.out > peterson1.dmp
./BinaryToKamiPgm.native peterson1.dmp > PgmPeterson1.v
rm peterson1.dmp a.out
$COMP -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld peterson2.c
$OBJDUMP -d a.out > peterson2.dmp
./BinaryToKamiPgm.native peterson2.dmp > PgmPeterson2.v
rm peterson2.dmp a.out
