#!/bin/bash
set -e

COMP=riscv32-unknown-elf-gcc
OBJDUMP=riscv32-unknown-elf-objdump

$COMP -O1 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld banker0.c
$OBJDUMP -d a.out > banker0.dmp
$COMP -O1 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld banker1.c
$OBJDUMP -d a.out > banker1.dmp
$COMP -O1 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld banker2.c
$OBJDUMP -d a.out > banker2.dmp
$COMP -O1 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld banker3.c
$OBJDUMP -d a.out > banker3.dmp
./BinaryToKamiPgm.native banker0.dmp > Banker0.v
./BinaryToKamiPgm.native banker1.dmp > Banker1.v
./BinaryToKamiPgm.native banker2.dmp > Banker2.v
./BinaryToKamiPgm.native banker3.dmp > Banker3.v
rm a.out
