#!/bin/bash
set -e

COMP=riscv32-unknown-elf-gcc
OBJDUMP=riscv32-unknown-elf-objdump

$COMP -D THREAD_IDX=0 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld matmul.c
$OBJDUMP -d a.out > matmul_init.dmp
$COMP -D THREAD_IDX=1 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld matmul.c
$OBJDUMP -d a.out > matmul_normal1.dmp
$COMP -D THREAD_IDX=2 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld matmul.c
$OBJDUMP -d a.out > matmul_normal2.dmp
$COMP -D THREAD_IDX=3 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld matmul.c
$OBJDUMP -d a.out > matmul_report.dmp
./BinaryToKamiPgm.native matmul_init.dmp > Matmul_init.v
./BinaryToKamiPgm.native matmul_normal1.dmp > Matmul_normal1.v
./BinaryToKamiPgm.native matmul_normal2.dmp > Matmul_normal2.v
./BinaryToKamiPgm.native matmul_report.dmp > Matmul_report.v
rm a.out
