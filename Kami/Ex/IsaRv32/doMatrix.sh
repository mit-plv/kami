#!/bin/bash

ccomp -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld matmul_init.c
riscv32-unknown-elf-objdump -d a.out > matmul_init.dmp
ccomp -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld matmul_normal1.c
riscv32-unknown-elf-objdump -d a.out > matmul_normal1.dmp
ccomp -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld matmul_normal2.c
riscv32-unknown-elf-objdump -d a.out > matmul_normal2.dmp
ccomp -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld matmul_report.c
riscv32-unknown-elf-objdump -d a.out > matmul_report.dmp
./BinaryToKamiPgm.native matmul_init.dmp > Matmul_init.v
./BinaryToKamiPgm.native matmul_normal1.dmp > Matmul_normal1.v
./BinaryToKamiPgm.native matmul_normal2.dmp > Matmul_normal2.v
./BinaryToKamiPgm.native matmul_report.dmp > Matmul_report.v
rm a.out
