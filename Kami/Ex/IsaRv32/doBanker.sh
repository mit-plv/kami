#!/bin/bash

ccomp -O1 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld banker0.c
riscv32-unknown-elf-objdump -d a.out > banker0.dmp
ccomp -O1 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld banker1.c
riscv32-unknown-elf-objdump -d a.out > banker1.dmp
ccomp -O1 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld banker2.c
riscv32-unknown-elf-objdump -d a.out > banker2.dmp
ccomp -O1 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld banker3.c
riscv32-unknown-elf-objdump -d a.out > banker3.dmp
./BinaryToKamiPgm.native banker0.dmp > Banker0.v
./BinaryToKamiPgm.native banker1.dmp > Banker1.v
./BinaryToKamiPgm.native banker2.dmp > Banker2.v
./BinaryToKamiPgm.native banker3.dmp > Banker3.v
rm a.out
