#!/bin/bash
set -e

COMP=riscv32-unknown-elf-gcc
OBJDUMP=riscv32-unknown-elf-objdump

$COMP -O1 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld banker0.c
$OBJDUMP -d a.out > banker_init.dmp
$COMP -O1 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld banker1.c
$OBJDUMP -d a.out > banker_worker1.dmp
$COMP -O1 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld banker2.c
$OBJDUMP -d a.out > banker_worker2.dmp
$COMP -O1 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld banker3.c
$OBJDUMP -d a.out > banker_worker3.dmp
./BinaryToKamiPgm.native banker_init.dmp > PgmBankerInit.v
./BinaryToKamiPgm.native banker_worker1.dmp > PgmBankerWorker1.v
./BinaryToKamiPgm.native banker_worker2.dmp > PgmBankerWorker2.v
./BinaryToKamiPgm.native banker_worker3.dmp > PgmBankerWorker3.v
rm a.out
