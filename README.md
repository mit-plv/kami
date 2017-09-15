Kami: A Coq Framework to Support Implementing and Verifying Bluespec-style Hardware Components
==============================================================================================

This repository contains the source code of Kami and the code for the multiprocessor case study.

Directory content
-----------------

- lib: Contains the generic library files that we developed for Kami, extending the standard Coq library, e.g. bit-vectors, decidable finite maps with strings as keys, etc.
- src: Contains the source code for syntax, semantics, theorems/properties and proof automation for Kami.
- examples: Contains the multiprocessor implementation and proof of correctness. Contains both the 4-stage processor implementation and the coherent caches attached to a backing memory.
- extraction: Files needed to extract designs developed in Kami into Bluespec
  + BluespecFrontEnd
    * fpga-connectal: Contains the files to compile Kami modules in FPGAs.
    * sim: Contains the files to simulate Kami modules on the Bluespec simulator.
  + Ocaml: Contains the files to pretty-print the OCaml code extracted from Coq.

Requirements
------------

### To Verify Kami modules
- Coq 8.6.1 (with $PATH containing the standard Coq binaries)

### To Generate Bluespec programs
- OCaml 4.0.4 (with $PATH containing the standard OCaml binaries)
- Batteries Library for OCaml (2.5.2)

### To Run Bluespec code (i.e. simulation)
- Bluespec 2014.07.A (with $PATH containing the Bluespec binaries and $LM\_LICENSE\_FILE contains Bluespec license)

### To Run Bluespec code on FPGAs
- Vivado 2015.4 (with $PATH containing the Bluespec binaries and $LM\_LICENSE\_FILE contains Bluespec license)
- Xilinx Virtex-7 VC707 Evaluation Kit FPGA

### To Compile C code to run on multiprocessor
- RISC-V gcc compiler 6.1.0

Instructions
------------

### To Verify Multiprocessor system and extract OCaml ASTs
- Run $ make in the top-level directory of Kami, i.e. the directory containing the Kami directory, henceforth called $TOP.

### To Generate Bluespec code from OCaml ASTs
```
$ cd $TOP/Kami/Ext/Ocaml
$ make
$ ./Main.native Proc.bsv
```

This generates the file Proc.bsv, which is the Bluespec code representing the multiprocessor system with coherent caches.

### To Simulate the Multiprocessor code in Bluespec (with already compiled benchmarks)
Once Proc.bsv is generated, do the following:

```
$ cp $TOP/Kami/Ext/Ocaml/Proc.bsv $TOP/Kami/Ext/BluespecFrontEnd/sim
$ cd $TOP/Kami/Ext/BluespecFrontEnd/sim
$ make
$ ./ProcSim
```

### To Run the Multiprocessor code in Bluespec (with already compiled benchmarks)
Once Proc.bsv is generated, do the following:

```
$ cp $TOP/Kami/Ext/Ocaml/Proc.bsv $TOP/Kami/Ext/BluespecFrontEnd/fpgaConnectal
$ cd $TOP/Kami/Ext/BluespecFrontEnd/fpgaConnectal
$ make build.vc707g2
```

### To change the benchmark being compiled
Multithreaded benchmarks can be run on 4 cores by modifying the program being
executed in line 57. For instance, replacing _IsaRv32.PgmMatMul1_, _IsaRv32.PgmMatMul2_, etc. in line 57
in $TOP/Kami/Ext/Extraction.v to _IsaRv32.PgmBanker1_, _IsaRv32.PgmBanker2_, etc. respectively, will run the
4-core version of the Banker example.

See the list of benchmarks (directly converted from C code), which are shown in $TOP/Ex/IsaRv32PgmExt.v.

Redo all the steps from the beginning to build and run the new Benchmark.

### To add a new benchmark
`$ cd $TOP/example/isa_rv32`

Here are the steps following that:
1) Write the C code that you want to compile into Kami (one program for each core).
2) Compile the C code (say test.c) into an assembly code using the RISC-V gcc
compiler as follows (assuming risc-v GCC is in your path):
```
$ riscv32-unknown-elf-gcc -O1 -nostartfiles -nodefaultlibs -nostdlib -static -S -T config.ld test.c
$ riscv32-unknown-elf-gcc -O1 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld test.c
$ riscv32-unknown-elf-objdump -d a.out > test.objdump
$ ./gen_kami_rv32_pgm.sh test.objdump IsaTest.v
```

Now add IsaTest.v to $TOP/Ex/IsaRv32PgmExt.v

This adds a new benchmark IsaTest.v. Redo all the steps from the beginning to build and run the new Benchmark.
