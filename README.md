Kami: A Coq Framework to Support Implementing and Verifying Bluespec-style Hardware Components
==============================================================================================

This repository contains the source code of Kami and the code for the multiprocessor case study.

Directory content:
- lib: Contains the generic library files that we developed for Kami, extending the standard Coq library, e.g. bit-vectors, decidable finite maps with strings as keys, etc
- src: Contains the source code for syntax, semantics, theorems/properties and proof automatation for Kami
- examples: Contains the multiprocessor implementation and proof of correctness. Contains both the 4-stage processor implementation and the coherent caches attached to a backing memory.
- extraction: Files needed to extract designs developed in Kami into Bluespec
  + BluespecFrontEnd: Contains the files to compile Kami modules in FPGAs
  + Ocaml: Contains the files to pretty-print the OCaml code extracted from Coq

Requirements
------------
To Verify Kami modules
----------------------
- Coq 8.5pl2

To Generate Bluespec Programs
-----------------------------
- OCaml 4.0.2.3
- Batteries Library for OCaml (2.5.2)

To Run Bluespec code (i.e. simulation)
--------------------------------------
- Bluespec 2014.07.A

To Run Bluespec code on FPGAs
-----------------------------
- Vivado 2015.4
- Xilinx Virtex-7 VC707 Evaluation Kit FPGA

To Compile C code to run on multiprocessor
------------------------------------------
- RISC-V gcc compiler 6.1.0

Instructions
------------

To Verify Multiprocessor system and extract OCaml ASTs 
------------------------------------------------------
- Run $ make in the top-level directory of Kami, i.e. the directory containing lib, src, examples and extraction directory, henceforth called $TOP.

To Generate Bluespec code from OCaml ASTs
-----------------------------------------
$ cd $TOP/extraction/Ocaml
$ make
$ ./Main.native -d Proc.bsv

This generates the file Proc.bsv, which is the Bluespec code representing the multiprocessor system with coherent caches.

To Simulate the Multiprocessor code in Bluespec (with already compiled benchmarks
---------------------------------------------------------------------------------
Once Proc.bsv is generated, do the following:

$ cp $TOP/extraction/Ocaml/Proc.bsv $TOP/extraction/BluespecFrontEnd/sim
$ cd $TOP/extraction/BluespecFrontEnd/sim
$ make
$ ./ProcSim

To Run the Multiprocessor code in Bluespec (with already compiled benchmarks
----------------------------------------------------------------------------
Once Proc.bsv is generated, do the following:

$ cp $TOP/extraction/Ocaml/Proc.bsv $TOP/extraction/BluespecFrontEnd/fpgaConnectal
$ cd $TOP/extraction/BluespecFrontEnd/fpgaConnectal
$ make

To change the benchmark being compiled
--------------------------------------
Multithreaded benchmarks can be run on 2 cores by modifying the program bein
executed in line 57. For instance, replacing IsaRv32PgmDekker1 and
IsaRv32PgmDekker2 in line 57 in $TOP/extraction/Extraction.v to
onIsaRv32PgmPeterson1 and IsaRv32PgmPeterson2, respectively, will run the
2-core version of Peterson's algorithm for incrementing counter.

In order to run the single-threaded programs, Extraction.v file has to be
changed considerably. First, line 21 denotes lg of the number of cores. That
should be changed to 0 for single-threaded programs. Then, the list in line 57
should contain just one element among the following:
IsaRv32PgmGcd, IsaRv32PgmFact, IsaRv32PgmBsort or IsaRv32PgmHanoi.

Then redo all the instructions from the beginning to execute the new benchmark.

To add a new benchmark
----------------------
$ cd $TOP/example/isa_rv32

Here are the steps following that:
1) Write the C code that you want to compile into Kami (1 program for each core).
2) Compile the C code (say test.c) into an assembly code using the RISC-V gcc
compiler as follows (assuming risc-v GCC is in your path)
:
$ riscv32-unknown-elf-gcc -O1 -nostartfiles -nodefaultlibs -nostdlib -static -S -T config.ld test.c
$ riscv32-unknown-elf-gcc -O1 -nostartfiles -nodefaultlibs -nostdlib -static -s -T config.ld test.c
$ riscv32-unknown-elf-objdump -d a.out > test.objdump
$ ./gen_kami_rv32_pgm.sh test.objdump IsaTest.v

Now add IsaTest.v to $TOP/IsaRv32PgmExt.v

This adds a new benchmark IsaTest.v. Redo all the steps from the beginning to execute this.


