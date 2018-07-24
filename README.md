Kami: A Coq Framework to Support Implementing and Verifying Bluespec-style Hardware Components
==============================================================================================

This repository (the "coq-8.8" branch) contains the source code of Kami.

DeepSpec Summer School 2018 lecture roadmap
-------------------------------------------

We won't get nearly through all the content of this library.
However, there are source files associated with each lecture.
They are created jointly by Joonwon Choi and Adam Chlipala, and each appears in the subdirectory `Kami/Ex`.

- Day 1: brief intro to the hardware state of mind; embedding a programming language inside of Coq
  + `ExpressionsTutorial.v`: different ways to implement an adder, leading up to generating combinational circuits in Kami
  + *Homework*: `PhoasExercise.v`, a verified static analysis that bounds how large of a value a circuit might compute
- Day 2: modular proofs of interacting components
  + `LtsTutorial.v`: introducing labeled transition systems
  + `InDepthTutorial.v`: a producer-consumer example in Kami, introducing stateful circuits
  + *Homework*: `LtsExercise.v`, proving some more refinement facts for the language from `LtsTutorial`
- Day 3: verifying computer processors
  + `ProcMemSpec.v`: the first of several files of code, specifications, and proofs for a pipelined processor; see the comment near the start for the roadmap within this case study
  + *Homework*: `CacheExercise.v`, proving correctness of memory systems with single-address caches

Directory content
-----------------

- ./: Contains the source code for syntax, semantics, theorems/properties and
  proof automation for Kami.
- Lib: Contains the generic library files that we developed for Kami, extending
  the standard Coq library, e.g. bit-vectors, decidable finite maps with strings
  as keys, etc.
- Ex: Contains basic examples and tutorials.
- Ext: Files needed to extract designs developed in Kami into Bluespec
  + BluespecFrontEnd
    * fpga-connectal: Contains the files to compile Kami modules in FPGAs.
    * sim: Contains the files to simulate Kami modules on the Bluespec simulator.
  + Ocaml: Contains the files to pretty-print the OCaml code extracted from Coq.

Requirements
------------

### To Verify Kami modules
- Coq 8.8.0 (with $PATH containing the standard Coq binaries)

### To Generate Bluespec programs
- OCaml 4.0.4 (with $PATH containing the standard OCaml binaries)
- Batteries Library for OCaml (2.5.2)

### To Run Bluespec code (i.e. simulation)
- Bluespec 2014.07.A (with $PATH containing the Bluespec binaries and
  $LM\_LICENSE\_FILE contains Bluespec license)

### To Run Bluespec code on FPGAs
- Vivado 2015.4 (with $PATH containing the Bluespec binaries and
  $LM\_LICENSE\_FILE contains Bluespec license)
- Xilinx Virtex-7 VC707 Evaluation Kit FPGA

