Kami: A Coq Framework to Support Implementing and Verifying Bluespec-style Hardware Components
==============================================================================================

This repository (the "master" branch) contains the source code of Kami.

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
- Coq 8.8.x (x=[0|1|2], with $PATH containing the standard Coq binaries)

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

