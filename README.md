Kami: A Platform for High-Level Parametric Hardware Specification and Its Modular Verification
==============================================================================================

Directory content
-----------------

- ./: Contains the source code for syntax, semantics, theorems/properties and
  proof automation for Kami.
- Lib: Contains the generic library files that we developed for Kami, extending
  the standard Coq library, e.g. bit-vectors, decidable finite maps with strings
  as keys, etc.
- Ex: Contains basic examples and tutorials.
- Ext: Files needed to extract designs developed in Kami into Bluespec
  + Ocaml: Contains the files to pretty-print the OCaml code extracted from Coq.

Requirements
------------

### To Verify Kami modules
- Coq 8.12.x with `$PATH` containing the standard Coq binaries

### To Generate Bluespec programs
- OCaml 4.0.4 (with `$PATH` containing the standard OCaml binaries)
- Batteries Library for OCaml (2.5.2)

### To Run Bluespec code (i.e. simulation)
- Bluespec 2014.07.A or the open-source version from https://github.com/B-Lang-org/bsc (with `$PATH` containing the Bluespec binaries)

### To Run Bluespec code on FPGAs
- Vivado 2015.4 (with `$PATH` containing the Bluespec binaries)
- Xilinx Virtex-7 VC707 Evaluation Kit FPGA
