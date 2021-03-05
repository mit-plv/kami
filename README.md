Kami: A Platform for High-Level Parametric Hardware Specification and Its Modular Verification
==============================================================================================

Directory content
-----------------

- `./`: Contains the source code for syntax, semantics, theorems/properties and
  proof automation for Kami.
- `Lib`: Contains the generic library files that we developed for Kami, extending
  the standard Coq library, e.g. bit-vectors, decidable finite maps with strings
  as keys, etc.
- `Ex`: Contains basic examples and tutorials.
- `Ext`: Files needed to extract designs developed in Kami into Bluespec
  + `Ocaml`: Contains the files to pretty-print the OCaml code extracted from Coq.

The `rv32i_artifact` branch
---------------------------

This branch (`rv32i_artifact`) additionally contains the Kami RV32I processor
implementation and provides extraction/compilation of it to the Verilog code.

- `Ex` contains the processor implementation.
- `Ext/BluespecFrontEnd/verilog` contains Bluespec files and `Makefile` to
  compile the Kami processor to the Verilog code.
  + `Ext/BluespecFrontEnd/verilog/prebuilt` already contains precompiled Verilog
    processor code (compiled with the Bluespec compiler build 88d4eef).

Makefiles
---------

- To machine-check the Coq proofs in Kami
  + Check all the Coq files, including all the examples: `make coq` (or just `make`)
  + Check only the library code: `make src`
- (Only in this branch) To extract/compile the Kami processor
  + `make proc_ext`
  + If the build succeeds, the Verilog code will be located in
    `Ext/BluespecFrontEnd/verilog/build`.

Requirements
------------

### To machine-check the Coq proofs in Kami
- Coq 8.12.x with `$PATH` containing the standard Coq binaries

### To extract the Kami processor into Bluespec
- OCaml 4.0.4 (with `$PATH` containing the standard OCaml binaries)
- Batteries Library for OCaml (2.5.2)

### To compile Bluespec code to Verilog
- Bluespec 2014.07.A or the open-source version from https://github.com/B-Lang-org/bsc
  + With `$PATH` containing the Bluespec binaries including `bsc`
  + A directory containing `bsc` and the one containing the Bluespec Verilog
    library should be in the same parent directory.
