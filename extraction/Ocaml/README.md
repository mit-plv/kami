- On this directory, you can convert an extracted Kami program to the corresponding Bluespec program.

Requirement
-----------

- Target.ml, Target.mli: they are automatically generated from `extraction/Extraction.v`

To build
--------

- `make` generates an executable named `Main.native`
- `./Main.native [bluespec_filename.bsv]` generates the Bluespec program
