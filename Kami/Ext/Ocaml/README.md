- On this directory, you can convert an extracted Kami program to the corresponding Bluespec program.

Requirement
-----------

- Target.ml, Target.mli: they are automatically generated from `Kami/Ext/Extraction.v`

To build
--------

- `make` generates an executable named `Main.native`
- `./Main.native -header Header.bsv [bluespec_filename.bsv]` generates the Bluespec program.
