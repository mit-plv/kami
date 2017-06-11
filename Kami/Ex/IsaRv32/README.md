- On this directory, you can generate Kami RV32I programs from actual C disassemblies (by objdump -d)

Requirement
-----------

- An output file by `objdump -d`, which makes an RV32 disassembly.

To build
--------

- `./gen_kami_rv32_pgm.sh [rv32_disassembly_filename] [output_filename.v]`
