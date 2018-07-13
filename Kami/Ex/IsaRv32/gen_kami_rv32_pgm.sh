#!/bin/bash

if [ $# -lt 2 ]
then
  echo "Usage: $0 [input_disassembly] [output_filename]"
else
  make
  ./BinaryToKamiPgm.native "$1" > "$2"
fi
