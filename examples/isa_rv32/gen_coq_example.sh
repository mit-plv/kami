#!/bin/bash

make
./BinaryToKamiPgm.native "$1" > ../IsaRv32PgmExt.v
