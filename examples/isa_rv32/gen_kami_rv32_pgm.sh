#!/bin/bash

make
./BinaryToKamiPgm.native "$1" > "$2"
