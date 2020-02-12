#!/bin/bash

b2h()(echo "obase=16; ibase=2; $1" | bc)

TEST_OBJDUMP=$1
TEST_VCD_FILE=$2

SUCCESS_PC_HEX_0X=$(awk 'END{print toupper($4)}' $TEST_OBJDUMP)
SUCCESS_PC_HEX=$(echo ${SUCCESS_PC_HEX_0X/0X/})

TEST_PC_BIN_B=$(tail -n2 $TEST_VCD_FILE | head -n1 | awk '{print $1}')
TEST_PC_BIN=$(echo ${TEST_PC_BIN_B/b/})
TEST_PC_HEX=$(b2h $TEST_PC_BIN)

if [ "$TEST_PC_HEX" = "$SUCCESS_PC_HEX" ]; then
    printf "Test passed! %s %s\n" "$TEST_PC_HEX" "$SUCCESS_PC_HEX"
    exit 0
else
    printf "Test failed.. %s %s\n" "$TEST_PC_HEX" "$SUCCESS_PC_HEX"
    exit 1
fi
