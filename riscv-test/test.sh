#!/bin/bash

TEST_VCD_FILE="system.vcd"
FAIL_PC="b100 !"
TEST_PC=$(tail -n2 $TEST_VCD_FILE | head -n1)

if [ "$TEST_PC" = "$FAIL_PC" ]; then
    echo "Failed :("
    exit 1
fi

