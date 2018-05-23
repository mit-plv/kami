#!/usr/bin/env python3

import sys

address = 0
labels = {}
registers = {"zero": "x0", "reserved1": "x1",}

def word(n, l):
    val = int(n)
    if val < 0:
        val += 2**l

    result = ""
    for i in range(l):
        result = "~" + str(val % 2) + result
        val = val // 2
    result = "WO" + result
    return result

def register(r):
    if r not in registers:
        registers[r] = "x" + str(len(registers))
    return registers[r]

def parseinst(inst):
    if inst == "call fromhost()":
        return ["FROMHOST {0}".format(register("a0"))]
    if inst == "call tohost(unsigned int)":
        return ["TOHOST {0}".format(register("a0"))]
    [op, args] = (inst.split() + [""])[:2]
    args = args.split(',')
    if op == "lw":
        rd = args[0]
        ofs = args[1].split('(')[0]
        rs1 = args[1].split('(')[1].strip(')')
        return ["LW {0} {1} {2}".format(register(rs1), register(rd), word(ofs, 12))]
    elif op == "sw":
        ofs = args[1].split('(')[0]
        rs1 = args[1].split('(')[1].strip(')')
        rs2 = args[0]
        return ["SW {0} {1} {2}".format(register(rs1), register(rs2), word(ofs, 12))]
    elif op == "addi":
        rd = args[0]
        rs1 = args[1]
        ofs = args[2]
        return ["ADDI {0} {1} {2}".format(register(rs1), register(rd), word(ofs, 12))]
    elif op == "mv":
        rd = args[0]
        rs1 = args[1]
        return ["MV {0} {1}".format(register(rs1), register(rd))]
    elif op == "li":
        rd = args[0]
        ofs = args[1]
        return ["LI {0} {1}".format(register(rd), word(ofs, 20))]
    elif op in ["andi", "slli", "srli"]:
        rd = args[0]
        rs1 = args[1]
        ofs = args[2]
        return ["LI {0} {1}".format(register("reserved1"), word(ofs, 20)),
                "{0} {1} {2} {3}".format(op[:-1].upper(), register(rs1), register("reserved1"), register(rd))]
    elif op in ["add", "sub", "and", "or", "xor", "sltu"]:
        rd = args[0]
        rs1 = args[1]
        rs2 = args[2]
        return ["{0} {1} {2} {3}".format(op.upper(), register(rs1), register(rs2), register(rd))]
    elif op == "bgt":
        return ["BGT unimplemented"]
    elif op == "bne":
        rs1 = args[0]
        rs2 = args[1]
        label = args[2]
        return ["BNE {0} {1} {2}".format(register(rs1), register(rs2), label)]
    elif op == "bnez":
        rs1 = args[0]
        label = args[1]
        return ["BNEZ {0} {1}".format(register(rs1), label)]
    elif op == "j":
        label = args[0]
        return ["J {0}".format(word((labels[label] - address)*2, 20))]
    elif op == "jr":
        rs1 = args[0]
        return ["JALR {0} x0 $0".format(register(rs1))]
    elif op == "call":
        label = inst.split(maxsplit=1)[1]
        return ["JALR x0 {0} {1}".format(register("ra"), word(labels[label]*4, 12))]
    elif op == "ret":
        return ["JALR {0} x0 $0".format(register("ra"))]
    elif op == "nop":
        return ["NOP"]
    else:
        print("unknown instruction {0}".format(inst))
        exit(1)

output = []

for line in sys.stdin.readlines():
    line = line.strip()
    if line.endswith(':'):
        labels[line.strip(':')] = address
        continue
    insts = parseinst(line)
    output += insts
    address += len(insts)

for i in range(len(output)):
    for label in labels:
        if label in output[i]:
            output[i] = output[i].replace(label, word((labels[label] - i)*2, 12))

print("[")
for i in range(len(output)):
    if i % 10 == 0:
        print("(* {0} *)".format(i))
    for label in labels:
        if i == labels[label]:
            print("(* {0} *)".format(label))
    print(output[i] + (";" if i < len(output) - 1 else ""))
print("]")
