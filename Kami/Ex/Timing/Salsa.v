Require Import List.
Require Import Notations.
Require Import Lib.Word.
Require Import Kami.Ex.Timing.Specification Kami.Ex.Timing.AbstractTaint Kami.Ex.Timing.SCSingle.
Require Import Kami.Ex.IsaRv32.
Require Import Kami.Syntax.
Require Import Logic.FunctionalExtensionality.

Definition salsa :=
[
(* 0 *)
(* quarter(unsigned int*, unsigned int*, unsigned int*, unsigned int* ) *)
LW x2 x3 WO~0~0~0~0~0~0~0~0~0~0~0~0;
LW x4 x5 WO~0~0~0~0~0~0~0~0~0~0~0~0;
ADD x5 x3 x5;
LI x1 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1;
SLL x5 x1 x3;
LI x1 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~0~1;
SRL x5 x1 x5;
OR x3 x5 x3;
LW x6 x5 WO~0~0~0~0~0~0~0~0~0~0~0~0;
XOR x3 x5 x3;
(* 10 *)
SW x6 x3 WO~0~0~0~0~0~0~0~0~0~0~0~0;
LW x2 x5 WO~0~0~0~0~0~0~0~0~0~0~0~0;
ADD x3 x5 x3;
LI x1 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~1;
SLL x3 x1 x5;
LI x1 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~1~1~1;
SRL x3 x1 x3;
OR x5 x3 x5;
LW x7 x3 WO~0~0~0~0~0~0~0~0~0~0~0~0;
XOR x5 x3 x5;
(* 20 *)
SW x7 x5 WO~0~0~0~0~0~0~0~0~0~0~0~0;
LW x6 x3 WO~0~0~0~0~0~0~0~0~0~0~0~0;
ADD x5 x3 x5;
LI x1 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~1;
SLL x5 x1 x3;
LI x1 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~1~1;
SRL x5 x1 x5;
OR x3 x5 x3;
LW x4 x5 WO~0~0~0~0~0~0~0~0~0~0~0~0;
XOR x3 x5 x3;
(* 30 *)
SW x4 x3 WO~0~0~0~0~0~0~0~0~0~0~0~0;
LW x7 x5 WO~0~0~0~0~0~0~0~0~0~0~0~0;
ADD x3 x5 x3;
LI x1 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~0;
SRL x3 x1 x5;
LI x1 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~1~0;
SLL x3 x1 x3;
OR x5 x3 x5;
LW x2 x3 WO~0~0~0~0~0~0~0~0~0~0~0~0;
XOR x3 x5 x3;
(* 40 *)
SW x2 x3 WO~0~0~0~0~0~0~0~0~0~0~0~0;
JALR x8 x0 $0;
(* salsa20_words(unsigned int*, unsigned int* ) *)
ADDI x9 x9 WO~1~1~1~1~1~0~1~1~0~0~0~0;
SW x9 x10 WO~0~0~0~0~0~1~0~0~1~0~0~0;
SW x9 x11 WO~0~0~0~0~0~1~0~0~0~1~0~0;
SW x9 x8 WO~0~0~0~0~0~1~0~0~1~1~0~0;
SW x9 x12 WO~0~0~0~0~0~1~0~0~0~0~0~0;
MV x2 x10;
MV x6 x11;
MV x6 x5;
(* 50 *)
LI x3 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0;
LI x7 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0;
(* .L3 *)
LI x1 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0;
SLL x3 x1 x4;
ADDI x9 x6 WO~0~0~0~0~0~1~0~0~0~0~0~0;
ADD x6 x4 x4;
LW x5 x6 WO~0~0~0~0~0~0~0~0~0~0~0~0;
ADDI x3 x3 WO~0~0~0~0~0~0~0~0~0~0~0~1;
ADDI x5 x5 WO~0~0~0~0~0~0~0~0~0~1~0~0;
SW x4 x6 WO~1~1~1~1~1~1~0~0~0~0~0~0;
(* 60 *)
BNE x3 x7 WO~1~1~1~1~1~1~1~1~0~0~0~0;
LI x12 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~1~0;
(* .L4 *)
ADDI x9 x4 WO~0~0~0~0~0~0~1~1~0~0~0~0;
ADDI x9 x7 WO~0~0~0~0~0~0~1~0~0~0~0~0;
ADDI x9 x6 WO~0~0~0~0~0~0~0~1~0~0~0~0;
MV x9 x2;
JALR x0 x8 WO~0~0~0~0~0~0~0~0~0~0~0~0;
ADDI x9 x4 WO~0~0~0~0~0~0~0~0~0~1~0~0;
ADDI x9 x7 WO~0~0~0~0~0~0~1~1~0~1~0~0;
ADDI x9 x6 WO~0~0~0~0~0~0~1~0~0~1~0~0;
(* 70 *)
ADDI x9 x2 WO~0~0~0~0~0~0~0~1~0~1~0~0;
JALR x0 x8 WO~0~0~0~0~0~0~0~0~0~0~0~0;
ADDI x9 x4 WO~0~0~0~0~0~0~0~1~1~0~0~0;
ADDI x9 x7 WO~0~0~0~0~0~0~0~0~1~0~0~0;
ADDI x9 x6 WO~0~0~0~0~0~0~1~1~1~0~0~0;
ADDI x9 x2 WO~0~0~0~0~0~0~1~0~1~0~0~0;
JALR x0 x8 WO~0~0~0~0~0~0~0~0~0~0~0~0;
ADDI x9 x4 WO~0~0~0~0~0~0~1~0~1~1~0~0;
ADDI x9 x7 WO~0~0~0~0~0~0~0~1~1~1~0~0;
ADDI x9 x6 WO~0~0~0~0~0~0~0~0~1~1~0~0;
(* 80 *)
ADDI x9 x2 WO~0~0~0~0~0~0~1~1~1~1~0~0;
JALR x0 x8 WO~0~0~0~0~0~0~0~0~0~0~0~0;
ADDI x9 x4 WO~0~0~0~0~0~0~0~0~1~1~0~0;
ADDI x9 x7 WO~0~0~0~0~0~0~0~0~1~0~0~0;
ADDI x9 x6 WO~0~0~0~0~0~0~0~0~0~1~0~0;
MV x9 x2;
JALR x0 x8 WO~0~0~0~0~0~0~0~0~0~0~0~0;
ADDI x9 x4 WO~0~0~0~0~0~0~0~1~0~0~0~0;
ADDI x9 x7 WO~0~0~0~0~0~0~0~1~1~1~0~0;
ADDI x9 x6 WO~0~0~0~0~0~0~0~1~1~0~0~0;
(* 90 *)
ADDI x9 x2 WO~0~0~0~0~0~0~0~1~0~1~0~0;
JALR x0 x8 WO~0~0~0~0~0~0~0~0~0~0~0~0;
ADDI x9 x4 WO~0~0~0~0~0~0~1~0~0~1~0~0;
ADDI x9 x7 WO~0~0~0~0~0~0~1~0~0~0~0~0;
ADDI x9 x6 WO~0~0~0~0~0~0~1~0~1~1~0~0;
ADDI x9 x2 WO~0~0~0~0~0~0~1~0~1~0~0~0;
JALR x0 x8 WO~0~0~0~0~0~0~0~0~0~0~0~0;
ADDI x9 x4 WO~0~0~0~0~0~0~1~1~1~0~0~0;
ADDI x9 x7 WO~0~0~0~0~0~0~1~1~0~1~0~0;
ADDI x9 x6 WO~0~0~0~0~0~0~1~1~0~0~0~0;
(* 100 *)
ADDI x9 x2 WO~0~0~0~0~0~0~1~1~1~1~0~0;
ADDI x12 x12 WO~1~1~1~1~1~1~1~1~1~1~1~1;
JALR x0 x8 WO~0~0~0~0~0~0~0~0~0~0~0~0;
BNEZ x12 WO~1~1~1~1~1~0~1~0~1~1~1~0;
MV x10 x2;
LI x3 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0;
LI x4 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0;
(* .L5 *)
LI x1 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0;
SLL x3 x1 x5;
ADDI x9 x7 WO~0~0~0~0~0~1~0~0~0~0~0~0;
(* 110 *)
ADD x7 x5 x5;
LW x5 x5 WO~1~1~1~1~1~1~0~0~0~0~0~0;
LW x11 x7 WO~0~0~0~0~0~0~0~0~0~0~0~0;
ADDI x3 x3 WO~0~0~0~0~0~0~0~0~0~0~0~1;
ADDI x11 x11 WO~0~0~0~0~0~0~0~0~0~1~0~0;
ADD x5 x7 x5;
SW x2 x5 WO~0~0~0~0~0~0~0~0~0~0~0~0;
ADDI x2 x2 WO~0~0~0~0~0~0~0~0~0~1~0~0;
BNE x3 x4 WO~1~1~1~1~1~1~1~0~1~0~1~0;
LW x9 x8 WO~0~0~0~0~0~1~0~0~1~1~0~0;
(* 120 *)
LW x9 x10 WO~0~0~0~0~0~1~0~0~1~0~0~0;
LW x9 x11 WO~0~0~0~0~0~1~0~0~0~1~0~0;
LW x9 x12 WO~0~0~0~0~0~1~0~0~0~0~0~0;
ADDI x9 x9 WO~0~0~0~0~0~1~0~1~0~0~0~0;
JALR x8 x0 $0;
(* salsa20_block(unsigned int*, unsigned int*, unsigned long long, unsigned long long) *)
LI x13 WO~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0;
ADDI x9 x9 WO~1~1~1~1~1~0~1~1~0~0~0~0;
ADDI x13 x13 WO~1~0~0~0~0~1~1~0~0~1~0~1;
SW x9 x13 WO~0~0~0~0~0~0~0~0~0~0~0~0;
LI x13 WO~0~0~0~0~0~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0;
(* 130 *)
ADDI x13 x13 WO~0~1~0~0~0~1~1~0~1~1~1~0;
SW x9 x13 WO~0~0~0~0~0~0~0~1~0~1~0~0;
LI x13 WO~0~0~1~0~0~0~1~1~0~0~0~0~0~0~0~0~0~0~0~0;
ADDI x13 x13 WO~1~1~0~1~0~0~1~1~0~0~1~0;
SW x9 x13 WO~0~0~0~0~0~0~1~0~1~0~0~0;
LI x13 WO~0~0~0~0~0~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0;
ADDI x13 x13 WO~0~1~0~1~0~1~1~1~0~1~0~0;
SW x9 x13 WO~0~0~0~0~0~0~1~1~1~1~0~0;
SW x9 x3 WO~0~0~0~0~0~0~1~0~0~1~0~0;
LW x6 x13 WO~0~0~0~0~0~0~0~0~0~0~0~0;
(* 140 *)
LW x6 x3 WO~0~0~0~0~0~0~0~1~0~0~0~0;
SW x9 x8 WO~0~0~0~0~0~1~0~0~1~1~0~0;
SW x9 x13 WO~0~0~0~0~0~0~0~0~0~1~0~0;
SW x9 x3 WO~0~0~0~0~0~0~1~0~1~1~0~0;
LW x6 x13 WO~0~0~0~0~0~0~0~0~0~1~0~0;
LW x6 x3 WO~0~0~0~0~0~0~0~1~0~1~0~0;
SW x9 x7 WO~0~0~0~0~0~0~0~1~1~0~0~0;
SW x9 x13 WO~0~0~0~0~0~0~0~0~1~0~0~0;
SW x9 x3 WO~0~0~0~0~0~0~1~1~0~0~0~0;
LW x6 x13 WO~0~0~0~0~0~0~0~0~1~0~0~0;
(* 150 *)
LW x6 x3 WO~0~0~0~0~0~0~0~1~1~0~0~0;
SW x9 x4 WO~0~0~0~0~0~0~0~1~1~1~0~0;
SW x9 x13 WO~0~0~0~0~0~0~0~0~1~1~0~0;
SW x9 x3 WO~0~0~0~0~0~0~1~1~0~1~0~0;
LW x6 x13 WO~0~0~0~0~0~0~0~0~1~1~0~0;
LW x6 x3 WO~0~0~0~0~0~0~0~1~1~1~0~0;
MV x9 x6;
SW x9 x13 WO~0~0~0~0~0~0~0~1~0~0~0~0;
SW x9 x5 WO~0~0~0~0~0~0~1~0~0~0~0~0;
SW x9 x3 WO~0~0~0~0~0~0~1~1~1~0~0~0;
(* 160 *)
JALR x0 x8 WO~0~0~0~0~1~0~1~0~1~0~0~0;
LW x9 x8 WO~0~0~0~0~0~1~0~0~1~1~0~0;
ADDI x9 x9 WO~0~0~0~0~0~1~0~1~0~0~0~0;
JALR x8 x0 $0;
(* salsa20(unsigned long long) *)
ADDI x9 x9 WO~1~1~1~1~0~1~1~1~0~0~0~0;
SW x9 x10 WO~0~0~0~0~1~0~0~0~1~0~0~0;
MV x9 x10;
SW x9 x11 WO~0~0~0~0~1~0~0~0~0~1~0~0;
SW x9 x12 WO~0~0~0~0~1~0~0~0~0~0~0~0;
SW x9 x14 WO~0~0~0~0~0~1~1~1~1~0~0~0;
(* 170 *)
SW x9 x15 WO~0~0~0~0~0~1~1~1~0~1~0~0;
SW x9 x16 WO~0~0~0~0~0~1~1~0~1~1~0~0;
SW x9 x8 WO~0~0~0~0~1~0~0~0~1~1~0~0;
SW x9 x17 WO~0~0~0~0~0~1~1~1~1~1~0~0;
SW x9 x18 WO~0~0~0~0~0~1~1~1~0~0~0~0;
MV x2 x14;
MV x6 x15;
LI x11 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0;
MV x10 x16;
LI x12 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0;
(* 180 *)
(* .L13 *)
FROMHOST x2;
SW x10 x2 WO~0~0~0~0~0~0~0~0~0~0~0~0;
ADDI x11 x11 WO~0~0~0~0~0~0~0~0~0~0~0~1;
ADDI x10 x10 WO~0~0~0~0~0~0~0~0~0~1~0~0;
BNE x11 x12 WO~1~1~1~1~1~1~1~1~1~0~0~0;
LI x10 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0;
LI x11 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0;
LI x18 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0;
(* .L15 *)
MV x10 x5;
MV x11 x3;
(* 190 *)
MV x14 x7;
MV x15 x4;
MV x16 x6;
ADDI x9 x2 WO~0~0~0~0~0~0~1~0~0~0~0~0;
JALR x0 x8 WO~0~0~0~1~1~1~1~1~0~1~0~0;
ADDI x9 x17 WO~0~0~0~0~0~0~1~0~0~0~0~0;
LI x12 WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0;
(* .L14 *)
FROMHOST x2;
LW x17 x3 WO~0~0~0~0~0~0~0~0~0~0~0~0;
ADDI x12 x12 WO~0~0~0~0~0~0~0~0~0~0~0~1;
(* 200 *)
ADDI x17 x17 WO~0~0~0~0~0~0~0~0~0~1~0~0;
XOR x2 x3 x2;
TOHOST x2;
BNE x12 x18 WO~1~1~1~1~1~1~1~1~0~1~0~0;
ADDI x10 x3 WO~0~0~0~0~0~0~0~0~0~0~0~1;
SLTU x3 x10 x5;
ADD x5 x11 x11;
MV x3 x10;
J WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~0~0
].

Definition initpc : address := $(164*4). (* address of salsa20() *)
Definition initmem : pseudoMemory := (fun _ => None).
Definition initrf : pseudoRegfile := (fun r =>
                                        if weqb r $0 (* x0 is always 0 *)
                                        then Some $0
                                        else if weqb r $9 (* x9 is our stack pointer *)
                                             then Some $1024
                                             else None).
Definition pm (code : list Rv32i) : progMem := fun a => rv32iToRaw (nth (wordToNat a) code NOP).

Definition looprf : pseudoRegfile := (fun r =>
                                        if weqb r $0 then Some $0
                                        else if weqb r $9
                                             then Some WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~1~1~1~0~0~0~0
                                             else if weqb r $16
                                                  then Some WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~1~1~1~0~0~0~0
                                                  else if weqb r $18
                                                       then Some $16
                                                       else None).
Definition looppc : address := $(188*4).
Definition loopmem : pseudoMemory := fun _ => None.

Definition concreterf := mask initrf (fun _ => $0).
Definition concretemem := mask initmem (fun _ => $0).

Theorem salsaAbstractHiding : abstractHiding concreterf (pm salsa) initpc concretemem.
  unfold concreterf, concretemem.
  apply abstractHiding_tainted_normal.
  apply (segmentSafeHiding 100 _ _ _ _ looprf looppc loopmem).
  - reflexivity.
  - apply (loopSafeHiding 5000).
    reflexivity.
Qed.

Theorem salsaKamiHiding :
  kamiHiding SCSingle.fhMeth SCSingle.thMeth (SCSingle.p ++ SCSingle.m)%kami (FMap.M.union (SCProcRegs initrf (pm salsa) initpc) (SCMemRegs initmem)).
Proof.
  apply SCSingleHiding.abstractToSCHiding.
  apply salsaAbstractHiding.
Qed.