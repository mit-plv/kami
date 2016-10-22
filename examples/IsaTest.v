Require Import Bool String List.
Require Import Lib.CommonTactics Lib.Word Lib.Struct.
Require Import Kami.Syntax.
Require Import Ex.MemTypes.
Require Import Ex.Isa.

Ltac init_pgm :=
  refine (ConstVector _);
  refine (VecNext
            (VecNext
               (VecNext
                  (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _)))
                  (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _))))
               (VecNext
                  (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _)))
                  (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _)))))
            (VecNext
               (VecNext
                  (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _)))
                  (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _))))
               (VecNext
                  (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _)))
                  (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _)))))).

Local Ltac line i c := exact (ConstBit (rv32iToRaw c)).
Local Ltac nop := exact (ConstBit (rv32iToRaw NOP)).
Local Notation "'Program'" := (ConstT (Vector (Data rv32iLgDataBytes) rv32iAddrSize)).

Definition branchTarget {sz} (ofs: nat) := natToWord sz (ofs * 4).

(* Expected output : 2 *)
Definition pgmJalTest1 : Program.
  init_pgm.
  line 0 (JAL x0 (branchTarget 5)).
  line 1 NOP.
  line 2 NOP.
  line 3 (LI x3 (natToWord _ 1)).
  line 4 (TOHOST x3).
  line 5 (LI x3 (natToWord _ 2)).
  line 6 (TOHOST x3).
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop.
Defined.

(* Expected output : 5 *)
Definition pgmJalTest2 : Program.
  init_pgm.
  line 0 (JAL x1 (branchTarget 5)).
  line 1 NOP.
  line 2 NOP.
  line 3 NOP.
  line 4 NOP.
  line 5 (TOHOST x1).
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop.
Defined.

(* Expected output : 2 *)
Definition pgmJalrTest1 : Program.
  init_pgm.
  line 0 (LI x1 (branchTarget 5)).
  line 1 (JALR x1 x0 (natToWord _ 0)).
  line 2 NOP.
  line 3 NOP.
  line 4 (LI x3 (natToWord _ 1)).
  line 5 (TOHOST x3).
  line 6 (LI x3 (natToWord _ 2)).
  line 7 (TOHOST x3).
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
Defined.

(* Expected output : 6 *)
Definition pgmJalrTest2 : Program.
  init_pgm.
  line 0 (LI x1 (branchTarget 5)).
  line 1 (JALR x1 x2 (natToWord _ 0)).
  line 2 NOP.
  line 3 NOP.
  line 4 NOP.
  line 5 NOP.
  line 6 (TOHOST x2).
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop.
Defined.

(* Expected output : 2 *)
Definition pgmBeqTest : Program.
  init_pgm.
  line 0 (LI x1 (natToWord _ 5)).
  line 1 (LI x2 (natToWord _ 5)).
  line 2 (BEQ x1 x2 (branchTarget 3)).
  line 3 (LI x3 (natToWord _ 1)).
  line 4 (TOHOST x3).
  line 5 (LI x3 (natToWord _ 2)).
  line 6 (TOHOST x3).
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop.
Defined.  

(* Expected output : 2 *)
Definition pgmBneTest : Program.
  init_pgm.
  line 0 (LI x1 (natToWord _ 4)).
  line 1 (LI x2 (natToWord _ 5)).
  line 2 (BNE x1 x2 (branchTarget 3)).
  line 3 (LI x3 (natToWord _ 1)).
  line 4 (TOHOST x3).
  line 5 (LI x3 (natToWord _ 2)).
  line 6 (TOHOST x3).
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop.
Defined.

(* Expected output : 2 *)
Definition pgmBltTest : Program.
  init_pgm.
  line 0 (LI x1 (natToWord _ 4)).
  line 1 (LI x2 (natToWord _ 5)).
  line 2 (BLT x1 x2 (branchTarget 3)).
  line 3 (LI x3 (natToWord _ 1)).
  line 4 (TOHOST x3).
  line 5 (LI x3 (natToWord _ 2)).
  line 6 (TOHOST x3).
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop.
Defined.

(* Expected output : 2 *)
Definition pgmBgeTest : Program.
  init_pgm.
  line 0 (LI x1 (natToWord _ 5)).
  line 1 (LI x2 (natToWord _ 4)).
  line 2 (BGE x1 x2 (branchTarget 3)).
  line 3 (LI x3 (natToWord _ 1)).
  line 4 (TOHOST x3).
  line 5 (LI x3 (natToWord _ 2)).
  line 6 (TOHOST x3).
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop.
Defined.

(* Expected output : 2 *)
Definition pgmLwSwTest1 : Program.
  init_pgm.
  line 0 (LI x3 (natToWord _ 2)).
  line 1 (SW x0 x3 (natToWord _ 0)).
  line 2 (LW x0 x5 (natToWord _ 0)).
  line 3 (TOHOST x5).
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop.
Defined.

(* Expected output : 2 *)
Definition pgmLwSwTest2: Program.
  init_pgm.
  line 0 (LI x3 (natToWord _ 1)).
  line 1 (LI x4 (natToWord _ 1)).
  line 2 (SW x0 x3 (natToWord _ 0)).
  line 3 (SW x0 x4 (natToWord _ 1)).
  line 4 (LW x0 x5 (natToWord _ 0)).
  line 5 (LW x0 x6 (natToWord _ 1)).
  line 6 (ADD x5 x6 x7).
  line 7 (TOHOST x7).
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
Defined.

(* Expected output : n *)
Definition pgmToHostTest (n: nat) : Program.
  init_pgm.
  line 0 (LI x3 (natToWord _ n)).
  line 1 (TOHOST x3).
  line 2 NOP.
  line 3 (J (branchTarget 30)). (* 3 + 30 == 1 *)
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop.
Defined.

(* Expected output : 2 *)
Definition pgmSubTest: Program.
  init_pgm.
  line 0 (LI x1 (natToWord _ 5)).
  line 1 (LI x2 (natToWord _ 5)).
  line 2 (SUB x1 x2 x3).
  line 3 (BEQ x3 x0 (branchTarget 3)).
  line 4 (LI x4 (natToWord _ 1)).
  line 5 (TOHOST x4).
  line 6 (LI x4 (natToWord _ 2)).
  line 7 (TOHOST x4).
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
Defined.

(* Expected output : 2 *)
Definition pgmSllTest: Program.
  init_pgm.
  line 0 (LI x1 (natToWord _ 3)).
  line 1 (LI x2 (natToWord _ 2)).
  line 2 (SLL x1 x2 x3). (* x3 = x1 << x2 *)
  line 3 (LI x4 (natToWord _ 12)). (* 12 = 3 << 2 *)
  line 4 (BEQ x3 x4 (branchTarget 3)).
  line 5 (LI x5 (natToWord _ 1)).
  line 6 (TOHOST x5).
  line 7 (LI x5 (natToWord _ 2)).
  line 8 (TOHOST x5).
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop.
Defined.

(* Expected output : 2 *)
Definition pgmSrlTest: Program.
  init_pgm.
  line 0 (LI x1 (natToWord _ 12)).
  line 1 (LI x2 (natToWord _ 2)).
  line 2 (SRL x1 x2 x3). (* x3 = x1 >> x2 *)
  line 3 (LI x4 (natToWord _ 3)). (* 3 = 12 >> 2 *)
  line 4 (BEQ x3 x4 (branchTarget 3)).
  line 5 (LI x5 (natToWord _ 1)).
  line 6 (TOHOST x5).
  line 7 (LI x5 (natToWord _ 2)).
  line 8 (TOHOST x5).
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop.
Defined.

(* Expected output : 2 *)
Definition pgmOrTest: Program.
  init_pgm.
  line 0 (LI x1 (natToWord _ 7)).
  line 1 (LI x2 (natToWord _ 56)).
  line 2 (OR x1 x2 x3).
  line 3 (LI x4 (natToWord _ 63)).
  line 4 (BEQ x3 x4 (branchTarget 3)).
  line 5 (LI x5 (natToWord _ 1)).
  line 6 (TOHOST x5).
  line 7 (LI x5 (natToWord _ 2)).
  line 8 (TOHOST x5).
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop.
Defined.

(* Expected output : 2 *)
Definition pgmAndTest: Program.
  init_pgm.
  line 0 (LI x1 (natToWord _ 7)).
  line 1 (LI x2 (natToWord _ 56)).
  line 2 (AND x1 x2 x3).
  line 3 (BEQ x3 x0 (branchTarget 3)).
  line 4 (LI x5 (natToWord _ 1)).
  line 5 (TOHOST x5).
  line 6 (LI x5 (natToWord _ 2)).
  line 7 (TOHOST x5).
  nop. nop. nop. nop. nop. nop. nop. nop.
  nop. nop. nop. nop. nop. nop. nop. nop.
  nop. nop. nop. nop. nop. nop. nop. nop.
Defined.

(* Expected output : 2 *)
Definition pgmXorTest: Program.
  init_pgm.
  line 0 (LI x1 (natToWord _ 37)). (* 100101 *)
  line 1 (LI x2 (natToWord _ 42)). (* 101010 *)
  line 2 (XOR x1 x2 x3).
  line 3 (LI x4 (natToWord _ 15)). (* 001111 *)
  line 4 (BEQ x3 x4 (branchTarget 3)).
  line 5 (LI x5 (natToWord _ 1)).
  line 6 (TOHOST x5).
  line 7 (LI x5 (natToWord _ 2)).
  line 8 (TOHOST x5).
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop.
Defined.

(* Expected output : Fib(n) *)
Definition pgmFibonacci (n: nat) : Program.
  init_pgm.
  line 0 (LI x21 (natToWord _ n)).
  line 1 (BLEZ x21 (natToWord _ 11)). (* to 12 *)
  line 2 (LI x9 (natToWord _ 1)).
  line 3 (MV x21 x6).
  line 4 (MV x9 x8).
  line 5 (MV x9 x7).
  line 6 (ADD x7 x8 x5).
  line 7 (ADDI x9 x9 (natToWord _ 1)).
  line 8 (MV x8 x7).
  line 9 (MV x5 x8).
  line 10 (BNE x6 x9 (branchTarget 28)). (* 10 + 28 == 6 *)
  line 11 (TOHOST x5).
  line 12 (J (natToWord _ 3)). (* to 15 *)
  line 13 (LI x5 (natToWord _ 1)).
  line 14 (J (branchTarget 29)). (* 14 + 29 == 11 *)
  line 15 NOP.
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop.
Defined.

(* Expected output : Gcd(n, m) *)
Definition pgmGcd (n m: nat) : Program.
  init_pgm.
  line 0 (LI x8 (natToWord _ n)).
  line 1 (LI x9 (natToWord _ m)).
  line 2 (MV x8 x4).
  line 3 (SUB x9 x8 x5).
  line 4 (SUB x8 x9 x6).
  line 5 (MV x9 x7).
  line 6 (BGE x8 x9 (branchTarget 2)).
  line 7 (MV x5 x7).
  line 8 (BLT x4 x9 (branchTarget 2)).
  line 9 (MV x6 x4).
  line 10 (MV x4 x8).
  line 11 (MV x7 x9).
  line 12 (BNE x4 x7 (natToWord _ 22)). (* 12 + 22 == 2 *)
  line 13 (TOHOST x4).
  nop. nop. nop. nop. nop. nop. nop. nop.
  nop. nop. nop. nop. nop. nop. nop. nop.
  nop. nop.
Defined.

(* Expected output : n! *)
Definition pgmFactorial (n: nat) : Program.
  init_pgm.
  line 0 (LI x4 (natToWord _ 1)).
  line 1 (MV x4 x9).
  line 2 (LI x8 (natToWord _ (S n))).
  line 3 (MUL x4 x9 x4).
  line 4 (ADDI x9 x9 (natToWord _ 1)).
  line 5 (BNE x9 x8 (branchTarget 30)). (* 5 + 30 == 3 *)
  line 6 (TOHOST x4).
  nop. nop. nop. nop. nop. nop. nop. nop.
  nop. nop. nop. nop. nop. nop. nop. nop.
  nop. nop. nop. nop. nop. nop. nop. nop.
  nop.
Defined.

