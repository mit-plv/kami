Require Import Bool String List.
Require Import Lib.CommonTactics Lib.Word Lib.Struct.
Require Import Kami.Syntax.
Require Import Ex.MemTypes.
Require Import Ex.IsaRv32.

Ltac init_pgm :=
  refine (ConstVector _);
  refine
    (VecNext
       (VecNext
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
                (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _))))))
       (VecNext
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
                (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _))))))).

Local Ltac line i c := exact (ConstBit (rv32iToRaw c)).
Local Ltac nop := exact (ConstBit (rv32iToRaw NOP)).
Notation "'Rv32Program'" := (ConstT (Vector (Data rv32iDataBytes) rv32iIAddrSize)).

(* The final address should be obtained by multiplying two by processor, 
 * according to RV32I specification. *)
Definition branchTarget {sz} (ofs: nat) := natToWord sz (ofs * 2).

Section TestPgms.

  (* Expected output : 2 *)
  Definition pgmJalTest1 : Rv32Program.
    init_pgm.
    line 0 (JAL x0 (branchTarget 5)).
    line 1 NOP.
    line 2 NOP.
    line 3 (LI x13 (natToWord _ 1)).
    line 4 (TOHOST x13).
    line 5 (LI x13 (natToWord _ 2)).
    line 6 (TOHOST x13).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop.
  Defined.

  (* Expected output : 5 *)
  Definition pgmJalTest2 : Rv32Program.
    init_pgm.
    line 0 (JAL x11 (branchTarget 5)).
    line 1 NOP.
    line 2 NOP.
    line 3 NOP.
    line 4 NOP.
    line 5 (TOHOST x11).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop.
  Defined.

  (* Expected output : 2 *)
  Definition pgmJalrTest1 : Rv32Program.
    init_pgm.
    line 0 (LI x11 (branchTarget 5)).
    line 1 (JALR x11 x0 (natToWord _ 0)).
    line 2 NOP.
    line 3 NOP.
    line 4 (LI x13 (natToWord _ 1)).
    line 5 (TOHOST x13).
    line 6 (LI x13 (natToWord _ 2)).
    line 7 (TOHOST x13).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
  Defined.

  (* Expected output : 6 *)
  Definition pgmJalrTest2 : Rv32Program.
    init_pgm.
    line 0 (LI x11 (branchTarget 5)).
    line 1 (JALR x11 x12 (natToWord _ 0)).
    line 2 NOP.
    line 3 NOP.
    line 4 NOP.
    line 5 NOP.
    line 6 (TOHOST x12).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop.
  Defined.

  (* Expected output : 2 *)
  Definition pgmBeqTest : Rv32Program.
    init_pgm.
    line 0 (LI x11 (natToWord _ 5)).
    line 1 (LI x12 (natToWord _ 5)).
    line 2 (BEQ x11 x12 (branchTarget 3)).
    line 3 (LI x13 (natToWord _ 1)).
    line 4 (TOHOST x13).
    line 5 (LI x13 (natToWord _ 2)).
    line 6 (TOHOST x13).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop.
  Defined.  

  (* Expected output : 2 *)
  Definition pgmBneTest : Rv32Program.
    init_pgm.
    line 0 (LI x11 (natToWord _ 4)).
    line 1 (LI x12 (natToWord _ 5)).
    line 2 (BNE x11 x12 (branchTarget 3)).
    line 3 (LI x13 (natToWord _ 1)).
    line 4 (TOHOST x13).
    line 5 (LI x13 (natToWord _ 2)).
    line 6 (TOHOST x13).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop.
  Defined.

  (* Expected output : 2 *)
  Definition pgmBltTest : Rv32Program.
    init_pgm.
    line 0 (LI x11 (natToWord _ 4)).
    line 1 (LI x12 (natToWord _ 5)).
    line 2 (BLT x11 x12 (branchTarget 3)).
    line 3 (LI x13 (natToWord _ 1)).
    line 4 (TOHOST x13).
    line 5 (LI x13 (natToWord _ 2)).
    line 6 (TOHOST x13).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop.
  Defined.

  (* Expected output : 2 *)
  Definition pgmBgeTest : Rv32Program.
    init_pgm.
    line 0 (LI x11 (natToWord _ 5)).
    line 1 (LI x12 (natToWord _ 4)).
    line 2 (BGE x11 x12 (branchTarget 3)).
    line 3 (LI x13 (natToWord _ 1)).
    line 4 (TOHOST x13).
    line 5 (LI x13 (natToWord _ 2)).
    line 6 (TOHOST x13).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop.
  Defined.

  (* Expected output : 2 *)
  Definition pgmLwSwTest1 : Rv32Program.
    init_pgm.
    line 0 (LI x13 (natToWord _ 2)).
    line 1 (SW x0 x13 (natToWord _ 0)).
    line 2 (LW x0 x15 (natToWord _ 0)).
    line 3 (TOHOST x15).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop.
  Defined.

  (* Expected output : 2 *)
  Definition pgmLwSwTest2: Rv32Program.
    init_pgm.
    line 0 (LI x13 (natToWord _ 1)).
    line 1 (LI x14 (natToWord _ 1)).
    line 2 (SW x0 x13 (natToWord _ 0)).
    line 3 (SW x0 x14 (natToWord _ 1)).
    line 4 (LW x0 x15 (natToWord _ 0)).
    line 5 (LW x0 x16 (natToWord _ 1)).
    line 6 (ADD x15 x16 x17).
    line 7 (TOHOST x17).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
  Defined.

  (* Expected output : n *)
  Definition pgmToHostTest (n: nat) : Rv32Program.
    init_pgm.
    line 0 (LI x13 (natToWord _ n)).
    line 1 (TOHOST x13).
    line 2 NOP.
    line 3 (J (branchTarget 62)). (* 3 + 62 == 1 *)
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop.
  Defined.

  (* Expected output : 2 *)
  Definition pgmSubTest: Rv32Program.
    init_pgm.
    line 0 (LI x11 (natToWord _ 5)).
    line 1 (LI x12 (natToWord _ 5)).
    line 2 (SUB x11 x12 x13).
    line 3 (BEQ x13 x0 (branchTarget 3)).
    line 4 (LI x14 (natToWord _ 1)).
    line 5 (TOHOST x14).
    line 6 (LI x14 (natToWord _ 2)).
    line 7 (TOHOST x14).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
  Defined.

  (* Expected output : 2 *)
  Definition pgmSllTest: Rv32Program.
    init_pgm.
    line 0 (LI x11 (natToWord _ 3)).
    line 1 (LI x12 (natToWord _ 2)).
    line 2 (SLL x11 x12 x13). (* x13 = x11 << x12 *)
    line 3 (LI x14 (natToWord _ 12)). (* 12 = 3 << 2 *)
    line 4 (BEQ x13 x14 (branchTarget 3)).
    line 5 (LI x15 (natToWord _ 1)).
    line 6 (TOHOST x15).
    line 7 (LI x15 (natToWord _ 2)).
    line 8 (TOHOST x15).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop.
  Defined.

  (* Expected output : 2 *)
  Definition pgmSrlTest: Rv32Program.
    init_pgm.
    line 0 (LI x11 (natToWord _ 12)).
    line 1 (LI x12 (natToWord _ 2)).
    line 2 (SRL x11 x12 x13). (* x3 = x1 >> x2 *)
    line 3 (LI x14 (natToWord _ 3)). (* 3 = 12 >> 2 *)
    line 4 (BEQ x13 x14 (branchTarget 3)).
    line 5 (LI x15 (natToWord _ 1)).
    line 6 (TOHOST x15).
    line 7 (LI x15 (natToWord _ 2)).
    line 8 (TOHOST x15).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop.
  Defined.

  (* Expected output : 2 *)
  Definition pgmOrTest: Rv32Program.
    init_pgm.
    line 0 (LI x11 (natToWord _ 7)).
    line 1 (LI x12 (natToWord _ 56)).
    line 2 (OR x11 x12 x13).
    line 3 (LI x14 (natToWord _ 63)).
    line 4 (BEQ x13 x14 (branchTarget 3)).
    line 5 (LI x15 (natToWord _ 1)).
    line 6 (TOHOST x15).
    line 7 (LI x15 (natToWord _ 2)).
    line 8 (TOHOST x15).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop.
  Defined.

  (* Expected output : 2 *)
  Definition pgmAndTest: Rv32Program.
    init_pgm.
    line 0 (LI x11 (natToWord _ 7)).
    line 1 (LI x12 (natToWord _ 56)).
    line 2 (AND x11 x12 x13).
    line 3 (BEQ x13 x0 (branchTarget 3)).
    line 4 (LI x15 (natToWord _ 1)).
    line 5 (TOHOST x15).
    line 6 (LI x15 (natToWord _ 2)).
    line 7 (TOHOST x15).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop.
    nop. nop. nop. nop. nop. nop. nop. nop.
    nop. nop. nop. nop. nop. nop. nop. nop.
  Defined.

  (* Expected output : 2 *)
  Definition pgmXorTest: Rv32Program.
    init_pgm.
    line 0 (LI x11 (natToWord _ 37)). (* 100101 *)
    line 1 (LI x12 (natToWord _ 42)). (* 101010 *)
    line 2 (XOR x11 x12 x13).
    line 3 (LI x14 (natToWord _ 15)). (* 001111 *)
    line 4 (BEQ x13 x14 (branchTarget 3)).
    line 5 (LI x15 (natToWord _ 1)).
    line 6 (TOHOST x15).
    line 7 (LI x15 (natToWord _ 2)).
    line 8 (TOHOST x15).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop.
  Defined.

  (* Expected output : Fib(n) *)
  Definition pgmFibonacci (n: nat) : Rv32Program.
    init_pgm.
    line 0 (LI x21 (natToWord _ n)).
    line 1 (BLEZ x21 (branchTarget 11)). (* to 12 *)
    line 2 (LI x9 (natToWord _ 1)).
    line 3 (MV x21 x6).
    line 4 (MV x9 x8).
    line 5 (MV x9 x7).
    line 6 (ADD x7 x8 x5).
    line 7 (ADDI x9 x9 (natToWord _ 1)).
    line 8 (MV x8 x7).
    line 9 (MV x5 x8).
    line 10 (BNE x6 x9 (branchTarget 60)). (* 10 + 60 == 6 *)
    line 11 (TOHOST x5).
    line 12 (J (branchTarget 3)). (* to 15 *)
    line 13 (LI x5 (natToWord _ 1)).
    line 14 (J (branchTarget 61)). (* 14 + 61 == 11 *)
    line 15 NOP.
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop.
  Defined.

  (* Expected output : Gcd(n, m) *)
  Definition pgmGcd (n m: nat) : Rv32Program.
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
    line 12 (BNE x4 x7 (branchTarget 54)). (* 12 + 54 == 2 *)
    line 13 (TOHOST x4).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop.
    nop. nop. nop. nop. nop. nop. nop. nop.
    nop. nop.
  Defined.

  (* Expected output : n! *)
  Definition pgmFactorial (n: nat) : Rv32Program.
    init_pgm.
    line 0 (LI x4 (natToWord _ 1)).
    line 1 (MV x4 x9).
    line 2 (LI x8 (natToWord _ (S n))).
    line 3 (MUL x4 x9 x4).
    line 4 (ADDI x9 x9 (natToWord _ 1)).
    line 5 (BNE x9 x8 (branchTarget 62)). (* 5 + 62 == 3 *)
    line 6 (TOHOST x4).
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop.
    nop. nop. nop. nop. nop. nop. nop. nop.
    nop. nop. nop. nop. nop. nop. nop. nop.
    nop.
  Defined.

  Definition pgmDekker1 : Rv32Program.
    init_pgm.
    line 0 (LI x10 (natToWord _ 0)).
    line 1 (LI x11 (natToWord _ 1)).
    line 2 (SW x0 x11 (natToWord _ 100)). (* enter[0] <- true *)
    line 3 (LW x0 x12 (natToWord _ 104)). (* enter[1] *)
    line 4 (BEQZ x12 (branchTarget 8)). (* 4 + 8 == 12 *)

    line 5 (LW x0 x13 (natToWord _ 108)). (* turn *)
    line 6 (BEQZ x13 (branchTarget 61)). (* 6 + 61 == 3 *)

    line 7 (SW x0 x10 (natToWord _ 100)). (* enter[0] <- false *)

    line 8 (LW x0 x13 (natToWord _ 108)). (* turn *)
    line 9 (BNEZ x13 (branchTarget 63)). (* 9 + 63 == 8 *)
    line 10 (SW x0 x11 (natToWord _ 100)). (* enter[0] <- true *)

    line 11 (J (branchTarget 56)). (* 11 + 56 == 3 *)

    (* cs starts *)
    line 12 (LW x0 x14 (natToWord _ 112)). (* counter *)
    line 13 (ADDI x14 x14 (natToWord _ 1)).
    line 14 (TOHOST x14).
    line 15 (SW x0 x14 (natToWord _ 112)).
    (* cs ends *)

    line 16 (SW x0 x11 (natToWord _ 108)). (* turn <- 1 *)
    line 17 (SW x0 x10 (natToWord _ 100)). (* enter[0] <- false *)

    line 18 (JAL x0 (branchTarget 46)). (* 18 + 46 == 0 *)

    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop.
    nop. nop. nop. nop. nop.
  Defined.

  Definition pgmDekker2 : Rv32Program.
    init_pgm.
    line 0 (LI x10 (natToWord _ 0)).
    line 1 (LI x11 (natToWord _ 1)).
    line 2 (SW x0 x11 (natToWord _ 104)). (* enter[1] <- true *)
    line 3 (LW x0 x12 (natToWord _ 100)). (* enter[0] *)
    line 4 (BEQZ x12 (branchTarget 8)). (* 4 + 8 == 12 *)

    line 5 (LW x0 x13 (natToWord _ 108)). (* turn *)
    line 6 (BNEZ x13 (branchTarget 61)). (* 6 + 61 == 3 *)

    line 7 (SW x0 x10 (natToWord _ 104)). (* enter[1] <- false *)

    line 8 (LW x0 x13 (natToWord _ 108)). (* turn *)
    line 9 (BEQZ x13 (branchTarget 63)). (* 9 + 63 == 8 *)
    line 10 (SW x0 x11 (natToWord _ 104)). (* enter[1] <- true *)

    line 11 (J (branchTarget 56)). (* 11 + 56 == 3 *)

    (* cs starts *)
    line 12 (LW x0 x14 (natToWord _ 112)). (* counter *)
    line 13 (ADDI x14 x14 (natToWord _ 1)).
    line 14 (TOHOST x14).
    line 15 (SW x0 x14 (natToWord _ 112)).
    (* cs ends *)

    line 16 (SW x0 x10 (natToWord _ 108)). (* turn <- 0 *)
    line 17 (SW x0 x10 (natToWord _ 104)). (* enter[1] <- false *)

    line 18 (JAL x0 (branchTarget 46)). (* 18 + 46 == 0 *)

    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop. 
    nop. nop. nop. nop. nop. nop. nop. nop.
    nop. nop. nop. nop. nop.
  Defined.

End TestPgms.

