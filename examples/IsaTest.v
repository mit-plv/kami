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

Definition pgmToHostTest (n: nat) : ConstT (Vector (Data rv32iLgDataBytes) rv32iAddrSize).
  init_pgm.
  line 0 (LI x3 (natToWord _ n)).
  line 1 (TOHOST x3).
  line 2 NOP.
  line 3 (J (natToWord _ 30)). (* 3 + 30 == 1 *)
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop.
Defined.

Definition pgmBranchTest: ConstT (Vector (Data rv32iLgDataBytes) rv32iAddrSize).
  init_pgm.
  line 0 (LI x3 (natToWord _ 3)).
  line 1 (LI x4 (natToWord _ 5)).
  line 2 (TOHOST x3).
  line 3 (TOHOST x4).
  line 4 (BLT x3 x4 (natToWord _ 6)).
  line 5 (TOHOST x0).
  line 6 (TOHOST x3).
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop.
  nop. 
Defined.

Definition pgmFibonacci (n: nat) : ConstT (Vector (Data rv32iLgDataBytes) rv32iAddrSize).
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
  line 10 (BNE x6 x9 (natToWord _ 28)). (* 10 + 28 == 6 *)
  line 11 (TOHOST x5).
  line 12 (J (natToWord _ 3)). (* to 15 *)
  line 13 (LI x5 (natToWord _ 1)).
  line 14 (J (natToWord _ 29)). (* 14 + 29 == 11 *)
  line 15 NOP.
  nop. nop. nop. nop. nop. nop. nop. nop. 
  nop. nop. nop. nop. nop. nop. nop. nop.
Defined.

