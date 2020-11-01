Require Import Bool String List.
Require Import Lib.CommonTactics Lib.Word Lib.Struct.
Require Import Kami.Syntax Kami.Semantics Kami.Notations.
Require Import Ex.MemTypes.
Require Import Ex.IsaRv32.

Definition rv32AddrSize := 11.
Definition rv32IAddrSize := 8.

(* For easy RV32 programming *)
Section RV32Struct.

  Inductive Gpr :=
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7
  | x8 | x9 | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23
  | x24 | x25 | x26 | x27 | x28 | x29 | x30 | x31.

  Definition gprToRaw (r: Gpr): word 5 :=
    match r with
    | x0 => natToWord _ 0 | x1 => natToWord _ 1 | x2 => natToWord _ 2 | x3 => natToWord _ 3
    | x4 => natToWord _ 4 | x5 => natToWord _ 5 | x6 => natToWord _ 6 | x7 => natToWord _ 7
    | x8 => natToWord _ 8 | x9 => natToWord _ 9 | x10 => natToWord _ 10 | x11 => natToWord _ 11
    | x12 => natToWord _ 12 | x13 => natToWord _ 13 | x14 => natToWord _ 14 | x15 => natToWord _ 15
    | x16 => natToWord _ 16 | x17 => natToWord _ 17 | x18 => natToWord _ 18 | x19 => natToWord _ 19
    | x20 => natToWord _ 20 | x21 => natToWord _ 21 | x22 => natToWord _ 22 | x23 => natToWord _ 23
    | x24 => natToWord _ 24 | x25 => natToWord _ 25 | x26 => natToWord _ 26 | x27 => natToWord _ 27
    | x28 => natToWord _ 28 | x29 => natToWord _ 29 | x30 => natToWord _ 30 | x31 => natToWord _ 31
    end.

  Inductive Rv32 :=
  | JAL (rd: Gpr) (ofs: word 20): Rv32
  | JALR (rd rs1: Gpr) (ofs: word 12): Rv32
  | BEQ (rs1 rs2: Gpr) (ofs: word 12): Rv32
  | BNE (rs1 rs2: Gpr) (ofs: word 12): Rv32
  | BLT (rs1 rs2: Gpr) (ofs: word 12): Rv32
  | BGE (rs1 rs2: Gpr) (ofs: word 12): Rv32
  | BLTU (rs1 rs2: Gpr) (ofs: word 12): Rv32
  | BGEU (rs1 rs2: Gpr) (ofs: word 12): Rv32
  | LW (rd rs1: Gpr) (ofs: word 12): Rv32
  | SW (rs1 rs2: Gpr) (ofs: word 12): Rv32
  | ADDI (rd rs1: Gpr) (ofs: word 12): Rv32
  | ADD (rd rs1 rs2: Gpr): Rv32
  | SUB (rd rs1 rs2: Gpr): Rv32
  | MUL (rd rs1 rs2: Gpr): Rv32
  | SLL (rd rs1 rs2: Gpr): Rv32
  | SRL (rd rs1 rs2: Gpr): Rv32
  | OR (rd rs1 rs2: Gpr): Rv32
  | AND (rd rs1 rs2: Gpr): Rv32
  | XOR (rd rs1 rs2: Gpr): Rv32
  (* pseudo-instructions *)
  | LI (rd: Gpr) (ofs: word 20): Rv32
  | MV (rd rs1: Gpr): Rv32
  | BEQZ (rs1: Gpr) (ofs: word 12): Rv32
  | BNEZ (rs1: Gpr) (ofs: word 12): Rv32
  | BLEZ (rs1: Gpr) (ofs: word 12): Rv32
  | BGEZ (rs1: Gpr) (ofs: word 12): Rv32
  | BLTZ (rs1: Gpr) (ofs: word 12): Rv32
  | BGTZ (rs1: Gpr) (ofs: word 12): Rv32
  | J (ofs: word 20): Rv32
  | NOP: Rv32.

  Local Infix "~~" := combine (at level 0).

  Definition offsetUJToRaw (ofs: word 20) :=
    let ofs20_12 := spl1 11 9 ofs in
    let ofs11_1 := spl2 11 9 ofs in
    cmb (cmb (spl1 8 1 ofs20_12) (spl2 10 1 ofs11_1))
        (cmb (spl1 10 1 ofs11_1) (spl2 8 1 ofs20_12)).

  Definition offsetSBToRaw12 (ofs: word 12) := spl1 11 1 ofs.
  Definition offsetSBToRaw11 (ofs: word 12) := spl2 1 1 (spl1 10 2 ofs).
  Definition offsetSBToRaw10_5 (ofs: word 12) := spl2 6 2 (spl1 4 8 ofs).
  Definition offsetSBToRaw4_1 (ofs: word 12) := spl2 4 8 ofs.

  Definition offsetSToRaw11_5 (ofs: word 12) := spl1 5 7 ofs.
  Definition offsetSToRaw4_0 (ofs: word 12) := spl2 5 7 ofs.

  Definition RtypeToRaw (op: nat) (rs1 rs2 rd: Gpr) (f7: nat) (f3: nat) :=
    (natToWord 7 op)~~(gprToRaw rd)~~(natToWord 3 f3)
                    ~~(gprToRaw rs1)~~(gprToRaw rs2)~~(natToWord 7 f7).
  Definition ItypeToRaw (op: nat) (rs1 rd: Gpr) (f3: nat) (ofs: word 12) :=
    (natToWord 7 op)~~(gprToRaw rd)~~(natToWord 3 f3)~~(gprToRaw rs1)~~ofs.
  Definition StypeToRaw (op: nat) (rs1 rs2: Gpr) (f3: nat) (ofs: word 12) :=
    (natToWord 7 op)~~(offsetSToRaw4_0 ofs)~~(natToWord 3 f3)
                    ~~(gprToRaw rs1)~~(gprToRaw rs2)~~(offsetSToRaw11_5 ofs).
  Definition SBtypeToRaw (op: nat) (rs1 rs2: Gpr) (f3: nat) (ofs: word 12) :=
    (natToWord 7 op)~~(offsetSBToRaw11 ofs)~~(offsetSBToRaw4_1 ofs)
                    ~~(natToWord 3 f3)~~(gprToRaw rs1)~~(gprToRaw rs2)
                    ~~(offsetSBToRaw10_5 ofs)~~(offsetSBToRaw12 ofs).
  Definition UJtypeToRaw (op: nat) (rd: Gpr) (ofs: word 20) :=
    (natToWord 7 op)~~(gprToRaw rd)~~(offsetUJToRaw ofs).

  Definition rv32ToRaw (inst: Rv32): word 32 :=
    match inst with
    | JAL rd ofs => UJtypeToRaw opcode_JAL rd ofs
    | JALR rd rs1 ofs => ItypeToRaw opcode_JALR rs1 rd 0 ofs
    | BEQ rs1 rs2 ofs => SBtypeToRaw opcode_BRANCH rs1 rs2 funct3_BEQ ofs
    | BNE rs1 rs2 ofs => SBtypeToRaw opcode_BRANCH rs1 rs2 funct3_BNE ofs
    | BLT rs1 rs2 ofs => SBtypeToRaw opcode_BRANCH rs1 rs2 funct3_BLT ofs
    | BGE rs1 rs2 ofs => SBtypeToRaw opcode_BRANCH rs1 rs2 funct3_BGE ofs
    | BLTU rs1 rs2 ofs => SBtypeToRaw opcode_BRANCH rs1 rs2 funct3_BLTU ofs
    | BGEU rs1 rs2 ofs => SBtypeToRaw opcode_BRANCH rs1 rs2 funct3_BGEU ofs
    | LW rd rs1 ofs => ItypeToRaw opcode_LOAD rs1 rd funct3_LW ofs
    | SW rs1 rs2 ofs => StypeToRaw opcode_STORE rs1 rs2 funct3_SW ofs
    | ADDI rd rs1 ofs => ItypeToRaw opcode_OP_IMM rs1 rd funct3_ADDI ofs
    | ADD rd rs1 rs2 => RtypeToRaw opcode_OP rs1 rs2 rd funct7_ADD funct3_ADD
    | SUB rd rs1 rs2 => RtypeToRaw opcode_OP rs1 rs2 rd funct7_SUB funct3_SUB
    | MUL rd rs1 rs2 => RtypeToRaw opcode_OP rs1 rs2 rd funct7_MUL funct3_MUL
    | SLL rd rs1 rs2 => RtypeToRaw opcode_OP rs1 rs2 rd funct7_SLL funct3_SLL
    | SRL rd rs1 rs2 => RtypeToRaw opcode_OP rs1 rs2 rd funct7_SRL funct3_SRL
    | OR rd rs1 rs2 => RtypeToRaw opcode_OP rs1 rs2 rd funct7_OR funct3_OR
    | AND rd rs1 rs2 => RtypeToRaw opcode_OP rs1 rs2 rd funct7_AND funct3_AND
    | XOR rd rs1 rs2 => RtypeToRaw opcode_OP rs1 rs2 rd funct7_XOR funct3_XOR
    (* pseudo-instructions *)
    | LI rd ofs => ItypeToRaw opcode_OP_IMM x0 rd funct3_ADDI (split1 12 8 ofs)
    | MV rd rs1 => ItypeToRaw opcode_OP_IMM rs1 rd funct3_ADDI (natToWord _ 0)
    | BEQZ rs1 ofs => SBtypeToRaw opcode_BRANCH rs1 x0 funct3_BEQ ofs
    | BNEZ rs1 ofs => SBtypeToRaw opcode_BRANCH rs1 x0 funct3_BNE ofs 
    | BLEZ rs1 ofs => SBtypeToRaw opcode_BRANCH x0 rs1 funct3_BGE ofs
    | BGEZ rs1 ofs => SBtypeToRaw opcode_BRANCH rs1 x0 funct3_BGE ofs
    | BLTZ rs1 ofs => SBtypeToRaw opcode_BRANCH rs1 x0 funct3_BLT ofs
    | BGTZ rs1 ofs => SBtypeToRaw opcode_BRANCH x0 rs1 funct3_BLT ofs
    | J ofs => UJtypeToRaw opcode_JAL x0 ofs
    | NOP => ItypeToRaw opcode_OP_IMM x0 x0 funct3_ADDI (wzero _)
    end.

End RV32Struct.

Section UnitTests.

  Definition RtypeToRaw_getOpcodeE_correct:
    evalExpr (getOpcodeE
                (Const _ (ConstBit (RtypeToRaw opcode_OP x1 x2 x3 funct6_SRLI funct3_SRLI)))) =
    natToWord _ opcode_OP := eq_refl.
  Definition RtypeToRaw_getRs1E_correct:
    evalExpr (getRs1E
                (Const _ (ConstBit (RtypeToRaw opcode_OP x1 x2 x3 funct6_SRLI funct3_SRLI)))) =
    gprToRaw x1 := eq_refl.
  Definition RtypeToRaw_getRs2E_correct:
    evalExpr (getRs2E
                (Const _ (ConstBit (RtypeToRaw opcode_OP x1 x2 x3 funct6_SRLI funct3_SRLI)))) =
    gprToRaw x2 := eq_refl.
  Definition RtypeToRaw_getRdE_correct:
    evalExpr (getRdE
                (Const _ (ConstBit (RtypeToRaw opcode_OP x1 x2 x3 funct6_SRLI funct3_SRLI)))) =
    gprToRaw x3 := eq_refl.
  Definition RtypeToRaw_getFunct7E_correct:
    evalExpr (getFunct7E
                (Const _ (ConstBit (RtypeToRaw opcode_OP x1 x2 x3 funct6_SRLI funct3_SRLI)))) =
    natToWord _ funct6_SRLI := eq_refl.
  Definition RtypeToRaw_getFunct3E_correct:
    evalExpr (getFunct3E
                (Const _ (ConstBit (RtypeToRaw opcode_OP x1 x2 x3 funct6_SRLI funct3_SRLI)))) =
    natToWord _ funct3_SRLI := eq_refl.

  Definition ItypeToRaw_getOpcodeE_correct:
    evalExpr (getOpcodeE
                (Const _ (ConstBit (ItypeToRaw opcode_OP_IMM x1 x2 funct3_SRLI (natToWord _ 5))))) =
    natToWord _ opcode_OP_IMM := eq_refl.
  Definition ItypeToRaw_getRs1E_correct:
    evalExpr (getRs1E
                (Const _ (ConstBit (ItypeToRaw opcode_OP_IMM x1 x2 funct3_SRLI (natToWord _ 5))))) =
    gprToRaw x1 := eq_refl.
  Definition ItypeToRaw_getRdE_correct:
    evalExpr (getRdE
                (Const _ (ConstBit (ItypeToRaw opcode_OP_IMM x1 x2 funct3_SRLI (natToWord _ 5))))) =
    gprToRaw x2 := eq_refl.
  Definition ItypeToRaw_getFunct3E_correct:
    evalExpr (getFunct3E
                (Const _ (ConstBit (ItypeToRaw opcode_OP_IMM x1 x2 funct3_SRLI (natToWord _ 5))))) =
    natToWord _ funct3_SRLI := eq_refl.
  Definition ItypeToRaw_getOffsetIE_correct:
    evalExpr (getOffsetIE
                (Const _ (ConstBit (ItypeToRaw opcode_OP_IMM x1 x2 funct3_SRLI (natToWord _ 5))))) =
    natToWord _ 5 := eq_refl.

  Definition StypeToRaw_getOpcodeE_correct:
    evalExpr (getOpcodeE
                (Const _ (ConstBit (StypeToRaw opcode_STORE x1 x2 funct3_SW (natToWord _ 5))))) =
    natToWord _ opcode_STORE := eq_refl.
  Definition StypeToRaw_getRs1E_correct:
    evalExpr (getRs1E
                (Const _ (ConstBit (StypeToRaw opcode_OP_IMM x1 x2 funct3_SW (natToWord _ 5))))) =
    gprToRaw x1 := eq_refl.
  Definition StypeToRaw_getRs2E_correct:
    evalExpr (getRs2E
                (Const _ (ConstBit (StypeToRaw opcode_OP_IMM x1 x2 funct3_SW (natToWord _ 5))))) =
    gprToRaw x2 := eq_refl.
  Definition StypeToRaw_getFunct3E_correct:
    evalExpr (getFunct3E
                (Const _ (ConstBit (StypeToRaw opcode_OP_IMM x1 x2 funct3_SW (natToWord _ 5))))) =
    natToWord _ funct3_SW := eq_refl.
  Definition StypeToRaw_getOffsetSE_correct:
    evalExpr (getOffsetSE
                (Const _ (ConstBit (StypeToRaw opcode_OP_IMM x1 x2 funct3_SW (natToWord _ 5))))) =
    natToWord _ 5 := eq_refl.

  Definition SBtypeToRaw_getOpcodeE_correct:
    evalExpr (getOpcodeE
                (Const _ (ConstBit (SBtypeToRaw opcode_BRANCH x1 x2 funct3_BGE (natToWord _ 5))))) =
    natToWord _ opcode_BRANCH := eq_refl.
  Definition SBtypeToRaw_getRs1E_correct:
    evalExpr (getRs1E
                (Const _ (ConstBit (SBtypeToRaw opcode_OP_IMM x1 x2 funct3_BGE (natToWord _ 5))))) =
    gprToRaw x1 := eq_refl.
  Definition SBtypeToRaw_getRs2E_correct:
    evalExpr (getRs2E
                (Const _ (ConstBit (SBtypeToRaw opcode_OP_IMM x1 x2 funct3_BGE (natToWord _ 5))))) =
    gprToRaw x2 := eq_refl.
  Definition SBtypeToRaw_getFunct3E_correct:
    evalExpr (getFunct3E
                (Const _ (ConstBit (SBtypeToRaw opcode_OP_IMM x1 x2 funct3_BGE (natToWord _ 5))))) =
    natToWord _ funct3_BGE := eq_refl.
  Definition SBtypeToRaw_getOffsetSE_correct:
    evalExpr (getOffsetSBE
                (Const _ (ConstBit (SBtypeToRaw opcode_OP_IMM x1 x2 funct3_BGE (natToWord _ 5))))) =
    natToWord _ 5 := eq_refl.

  Definition UJtypeToRaw_getOpcodeE_correct:
    evalExpr (getOpcodeE
                (Const _ (ConstBit (UJtypeToRaw opcode_JAL x1 (natToWord _ 5))))) =
    natToWord _ opcode_JAL := eq_refl.
  Definition UJtypeToRaw_getRdE_correct:
    evalExpr (getRdE
                (Const _ (ConstBit (UJtypeToRaw opcode_JAL x1 (natToWord _ 5))))) =
    gprToRaw x1 := eq_refl.
  Definition UJtypeToRaw_getOffsetUJE_correct:
    evalExpr (getOffsetUJE
                (Const _ (ConstBit (UJtypeToRaw opcode_JAL x1 (natToWord _ 5))))) =
    natToWord _ 5 := eq_refl.
  
End UnitTests.

Local Ltac line i c := exact (ConstBit (rv32ToRaw c)).
Local Ltac nop := exact (ConstBit (rv32ToRaw NOP)).
Notation "'Rv32Program'" := (ConstT (Vector (Data rv32DataBytes) rv32IAddrSize)).

Ltac init_pgm :=
  refine (ConstVector _);
  refine
    (VecNext
       (VecNext
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
                      (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _)))))))
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
                      (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _))))))))
       (VecNext
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
                      (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _)))))))
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
                      (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _))))))))).

Fixpoint nop_n (n: nat) :=
  match n with
  | O => Vec0 (ConstBit (rv32ToRaw NOP))
  | S n' => VecNext (nop_n n') (nop_n n')
  end.

Ltac init_pgm_64 :=
  refine (ConstVector _);
  refine
    (VecNext
       (VecNext
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
                      (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _)))))))
          (nop_n 6))
       (nop_n 7)).

(* The final address should be obtained by multiplying two by processor, 
 * according to RV32 specification. *)
Definition branchTarget {sz} (ofs: nat) := natToWord sz (ofs * 2).

