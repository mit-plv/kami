Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics.
Require Import Kami.PrimFifo.

Require Import Ex.MemTypes.

Set Implicit Arguments.
Open Scope string.

Section BTB.
  Variable addrSize: nat.

  (** Heads up: should satisfy [indexSize + tagSize = addrSize] *)
  Context {indexSize tagSize: nat}.
  Variables (getIndex: forall ty, fullType ty (SyntaxKind (Bit addrSize)) ->
                                  Expr ty (SyntaxKind (Bit indexSize)))
            (getTag: forall ty, fullType ty (SyntaxKind (Bit addrSize)) ->
                                Expr ty (SyntaxKind (Bit tagSize))).

  Definition BtbUpdateStr :=
    STRUCT { "curPc" :: Bit addrSize; "nextPc" :: Bit addrSize }.

  Definition btbPredPc := MethodSig "btbPredPc"(Bit addrSize): Bit addrSize.
  Definition btbUpdate := MethodSig "btbUpdate"(Struct BtbUpdateStr): Void.

  Definition btb :=
    MODULE {
      Register "btbTargets" : Vector (Bit addrSize) indexSize <- Default
      with Register "btbTags" : Vector (Bit tagSize) indexSize <- Default
      with Register "btbValid" : Vector Bool indexSize <- Default

      with Method "btbPredPc" (pc: Bit addrSize): Bit addrSize :=
        LET index <- getIndex _ pc;
        LET tag <- getTag _ pc;
        Read targets <- "btbTargets";
        Read valid <- "btbValid";
        Read tags <- "btbTags";
        If (#valid@[#index] && (#tag == #tags@[#index]))
        then Ret #targets@[#index]
        else Ret (#pc + $4)
        as npc;
        Ret #npc
            
      with Method "btbUpdate" (upd: Struct BtbUpdateStr): Void :=
        LET curPc <- #upd ! BtbUpdateStr @."curPc";
        LET nextPc <- #upd ! BtbUpdateStr @."nextPc";
        LET index <- getIndex _ curPc;
        LET tag <- getTag _ curPc;
        Read targets: Vector (Bit addrSize) indexSize <- "btbTargets";
        Read valid: Vector Bool indexSize <- "btbValid";
        Read tags: Vector (Bit tagSize) indexSize <- "btbTags";
        If (#nextPc != (#curPc + $1))
        then
          Write "btbValid" <- #valid@[#index <- $$true];
          Write "btbTags" <- #tags@[#index <- #tag];
          Write "btbTargets" <- #targets@[#index <- #nextPc];
          Retv
        else
          If (#tag == #tags@[#index])
          then Write "btbValid" <- #valid@[#index <- $$false]; Retv;
          Retv;
        Retv
      }.

End BTB.

#[global] Hint Unfold btb : ModuleDefs.
#[global] Hint Unfold BtbUpdateStr btbPredPc btbUpdate : MethDefs.

Section Wf.
  Variable addrSize: nat.
  Context {indexSize tagSize: nat}.
  Variables (getIndex: forall ty, fullType ty (SyntaxKind (Bit addrSize)) ->
                                  Expr ty (SyntaxKind (Bit indexSize)))
            (getTag: forall ty, fullType ty (SyntaxKind (Bit addrSize)) ->
                                Expr ty (SyntaxKind (Bit tagSize))).

  Lemma btb_ModEquiv:
    ModPhoasWf (btb getIndex getTag).
  Proof. kequiv. Qed.

  Lemma btb_ModRegsWf:
    ModRegsWf (btb getIndex getTag).
  Proof. kvr. Qed.

End Wf.

#[global] Hint Resolve btb_ModEquiv.
#[global] Hint Resolve btb_ModRegsWf.

