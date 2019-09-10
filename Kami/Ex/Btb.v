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
  Variable iaddrSize: nat.

  (** Heads up: should satisfy [indexSize + tagSize = iaddrSize] *)
  Context {indexSize tagSize: nat}.
  Variables (getIndex: forall ty, fullType ty (SyntaxKind (Bit iaddrSize)) ->
                                  Expr ty (SyntaxKind (Bit indexSize)))
            (getTag: forall ty, fullType ty (SyntaxKind (Bit iaddrSize)) ->
                                Expr ty (SyntaxKind (Bit tagSize))).

  Definition BtbUpdateStr :=
    STRUCT { "curPc" :: Bit iaddrSize; "nextPc" :: Bit iaddrSize }.

  Definition btbPredPc := MethodSig "btbPredPc"(Bit iaddrSize): Bit iaddrSize.
  Definition btbUpdate := MethodSig "btbUpdate"(Struct BtbUpdateStr): Void.

  Definition btb :=
    MODULE {
      Register "btbTargets" : Vector (Bit iaddrSize) indexSize <- Default
      with Register "btbTags" : Vector (Bit tagSize) indexSize <- Default
      with Register "btbValid" : Vector Bool indexSize <- Default

      with Method "btbPredPc" (pc: Bit iaddrSize): Bit iaddrSize :=
        LET index <- getIndex _ pc;
        LET tag <- getTag _ pc;
        Read targets <- "btbTargets";
        Read valid <- "btbValid";
        Read tags <- "btbTags";
        If (#valid@[#index] && (#tag == #tags@[#index]))
        then Ret #targets@[#index]
        else Ret (#pc + $1)
        as npc;
        Ret #npc
            
      with Method "btbUpdate" (upd: Struct BtbUpdateStr): Void :=
        LET curPc <- #upd ! BtbUpdateStr @."curPc";
        LET nextPc <- #upd ! BtbUpdateStr @."nextPc";
        LET index <- getIndex _ curPc;
        LET tag <- getTag _ curPc;
        Read targets: Vector (Bit iaddrSize) indexSize <- "btbTargets";
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

Hint Unfold btb : ModuleDefs.
Hint Unfold BtbUpdateStr btbPredPc btbUpdate : MethDefs.

Section Wf.
  Variable iaddrSize: nat.
  Context {indexSize tagSize: nat}.
  Variables (getIndex: forall ty, fullType ty (SyntaxKind (Bit iaddrSize)) ->
                                  Expr ty (SyntaxKind (Bit indexSize)))
            (getTag: forall ty, fullType ty (SyntaxKind (Bit iaddrSize)) ->
                                Expr ty (SyntaxKind (Bit tagSize))).

  Lemma btb_ModEquiv:
    ModPhoasWf (btb getIndex getTag).
  Proof. kequiv. Qed.

  Lemma btb_ModRegsWf:
    ModRegsWf (btb getIndex getTag).
  Proof. kvr. Qed.

End Wf.

Hint Resolve btb_ModEquiv.
Hint Resolve btb_ModRegsWf.

