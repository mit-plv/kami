Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.Semantics Lts.Renaming Lts.Equiv.
Require Import Ex.SC Ex.Fifo.

Set Implicit Arguments.

Section Middleman.
  Variable inName outName: string.
  Variable addrSize: nat.
  Variable dType: Kind.

  Definition getReq := MethodSig (inName -n- "deq")() : atomK addrSize dType.
  Definition setRep := MethodSig (outName -n- "enq")(atomK addrSize dType) : Void.
  Definition exec := MethodSig "exec"(atomK addrSize dType) : atomK addrSize dType.

  Definition processLd {ty} : ActionT ty Void :=
    (Call req <- getReq();
     Assert #req@."type" == $$memLd;
     Call rep <- exec(#req);
     Assert #rep@."type" == $$memLd;
     Call setRep(#rep);
     Retv)%kami.

  Definition processSt {ty} : ActionT ty Void :=
    (Call req <- getReq();
     Assert #req@."type" == $$memSt;
     Call rep <- exec(#req);
     Assert #rep@."type" == $$memSt;
     Call setRep(#rep);
     Retv)%kami.

  Definition mid := MODULE {
    Rule "processLd" := processLd
    with Rule "processSt" := processSt
  }.

End Middleman.

Hint Unfold mid : ModuleDefs.
Hint Unfold getReq setRep exec processLd processSt : MethDefs.

Section MemAtomic.
  Variable addrSize fifoSize : nat.
  Variable dType : Kind.

  Variable n: nat.

  Definition minst := memInst n addrSize dType.

  Definition inQ := simpleFifo "Ins" fifoSize (atomK addrSize dType).
  Definition outQ := simpleFifo "Outs" fifoSize (atomK addrSize dType).
  Definition ioQ := ConcatMod inQ outQ.

  Definition midQ := mid "Ins" "Outs" addrSize dType.
  Definition iom := ConcatMod ioQ midQ.

  Definition iomi (i: nat) := specializeMod iom i.

  Fixpoint ioms (i: nat) :=
    match i with
      | O => iomi O
      | S i' => ConcatMod (iomi i) (ioms i')
    end.

  Definition memAtomic := ConcatMod (ioms n) minst.

End MemAtomic.

Hint Unfold minst inQ outQ ioQ midQ iom iomi ioms memAtomic : ModuleDefs.

Section Facts.
  Lemma ioms_ModEquiv:
    forall a sz d n, ModEquiv type typeUT (ioms a sz d n).
  Proof.
    induction n; simpl; intros.
    - equiv_tac.
    - apply ModEquiv_modular.
      + equiv_tac.
      + auto.
  Qed.

  Lemma memAtomic_ModEquiv:
    forall a sz d n, ModEquiv type typeUT (memAtomic a sz d n).
  Proof.
    intros; apply ModEquiv_modular.
    - apply ioms_ModEquiv.
    - apply memInst_ModEquiv.
  Qed.

End Facts.

