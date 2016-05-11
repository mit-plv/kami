Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Lts.Syntax Lts.Semantics Lts.Specialize Lts.Equiv Lts.Tactics.
Require Import Ex.SC Ex.Fifo.

Set Implicit Arguments.

Section Middleman.
  Variable inName outName: string.
  Variable addrSize: nat.
  Variable dType: Kind.

  Definition getReq := MethodSig (inName .. "deq")() : atomK addrSize dType.
  Definition setRep := MethodSig (outName .. "enq")(atomK addrSize dType) : Void.
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
  Definition ioms (i: nat) := duplicate iom i.
  Definition memAtomic := ConcatMod (ioms n) minst.

End MemAtomic.

Hint Unfold minst inQ outQ ioQ midQ iom ioms memAtomic : ModuleDefs.

Section Facts.

  Lemma ioms_ModEquiv:
    forall a sz d n m,
      m = ioms a sz d n ->
      ModEquiv type typeUT m.
  Proof.
    kequiv.
  Qed.
  Hint Resolve ioms_ModEquiv.

  Lemma memAtomic_ModEquiv:
    forall a sz d n m,
      m = memAtomic a sz d n ->
      ModEquiv type typeUT m.
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Immediate ioms_ModEquiv memAtomic_ModEquiv.

