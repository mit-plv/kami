Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FnMap.
Require Import Lts.Syntax Lts.Semantics.
Require Import Ex.SC Ex.Fifo.

Set Implicit Arguments.

Section Middleman.
  Variable midName inName outName: string.
  Variable memi: nat.
  Variable addrSize: nat.
  Variable dType: Kind.

  Definition getReq := MethodSig (inName -n- "deq")() : atomK addrSize dType.
  Definition setRep := MethodSig (outName -n- "enq")(atomK addrSize dType) : Void.
  Definition exec := MethodSig ("exec"__ memi)(atomK addrSize dType) : atomK addrSize dType.

  Definition processLd :=
    (Call req <- getReq();
     Assert #req@."type" == $$memLd;
     Call rep <- exec(#req);
     Assert #rep@."type" == $$memLd;
     Call setRep(#rep);
     Retv)%kami.

  Definition processSt :=
    (Call req <- getReq();
     Assert #req@."type" == $$memSt;
     Call rep <- exec(#req);
     Assert #rep@."type" == $$memSt;
     Call setRep(#rep);
     Retv)%kami.

  Definition mid := MODULE {
    Rule (midName -n- "processLd") := processLd
    with Rule (midName -n- "processSt") := processSt
  }.

  Section Facts.
    Lemma regsInDomain_mid: RegsInDomain mid.
    Proof.
      regsInDomain_tac.
    Qed.
  End Facts.

End Middleman.

Hint Unfold getReq setRep exec.
Hint Unfold mid : ModuleDefs.

Section MemAtomic.
  Variable addrSize : nat.
  Variable dType : Kind.

  Variable n: nat.

  Definition minst := memInst n addrSize dType.

  Definition insi (i: nat) := simpleFifo ("Ins"__ i) O (atomK addrSize dType).
  Definition outsi (i: nat) := simpleFifo ("Outs"__ i) O (atomK addrSize dType).
  Definition ioi (i: nat) := ConcatMod (insi i) (outsi i).

  Definition midi (i: nat) := mid ("Mid"__ i) ("Ins"__ i) ("Outs"__ i) i addrSize dType.
  Definition iomi (i: nat) := ConcatMod (ioi i) (midi i).

  Fixpoint ioms (i: nat) :=
    match i with
      | O => iomi O
      | S i' => ConcatMod (iomi i) (ioms i')
    end.

  Definition memAtomic := ConcatMod (ioms n) minst.

  Section Facts.
    Lemma regsInDomain_ioi i: RegsInDomain (ioi i).
    Proof.
      apply concatMod_RegsInDomain; apply regsInDomain_simpleFifo.
    Qed.

    Lemma regsInDomain_iomi i: RegsInDomain (iomi i).
    Proof.
      apply concatMod_RegsInDomain;
      [apply regsInDomain_ioi|apply regsInDomain_mid].
    Qed.

  End Facts.

End MemAtomic.

Hint Unfold minst insi outsi ioi midi iomi ioms memAtomic : ModuleDefs.
