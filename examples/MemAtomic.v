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

  Definition midRegs : list RegInitT := nil.

  Definition midDms : list (DefMethT type) := nil.

  Definition getReqSig : Attribute SignatureT :=
    Method Value#(atomK addrSize dType) (inName -n- "deq") #(Bit 0);.
  Definition setRepSig : Attribute SignatureT :=
    Method Value#(Bit 0) (outName -n- "enq") #(atomK addrSize dType);.
  Definition execSig : Attribute SignatureT :=
    Method Value#(atomK addrSize dType) ("exec"__ memi) #(atomK addrSize dType);.

  Definition processLd: Action type (Bit 0) :=
    vcall req <- (attrName getReqSig) :@: (attrType getReqSig) #(Cd _) #;
    vassert (V req @> "type" #[] == C memLd) #;
    vcall rep <- (attrName execSig) :@: (attrType execSig) #(V req) #;
    vassert (V rep @> "type" #[] == C memLd) #;
    vcall (attrName setRepSig) :@: (attrType setRepSig) #(V rep) #;
    vret (Cd _) #;.
    
  Definition processSt: Action type (Bit 0) :=
    vcall req <- (attrName getReqSig) :@: (attrType getReqSig) #(Cd _) #;
    vassert (V req @> "type" #[] == C memSt) #;
    vcall rep <- (attrName execSig) :@: (attrType execSig) #(V req) #;
    vassert (V rep @> "type" #[] == C memSt) #;
    vcall (attrName setRepSig) :@: (attrType setRepSig) #(V rep) #;
    vret (Cd _) #;.

  Definition midRules :=
    (Build_Attribute (midName -n- "processLd") processLd)
      :: (Build_Attribute (midName -n- "processSt") processSt)
      :: nil.

  Definition midDefMeths : list (DefMethT type) := nil.

  Definition mid := Mod midRegs midRules midDefMeths.

  Section Facts.
    Lemma regsInDomain_mid: RegsInDomain mid.
    Proof.
      unfold RegsInDomain; intros.
      destRule H; try (inv HSemMod); invertActionRep; inDomain_tac.
      inv Hltsmod; reflexivity.
    Qed.

  End Facts.

End Middleman.

Hint Unfold getReqSig setRepSig execSig.
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
    Proof. apply concatMod_RegsInDomain; apply regsInDomain_simpleFifo. Qed.

    Lemma regsInDomain_iomi i: RegsInDomain (iomi i).
    Proof.
      apply concatMod_RegsInDomain;
      [apply regsInDomain_ioi|apply regsInDomain_mid].
    Qed.

  End Facts.

End MemAtomic.

Hint Unfold minst insi outsi ioi midi iomi ioms memAtomic : ModuleDefs.

