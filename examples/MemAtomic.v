Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Lts.Syntax Lts.Notations Lts.Semantics Lts.Specialize Lts.Duplicate.
Require Import Lts.Equiv Lts.ParametricEquiv Lts.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.NativeFifo.

Set Implicit Arguments.

Section Middleman.
  Variable inName outName: string.
  Variable addrSize lgDataBytes: nat.

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  Definition getReq := MethodSig (inName -- "deq")() : RqFromProc.
  Definition setRep := MethodSig (outName -- "enq")(RsToProc) : Void.
  Definition exec := MethodSig "exec"(RqFromProc) : RsToProc.

  Definition processLd {ty} : ActionT ty Void :=
    (Call req <- getReq();
     Assert !#req@."op";
     Call rep <- exec(#req);
     Call setRep(#rep);
     Retv)%kami_action.

  Definition processSt {ty} : ActionT ty Void :=
    (Call req <- getReq();
     Assert #req@."op";
     Call rep <- exec(#req);
     Call setRep(#rep);
     Retv)%kami_action.

  Definition mid := MODULE {
    Rule "processLd" := processLd
    with Rule "processSt" := processSt
  }.

End Middleman.

Hint Unfold mid : ModuleDefs.
Hint Unfold RqFromProc RsToProc getReq setRep exec processLd processSt : MethDefs.

Section MemAtomic.
  Variables (addrSize lgDataBytes: nat).

  Variable n: nat.

  Definition minst := memInst n addrSize lgDataBytes.

  Definition inQ := @nativeSimpleFifo "Ins" (RqFromProc addrSize lgDataBytes) Default.
  Definition outQ := @nativeSimpleFifo "Outs" (RsToProc lgDataBytes) Default.
  Definition ioQ := ConcatMod inQ outQ.

  Definition midQ := mid "Ins" "Outs" addrSize lgDataBytes.
  Definition iom := ConcatMod ioQ midQ.
  Definition ioms (i: nat) := duplicate iom i.
  Definition memAtomic := ConcatMod (ioms n) minst.

End MemAtomic.

Hint Unfold minst inQ outQ ioQ midQ iom ioms memAtomic : ModuleDefs.

Section Facts.
  Variables (addrSize lgDataBytes: nat).

  Lemma iom_ModEquiv:
    forall ty1 ty2, ModEquiv ty1 ty2 (iom addrSize lgDataBytes).
  Proof.
    kequiv.
  Qed.
  Hint Resolve iom_ModEquiv.

  Variable n: nat.

  Lemma ioms_ModEquiv:
    forall ty1 ty2, ModEquiv ty1 ty2 (ioms addrSize lgDataBytes n).
  Proof.
    kequiv.
  Qed.
  Hint Resolve ioms_ModEquiv.

  Lemma memAtomic_ModEquiv:
    forall ty1 ty2, ModEquiv ty1 ty2 (memAtomic addrSize lgDataBytes n).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Immediate iom_ModEquiv ioms_ModEquiv memAtomic_ModEquiv.

