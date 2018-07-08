Require Import Bool String List.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct Lib.Reflection Lib.ilist Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate Kami.RefinementFacts.
Require Import Kami.SemFacts Kami.Wf Kami.ParametricSyntax Kami.ParametricEquiv Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo.

Set Implicit Arguments.

Section Middleman.
  Variable inName outName: string.
  Variable addrSize dataBytes: nat.

  Definition RqFromProc := MemTypes.RqFromProc dataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc dataBytes.

  Definition getReq := MethodSig (inName -- "deq")() : Struct RqFromProc.
  Definition setRep := MethodSig (outName -- "enq")(Struct RsToProc) : Void.
  Definition exec := MethodSig "exec"(Struct RqFromProc) : Struct RsToProc.

  Definition processLd {ty} : ActionT ty Void :=
    (Call req <- getReq();
     Assert !#req!RqFromProc@."op";
     Call rep <- exec(#req);
     Call setRep(#rep);
     Retv)%kami_action.

  Definition processSt {ty} : ActionT ty Void :=
    (Call req <- getReq();
     Assert #req!RqFromProc@."op";
     Call rep <- exec(#req);
     Call setRep(#rep);
     Retv)%kami_action.

  Definition mid := MODULE {
    Rule "processLd" := processLd
    with Rule "processSt" := processSt
  }.

  Section MemAtomicWoQInl.
    Variable n: nat.

    Hypothesis HinName: index 0 indexSymbol (inName -- "deq") = None.
    Hypothesis HoutName: index 0 indexSymbol (outName -- "enq") = None.

    Definition getReqI (i: nat) := MethodSig (inName -- "deq" __ i)() : Struct RqFromProc.
    Definition setRepI (i: nat) := MethodSig (outName -- "enq" __ i)(Struct RsToProc) : Void.

    Definition processLdInlGen: GenAction Void Void :=
      fun ty =>
        (Calli req <- { getReq | HinName } ();
           Assert !#req!RqFromProc@."op";
           Read memv <- "mem";
           LET ldval <- #memv@[#req!RqFromProc@."addr"];
           LET rep <- STRUCT { "data" ::= #ldval } :: Struct RsToProc;
           Calli { setRep | HoutName } (#rep);
           Retv)%kami_gen.

    Definition processStInlGen: GenAction Void Void :=
      fun ty =>
        (Calli req <- { getReq | HinName } ();
           Assert #req!RqFromProc@."op";
           Read memv <- "mem";
           Write "mem" <- #memv@[ #req!RqFromProc@."addr" <- #req!RqFromProc@."data" ];
           LET rep <- STRUCT { "data" ::= $$Default } :: Struct RsToProc;
           Calli { setRep | HoutName } (#rep);
           Retv)%kami_gen.

    Definition memAtomicWoQInlM := META {
      Register "mem" : Vector (Data dataBytes) addrSize <- Default
      with Repeat Rule till n by "processLd" := (processLdInlGen _)
      with Repeat Rule till n by "processSt" := (processStInlGen _)
    }.
    
  End MemAtomicWoQInl.
  
End Middleman.

Hint Unfold mid memAtomicWoQInlM : ModuleDefs.
Hint Unfold RqFromProc RsToProc getReq setRep exec
     getReqI setRepI processLdInlGen processStInlGen
     processLd processSt : MethDefs.

Section MemAtomic.
  Variables (addrSize fifoSize dataBytes: nat).

  Variable n: nat.

  Definition minst := memInst n addrSize dataBytes.

  Definition inQ := @simpleFifo "rqFromProc" fifoSize (Struct (RqFromProc addrSize dataBytes)).
  Definition outQ := @simpleFifo "rsToProc" fifoSize (Struct (RsToProc dataBytes)).
  Definition ioQ := ConcatMod inQ outQ.

  Definition ios (i: nat) := duplicate (fun _ => ioQ) i.

  Definition midQ := mid "rqFromProc" "rsToProc" addrSize dataBytes.
  Definition mids (i: nat) := duplicate (fun _ => midQ) i.
  
  Definition iom := ConcatMod ioQ midQ.
  Definition ioms (i: nat) := duplicate (fun _ => iom) i.

  Definition memAtomicWoQ := ConcatMod (mids n) minst.
  Definition memAtomicWoQInl :=
    modFromMeta (memAtomicWoQInlM "rqFromProc" "rsToProc" addrSize dataBytes n
                                  eq_refl eq_refl).
  Definition memAtomic := ConcatMod (ioms n) minst.

End MemAtomic.

Hint Unfold minst inQ outQ ioQ midQ mids iom ioms
     memAtomicWoQInl memAtomicWoQ memAtomic : ModuleDefs.

Section Facts.
  Variables (addrSize fifoSize dataBytes: nat).

  Lemma midQ_ModEquiv:
    ModPhoasWf (midQ addrSize dataBytes).
  Proof.
    kequiv.
  Qed.
  Hint Resolve midQ_ModEquiv.

  Lemma iom_ModEquiv:
    ModPhoasWf (iom addrSize fifoSize dataBytes).
  Proof.
    kequiv.
  Qed.
  Hint Resolve iom_ModEquiv.

  Variable n: nat.

  Lemma mids_ModEquiv:
    ModPhoasWf (mids addrSize dataBytes n).
  Proof.
    kequiv.
  Qed.
  Hint Resolve mids_ModEquiv.

  Lemma ioms_ModEquiv:
    ModPhoasWf (ioms addrSize fifoSize dataBytes n).
  Proof.
    kequiv.
  Qed.
  Hint Resolve ioms_ModEquiv.

  Lemma memAtomicWoQInl_ModEquiv:
    ModPhoasWf (memAtomicWoQInl addrSize dataBytes n).
  Proof.
    kequiv.
  Qed.

  Lemma memAtomicWoQ_ModEquiv:
    ModPhoasWf (memAtomicWoQ addrSize dataBytes n).
  Proof.
    kequiv.
  Qed.

  Lemma memAtomic_ModEquiv:
    ModPhoasWf (memAtomic addrSize fifoSize dataBytes n).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Immediate midQ_ModEquiv iom_ModEquiv
     mids_ModEquiv ioms_ModEquiv
     memAtomicWoQ_ModEquiv memAtomicWoQInl_ModEquiv memAtomic_ModEquiv.

