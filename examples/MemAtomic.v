Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate Kami.RefinementFacts.
Require Import Kami.Wf Kami.ParametricSyntax Kami.ParametricEquiv Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo.

Set Implicit Arguments.

Section Middleman.
  Variable inName outName: string.
  Variable addrSize lgDataBytes: nat.

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

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

    Definition memAtomicWoQInlM := META {
      Register "mem" : Vector (Data lgDataBytes) addrSize <- Default

      with Repeat Rule till n by "processLd" :=
        Calli req <- { getReq | HinName } ();
        Assert !#req!RqFromProc@."op";
        Read memv <- "mem";
        LET ldval <- #memv@[#req!RqFromProc@."addr"];
        LET rep <- STRUCT { "data" ::= #ldval } :: Struct RsToProc;
        Calli { setRep | HoutName } (#rep);
        Retv

      with Repeat Rule till n by "processSt" :=
        Calli req <- { getReq | HinName } ();
        Assert #req!RqFromProc@."op";
        Read memv <- "mem";
        Write "mem" <- #memv@[ #req!RqFromProc@."addr" <- #req!RqFromProc@."data" ];
        LET rep <- STRUCT { "data" ::= $$Default } :: Struct RsToProc;
        Calli { setRep | HoutName } (#rep);
        Retv
    }.
    
  End MemAtomicWoQInl.
  
End Middleman.

Hint Unfold mid memAtomicWoQInlM : ModuleDefs.
Hint Unfold RqFromProc RsToProc getReq setRep exec processLd processSt : MethDefs.

Section MemAtomic.
  Variables (addrSize fifoSize lgDataBytes: nat).

  Variable n: nat.

  Definition minst := memInst n addrSize lgDataBytes.

  Definition inQ := @simpleFifo "rqFromProc" fifoSize (Struct (RqFromProc addrSize lgDataBytes)).
  Definition outQ := @simpleFifo "rsToProc" fifoSize (Struct (RsToProc lgDataBytes)).
  Definition ioQ := ConcatMod inQ outQ.

  Definition ios (i: nat) := duplicate ioQ i.

  Definition midQ := mid "rqFromProc" "rsToProc" addrSize lgDataBytes.
  Definition mids (i: nat) := duplicate midQ i.
  
  Definition iom := ConcatMod ioQ midQ.
  Definition ioms (i: nat) := duplicate iom i.

  Definition memAtomicWoQ := ConcatMod (mids n) minst.
  Definition memAtomicWoQInl :=
    modFromMeta (memAtomicWoQInlM "rqFromProc" "rsToProc" addrSize lgDataBytes n
                                  eq_refl eq_refl).
  Definition memAtomic := ConcatMod (ioms n) minst.

End MemAtomic.

Hint Unfold minst inQ outQ ioQ midQ mids iom ioms
     memAtomicWoQInl memAtomicWoQ memAtomic : ModuleDefs.

Section Facts.
  Variables (addrSize fifoSize lgDataBytes: nat).

  Lemma midQ_ModEquiv:
    ModPhoasWf (midQ addrSize lgDataBytes).
  Proof.
    kequiv.
  Qed.
  Hint Resolve midQ_ModEquiv.

  Lemma iom_ModEquiv:
    ModPhoasWf (iom addrSize fifoSize lgDataBytes).
  Proof.
    kequiv.
  Qed.
  Hint Resolve iom_ModEquiv.

  Variable n: nat.

  Lemma mids_ModEquiv:
    ModPhoasWf (mids addrSize lgDataBytes n).
  Proof.
    kequiv.
  Qed.
  Hint Resolve mids_ModEquiv.

  Lemma ioms_ModEquiv:
    ModPhoasWf (ioms addrSize fifoSize lgDataBytes n).
  Proof.
    kequiv.
  Qed.
  Hint Resolve ioms_ModEquiv.

  Lemma memAtomicWoQInl_ModEquiv:
    ModPhoasWf (memAtomicWoQInl addrSize lgDataBytes n).
  Proof.
    kequiv.
  Qed.

  Lemma memAtomicWoQ_ModEquiv:
    ModPhoasWf (memAtomicWoQ addrSize lgDataBytes n).
  Proof.
    kequiv.
  Qed.

  Lemma memAtomic_ModEquiv:
    ModPhoasWf (memAtomic addrSize fifoSize lgDataBytes n).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Immediate midQ_ModEquiv iom_ModEquiv
     mids_ModEquiv ioms_ModEquiv
     memAtomicWoQ_ModEquiv memAtomicWoQInl_ModEquiv memAtomic_ModEquiv.

Section MemAtomicWoQ.
  Variables (addrSize fifoSize lgDataBytes: nat).
  Variable n: nat.

  Lemma ios_memAtomicWoQ_memAtomic:
    ((ios addrSize fifoSize lgDataBytes n ++ memAtomicWoQ addrSize lgDataBytes n)%kami)
      <<== (memAtomic addrSize fifoSize lgDataBytes n).
  Proof.
    unfold memAtomic, memAtomicWoQ.
    krewrite assoc left.
    kmodular_sim_l.
    - apply duplicate_regs_ConcatMod; [kequiv|kequiv|kvr|kvr| |]; auto.
    - apply duplicate_rules_ConcatMod; [kequiv|kequiv|kvr|kvr| |]; auto.
    - apply duplicate_defs_ConcatMod; [kequiv|kequiv|kvr|kvr| |]; auto.
  Qed.

End MemAtomicWoQ.

Require Import Lib.FMap Lib.Reflection.

Section MemAtomicWoQInl.
  Variables addrSize lgDataBytes: nat.
  Variable n: nat.

  Definition memAtomicWoQ_regMap (r: RegsT) := r.
  Definition memAtomicWoQ_ruleMap (o: RegsT) (rn: string) := Some rn.

  Lemma memAtomicWoQInl_refines_memAtomicWoQ:
    memAtomicWoQInl addrSize lgDataBytes n <<== memAtomicWoQ addrSize lgDataBytes n.
  Proof.
    apply stepRefinement with (ruleMap:= memAtomicWoQ_ruleMap) (theta:= memAtomicWoQ_regMap);
      [admit|].

    intros; clear H.
    apply SemFacts.step_zero in H0; [|reflexivity]; dest.
    destruct l as [ann ds cs]; simpl in *; subst; cbn.
    destruct ann as [r|].

    - inv H0.
      + exists (M.empty _); cbn; split; auto.
        admit. (* empty-step *)

      + unfold memAtomicWoQ_ruleMap.
        admit.

    - inv H0; exists (M.empty _); cbn; split; auto.
      admit. (* empty-step *)
  Admitted.

End MemAtomicWoQInl.
  