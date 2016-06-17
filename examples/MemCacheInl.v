Require Import Ex.MemCache Lts.Notations Lts.Syntax Lts.Semantics Lts.SemFacts Lts.Refinement.
Require Import Lts.ParametricEquiv Lts.ParametricInline Lts.ParametricInlineLtac String.
Require Import Lts.ParametricSyntax Lib.CommonTactics Lib.Reflection Lts.Tactics List.

Set Implicit Arguments.

Theorem traceRefines_trans_elem: forall m1 m2 m3: Modules,
                                   (m1 <<== m2) -> (m2 <<== m3) -> (m1 <<== m3).
Proof.
  intros.
  unfold MethsT in *; rewrite idElementwiseId in *.
  eapply traceRefines_trans; eauto.
Qed.

Section MemCacheInl.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable FifoSize: nat.

  Open Scope string.

  Ltac noFilt ltac dm r :=
    match goal with
      | mRef:
          modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize)
                      <<== modFromMeta ?m,
          mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
        ltac m mEquiv dm r;
          match goal with
            | m'Ref:
                modFromMeta ?m <<== modFromMeta ?m',
                m'Equiv: forall ty, MetaModEquiv ty typeUT ?m' |- _ =>
                apply (traceRefines_trans_elem mRef) in m'Ref; clear mRef;
                let newm := fresh in
                pose m' as newm;
                  fold newm in m'Ref;
                  fold newm in m'Equiv;
                  simpl in newm; clear m mEquiv
          end
    end.

  Ltac ggNoFilt dm r := noFilt inlineGenDmGenRule_NoFilt dm r.
  Ltac gsNoFilt dm r := noFilt inlineSinDmGenRule_NoFilt dm r.
  Ltac ssNoFilt dm r := noFilt inlineSinDmSinRule_NoFilt dm r.

  
  
  Ltac simplifyMod :=
    match goal with
      | mRef:
          modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize)
                      <<== modFromMeta ?m,
          mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
        unfold m in mRef, mEquiv;
        clear m;
        repeat
          unfold getGenGenBody, getGenSinBody, getSinSinBody,
                 convNameRec, nameVal, nameRec, isRep, projT1 in mRef, mEquiv;
        repeat autounfold with MethDefs in mRef, mEquiv;
        rewrite signature_eq in mRef, mEquiv; unfold eq_rect in mRef, mEquiv
    end;
    match goal with
      | mRef:
          modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize)
                      <<== modFromMeta ?m,
          mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
        let newm := fresh in
        pose m as newm;
          fold newm in mRef;
          fold newm in mEquiv
    end.
  
  Ltac filt ltac dm r :=
    match goal with
      | mRef:
          modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize)
                      <<== modFromMeta ?m,
          mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
        ltac m mEquiv dm r;
          match goal with
            | m'Ref:
                modFromMeta ?m <<== modFromMeta ?m',
                m'Equiv: forall ty, MetaModEquiv ty typeUT ?m' |- _ =>
                apply (traceRefines_trans_elem mRef) in m'Ref; clear mRef;
                let newm := fresh in
                pose m' as newm;
                  fold newm in m'Ref;
                  fold newm in m'Equiv;
                  simpl in newm; clear m mEquiv
          end
    end; simplifyMod.

  Ltac ggFilt dm r := filt inlineGenDmGenRule_Filt dm r.
  Ltac gsFilt dm r := filt inlineSinDmGenRule_Filt dm r.
  Ltac ssFilt dm r := filt inlineSinDmSinRule_Filt dm r.

  (*
  Local Notation "'LargeMetaModule'" := {| metaRegs := _;
                                           metaRules := _;
                                           metaMeths := _ |}.
   *)
  
  Definition nmemCacheInl':
    {m: MetaModule &
       (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                               LgDataBytes Id FifoSize) <<== modFromMeta m) /\
        forall ty, MetaModEquiv ty typeUT m}.
  Proof.
    pose (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize) as m.

    repeat autounfold with ModuleDefs in m;
    cbv [makeMetaModule getMetaFromSinNat makeSinModule getMetaFromSin
                        sinRegs sinRules sinMeths rulesToRep regsToRep methsToRep
                        convSinToGen concatMetaMod app metaRegs
                        metaRules metaMeths] in m.
    repeat (unfold Indexer.withPrefix, Indexer.prefixSymbol in m; simpl in m).
                                                                                
    (*
    simpl in m; unfold concatMetaMod in m; simpl in m; unfold Indexer.withPrefix in m;
    simpl in m.
     *)
    assert (mRef: modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize)
                                <<== modFromMeta m) by
        (unfold MethsT; rewrite @idElementwiseId; apply traceRefines_refl).
    assert (mEquiv: forall ty, MetaModEquiv ty typeUT m) by kequiv.


    ssNoFilt "read.mline" "hit".
    simplifyMod; ssFilt "read.mline" "deferred".

    ssNoFilt "read.mcs" "hit".
    ssNoFilt "read.mcs" "missByState".
    ssNoFilt "read.mcs" "dwnRq".
    ssNoFilt "read.mcs" "dwnRs".
    simplifyMod; ssFilt "read.mcs" "deferred".

    ssFilt "write.mline" "dwnRs".

    ssNoFilt "write.mcs" "hit".
    ssNoFilt "write.mcs" "dwnRs".
    simplifyMod; ssFilt "write.mcs" "deferred".

    ssNoFilt "enq.toChild" "hit".
    ssNoFilt "enq.toChild" "dwnRq".
    simplifyMod; ssFilt "enq.toChild" "deferred".
    
    ssNoFilt "deq.rqFromChild" "hit".
    ssNoFilt "deq.rqFromChild" "missByState".
    simplifyMod; ssFilt "deq.rqFromChild" "deferred".

    ssFilt "deq.rsFromChild" "dwnRs".
    
    gsFilt "enq.rsFromChild" "rsFromCToP".

    gsFilt "enq.rqFromChild" "rqFromCToP".
    
    gsFilt "deq.toChild" "fromPToC".

    ggNoFilt "read.cs" "ldHit".
    ggNoFilt "read.cs" "stHit".
    ggNoFilt "read.cs" "l1MissByState".
    ggNoFilt "read.cs" "l1MissByLine".
    ggNoFilt "read.cs" "writeback".
    ggNoFilt "read.cs" "upgRq".
    ggNoFilt "read.cs" "upgRs".
    ggNoFilt "read.cs" "ldDeferred".
    ggNoFilt "read.cs" "stDeferred".
    ggNoFilt "read.cs" "drop".
    simplifyMod; ggFilt "read.cs" "pProcess".

    ggNoFilt "read.tag" "ldHit".
    ggNoFilt "read.tag" "stHit".
    ggNoFilt "read.tag" "l1MissByState".
    ggNoFilt "read.tag" "l1MissByLine".
    ggNoFilt "read.tag" "writeback".
    ggNoFilt "read.tag" "drop".
    simplifyMod; ggFilt "read.tag" "pProcess".

    ggNoFilt "read.line" "ldHit".
    ggNoFilt "read.line" "stHit".
    ggNoFilt "read.line" "writeback".
    ggNoFilt "read.line" "ldDeferred".
    ggNoFilt "read.line" "stDeferred".
    ggNoFilt "read.line" "stDeferred".
    simplifyMod; ggFilt "read.line" "pProcess".

    ggNoFilt "write.cs" "writeback".
    ggNoFilt "write.cs" "upgRs".

    simplifyMod; ggFilt "write.cs" "pProcess".

    ggFilt "write.tag" "upgRs".

    ggNoFilt "write.line" "stHit".
    ggNoFilt "write.line" "upgRs".
    simplifyMod; ggFilt "write.line" "stDeferred".

    ggNoFilt "deq.fromParent" "upgRs".
    ggNoFilt "deq.fromParent" "drop".
    simplifyMod; ggFilt "deq.fromParent" "pProcess".
    
    ggNoFilt "enq.rsToProc" "ldHit".
    ggNoFilt "enq.rsToProc" "stHit".
    ggNoFilt "enq.rsToProc" "ldDeferred".
    simplifyMod; ggFilt "enq.rsToProc" "stDeferred".

    ggFilt "enq.rqToParent" "upgRq".

    ggNoFilt "enq.rsToParent" "writeback".
    simplifyMod; ggFilt "enq.rsToParent" "pProcess".

    ggFilt "deq.rqToParent" "rqFromCToP".
    ggFilt "deq.rsToParent" "rsFromCToP".
    ggFilt "enq.fromParent" "fromPToC".

    match goal with
      | mRef:
          modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize)
                      <<== modFromMeta ?m,
          mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
        exact (existT _ m (conj mRef mEquiv))
    end.
  Defined.

  Definition nmemCacheInl := projT1 nmemCacheInl'.

  Theorem nmemCacheInl_refines:
    modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                           LgDataBytes Id FifoSize) <<== modFromMeta nmemCacheInl.
  Proof.
    pose proof (projT2 nmemCacheInl') as sth.
    destruct sth.
    assumption.
  Qed.

  Theorem nmemCacheInl_equiv:
    forall ty, MetaModEquiv ty typeUT nmemCacheInl.
  Proof.
    pose proof (projT2 nmemCacheInl') as sth.
    destruct sth.
    assumption.
  Qed.

  Close Scope string.
End MemCacheInl.
