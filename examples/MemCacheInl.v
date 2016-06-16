Require Import Ex.MemCache Lts.Notations Lts.Syntax Lts.Semantics Lts.SemFacts Lts.Refinement.
Require Import Lts.ParametricEquiv Lts.ParametricInline Lts.ParametricInlineLtac String.
Require Import Lts.ParametricSyntax Lib.CommonTactics Lib.Reflection Lts.Tactics.

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

  Require Import Lts.ParametricInlineLtac.

  Ltac ggNoFilt dm r :=
    match goal with
      | mRef:
          modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize)
                      <<== modFromMeta ?m,
          mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
        inlineGenDmGenRule_NoFilt m mEquiv dm r;
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

  Ltac simplifyMod :=
    match goal with
      | mRef:
          modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize)
                      <<== modFromMeta ?m,
          mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
        unfold m in mRef, mEquiv;
        clear m;
        repeat
          unfold getGenGenBody, convNameRec, nameVal, nameRec, isRep, projT1 in mRef, mEquiv;
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
  
  Ltac ggFilt dm r :=
    match goal with
      | mRef:
          modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize)
                      <<== modFromMeta ?m,
          mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
        inlineGenDmGenRule_Filt m mEquiv dm r;
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

  Local Notation "'LargeMetaModule'" := {| metaRegs := _;
                                           metaRules := _;
                                           metaMeths := _ |}.

  
  Definition nmemCacheInl:
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
    repeat unfold Indexer.withPrefix in m.
    (*
    simpl in m; unfold concatMetaMod in m; simpl in m; unfold Indexer.withPrefix in m;
    simpl in m.
     *)
    assert (mRef: modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize)
                                <<== modFromMeta m) by
        (unfold MethsT; rewrite @idElementwiseId; apply traceRefines_refl).
    assert (mEquiv: forall ty, MetaModEquiv ty typeUT m) by admit.

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


    Require Import List.
    assert (noDupMeth: NoDup (map getMetaMethName (metaMeths H))) by
        (subst; simpl; clear; noDup_tac);
    assert (noDupRule: NoDup (map getMetaRuleName (metaRules H))) by
        (subst; simpl; clear; noDup_tac).

    let dmTriple := eval simpl in (findDm "deq.rqToParent" nil (metaMeths H)) in
        let rTriple := eval simpl in (findR "rqFromCToP" nil (metaRules H)) in
            match dmTriple with
              | Some (?preDm, @RepMeth ?A ?strA ?goodFn ?GenK ?getConstK
                                       ?goodFn2 ?bdm ?dmn ?ls ?noDup, ?sufDm) =>
                match rTriple with
                  | Some (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                          ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                    pose bdm;
                    let m'Ref := fresh in
                    let m'Equiv := fresh in
                    pose proof (@inlineGenGenDmToRule_traceRefines_NoFilt
                                  H A strA goodFn GenK getConstK goodFn2) (*
                                  bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                  sufR eq_refl noDupMeth noDupRule);
                      pose proof (@inlineGenGenDmToRule_ModEquiv_NoFilt
                                    H H8 A strA goodFn GenK getConstK goodFn2
                                    bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                    sufR eq_refl noDupMeth noDupRule);
                    clear noDupMeth noDupRule *)
                                  
                end
            end.
    
    Unset Printing Notations.
    simpl.
    ggNoFilt "deq.rqToParent" "rqFromCToP".

    ggFilt "de"

    unfold H in H1, H2.
    unfold getGenGenBody, convNameRec, nameVal, nameRec, isRep, projT1 in H1, H2.
    rewrite signature_eq in H2.
    rewrite signature_eq in H1.
    clear H.


    Unset Printing Notations.
    unfold getGenGenBody, convNameRec, nameVal,
    nameRec, isRep, projT1 in H;
      repeat autounfold with MethDefs in H.
    match H with
      | context[SignatureT_dec ?s ?s] =>
        rewrite (signature_eq s s) in H;
          unfold eq_rect in H
    end.
      ggNoFilt "read.cs" "stHit".
    ggNoFilt "read.cs" "l1MissByState".
    ggNoFilt "read.cs" "l1MissByLine".
    ggNoFilt "read.cs" "writeback".
    ggNoFilt "read.cs" "upgRq".
    ggNoFilt "read.cs" "upgRs".
    ggNoFilt "read.cs" "ldDeferred".
    ggNoFilt "read.cs" "stDeferred".
    ggNoFilt "read.cs" "drop".
    Stop Profiling.  (*

    Show Profile.
    ggFilt "read.cs" "pProcess".
    ggNoFilt "read.tag" "ldHit".
    ggNoFilt "read.tag" "stHit".
    ggNoFilt "read.tag" "l1MissByState".
    ggNoFilt "read.tag" "l1MissByLine".
    ggNoFilt "read.tag" "writeback".
    ggNoFilt "read.tag" "drop".

    let noDupMeth := fresh in
  let noDupRule := fresh in
  assert (noDupMeth: NoDup (map getMetaMethName (metaMeths H))) by
      (subst; simpl; clear; noDup_tac);
    assert (noDupRule: NoDup (map getMetaRuleName (metaRules H))) by
      (subst; simpl; clear; noDup_tac);
    let dmTriple := eval simpl in (findDm "read.tag" nil (metaMeths H)) in
        let rTriple := eval simpl in (findR "pProcess" nil (metaRules H)) in
            match dmTriple with
              | Some (?preDm, @RepMeth ?A ?strA ?goodFn ?GenK ?getConstK
                                       ?goodFn2 ?bdm ?dmn ?ls ?noDup, ?sufDm) =>
                match rTriple with
                  | Some (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                          ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                    let K1 := fresh in
                    let K2 := fresh in
                    let K3 := fresh in
                    assert
                      (K1:
                         forall r',
                           In r' (preR ++ sufR) ->
                           match r' with
                             | OneRule _ _ => true
                             | RepRule _ _ _ _ _ _ bgenB _ _ _ =>
                               noCallDmSigGenA (bgenB typeUT)
                                               {| isRep := true; nameRec := dmn |}
                                               (projT1 bdm)
                           end = true) by
                        (intro;
                         apply boolListReflection with
                         (f := (fun r' =>
                                  match r' with
                                    | OneRule _ _ => true
                                    | RepRule _ _ _ _ _ _ bgenB _ _ _ =>
                                      noCallDmSigGenA (bgenB typeUT)
                                                      {| isRep := true; nameRec := dmn |}
                                                      (projT1 bdm)
                                  end));
                         repeat
                           (unfold getGenGenBody, convNameRec, nameVal, nameRec, isRep, projT1;
                            repeat autounfold with MethDefs;
                            
                            repeat match goal with
                                     | [ |- context[SignatureT_dec ?s ?s] ] =>
                                       rewrite (signature_eq s); unfold eq_rect
                                   end; simpl);
                            apply eq_refl
                          );
                      assert
                        (K2:
                           forall dm',
                             In dm' (metaMeths H) ->
                             match dm' with
                               | OneMeth _ _ => true
                               | RepMeth _ _ _ _ _ _ bgenB _ _ _ =>
                                 noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                 {| isRep := true; nameRec := dmn |}
                                                 (projT1 bdm)
                             end = true) by
                        (intro;
                         apply boolListReflection with
                         (f := (fun dm' =>
                                  match dm' with
                                    | OneMeth _ _ => true
                                    | RepMeth _ _ _ _ _ _ bgenB _ _ _ =>
                                      noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                      {| isRep := true; nameRec := dmn |}
                                                      (projT1 bdm)
                                  end)); apply eq_refl);
                      assert
                        (K3: exists call : NameRecIdx,
                               In call (getCallsGenA (bdr typeUT)) /\
                               nameVal (nameRec call) = nameVal dmn /\ isRep call = true)
                        by
                          (eexists {| isRep := true;
                                      nameRec := {| nameVal := nameVal dmn;
                                                    goodName := _ |} |};
                           split; [
                             
                             repeat (unfold getGenGenBody, convNameRec, nameVal, nameRec, isRep, projT1;
                             repeat autounfold with MethDefs;
                             
                             repeat match goal with
                                      | [ |- context[SignatureT_dec ?s ?s] ] =>
                                        rewrite (signature_eq s); unfold eq_rect
                                    end; simpl)
                             ; tauto | split; reflexivity]);
                      pose proof (@inlineGenGenDmToRule_traceRefines_Filt'
                                    H H5 A strA goodFn GenK getConstK goodFn2
                                    bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                    sufR eq_refl noDupMeth noDupRule K1 K2 K3);
                        pose proof (@inlineGenGenDmToRule_ModEquiv_Filt'
                                      H H5 A strA goodFn GenK getConstK goodFn2
                                      bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                      sufR eq_refl noDupMeth noDupRule K2);
                        clear noDupMeth noDupRule K1 K2 K3
                end
            end.
    eexists {| isRep := true;
               nameRec := {| nameVal := "read.tag";
                             goodName := _ |} |}.
    split; [| split; reflexivity].
    unfold getGenGenBody, convNameRec, nameVal, nameRec, isRep, projT1;
      repeat autounfold with MethDefs;
      
      repeat match goal with
               | [ |- context[SignatureT_dec ?s ?s] ] =>
                 rewrite (signature_eq s); unfold eq_rect
             end; simpl. tauto.
    unfold getGenGenBody, convNameRec.    simpl.
    simpl.
    intro;
      eapply boolListReflection with
      (f := (fun r' =>
               match r' with
                 | OneRule _ _ => true
                 | RepRule _ _ _ _ _ _ bgenB _ _ _ =>
                   noCallDmSigGenA (bgenB typeUT)
                                   {| isRep := true; nameRec := _ |}
                                   (projT1 _)
               end)).
    repeat (unfold getGenGenBody, convNameRec, nameVal, nameRec, isRep, projT1;
      repeat autounfold with MethDefs;
      repeat match goal with
               | [ |- context[SignatureT_dec ?s ?s] ] =>
                 rewrite (signature_eq s); unfold eq_rect
             end; simpl);
      reflexivity.

    eexists {| isRep := true;
               nameRec := {| nameVal := nameVal _;
                             goodName := _ |} |}.
      split; [simpl; tauto | split; reflexivity]
               apply eq_refl.
                         
    
    inlineGenDmGenRule_Filt H H5 "read.tag" "pProcess".

    ggFilt "read.tag" "pProcess".
    ggNoFilt "read.line" "ldHit".
    ggNoFilt "read.line" "stHit".
    ggNoFilt "read.cs" "writeback".
    ggNoFilt "read.cs" "ldDeferred".
    ggNoFilt "read.cs" "stDeferred".
    ggFilt "read.cs" "pProcess".

    Stop Profiling.
    Show Profile.

inlineGenDmGenRule_Filt H0 H5 "read.cs" "pProcess".
intro.
apply boolListReflection with (f := (fun dm' =>
                                       match dm' with
                                         | OneMeth _ _ => true
                                         | RepMeth _ _ _ _ _ _ bgenB _ _ _ =>
                                           noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                           {| isRep := true; nameRec := dmn |}
                                                           (projT1 bdm)
                                       end)).
                                     .
clear; intros; dest_in; simpl.
unfold getGenGenBody, convNameRec, nameVal, nameRec, isRep, projT1;
  repeat autounfold with MethDefs.
match goal with
  | [ |- context[SignatureT_dec ?s ?s] ] =>
    rewrite (signature_eq s); unfold eq_rect
end.
reflexivity.

unfold getGenGenBody.
unfold convNameRec.
unfold nameVal.
unfold nameRec.
unfold isRep.
unfold projT1.
unfold StringEq.string_eq.
reflexivity.
    let isIn := fresh in
    clear; intros ? isIn;
    repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
    exfalso; apply isIn.
               destruct isIn.
    
                        (*(let isIn := fresh in
                         intros ? ? ? ? ? ? ? ? ? ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn); *)

    
    intros ? ? ? ? ? ? ? ? ? ? isIn; simpl in isIn.
    destruct isIn as [murali | isIn].
    
    inversion murali.
    injection murali as [_ _ _ _ bgen _ _].
    inversion murali; subst; clear murali.
    simpl.
    inv murali.
    [subst; reflexivity | ].
    repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]).
    repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]).
    destruct isIn.
                    asser
    clear m.
    match goal with
      | m'Ref:
          modFromMeta _ <<== modFromMeta ?m',
          m'Equiv: forall ty, MetaModEquiv ty typeUT ?m' |- _ =>
        let newm := fresh in
        pose m' as newm;
          fold newm in m'Ref;
          fold newm in m'Equiv;
          simpl in newm;
          clear m
    end.
    clear m.
    inlineGenDmGenRule_NoFilt m mEquiv "read.cs" "ldHit".
    Reset Profile.
    Start Profiling.

    let noDupMeth := fresh in
  let noDupRule := fresh in
  assert (noDupMeth: NoDup (map getMetaMethName (metaMeths m))) by
    (subst; simpl; clear; noDup_tac);
    assert (noDupRule: NoDup (map getMetaRuleName (metaRules m))) by
      (subst; simpl; clear; noDup_tac);
    let dmTriple := eval simpl in (findDm "read.cs" nil (metaMeths m)) in
        let rTriple := eval simpl in (findR "ldHit" nil (metaRules m)) in
            match dmTriple with
              | Some (?preDm, @RepMeth ?A ?strA ?goodFn ?GenK ?getConstK
                                       ?goodFn2 ?bdm ?dmn ?ls ?noDup, ?sufDm) =>
                match rTriple with
                  | Some (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                          ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                    let m'Ref := fresh in
                    let m'Equiv := fresh in
                    pose proof (@inlineGenGenDmToRule_traceRefines_NoFilt
                                  m A strA goodFn GenK getConstK goodFn2
                                  bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                  sufR eq_refl noDupMeth noDupRule) as m'Ref;
                      pose proof (@inlineGenGenDmToRule_ModEquiv_NoFilt
                                    m mEquiv A strA goodFn GenK getConstK goodFn2
                                    bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                    sufR eq_refl noDupMeth noDupRule) as m'Equiv;
                      clear noDupMeth noDupRule
                end
            end.

    
    inlineGenDmGenRule_NoFilt m mEquiv "read.cs" "ldHit".
    match goal with
      | mRef:
          modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize)
                      <<== modFromMeta ?m,
          mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
        inlineGenDmGenRule_NoFilt m mEquiv dm r;
          match goal with
            | m'Ref:
                modFromMeta ?m <<== modFromMeta ?m',
              m'Equiv: forall ty, MetaModEquiv ty typeUT ?m' |- _ =>
              pose proof (traceRefines_trans_elem mRef m'Ref); clear mRef m'Ref;
              pose m' as newm;
              fold newm in m'Ref;
              fold newm in m'Equiv;
              clear m
          end;
          clear mEquiv
    end.
    
    ggNoFilt "read.cs" "ldHit".

    ggNoFilt "read.cs" "stHit".


    ggNoFilt "read.cs" "upgRq".

    Stop Profiling.
    Show Profile.

    Reset Profile.
    Start Profiling.
    ggNoFilt "read.cs" "upgRs".
    Stop Profiling.
    Show Profile.


    ggNoFilt "read.cs" "l1MissByState".

    Stop Profiling.
    Show Profile.

    Reset Profile.
    Start Profiling.
    
    ggNoFilt mod modRef modEquiv "read.cs" "l1MissByLine".
    Stop Profiling.
    Show Profile.
    
    ggNoFilt mod modRef modEquiv "read.cs" "ldDeferred".
    ggNoFilt mod modRef modEquiv "read.cs" "stDeferred".
    ggNoFilt mod modRef modEquiv "read.cs" "drop".
    ggNoFilt mod modRef modEquiv "read.cs" "writeback".
    ggFilt mod modRef modEquiv "read.cs" "pProcess".
    
    exact (existT _ mod (conj modRef modEquiv)).
    admit.
  Defined.

  Close Scope string.

  *)
End MemCacheInl.
