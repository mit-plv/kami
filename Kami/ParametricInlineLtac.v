Require Import Kami.ParametricInline List Kami.ParametricSyntax String Kami.Syntax Kami.Semantics
        Lib.CommonTactics Lib.Reflection Kami.Tactics Kami.ParametricEquiv Kami.Notations
        Kami.RefinementFacts.

Set Asymmetric Patterns.

Ltac app_ltac ls x :=
  match ls with
    | ?y :: ?ys =>
      let ns := app_ltac ys x in
      constr:(y :: ns)
    | nil => constr:(x :: nil)
  end.

Ltac find dm pre ls :=
  match ls with
    | ?x :: ?xs =>
      match x with
        | context[dm] =>
          constr:((pre, x, xs))
        | _ =>
          let y := app_ltac pre x in
          find dm y xs
      end
  end.

Ltac inlineGenDmGenRule_NoFilt dm r :=
  match goal with
    | m := {| metaRegs := _; metaRules := ?rls; metaMeths := ?mts |},
           mEquiv: forall ty, MetaModEquiv ty typeUT _ |- _ =>
           let noDupMeth := fresh in
           let noDupRule := fresh in
           assert (noDupMeth: NoDup (map getMetaMethName mts)) by
               ( (subst; simpl; clear; noDup_tac));
             assert (noDupRule: NoDup (map getMetaRuleName rls)) by
               ( (subst; simpl; clear; noDup_tac));
             let dmTriple := find dm (@nil MetaMeth) mts in
             let rTriple := find r (@nil MetaRule) rls in
             match dmTriple with
               | (?preDm, @RepMeth ?A ?strA ?goodFn ?GenK ?getConstK
                                   ?goodFn2 ?bdm ?dmn ?ls ?noDup, ?sufDm) =>
                 match rTriple with
                   | (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                      ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                     pose proof (@inlineGenGenDmToRule_traceRefines_NoFilt
                                   m A strA goodFn GenK getConstK goodFn2
                                   bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                   sufR eq_refl noDupMeth noDupRule);
                       pose proof (@inlineGenGenDmToRule_ModEquiv_NoFilt
                                     m mEquiv A strA goodFn GenK getConstK goodFn2
                                     bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                     sufR eq_refl noDupMeth noDupRule);
                       clear noDupMeth noDupRule
                 end
             end
  end.

Ltac inlineGenDmGenRule_Filt dm r :=
  match goal with
    | m := {| metaRegs := _; metaRules := ?rls; metaMeths := ?mts |},        
           mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
           let noDupMeth := fresh in
           let noDupRule := fresh in
           assert (noDupMeth: NoDup (map getMetaMethName mts)) by
               ( (subst; simpl; clear; noDup_tac));
             assert (noDupRule: NoDup (map getMetaRuleName rls)) by
               ( (subst; simpl; clear; noDup_tac));
             let dmTriple := find dm (@nil MetaMeth) mts in
             let rTriple := find r (@nil MetaRule) rls in
             match dmTriple with
               | (?preDm, @RepMeth ?A ?strA ?goodFn ?GenK ?getConstK
                                   ?goodFn2 ?bdm ?dmn ?ls ?noDup, ?sufDm) =>
                 match rTriple with
                   | (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                      ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                     let H3 := fresh in
                     let H4 := fresh in
                     let H5 := fresh in
                     assert
                       (H3:
                          forall r',
                            In r' (preR ++ sufR) ->
                            match r' with
                              | OneRule _ _ => true
                              | RepRule _ _ _ _ _ _ bgenB _ _ _ =>
                                noCallDmSigGenA (bgenB typeUT)
                                                {| isRep := true; nameRec := dmn |}
                                                (projT1 bdm)
                            end = true) by
                         ( (intro;
                                    apply boolListReflection with
                                    (f := (fun r' =>
                                             match r' with
                                               | OneRule _ _ => true
                                               | RepRule _ _ _ _ _ _ bgenB _ _ _ =>
                                                 noCallDmSigGenA (bgenB typeUT)
                                                                 {| isRep := true; nameRec := dmn |}
                                                                 (projT1 bdm)
                                             end)); apply eq_refl));
                       assert
                         (H4:
                            forall dm',
                              In dm' (metaMeths m) ->
                              match dm' with
                                | OneMeth _ _ => true
                                | RepMeth _ _ _ _ _ _ bgenB _ _ _ =>
                                  noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                  {| isRep := true; nameRec := dmn |}
                                                  (projT1 bdm)
                              end = true) by
                         ( (intro;
                                    apply boolListReflection with
                                    (f := (fun dm' =>
                                             match dm' with
                                               | OneMeth _ _ => true
                                               | RepMeth _ _ _ _ _ _ bgenB _ _ _ =>
                                                 noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                                 {| isRep := true; nameRec := dmn |}
                                                                 (projT1 bdm)
                                             end)); apply eq_refl));
                       assert
                         (H5: exists call : NameRecIdx,
                                In call (getCallsGenA (bdr typeUT)) /\
                                nameVal (nameRec call) = nameVal dmn /\ isRep call = true) by
                           ( (eexists {| isRep := true;
                                                 nameRec := {| nameVal := nameVal dmn;
                                                               goodName := _ |} |};
                                      split; [
                                        simpl; tauto | split; reflexivity]));
                       pose proof (@inlineGenGenDmToRule_traceRefines_Filt'
                                     m mEquiv A strA goodFn GenK getConstK goodFn2
                                     bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                     sufR eq_refl noDupMeth noDupRule H3 H4 H5);
                       pose proof (@inlineGenGenDmToRule_ModEquiv_Filt'
                                     m mEquiv A strA goodFn GenK getConstK goodFn2
                                     bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                     sufR eq_refl noDupMeth noDupRule H4);
                       clear noDupMeth noDupRule H3 H4 H5
                 end
             end
  end.

Ltac inlineSinDmGenRule_NoFilt dm r :=
  match goal with
    | m := {| metaRegs := _; metaRules := ?rls; metaMeths := ?mts |},        
           mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
           let noDupMeth := fresh in
           let noDupRule := fresh in
           assert (noDupMeth: NoDup (map getMetaMethName mts)) by
               ( (subst; simpl; clear; noDup_tac));
             assert (noDupRule: NoDup (map getMetaRuleName rls)) by
               ( (subst; simpl; clear; noDup_tac));
             let dmTriple := find dm (@nil MetaMeth) mts in
             let rTriple := find r (@nil MetaRule) rls in
             match dmTriple with
               | (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
                 match rTriple with
                   | (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                      ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                     pose proof (@inlineGenSinDmToRule_traceRefines_NoFilt
                                   m A strA goodFn GenK getConstK goodFn2
                                   bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                   sufR eq_refl noDupMeth noDupRule);
                       pose proof (@inlineGenSinDmToRule_ModEquiv_NoFilt
                                     m mEquiv A strA goodFn GenK getConstK goodFn2
                                     bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                     sufR eq_refl noDupMeth noDupRule);
                       clear noDupMeth noDupRule
                 end
             end
  end.

Theorem notNilNatList: forall n,
                         getNatListToN (Word.wordToNat (Word.wones n)) <> nil.
Proof.
  induction n; simpl in *; unfold not; intros; discriminate.
Qed.

Ltac inlineSinDmGenRule_Filt dm r :=
  match goal with
    | m := {| metaRegs := _; metaRules := ?rls; metaMeths := ?mts |},        
           mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
           let noDupMeth := fresh in
           let noDupRule := fresh in
           assert (noDupMeth: NoDup (map getMetaMethName mts)) by
               ( (subst; simpl; clear; noDup_tac));
             assert (noDupRule: NoDup (map getMetaRuleName rls)) by
               ( (subst; simpl; clear; noDup_tac));
             let dmTriple := find dm (@nil MetaMeth) mts in
             let rTriple := find r (@nil MetaRule) rls in
             match dmTriple with
               | (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
                 match rTriple with
                   | (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                      ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                     let H3 := fresh in
                     let H4 := fresh in
                     let H5 := fresh in
                     let H6 := fresh in
                     assert
                       (H3:
                          forall r',
                            In r' (preR ++ sufR) ->
                            match r' with
                              | OneRule bgenB _ =>
                                noCallDmSigSinA (bgenB typeUT) dmn (projT1 bdm)
                              | RepRule _ _ _ _ _ _ bgenB _ _ _ =>
                                noCallDmSigGenA (bgenB typeUT)
                                                {| isRep := false; nameRec := dmn |}
                                                (projT1 bdm)
                            end = true) by
                         ( (intro;
                                    apply boolListReflection with
                                    (f := (fun r' =>
                                             match r' with
                                               | OneRule bgenB _ =>
                                                 noCallDmSigSinA (bgenB typeUT) dmn (projT1 bdm)
                                               | RepRule _ _ _ _ _ _ bgenB _ _ _ =>
                                                 noCallDmSigGenA (bgenB typeUT)
                                                                 {| isRep := false;
                                                                    nameRec := dmn |}
                                                                 (projT1 bdm)
                                             end)); apply eq_refl));
                       assert
                         (H4:
                            forall dm',
                              In dm' (metaMeths m) ->
                              match dm' with
                                | OneMeth bgenB _ =>
                                  noCallDmSigSinA (projT2 bgenB typeUT tt) dmn (projT1 bdm)
                                | RepMeth _ _ _ _ _ _ bgenB _ _ _ =>
                                  noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                  {| isRep := false; nameRec := dmn |}
                                                  (projT1 bdm)
                              end = true) by
                         ( (intro;
                                    apply boolListReflection with
                                    (f := (fun dm' =>
                                             match dm' with
                                               | OneMeth bgenB _ =>
                                                 noCallDmSigSinA (projT2 bgenB typeUT tt)
                                                                 dmn (projT1 bdm)
                                               | RepMeth _ _ _ _ _ _ bgenB _ _ _ =>
                                                 noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                                 {| isRep := false;
                                                                    nameRec := dmn |}
                                                                 (projT1 bdm)
                                             end)); apply eq_refl));
                       assert
                         (H5: exists call : NameRecIdx,
                                In call (getCallsGenA (bdr typeUT)) /\
                                nameVal (nameRec call) = nameVal dmn /\ isRep call = false) by
                           ( (eexists {| isRep := false;
                                                 nameRec := {| nameVal := nameVal dmn;
                                                               goodName := _ |} |};
                                      split; [
                                        simpl; tauto | split; reflexivity]));
                       assert
                         (H6: ls <> nil) by ( (apply notNilNatList; auto));
                       pose proof (@inlineGenSinDmToRule_traceRefines_Filt'
                                     m mEquiv A strA goodFn GenK getConstK goodFn2
                                     bdm dmn preDm sufDm ls H6 noDup eq_refl bdr rn preR
                                     sufR eq_refl noDupMeth noDupRule H3 H4 H5);
                       pose proof (@inlineGenSinDmToRule_ModEquiv_Filt'
                                     m mEquiv A strA goodFn GenK getConstK goodFn2
                                     bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                     sufR eq_refl noDupMeth noDupRule H4);
                       clear noDupMeth noDupRule H3 H4 H5 H6
                 end
             end
  end.

Ltac inlineSinDmSinRule_NoFilt dm r :=
  match goal with
    | m := {| metaRegs := _; metaRules := ?rls; metaMeths := ?mts |},        
           mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
           let noDupMeth := fresh in
           let noDupRule := fresh in
           assert (noDupMeth: NoDup (map getMetaMethName mts)) by
               ( (subst; simpl; clear; noDup_tac));
             assert (noDupRule: NoDup (map getMetaRuleName rls)) by
               ( (subst; simpl; clear; noDup_tac));
             let dmTriple := find dm (@nil MetaMeth) mts in
             let rTriple := find r (@nil MetaRule) rls in
             match dmTriple with
               | (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
                 match rTriple with
                   | (?preR, @OneRule ?bdr ?rn, ?sufR) =>
                     pose proof (@inlineSinSinDmToRule_traceRefines_NoFilt
                                   m
                                   bdm dmn preDm sufDm eq_refl bdr rn preR
                                   sufR eq_refl noDupMeth noDupRule);
                       pose proof (@inlineSinSinDmToRule_ModEquiv_NoFilt
                                     m mEquiv
                                     bdm dmn preDm sufDm eq_refl bdr rn preR
                                     sufR eq_refl noDupMeth noDupRule);
                       clear noDupMeth noDupRule
                 end
             end
  end.

Ltac inlineSinDmSinRule_Filt dm r :=
  match goal with
    | m := {| metaRegs := _; metaRules := ?rls; metaMeths := ?mts |},        
           mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
           let noDupMeth := fresh in
           let noDupRule := fresh in
           assert (noDupMeth: NoDup (map getMetaMethName mts)) by
               ( (subst; simpl; clear; noDup_tac));
             assert (noDupRule: NoDup (map getMetaRuleName rls)) by
               ( (subst; simpl; clear; noDup_tac));
             let dmTriple := find dm (@nil MetaMeth) mts in
             let rTriple := find r (@nil MetaRule) rls in
             match dmTriple with
               | (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
                 match rTriple with
                   | (?preR, @OneRule ?bdr ?rn, ?sufR) =>
                     let H3 := fresh in
                     let H4 := fresh in
                     let H5 := fresh in
                     assert
                       (H3:
                          forall r',
                            In r' (preR ++ sufR) ->
                            match r' with
                              | OneRule bgenB _ =>
                                noCallDmSigSinA (bgenB typeUT) dmn (projT1 bdm)
                              | RepRule _ _ _ _ _ _ bgenB _ _ _ =>
                                noCallDmSigGenA (bgenB typeUT)
                                                {| isRep := false; nameRec := dmn |}
                                                (projT1 bdm)
                            end = true) by
                         ( (intro;
                                    apply boolListReflection with
                                    (f := (fun r' =>
                                             match r' with
                                               | OneRule bgenB _ =>
                                                 noCallDmSigSinA (bgenB typeUT) dmn (projT1 bdm)
                                               | RepRule _ _ _ _ _ _ bgenB _ _ _ =>
                                                 noCallDmSigGenA (bgenB typeUT)
                                                                 {| isRep := false;
                                                                    nameRec := dmn |}
                                                                 (projT1 bdm)
                                             end)); apply eq_refl));
                       assert
                         (H4:
                            forall dm',
                              In dm' (metaMeths m) ->
                              match dm' with
                                | OneMeth bgenB _ =>
                                  noCallDmSigSinA (projT2 bgenB typeUT tt) dmn (projT1 bdm)
                                | RepMeth _ _ _ _ _ _ bgenB _ _ _ =>
                                  noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                  {| isRep := false; nameRec := dmn |}
                                                  (projT1 bdm)
                              end = true) by
                         ( (intro;
                                    apply boolListReflection with
                                    (f := (fun dm' =>
                                             match dm' with
                                               | OneMeth bgenB _ =>
                                                 noCallDmSigSinA (projT2 bgenB typeUT tt)
                                                                 dmn (projT1 bdm)
                                               | RepMeth _ _ _ _ _ _ bgenB _ _ _ =>
                                                 noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                                 {| isRep := false;
                                                                    nameRec := dmn |}
                                                                 (projT1 bdm)
                                             end)); apply eq_refl));
                       assert
                         (H5: exists call : NameRec,
                                In call (getCallsSinA (bdr typeUT)) /\
                                nameVal call = nameVal dmn) by
                           ( (eexists {| nameVal := nameVal dmn;
                                                 goodName := _ |};
                                      split; [
                                        simpl; tauto | reflexivity]));
                       pose proof (@inlineSinSinDmToRule_traceRefines_Filt'
                                     m mEquiv
                                     bdm dmn preDm sufDm eq_refl bdr rn preR
                                     sufR eq_refl noDupMeth noDupRule H3 H4 H5);
                       pose proof (@inlineSinSinDmToRule_ModEquiv_Filt'
                                     m mEquiv
                                     bdm dmn preDm sufDm eq_refl bdr rn preR
                                     sufR eq_refl noDupMeth noDupRule H4);
                       clear noDupMeth noDupRule H3 H4 H5
                 end
             end
  end.


Ltac commonCbv H :=
    cbv [inlineGenGenDm
           inlineGenSinDm inlineSinSinDm
           getGenGenBody
           getGenSinBody getSinSinBody
           appendGenGenAction appendSinSinAction appendSinGenAction
           convNameRec nameVal nameRec isRep projT1 projT2
           StringEq.string_eq StringEq.ascii_eq Bool.eqb andb
           eq_rect ret arg
           String.append
           fullType
           Lib.VectorFacts.Vector_find
           makeMetaModule
           getMetaFromSinNat makeSinModule getMetaFromSin
           sinRegs sinRules sinMeths rulesToRep regsToRep methsToRep
           convSinToGen concatMetaMod app metaRegs
           metaRules metaMeths
           flattenMeta
           metaModulesRegs metaModulesRules metaModulesMeths
           sinRegToMetaReg sinRuleToMetaRule sinMethToMetaMeth sinModuleToMetaModule
        ] in H.

Ltac simplMod whichCbv :=
  match goal with
    | m :=
  ?modM: MetaModule |- _ =>
  let mEq := fresh "mEq" in
  let HeqmEq := fresh "HeqmEq" in
  remember m as mEq;
    unfold m in HeqmEq;
    clear m;
    whichCbv HeqmEq;
    commonCbv HeqmEq;
    rewrite signature_eq in HeqmEq; unfold eq_rect in HeqmEq;
    simpl in HeqmEq;
    match type of HeqmEq with
      | ?sth = ?m => pose m; clear sth HeqmEq
    end
  end.

Ltac ggNoF whichCbv dm r :=
  match goal with
    | m := {| metaRegs :=?rgs; metaRules := ?rls; metaMeths := ?mts |} |- _ =>
           let dmTriple := find dm (@nil MetaMeth) mts in
           let rTriple := find r (@nil MetaRule) rls in
           match dmTriple with
             | (?preDm, @RepMeth ?A ?strA ?goodFn ?GenK ?getConstK
                                 ?goodFn2 ?bdm ?dmn ?ls ?noDup, ?sufDm) =>
               match rTriple with
                 | (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                    ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                   pose
                     {| metaRegs := rgs;
                        metaRules := preR ++
                                          RepRule strA goodFn getConstK goodFn2
                                          (fun ty =>
                                             inlineGenGenDm
                                               (bdr ty)
                                               (nameVal dmn) bdm) rn noDup :: sufR;
                        metaMeths := mts |}; clear m
               end
           end
  end; simplMod whichCbv.

Ltac ggF whichCbv dm r :=
  match goal with
    | m := {| metaRegs :=?rgs; metaRules := ?rls; metaMeths := ?mts |} |- _ =>
           let dmTriple := find dm (@nil MetaMeth) mts in
           let rTriple := find r (@nil MetaRule) rls in
           match dmTriple with
             | (?preDm, @RepMeth ?A ?strA ?goodFn ?GenK ?getConstK
                                 ?goodFn2 ?bdm ?dmn ?ls ?noDup, ?sufDm) =>
               match rTriple with
                 | (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                    ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                   pose
                     {| metaRegs := rgs;
                        metaRules := preR ++
                                          RepRule strA goodFn getConstK goodFn2
                                          (fun ty =>
                                             inlineGenGenDm
                                               (bdr ty)
                                               (nameVal dmn) bdm) rn noDup :: sufR;
                        metaMeths := preDm ++ sufDm |}; clear m
               end
           end
  end; simplMod whichCbv.

Ltac gsNoF whichCbv dm r :=
  match goal with
    | m := {| metaRegs :=?rgs; metaRules := ?rls; metaMeths := ?mts |} |- _ =>
           let dmTriple := find dm (@nil MetaMeth) mts in
           let rTriple := find r (@nil MetaRule) rls in
           match dmTriple with
             | (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
               match rTriple with
                 | (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                    ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                   pose
                     {| metaRegs := rgs;
                        metaRules := preR ++
                                          RepRule strA goodFn getConstK goodFn2
                                          (fun ty =>
                                             inlineGenSinDm
                                               (bdr ty)
                                               (nameVal dmn) bdm) rn noDup :: sufR;
                        metaMeths := mts |}; clear m
               end
           end
  end; simplMod whichCbv.

Ltac gsF whichCbv dm r :=
  match goal with
    | m := {| metaRegs :=?rgs; metaRules := ?rls; metaMeths := ?mts |} |- _ =>
           let dmTriple := find dm (@nil MetaMeth) mts in
           let rTriple := find r (@nil MetaRule) rls in
           match dmTriple with
             | (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
               match rTriple with
                 | (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                    ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                   pose
                     {| metaRegs := rgs;
                        metaRules := preR ++
                                          RepRule strA goodFn getConstK goodFn2
                                          (fun ty =>
                                             inlineGenSinDm
                                               (bdr ty)
                                               (nameVal dmn) bdm) rn noDup :: sufR;
                        metaMeths := preDm ++ sufDm |}; clear m
               end
           end
  end; simplMod whichCbv.

Ltac ssNoF whichCbv dm r :=
  match goal with
    | m := {| metaRegs :=?rgs; metaRules := ?rls; metaMeths := ?mts |} |- _ =>
           let dmTriple := find dm (@nil MetaMeth) mts in
           let rTriple := find r (@nil MetaRule) rls in
           match dmTriple with
             | (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
               match rTriple with
                 | (?preR, @OneRule ?bdr ?rn, ?sufR) =>
                   pose
                     {| metaRegs := rgs;
                        metaRules := preR ++
                                          OneRule
                                          (fun ty =>
                                             inlineSinSinDm
                                               (bdr ty)
                                               (nameVal dmn) bdm) rn :: sufR;
                        metaMeths := mts |}; clear m
               end
           end
  end; simplMod whichCbv.

Ltac ssF whichCbv dm r :=
  match goal with
    | m := {| metaRegs :=?rgs; metaRules := ?rls; metaMeths := ?mts |} |- _ =>
           let dmTriple := find dm (@nil MetaMeth) mts in
           let rTriple := find r (@nil MetaRule) rls in
           match dmTriple with
             | (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
               match rTriple with
                 | (?preR, @OneRule ?bdr ?rn, ?sufR) =>
                   pose
                     {| metaRegs := rgs;
                        metaRules := preR ++
                                          OneRule
                                          (fun ty =>
                                             inlineSinSinDm
                                               (bdr ty)
                                               (nameVal dmn) bdm) rn :: sufR;
                        metaMeths := preDm ++ sufDm |}; clear m
               end
           end
  end; simplMod whichCbv.

Ltac start_def m := let mod := fresh in pose m as mod; cbv [m] in mod.

Ltac finish_def :=
  match goal with
    | m := ?mod: MetaModule |- _ =>
           simpl in m; clear -m;
           exact mod
  end.


Ltac start_ref m mpf :=
  let mod := fresh in
  let pf1 := fresh in
  let pf2 := fresh in
  pose m as mod;
    pose proof mpf as [pf1 pf2];
    fold mod in pf1, pf2;
    cbv [m] in mod.

Ltac finish_ref :=
  match goal with
    | mRef: _ _ <<== modFromMeta ?m,
        mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
      (exact (conj mRef mEquiv))
  end.




Ltac simplifyMod whichCbv :=
  match goal with
    | mRef: _ _ <<== modFromMeta ?m,
        mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
      unfold m in mRef, mEquiv;
  clear m;
  whichCbv mRef; commonCbv mRef;
  whichCbv mEquiv; commonCbv mEquiv;
  rewrite ?signature_eq in mRef, mEquiv; unfold eq_rect in mRef, mEquiv;
  simpl in mRef, mEquiv
end;
  match goal with
    | mRef: _ _ <<== modFromMeta ?m,
        mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
      let newm := fresh in
      pose m as newm;
        fold newm in mRef;
        fold newm in mEquiv
  end.


Ltac noFilt whichCbv ltac dm r :=
  match goal with
    | mRef: _ _ <<== modFromMeta ?m,
        mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
      ltac dm r;
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
  end; simplifyMod whichCbv.

Ltac ggNoFilt whichCbv dm r := noFilt whichCbv inlineGenDmGenRule_NoFilt dm r.
Ltac gsNoFilt whichCbv dm r := noFilt whichCbv inlineSinDmGenRule_NoFilt dm r.
Ltac ssNoFilt whichCbv dm r := noFilt whichCbv inlineSinDmSinRule_NoFilt dm r.

Ltac ggFilt whichCbv dm r := noFilt whichCbv inlineGenDmGenRule_Filt dm r.
Ltac gsFilt whichCbv dm r := noFilt whichCbv inlineSinDmGenRule_Filt dm r.
Ltac ssFilt whichCbv dm r := noFilt whichCbv inlineSinDmSinRule_Filt dm r.
