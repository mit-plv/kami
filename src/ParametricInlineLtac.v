Require Import Kami.ParametricInline List Kami.ParametricSyntax String Kami.Syntax
        Lib.CommonTactics Lib.Reflection Kami.Tactics Kami.ParametricEquiv.

Set Asymmetric Patterns.

Open Scope string.

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
          constr:(pre, x, xs)
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




Close Scope string.
