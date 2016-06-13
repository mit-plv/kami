Require Import PartialInline Equiv
        PartialInline2 ParametricSyntax ParametricEquiv Syntax String List Semantics
        Lib.Struct Program.Equality Lib.CommonTactics Lib.Indexer Lib.StringExtension Lib.Concat.

Set Implicit Arguments.

Section IndexSymbol.
  Lemma namesMatch:
    forall s1 s2 a l1 l2, ~ S_In a s1 -> ~ S_In a s2 ->
                          (s1 ++ String a l1 = s2 ++ String a l2)%string -> s1 = s2.
  Proof.
    induction s1; destruct s2; simpl in *; auto; intros.
    inv H1; intuition auto.
    inv H1; intuition auto.
    inv H1.
    assert (~ S_In a1 s1) by intuition auto.
    assert (~ S_In a1 s2) by intuition auto.
    f_equal; eapply IHs1; eauto.
  Qed.
End IndexSymbol.

Section NoDup2.
  Variable l: list MetaMeth.
  Lemma noDup_preserveMeth: NoDup (map getMetaMethName l) ->
                            NoDup (namesOf (concat (map getListFromMetaMeth l))).
  Proof.
    induction l; simpl in *; auto; intros.
    dependent destruction H.
    specialize (IHl0 H0).
    unfold namesOf; rewrite map_app;
    fold (namesOf (getListFromMetaMeth a));
    fold (namesOf (concat (map getListFromMetaMeth l0))).
    apply noDupApp; auto; unfold not; intros.
    - destruct a; simpl in *; auto.
      unfold repMeth, getListFromRep, namesOf; simpl.
      rewrite map_map; simpl.
      clear - goodStrFn2 ls noDup.
      induction ls; simpl; intros; [auto|].
      inv noDup; constructor; auto.
      unfold not; intros.
      apply in_map_iff in H; dest.
      specialize (goodStrFn2 _ _ _ _ H); dest; subst.
      auto.
    - destruct a; simpl in *; auto.
      destruct H1; auto; subst.
      unfold namesOf in H2; apply in_map_iff in H2; dest; subst.

      destruct x.
      destruct attrType; simpl in *.
      apply in_concat_iff in H2; dest.
      apply in_map_iff in H2; dest; subst.
      unfold getListFromMetaMeth in H3; simpl in H3.

      
      destruct x1; simpl in *; auto.
      inv H3; subst; auto.
      destruct s0, s; simpl in *.
      inv H1.
      destruct_existT.
      assert (In nameVal0 (map getMetaMethName l0)).
      { apply in_map_iff.
        exists (OneMeth b0 {| nameVal := nameVal0; goodName := goodName |}); simpl; auto.
      }
      intuition auto.

      
      unfold repMeth, getListFromRep in H3.
      apply in_map_iff in H3; dest.
      inv H1; destruct_existT.
      destruct s0, s; simpl in *.
      rewrite <- H5 in *.
      unfold addIndexToStr in goodName0.
      apply (badIndex _ _ goodName0).

      
      unfold repMeth, getListFromRep in H1.
      unfold namesOf in H1, H2.
      
      apply in_map_iff in H1.
      apply in_map_iff in H2.
      dest; subst.
      destruct x0, x.
      destruct attrType, attrType0.
      simpl in *.
      apply in_map_iff in H4; dest.
      apply in_concat_iff in H3; dest.
      apply in_map_iff in H3; dest; subst.
      unfold getListFromMetaMeth in H5.
      inv H1; destruct_existT; subst.
      destruct x3; simpl in *.
      destruct H5; [|auto].
      inv H1; destruct_existT; subst.
      destruct s0; simpl in *; subst.
      unfold addIndexToStr in goodName.
      apply (badIndex _ _ goodName).
      unfold repMeth, getListFromRep in H5.
      apply in_map_iff in H5; dest; subst.
      inv H1; destruct_existT; subst.
      unfold addIndexToStr in H5.
      assert (nameVal s <> nameVal s0).
      { unfold not; intros.
        rewrite H1 in H.
        apply in_map with (f := getMetaMethName) in H6; simpl in H6.
        auto.
      }
      clear - H5 H1.
      destruct s, s0; simpl in *.
      apply index_not_in in goodName; apply index_not_in in goodName0.
      assert (nameVal = nameVal0) by (eapply namesMatch; eauto).
      intuition auto.
  Qed.
End NoDup2.

Section NoDup3.
  Variable l: list MetaRule.
  Lemma noDup_preserveRule: NoDup (map getMetaRuleName l) ->
                            NoDup (namesOf (concat (map getListFromMetaRule l))).
  Proof.
    induction l; simpl in *; auto; intros.
    dependent destruction H.
    specialize (IHl0 H0).
    unfold namesOf; rewrite map_app;
    fold (namesOf (getListFromMetaRule a));
    fold (namesOf (concat (map getListFromMetaRule l0))).
    apply noDupApp; auto; unfold not; intros.
    - destruct a; simpl in *; auto.
      unfold repRule, getListFromRep, namesOf; simpl.
      rewrite map_map; simpl.
      clear - goodStrFn2 ls noDup.
      induction ls; simpl; intros; [auto|].
      inv noDup; constructor; auto.
      unfold not; intros.
      apply in_map_iff in H; dest.
      specialize (goodStrFn2 _ _ _ _ H); dest; subst.
      auto.
    - destruct a; simpl in *; auto.
      destruct H1; auto; subst.
      unfold namesOf in H2; apply in_map_iff in H2; dest; subst.

      destruct x; simpl in *.
      apply in_concat_iff in H2; dest.
      apply in_map_iff in H2; dest; subst.
      unfold getListFromMetaRule in H3; simpl in H3.

      
      destruct x0; simpl in *; auto.
      inv H3; subst; auto.
      destruct s0, s; simpl in *.
      inv H1.
      destruct_existT.
      assert (In nameVal0 (map getMetaRuleName l0)).
      { apply in_map_iff.
        exists (OneRule b0 {| nameVal := nameVal0; goodName := goodName |}); simpl; auto.
      }
      intuition auto.

      
      unfold repRule, getListFromRep in H3.
      apply in_map_iff in H3; dest.
      inv H1; destruct_existT.
      destruct s0, s; simpl in *.
      rewrite <- H5 in *.
      unfold addIndexToStr in goodName0.
      apply (badIndex _ _ goodName0).

      
      unfold repRule, getListFromRep in H1.
      unfold namesOf in H1, H2.
      
      apply in_map_iff in H1.
      apply in_map_iff in H2.
      dest; subst.
      destruct x0, x.
      simpl in *.
      apply in_map_iff in H4; dest.
      apply in_concat_iff in H3; dest.
      apply in_map_iff in H3; dest; subst.
      unfold getListFromMetaRule in H5.
      inv H1; destruct_existT; subst.
      destruct x1; simpl in *.
      destruct H5; [|auto].
      inv H1; destruct_existT; subst.
      destruct s0; simpl in *; subst.
      unfold addIndexToStr in goodName.
      apply (badIndex _ _ goodName).
      unfold repRule, getListFromRep in H5.
      apply in_map_iff in H5; dest; subst.
      inv H1; destruct_existT; subst.
      unfold addIndexToStr in H5.
      assert (nameVal s <> nameVal s0).
      { unfold not; intros.
        rewrite H1 in H.
        apply in_map with (f := getMetaRuleName) in H6; simpl in H6.
        auto.
      }
      clear - H5 H1.
      destruct s, s0; simpl in *.
      apply index_not_in in goodName; apply index_not_in in goodName0.
      assert (nameVal = nameVal0) by (eapply namesMatch; eauto).
      intuition auto.
  Qed.
End NoDup3.

Section GenGen.
  Variable m: MetaModule.
  Variable mEquiv: forall ty, MetaModEquiv ty typeUT m.

  Variable A: Type.
  Variable strA: A -> string.
  Variable goodStrFn: forall i j, strA i = strA j -> i = j.
  Variable GenK: Kind.
  Variable getConstK: A -> ConstT GenK.
  Variable goodStrFn2: forall si sj i j,
                         addIndexToStr strA i si = addIndexToStr strA j sj ->
                         si = sj /\ i = j.
  Variable dm: sigT (GenMethodT GenK).
  Variable dmName: NameRec.
  Variable preDm sufDm: list MetaMeth.
  Variable ls: list A.
  Variable noDupLs: NoDup ls.
  Variable Hdm: metaMeths m =
                preDm ++ RepMeth strA goodStrFn getConstK goodStrFn2 dm dmName noDupLs :: sufDm.

  Variable r: GenAction GenK Void.
  Variable rName: NameRec.
  Variable preR sufR: list MetaRule.
  Variable Hrule: metaRules m =
                  preR ++ RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs :: sufR.

  Hypotheses (HnoDupMeths: NoDup (map getMetaMethName (metaMeths m)))
             (HnoDupRules: NoDup (map getMetaRuleName (metaRules m))).

  Lemma inlineGenGenDmToRule_traceRefines_NoFilt:
    makeModule m <<==
               makeModule
               {| metaRegs := metaRegs m;
                  metaRules :=
                    preR ++ RepRule strA goodStrFn getConstK goodStrFn2
                         (fun ty => inlineGenGenDm (r ty) (nameVal dmName) dm) rName noDupLs ::
                         sufR;
                  metaMeths := metaMeths m |}.
  Proof.
    unfold makeModule; simpl.
    rewrite Hrule.
    repeat rewrite map_app; simpl.
    repeat rewrite concat_app; simpl.
    unfold repRule at 2; unfold getListFromRep.
    rewrite mapFoldInlineDmsGenGen_matchesGen; auto.
    rewrite Hdm.
    repeat rewrite map_app; simpl.
    repeat rewrite concat_app; simpl.
    match goal with
      | H: metaMeths m = ?l |- _ =>
        assert (sth1: concat (map getListFromMetaMeth (metaMeths m)) =
                concat (map getListFromMetaMeth l))
          by (rewrite H; reflexivity);
          repeat rewrite map_app in sth1; simpl in sth1; repeat rewrite concat_app in sth1;
          simpl in sth1
    end.
    match goal with
      | H: metaRules m = ?l |- _ =>
        assert (sth2: concat (map getListFromMetaRule (metaRules m)) =
                concat (map getListFromMetaRule l))
          by (rewrite H; reflexivity);
          repeat rewrite map_app in sth2; simpl in sth2; repeat rewrite concat_app in sth2;
          simpl in sth2
    end.
    apply inlineDmsToRules_traceRefines_NoFilt
    with (preDm := concat (map getListFromMetaMeth preDm))
           (sufDm := concat (map getListFromMetaMeth sufDm)); auto; simpl;
    [rewrite <- sth1 | rewrite <- sth2].
    apply noDup_preserveMeth; auto.
    apply noDup_preserveRule; auto.
  Qed.

  Lemma inlineGenGenDmToRule_ModEquiv_NoFilt ty:
    MetaModEquiv ty typeUT{| metaRegs := metaRegs m;
                             metaRules :=
                               preR ++ RepRule strA goodStrFn getConstK goodStrFn2
                                    (fun ty =>
                                       inlineGenGenDm (r ty) (nameVal dmName) dm) rName noDupLs ::
                                    sufR;
                             metaMeths := metaMeths m |}.
  Proof.
    specialize (mEquiv ty); destruct mEquiv as [rEquiv dEquiv].
    rewrite Hrule, Hdm in *.
    pose proof (proj1 (@MetaRulesEquiv_in ty _ _) rEquiv) as rEquiv'; clear rEquiv.
    pose proof (proj1 (@MetaMethsEquiv_in ty _ _) dEquiv) as dEquiv'; clear dEquiv.
    constructor; simpl in *; [apply MetaRulesEquiv_in | apply MetaMethsEquiv_in]; intros.
    - apply in_app_or in H.
      destruct H; simpl in *.
      + specialize (rEquiv' r0).
        assert (sth: In r0 (preR ++ RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs
                                 :: sufR)) by (apply in_or_app; left; auto).
        apply rEquiv'; auto.
      + destruct H; subst.
        * specialize (rEquiv' (RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs)).
          apply inlineGenGenDm_Equiv with (strA := strA) (goodFn1 := goodStrFn)
                                                         (getConstK := getConstK) (goodFn2 := goodStrFn2) (noDup := noDupLs); auto.
          assert (sth: In (RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs) (preR ++ RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs
                                                                                              :: sufR)) by (apply in_or_app; right; simpl; left; auto).
          specialize (rEquiv' sth); intuition auto.
          assert (sth: In (RepMeth strA goodStrFn getConstK goodStrFn2 dm dmName noDupLs)
                          (preDm ++ RepMeth strA goodStrFn getConstK goodStrFn2 dm dmName noDupLs :: sufDm)) by (apply in_or_app; right; simpl; left; auto).
          specialize (dEquiv' _ sth); auto.
        * assert (sth: In r0 (preR ++ RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs
                                   :: sufR)) by (apply in_or_app; right; simpl; right; auto).
          apply rEquiv'; auto.
    - apply dEquiv'; auto.
  Qed.
  
  Hypothesis HdmNoRule:
    forall B strB goodStrFnB GenKB getConstKB goodStrFn2B bgenB rb lsB noDupLsB,
      In (@RepRule B strB goodStrFnB GenKB getConstKB goodStrFn2B bgenB rb lsB noDupLsB)
         (preR ++ sufR) ->
      noCallDmSigGenA (bgenB typeUT) {| isRep := true; nameRec := dmName |} (projT1 dm) = true.

  Hypothesis HdmNoMeth:
    forall B strB goodStrFnB GenKB getConstKB goodStrFn2B bgenB rb lsB noDupLsB,
      In (@RepMeth B strB goodStrFnB GenKB getConstKB goodStrFn2B bgenB rb lsB noDupLsB)
         (metaMeths m) ->
      noCallDmSigGenA (projT2 bgenB typeUT tt) {| isRep := true; nameRec := dmName |}
                      (projT1 dm) = true.

  Hypothesis HDmInR:
    exists call, 
      In call (getCallsGenA (r typeUT)) /\
      nameVal (nameRec call) = nameVal dmName /\ isRep call = true.
    
  Lemma inlineGenGenDmToRule_traceRefines_Filt:
    makeModule m <<==
               makeModule
               {| metaRegs := metaRegs m;
                  metaRules :=
                    preR ++ RepRule strA goodStrFn getConstK goodStrFn2
                         (fun ty => inlineGenGenDm (r ty) (nameVal dmName) dm) rName noDupLs ::
                         sufR;
                  metaMeths := preDm ++ sufDm |}.
  Proof.
    unfold makeModule; simpl.
    rewrite Hrule.
    repeat rewrite map_app; simpl.
    repeat rewrite concat_app; simpl.
    unfold repRule at 2; unfold getListFromRep.
    rewrite mapFoldInlineDmsGenGen_matchesGen; auto.
    rewrite Hdm.
    repeat rewrite map_app; simpl.
    repeat rewrite concat_app; simpl.
    match goal with
      | H: metaMeths m = ?l |- _ =>
        assert (sth1: concat (map getListFromMetaMeth (metaMeths m)) =
                concat (map getListFromMetaMeth l))
          by (rewrite H; reflexivity);
          repeat rewrite map_app in sth1; simpl in sth1; repeat rewrite concat_app in sth1;
          simpl in sth1
    end.
    match goal with
      | H: metaRules m = ?l |- _ =>
        assert (sth2: concat (map getListFromMetaRule (metaRules m)) =
                concat (map getListFromMetaRule l))
          by (rewrite H; reflexivity);
          repeat rewrite map_app in sth2; simpl in sth2; repeat rewrite concat_app in sth2;
          simpl in sth2
    end.
    assert (mEquiv': forall ty, ModEquiv ty typeUT (makeModule m)) by
        (intros; apply metaModEquiv_modEquiv; auto); unfold makeModule in mEquiv';
    rewrite sth1 in *; rewrite sth2 in *.
    apply inlineDmsToRules_traceRefines_Filt
    with (preDm := concat (map getListFromMetaMeth preDm))
           (sufDm := concat (map getListFromMetaMeth sufDm)); auto; simpl in *; intros.
    - rewrite <- sth1.
      apply noDup_preserveMeth; auto.
    - rewrite <- sth2.
      apply noDup_preserveRule; auto.
    - clear HDmInR.
      rewrite <- concat_app in H.
      pose proof (proj1 (in_concat_iff _ _) H);
        clear H; dest.
      rewrite <- map_app in H.
      apply in_map_iff in H; dest; subst.
      destruct x0; simpl in *; intuition auto; subst; simpl in *.
      + unfold repMeth, getListFromRep in H0.
        apply in_map_iff in H0; dest; subst; simpl in *.
        apply noCallDmSigA_forSin_true.
      + unfold repRule, repMeth, getListFromRep in H0, H1.
        apply in_map_iff in H0; apply in_map_iff in H1; dest; subst; simpl in *.
        unfold getActionFromGen.
        apply HdmNoRule in H2.
        assert (sth: strFromName strA x0 {| isRep := true; nameRec := dmName |} =
                     addIndexToStr strA x0 (nameVal dmName)) by reflexivity.
        apply noCallDmSigGenA_implies; auto.
    - clear HDmInR.
      rewrite <- sth1 in H.
      pose proof (proj1 (in_concat_iff _ _) H); clear H; dest.
      apply in_map_iff in H; dest; subst.
      destruct x0; simpl in *; intuition auto; subst; simpl in *.
      + unfold repMeth, getListFromRep in H0.
        apply in_map_iff in H0; dest; subst; simpl in *.
        apply noCallDmSigA_forSin_true.
      + unfold repRule, repMeth, getListFromRep in H0, H1.
        apply in_map_iff in H0; apply in_map_iff in H1; dest; subst; simpl in *.
        unfold getActionFromGen.
        apply HdmNoMeth in H2.
        assert (sth: strFromName strA x0 {| isRep := true; nameRec := dmName |} =
                     addIndexToStr strA x0 (nameVal dmName)) by reflexivity.
        apply noCallDmSigGenA_implies; auto.
    - destruct HDmInR as [call [inCall [nameMatch rep]]]; clear HDmInR.
      unfold repMeth, getListFromRep in H.
      apply in_map_iff in H; dest.
      exists (addIndexToStr strA x (nameVal rName) ::
                            getActionFromGen strA getConstK r x)%struct;
        simpl.
      constructor; auto.
      unfold getActionFromGen.
      unfold repRule, getListFromRep.
      apply in_map_iff; simpl.
      exists x; simpl; unfold getActionFromGen.
      constructor; auto.
      rewrite <- H; simpl.
      unfold getActionFromGen.
      rewrite getCallsGenA_matches.
      unfold strFromName; simpl.
      apply in_map_iff; simpl.
      exists call; subst; simpl.
      rewrite rep, nameMatch; simpl.
      constructor; auto.
  Qed.

  Lemma inlineGenGenDmToRule_ModEquiv_Filt ty:
    MetaModEquiv ty typeUT{| metaRegs := metaRegs m;
                             metaRules :=
                               preR ++ RepRule strA goodStrFn getConstK goodStrFn2
                                    (fun ty =>
                                       inlineGenGenDm (r ty) (nameVal dmName) dm) rName noDupLs ::
                                    sufR;
                             metaMeths := preDm ++ sufDm |}.
  Proof.
    specialize (mEquiv ty); destruct mEquiv as [rEquiv dEquiv].
    rewrite Hrule, Hdm in *.
    pose proof (proj1 (@MetaRulesEquiv_in ty _ _) rEquiv) as rEquiv'; clear rEquiv.
    pose proof (proj1 (@MetaMethsEquiv_in ty _ _) dEquiv) as dEquiv'; clear dEquiv.
    constructor; simpl in *; [apply MetaRulesEquiv_in | apply MetaMethsEquiv_in]; intros.
    - apply in_app_or in H.
      destruct H; simpl in *.
      + specialize (rEquiv' r0).
        assert (sth: In r0 (preR ++ RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs
                                 :: sufR)) by (apply in_or_app; left; auto).
        apply rEquiv'; auto.
      + destruct H; subst.
        * specialize (rEquiv' (RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs)).
          apply inlineGenGenDm_Equiv with (strA := strA) (goodFn1 := goodStrFn)
                                                         (getConstK := getConstK) (goodFn2 := goodStrFn2) (noDup := noDupLs); auto.
          assert (sth: In (RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs) (preR ++ RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs
                                                                                              :: sufR)) by (apply in_or_app; right; simpl; left; auto).
          specialize (rEquiv' sth); intuition auto.
          assert (sth: In (RepMeth strA goodStrFn getConstK goodStrFn2 dm dmName noDupLs)
                          (preDm ++ RepMeth strA goodStrFn getConstK goodStrFn2 dm dmName noDupLs :: sufDm)) by (apply in_or_app; right; simpl; left; auto).
          specialize (dEquiv' _ sth); auto.
        * assert (sth: In r0 (preR ++ RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs
                                   :: sufR)) by (apply in_or_app; right; simpl; right; auto).
          apply rEquiv'; auto.
    - apply dEquiv'.
      apply in_app_or in H.
      apply in_or_app; simpl.
      intuition auto.
  Qed.

End GenGen.

Section GenSin.
  Variable m: MetaModule.
  Variable mEquiv: forall ty, MetaModEquiv ty typeUT m.

  Variable A: Type.
  Variable strA: A -> string.
  Variable goodStrFn: forall i j, strA i = strA j -> i = j.
  Variable GenK: Kind.
  Variable getConstK: A -> ConstT GenK.
  Variable goodStrFn2: forall si sj i j,
                         addIndexToStr strA i si = addIndexToStr strA j sj ->
                         si = sj /\ i = j.
  Variable dm: sigT SinMethodT.
  Variable dmName: NameRec.
  Variable preDm sufDm: list MetaMeth.
  Variable ls: list A.
  Variable lsNotNil: ls <> nil.
  Variable noDupLs: NoDup ls.
  Variable Hdm: metaMeths m =
                preDm ++ OneMeth dm dmName :: sufDm.

  Variable r: GenAction GenK Void.
  Variable rName: NameRec.
  Variable preR sufR: list MetaRule.
  Variable Hrule: metaRules m =
                  preR ++ RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs :: sufR.

  Hypotheses (HnoDupMeths: NoDup (map getMetaMethName (metaMeths m)))
             (HnoDupRules: NoDup (map getMetaRuleName (metaRules m))).

  Lemma inlineGenSinDmToRule_traceRefines_NoFilt:
    makeModule m <<==
               makeModule
               {| metaRegs := metaRegs m;
                  metaRules :=
                    preR ++ RepRule strA goodStrFn getConstK goodStrFn2
                         (fun ty => inlineGenSinDm (r ty) (nameVal dmName) dm) rName noDupLs ::
                         sufR;
                  metaMeths := metaMeths m |}.
  Proof.
    unfold makeModule; simpl.
    rewrite Hrule.
    repeat rewrite map_app; simpl.
    repeat rewrite concat_app; simpl.
    unfold repRule at 2; unfold getListFromRep.
    rewrite mapInlineDmsGenSin_matchesGen; auto; [| destruct dmName; simpl; auto].
    rewrite Hdm.
    repeat rewrite map_app; simpl.
    repeat rewrite concat_app; simpl.
    match goal with
      | H: metaMeths m = ?l |- _ =>
        assert (sth1: concat (map getListFromMetaMeth (metaMeths m)) =
                concat (map getListFromMetaMeth l))
          by (rewrite H; reflexivity);
          repeat rewrite map_app in sth1; simpl in sth1; repeat rewrite concat_app in sth1;
          simpl in sth1
    end.
    match goal with
      | H: metaRules m = ?l |- _ =>
        assert (sth2: concat (map getListFromMetaRule (metaRules m)) =
                concat (map getListFromMetaRule l))
          by (rewrite H; reflexivity);
          repeat rewrite map_app in sth2; simpl in sth2; repeat rewrite concat_app in sth2;
          simpl in sth2
    end.
    apply inlineDmToRules_traceRefines_NoFilt
    with (preDm := concat (map getListFromMetaMeth preDm))
           (sufDm := concat (map getListFromMetaMeth sufDm)); auto; simpl;
    [rewrite <- sth1 | rewrite <- sth2].
    apply noDup_preserveMeth; auto.
    apply noDup_preserveRule; auto.
  Qed.

  Lemma inlineGenSinDmToRule_ModEquiv_NoFilt ty:
    MetaModEquiv ty typeUT{| metaRegs := metaRegs m;
                             metaRules :=
                               preR ++ RepRule strA goodStrFn getConstK goodStrFn2
                                    (fun ty =>
                                       inlineGenSinDm (r ty) (nameVal dmName) dm) rName noDupLs ::
                                    sufR;
                             metaMeths := metaMeths m |}.
  Proof.
    specialize (mEquiv ty); destruct mEquiv as [rEquiv dEquiv].
    rewrite Hrule, Hdm in *.
    pose proof (proj1 (@MetaRulesEquiv_in ty _ _) rEquiv) as rEquiv'; clear rEquiv.
    pose proof (proj1 (@MetaMethsEquiv_in ty _ _) dEquiv) as dEquiv'; clear dEquiv.
    constructor; simpl in *; [apply MetaRulesEquiv_in | apply MetaMethsEquiv_in]; intros.
    - apply in_app_or in H.
      destruct H; simpl in *.
      + specialize (rEquiv' r0).
        assert (sth: In r0 (preR ++ RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs
                                 :: sufR)) by (apply in_or_app; left; auto).
        apply rEquiv'; auto.
      + destruct H; subst.
        * specialize (rEquiv' (RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs)).
          apply inlineGenSinDm_Equiv; auto.
          assert (sth: In (RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs) (preR ++ RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs
                                                                                              :: sufR)) by (apply in_or_app; right; simpl; left; auto).
          specialize (rEquiv' sth); intuition auto.
          assert (sth: In (OneMeth dm dmName)
                          (preDm ++ OneMeth dm dmName :: sufDm)) by (apply in_or_app; right; simpl; left; auto).
          specialize (dEquiv' _ sth); auto.
        * assert (sth: In r0 (preR ++ RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs
                                   :: sufR)) by (apply in_or_app; right; simpl; right; auto).
          apply rEquiv'; auto.
    - apply dEquiv'.
      apply in_app_or in H.
      apply in_or_app; simpl.
      intuition auto.
  Qed.
  
  Hypothesis HdmNoRule1:
    forall rbody rb, In (@OneRule rbody rb) (preR ++ sufR) ->
                     noCallDmSigSinA (rbody typeUT) dmName (projT1 dm) = true.
  
  Hypothesis HdmNoRule2:
    forall B strB goodStrFnB GenKB getConstKB goodStrFn2B bgenB rb lsB noDupLsB,
      In (@RepRule B strB goodStrFnB GenKB getConstKB goodStrFn2B bgenB rb lsB noDupLsB)
         (preR ++ sufR) ->
      noCallDmSigGenA (bgenB typeUT) {| isRep := false; nameRec := dmName |} (projT1 dm) = true.

  Hypothesis HdmNoMeth1:
    forall dbody db, In (@OneMeth dbody db) (metaMeths m) ->
                     noCallDmSigSinA (projT2 dbody typeUT tt) dmName (projT1 dm) = true.
  
  Hypothesis HdmNoMeth2:
    forall B strB goodStrFnB GenKB getConstKB goodStrFn2B bgenB rb lsB noDupLsB,
      In (@RepMeth B strB goodStrFnB GenKB getConstKB goodStrFn2B bgenB rb lsB noDupLsB)
         (metaMeths m) ->
      noCallDmSigGenA (projT2 bgenB typeUT tt) {| isRep := false; nameRec := dmName |}
                      (projT1 dm) = true.

  Hypothesis HDmInR:
    exists call, 
      In call (getCallsGenA (r typeUT)) /\
      nameVal (nameRec call) = nameVal dmName /\ isRep call = false.
    
  Lemma inlineGenSinDmToRule_traceRefines_Filt:
    makeModule m <<==
               makeModule
               {| metaRegs := metaRegs m;
                  metaRules :=
                    preR ++ RepRule strA goodStrFn getConstK goodStrFn2
                         (fun ty => inlineGenSinDm (r ty) (nameVal dmName) dm) rName noDupLs ::
                         sufR;
                  metaMeths := preDm ++ sufDm |}.
  Proof.
    unfold makeModule; simpl.
    rewrite Hrule.
    repeat rewrite map_app; simpl.
    repeat rewrite concat_app; simpl.
    unfold repRule at 2; unfold getListFromRep.
    rewrite mapInlineDmsGenSin_matchesGen; auto.
    rewrite Hdm.
    repeat rewrite map_app; simpl.
    repeat rewrite concat_app; simpl.
    match goal with
      | H: metaMeths m = ?l |- _ =>
        assert (sth1: concat (map getListFromMetaMeth (metaMeths m)) =
                concat (map getListFromMetaMeth l))
          by (rewrite H; reflexivity);
          repeat rewrite map_app in sth1; simpl in sth1; repeat rewrite concat_app in sth1;
          simpl in sth1
    end.
    match goal with
      | H: metaRules m = ?l |- _ =>
        assert (sth2: concat (map getListFromMetaRule (metaRules m)) =
                concat (map getListFromMetaRule l))
          by (rewrite H; reflexivity);
          repeat rewrite map_app in sth2; simpl in sth2; repeat rewrite concat_app in sth2;
          simpl in sth2
    end.
    assert (mEquiv': forall ty, ModEquiv ty typeUT (makeModule m)) by
        (intros; apply metaModEquiv_modEquiv; auto); unfold makeModule in mEquiv';
    rewrite sth1 in *; rewrite sth2 in *.
    apply inlineDmToRules_traceRefines_Filt
    with (preDm := concat (map getListFromMetaMeth preDm))
           (sufDm := concat (map getListFromMetaMeth sufDm)); auto; simpl in *; intros.
    - rewrite <- sth1.
      apply noDup_preserveMeth; auto.
    - rewrite <- sth2.
      apply noDup_preserveRule; auto.
    - clear HDmInR.
      rewrite <- concat_app in H.
      pose proof (proj1 (in_concat_iff _ _) H);
        clear H; dest.
      rewrite <- map_app in H.
      apply in_map_iff in H; dest; subst.
      destruct x0; simpl in *; intuition auto; subst; simpl in *.
      + apply HdmNoRule1 in H1.
        unfold getActionFromSin.
        erewrite noCallDmSigSinA_matches; eauto.
      + unfold repRule, repMeth, getListFromRep in H0, H1.
        apply in_map_iff in H0; dest; subst; simpl in *.
        unfold getActionFromGen.
        apply HdmNoRule2 in H1.
        assert (sth: strFromName strA0 x {| isRep := false; nameRec := dmName |} =
                     nameVal dmName) by reflexivity.
        rewrite <- sth.
        rewrite noCallDmSigGenA_matches; auto.
    - clear HDmInR.
      rewrite <- sth1 in H.
      pose proof (proj1 (in_concat_iff _ _) H); clear H; dest.
      apply in_map_iff in H; dest; subst.
      destruct x0; simpl in *; intuition auto; subst; simpl in *.
      + apply HdmNoMeth1 in H1.
        erewrite noCallDmSigSinA_matches; eauto.
      + unfold repRule, repMeth, getListFromRep in H0, H1.
        apply in_map_iff in H0; dest; subst; simpl in *.
        unfold getActionFromGen in *.
        apply HdmNoMeth2 in H1.
        assert (sth: strFromName strA0 x {| isRep := false; nameRec := dmName |} =
                     nameVal dmName) by reflexivity.
        rewrite <- sth.
        rewrite noCallDmSigGenA_matches; auto.
    - destruct HDmInR as [call [inCall [nameMatch rep]]]; clear HDmInR.
      destruct ls; intuition auto.
      exists (addIndexToStr strA a (nameVal rName) ::
                            getActionFromGen strA getConstK r a)%struct; simpl.
      constructor; auto.
      unfold getActionFromGen.
      rewrite getCallsGenA_matches.
      apply in_map_iff; simpl.
      exists call; constructor; unfold strFromName; subst; auto.
      rewrite rep; auto.
    - destruct dmName; simpl in *; auto.
  Qed.

  Lemma inlineGenSinDmToRule_ModEquiv_Filt ty:
    MetaModEquiv ty typeUT{| metaRegs := metaRegs m;
                             metaRules :=
                               preR ++ RepRule strA goodStrFn getConstK goodStrFn2
                                    (fun ty =>
                                       inlineGenSinDm (r ty) (nameVal dmName) dm) rName noDupLs ::
                                    sufR;
                             metaMeths := preDm ++ sufDm |}.
  Proof.
    specialize (mEquiv ty); destruct mEquiv as [rEquiv dEquiv].
    rewrite Hrule, Hdm in *.
    pose proof (proj1 (@MetaRulesEquiv_in ty _ _) rEquiv) as rEquiv'; clear rEquiv.
    pose proof (proj1 (@MetaMethsEquiv_in ty _ _) dEquiv) as dEquiv'; clear dEquiv.
    constructor; simpl in *; [apply MetaRulesEquiv_in | apply MetaMethsEquiv_in]; intros.
    - apply in_app_or in H.
      destruct H; simpl in *.
      + specialize (rEquiv' r0).
        assert (sth: In r0 (preR ++ RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs
                                 :: sufR)) by (apply in_or_app; left; auto).
        apply rEquiv'; auto.
      + destruct H; subst.
        * specialize (rEquiv' (RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs)).
          apply inlineGenSinDm_Equiv; auto.
          assert (sth: In (RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs) (preR ++ RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs
                                                                                              :: sufR)) by (apply in_or_app; right; simpl; left; auto).
          specialize (rEquiv' sth); intuition auto.
          assert (sth: In (OneMeth dm dmName)
                          (preDm ++ OneMeth dm dmName :: sufDm)) by (apply in_or_app; right; simpl; left; auto).
          specialize (dEquiv' _ sth); auto.
        * assert (sth: In r0 (preR ++ RepRule strA goodStrFn getConstK goodStrFn2 r rName noDupLs
                                   :: sufR)) by (apply in_or_app; right; simpl; right; auto).
          apply rEquiv'; auto.
    - apply dEquiv'.
      apply in_app_or in H.
      apply in_or_app; simpl.
      intuition auto.
  Qed.
  

End GenSin.

Section SinSin.
  Variable m: MetaModule.
  Variable mEquiv: forall ty, MetaModEquiv ty typeUT m.

  Variable dm: sigT SinMethodT.
  Variable dmName: NameRec.
  Variable preDm sufDm: list MetaMeth.
  Variable Hdm: metaMeths m =
                preDm ++ OneMeth dm dmName :: sufDm.

  Variable r: SinAction Void.
  Variable rName: NameRec.
  Variable preR sufR: list MetaRule.
  Variable Hrule: metaRules m =
                  preR ++ OneRule r rName :: sufR.

  Hypotheses (HnoDupMeths: NoDup (map getMetaMethName (metaMeths m)))
             (HnoDupRules: NoDup (map getMetaRuleName (metaRules m))).

  Lemma inlineSinSinDmToRule_traceRefines_NoFilt:
    makeModule m <<==
               makeModule
               {| metaRegs := metaRegs m;
                  metaRules :=
                    preR ++ OneRule
                         (fun ty => inlineSinSinDm (r ty) (nameVal dmName) dm) rName ::
                         sufR;
                  metaMeths := metaMeths m |}.
  Proof.
    unfold makeModule; simpl.
    repeat rewrite map_app; simpl.
    repeat rewrite concat_app; simpl.
    unfold getActionFromSin; simpl in *.
    destruct dmName as [dName dGood].
    rewrite inlineSinSinDmFn_matches; auto; simpl in *.
    assert (sth1: concat (map getListFromMetaMeth (metaMeths m)) =
                  (concat (map getListFromMetaMeth preDm) ++
                          (dName :: getMethFromSin dm)%struct ::
                          concat (map getListFromMetaMeth sufDm))).
    { rewrite Hdm; simpl.
      rewrite map_app; simpl.
      rewrite concat_app; simpl.
      reflexivity.
    } 
    assert (sth2: concat (map getListFromMetaRule (metaRules m)) =
                  (concat (map getListFromMetaRule preR) ++
                          (nameVal rName :: getActionFromSin r)%struct ::
                          concat (map getListFromMetaRule sufR))).
    { rewrite Hrule; simpl.
      rewrite map_app; simpl.
      rewrite concat_app; simpl.
      reflexivity.
    }
    match goal with
      | |- ?m2 <<== ?m3 =>
        apply (inlineDmToRule_traceRefines_NoFilt
                      m2 (dName :: getMethFromSin dm)%struct
                      (concat (map getListFromMetaMeth preDm)) 
                      (concat (map getListFromMetaMeth sufDm))
                      sth1 (noDup_preserveMeth _ HnoDupMeths)
                      (concat (map getListFromMetaRule preR))
                      (concat (map getListFromMetaRule sufR))
                      _ sth2 (noDup_preserveRule _ HnoDupRules)
                   )
    end.
  Qed.

  Lemma inlineSinSinDmToRule_ModEquiv_NoFilt ty:
    MetaModEquiv ty typeUT{| metaRegs := metaRegs m;
                             metaRules :=
                               preR ++ OneRule
                                    (fun ty =>
                                       inlineSinSinDm (r ty) (nameVal dmName) dm) rName ::
                                    sufR;
                             metaMeths := metaMeths m |}.
  Proof.
    specialize (mEquiv ty); destruct mEquiv as [rEquiv dEquiv].
    rewrite Hrule, Hdm in *.
    pose proof (proj1 (@MetaRulesEquiv_in ty _ _) rEquiv) as rEquiv'; clear rEquiv.
    pose proof (proj1 (@MetaMethsEquiv_in ty _ _) dEquiv) as dEquiv'; clear dEquiv.
    constructor; simpl in *; [apply MetaRulesEquiv_in | apply MetaMethsEquiv_in]; intros.
    - apply in_app_or in H.
      destruct H; simpl in *.
      + specialize (rEquiv' r0).
        assert (sth: In r0 (preR ++ OneRule r rName
                                 :: sufR)) by (apply in_or_app; left; auto).
        apply rEquiv'; auto.
      + destruct H; subst.
        * specialize (rEquiv' (OneRule r rName)).
          apply inlineSinSinDm_Equiv; auto.
          assert (sth: In (OneRule r rName) (preR ++ OneRule r rName :: sufR)) by (apply in_or_app; right; simpl; left; auto).
          specialize (rEquiv' sth); intuition auto.
          assert (sth: In (OneMeth dm dmName)
                          (preDm ++ OneMeth dm dmName :: sufDm)) by (apply in_or_app; right; simpl; left; auto).
          specialize (dEquiv' _ sth); auto.
        * assert (sth: In r0 (preR ++ OneRule r rName
                                   :: sufR)) by (apply in_or_app; right; simpl; right; auto).
          apply rEquiv'; auto.
    - apply dEquiv'.
      apply in_app_or in H.
      apply in_or_app; simpl.
      intuition auto.
  Qed.
  

  
  Hypothesis HdmNoRule1:
    forall rbody rb, In (@OneRule rbody rb) (preR ++ sufR) ->
                     noCallDmSigSinA (rbody typeUT) dmName (projT1 dm) = true.
  
  Hypothesis HdmNoRule2:
    forall B strB goodStrFnB GenKB getConstKB goodStrFn2B bgenB rb lsB noDupLsB,
      In (@RepRule B strB goodStrFnB GenKB getConstKB goodStrFn2B bgenB rb lsB noDupLsB)
         (preR ++ sufR) ->
      noCallDmSigGenA (bgenB typeUT) {| isRep := false; nameRec := dmName |} (projT1 dm) = true.

  Hypothesis HdmNoMeth1:
    forall dbody db, In (@OneMeth dbody db) (metaMeths m) ->
                     noCallDmSigSinA (projT2 dbody typeUT tt) dmName (projT1 dm) = true.
  
  Hypothesis HdmNoMeth2:
    forall B strB goodStrFnB GenKB getConstKB goodStrFn2B bgenB rb lsB noDupLsB,
      In (@RepMeth B strB goodStrFnB GenKB getConstKB goodStrFn2B bgenB rb lsB noDupLsB)
         (metaMeths m) ->
      noCallDmSigGenA (projT2 bgenB typeUT tt) {| isRep := false; nameRec := dmName |}
                      (projT1 dm) = true.

  Hypothesis HDmInR:
    exists call, 
      In call (getCallsSinA (r typeUT)) /\
      nameVal call = nameVal dmName.
    
  Lemma inlineSinSinDmToRule_traceRefines_Filt:
    makeModule m <<==
               makeModule
               {| metaRegs := metaRegs m;
                  metaRules :=
                    preR ++ OneRule
                         (fun ty => inlineSinSinDm (r ty) (nameVal dmName) dm) rName ::
                         sufR;
                  metaMeths := preDm ++ sufDm |}.
  Proof.
    unfold makeModule; simpl.
    repeat rewrite map_app; simpl.
    repeat rewrite concat_app; simpl.
    unfold getActionFromSin; simpl in *.
    rewrite inlineSinSinDmFn_matches; auto; simpl in *.
    assert (sth1: concat (map getListFromMetaMeth (metaMeths m)) =
                  (concat (map getListFromMetaMeth preDm) ++
                          (nameVal dmName :: getMethFromSin dm)%struct ::
                          concat (map getListFromMetaMeth sufDm))).
    { rewrite Hdm; simpl.
      rewrite map_app; simpl.
      rewrite concat_app; simpl.
      reflexivity.
    } 
    assert (sth2: concat (map getListFromMetaRule (metaRules m)) =
                  (concat (map getListFromMetaRule preR) ++
                          (nameVal rName :: getActionFromSin r)%struct ::
                          concat (map getListFromMetaRule sufR))).
    { rewrite Hrule; simpl.
      rewrite map_app; simpl.
      rewrite concat_app; simpl.
      reflexivity.
    }
    match goal with
      | |- ?m2 <<== ?m3 =>
        apply (inlineDmToRule_traceRefines_Filt
                      m2 (nameVal dmName :: getMethFromSin dm)%struct
                      (concat (map getListFromMetaMeth preDm)) 
                      (concat (map getListFromMetaMeth sufDm))
                      sth1 (noDup_preserveMeth _ HnoDupMeths)
                      (concat (map getListFromMetaRule preR))
                      (concat (map getListFromMetaRule sufR))
                      _ sth2 (noDup_preserveRule _ HnoDupRules)
              ); auto
    end; intros.
    - apply metaModEquiv_modEquiv; auto.
    - clear HDmInR.
      rewrite <- concat_app in H.
      pose proof (proj1 (in_concat_iff _ _) H);
        clear H; dest.
      rewrite <- map_app in H.
      apply in_map_iff in H; dest; subst.
      destruct x0; simpl in *; intuition auto; subst; simpl in *.
      + apply HdmNoRule1 in H1.
        unfold getActionFromSin.
        erewrite noCallDmSigSinA_matches; eauto.
      + unfold repRule, repMeth, getListFromRep in H0, H1.
        apply in_map_iff in H0; dest; subst; simpl in *.
        unfold getActionFromGen.
        apply HdmNoRule2 in H1.
        assert (sth: strFromName strA x {| isRep := false; nameRec := dmName |} =
                     nameVal dmName) by reflexivity.
        rewrite <- sth.
        rewrite noCallDmSigGenA_matches; auto.
    - clear HDmInR.
      simpl in H.
      pose proof (proj1 (in_concat_iff _ _) H); clear H; dest.
      apply in_map_iff in H; dest; subst.
      destruct x0; simpl in *; intuition auto; subst; simpl in *.
      + apply HdmNoMeth1 in H1.
        erewrite noCallDmSigSinA_matches; eauto.
      + unfold repRule, repMeth, getListFromRep in H0, H1.
        apply in_map_iff in H0; dest; subst; simpl in *.
        unfold getActionFromGen in *.
        apply HdmNoMeth2 in H1.
        assert (sth: strFromName strA x {| isRep := false; nameRec := dmName |} =
                     nameVal dmName) by reflexivity.
        rewrite <- sth.
        rewrite noCallDmSigGenA_matches; auto.
    - destruct HDmInR as [call [incall nameeq]]; subst; simpl.
      unfold getActionFromSin.
      rewrite getCallsSinA_matches.
      apply in_map_iff.
      exists call; auto.
    - destruct dmName; auto.
  Qed.

  Lemma inlineSinSinDmToRule_ModEquiv_Filt ty:
    MetaModEquiv ty typeUT{| metaRegs := metaRegs m;
                             metaRules :=
                               preR ++ OneRule
                                    (fun ty =>
                                       inlineSinSinDm (r ty) (nameVal dmName) dm) rName ::
                                    sufR;
                             metaMeths := preDm ++ sufDm |}.
  Proof.
    specialize (mEquiv ty); destruct mEquiv as [rEquiv dEquiv].
    rewrite Hrule, Hdm in *.
    pose proof (proj1 (@MetaRulesEquiv_in ty _ _) rEquiv) as rEquiv'; clear rEquiv.
    pose proof (proj1 (@MetaMethsEquiv_in ty _ _) dEquiv) as dEquiv'; clear dEquiv.
    constructor; simpl in *; [apply MetaRulesEquiv_in | apply MetaMethsEquiv_in]; intros.
    - apply in_app_or in H.
      destruct H; simpl in *.
      + specialize (rEquiv' r0).
        assert (sth: In r0 (preR ++ OneRule r rName
                                 :: sufR)) by (apply in_or_app; left; auto).
        apply rEquiv'; auto.
      + destruct H; subst.
        * specialize (rEquiv' (OneRule r rName)).
          apply inlineSinSinDm_Equiv; auto.
          assert (sth: In (OneRule r rName) (preR ++ OneRule r rName :: sufR)) by (apply in_or_app; right; simpl; left; auto).
          specialize (rEquiv' sth); intuition auto.
          assert (sth: In (OneMeth dm dmName)
                          (preDm ++ OneMeth dm dmName :: sufDm)) by (apply in_or_app; right; simpl; left; auto).
          specialize (dEquiv' _ sth); auto.
        * assert (sth: In r0 (preR ++ OneRule r rName
                                   :: sufR)) by (apply in_or_app; right; simpl; right; auto).
          apply rEquiv'; auto.
    - apply dEquiv'.
      apply in_app_or in H.
      apply in_or_app; simpl.
      intuition auto.
  Qed.
End SinSin.

Fixpoint findDm dm pre ls :=
  match ls with
    | nil => None
    | OneMeth bd {| nameVal := dmName; goodName := pf |} :: xs =>
      match string_dec dmName dm with
        | left isEq =>
          Some (pre, OneMeth bd {| nameVal := dm; goodName := match isEq with
                                                                | eq_refl => pf
                                                              end |}, xs)
        | right _ =>
          findDm dm (pre ++ OneMeth bd {| nameVal := dmName; goodName := pf |} :: nil) xs
      end
    | RepMeth A strA goodFn GenK getConstK goodFn2 bd
              {| nameVal := dmName; goodName := pf |} _ noDup :: xs =>
      match string_dec dmName dm with
        | left isEq =>
          Some (pre, RepMeth strA goodFn getConstK
                             goodFn2 bd {| nameVal := dm; goodName :=
                                                            match isEq with
                                                              | eq_refl => pf
                                                            end |} noDup, xs)
        | right _ =>
          findDm dm (pre ++ RepMeth strA goodFn getConstK goodFn2
                         bd {| nameVal := dmName; goodName := pf |} noDup :: nil) xs
      end
  end.

Fixpoint findR dm pre ls :=
  match ls with
    | nil => None
    | OneRule bd {| nameVal := dmName; goodName := pf |} :: xs =>
      match string_dec dmName dm with
        | left isEq =>
          Some (pre, OneRule bd {| nameVal := dm; goodName := match isEq with
                                                                | eq_refl => pf
                                                              end |}, xs)
        | right _ =>
          findR dm (pre ++ OneRule bd {| nameVal := dmName; goodName := pf |} :: nil) xs
      end
    | RepRule A strA goodFn GenK getConstK goodFn2 bd
              {| nameVal := dmName; goodName := pf |} _ noDup :: xs =>
      match string_dec dmName dm with
        | left isEq =>
          Some (pre, RepRule strA goodFn getConstK
                             goodFn2 bd {| nameVal := dm; goodName :=
                                                            match isEq with
                                                              | eq_refl => pf
                                                            end |} noDup, xs)
        | right _ =>
          findR dm (pre ++ RepRule strA goodFn getConstK goodFn2
                        bd {| nameVal := dmName; goodName := pf |} noDup :: nil) xs
      end
  end.

Ltac noDupLtac :=  repeat (
                       apply NoDup_cons;
                       [unfold not; let H := fresh in
                                    intros H;
                                      repeat (destruct H; [discriminate | ]); assumption| ]);
    apply NoDup_nil.

Theorem test1 x (isIn: In x [8;8;8;8;8;8;8;8;8;8]): x = 8.
Proof.
  repeat (destruct isIn as [? | isIn]; [subst; reflexivity|]);
  destruct isIn.
Qed.

Theorem test2: exists x, In x [(3, true); (4, true); (5, false)] /\ fst x = 4.
Proof.
  eexists (4, _);
  split;
  [simpl; tauto | reflexivity].
Qed.

Ltac inlineGenDmGenRule_Filt m mEquiv dm r :=
  let dmTriple := eval simpl in (findDm dm nil (metaMeths m)) in
      let rTriple := eval simpl in (findR r nil (metaRules m)) in
          match dmTriple with
            | Some (?preDm, @RepMeth ?A ?strA ?goodFn ?GenK ?getConstK
                                     ?goodFn2 ?bdm ?dmn ?ls ?noDup, ?sufDm) =>
              match rTriple with
                | Some (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                        ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                  let H1 := fresh in
                  let H2 := fresh in
                  let H3 := fresh in
                  let H4 := fresh in
                  let H5 := fresh in
                  assert (H1: NoDup (map getMetaMethName (metaMeths m))) by
                      noDupLtac;
                    assert (H2: NoDup (map getMetaRuleName (metaRules m))) by
                      noDupLtac;
                    assert (H3:
                              forall (B : Type) (strB : B -> string)
                                     (goodStrFnB : forall i j : B, strB i = strB j -> i = j) 
                                     (GenKB : Kind) (getConstKB : B -> ConstT GenKB)
                                     (goodStrFn2B : forall (si sj : string) (i j : B),
                                                      addIndexToStr strB i si =
                                                      addIndexToStr strB j sj ->
                                                      si = sj /\ i = j)
                                     (bgenB : GenAction GenKB Void)
                                     (rb : NameRec) (lsB : list B) (noDupLsB : NoDup lsB),
                                In
                                  (RepRule strB goodStrFnB getConstKB
                                           goodStrFn2B bgenB rb noDupLsB)
                                  (preR ++ sufR) ->
                                noCallDmSigGenA (bgenB typeUT)
                                                {| isRep := true; nameRec := dmn |}
                                                (projT1 dm) = true) by
                        (let isIn := fresh in
                         intros ? ? ? ? ? ? ? ? ? ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn);
                    assert (H4:
                              forall (B : Type) (strB : B -> string)
                                     (goodStrFnB : forall i j : B, strB i = strB j -> i = j) 
                                     (GenKB : Kind) (getConstKB : B -> ConstT GenKB)
                                     (goodStrFn2B : forall (si sj : string) (i j : B),
                                                      addIndexToStr strB i si =
                                                      addIndexToStr strB j sj ->
                                                      si = sj /\ i = j)
                                     (bgenB : sigT (GenMethodT GenKB))
                                     (rb : NameRec) (lsB : list B) (noDupLsB : NoDup lsB),
                                In
                                  (RepMeth strB goodStrFnB getConstKB
                                           goodStrFn2B bgenB rb noDupLsB)
                                  (metaMeths m) ->
                                noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                {| isRep := true; nameRec := dmn |}
                                                (projT1 dm) = true) by
                        (let isIn := fresh in
                         intros ? ? ? ? ? ? ? ? ? ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn);
                    assert
                      (H5: exists call : NameRecIdx,
                             In call (getCallsGenA (r typeUT)) /\
                             nameVal (nameRec call) = nameVal dmn /\ isRep call = true) by
                        (eexists {| isRep := true;
                                    nameRec := {| nameVal := nameVal dmn;
                                                  goodName := _ |} |};
                         split; [simpl; tauto | split; reflexivity]);
                    constr:({| metaRegs := metaRegs m;
                               metaRules :=
                                 preR ++ RepRule strA goodFn getConstK goodFn2
                                      (fun ty => inlineGenGenDm (bdr ty) dm bdm)
                                      rn noDup :: sufR;
                                     metaMeths := preDm ++ sufDm |},
                            inlineGenGenDmToRule_traceRefines_Filt
                              mEquiv strA goodFn getConstK goodFn2
                              bdm dmn preDm sufDm noDup eq_refl bdr rn preR
                              sufR eq_refl H1 H2 H3 H4 H5,
                            inlineGenGenDmToRule_ModEquiv_Filt
                              mEquiv strA goodFn getConstK goodFn2
                              bdm dmn preDm sufDm noDup eq_refl bdr rn preR
                              sufR eq_refl H1 H2 H4
                           )
              end
          end.

Ltac inlineGenDmGenRule_NoFilt m mEquiv dm r :=
  let dmTriple := eval simpl in (findDm dm nil (metaMeths m)) in
      let rTriple := eval simpl in (findR r nil (metaRules m)) in
          match dmTriple with
            | Some (?preDm, @RepMeth ?A ?strA ?goodFn ?GenK ?getConstK
                                     ?goodFn2 ?bdm ?dmn ?ls ?noDup, ?sufDm) =>
              match rTriple with
                | Some (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                        ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                  let H1 := fresh in
                  let H2 := fresh in
                  assert (H1: NoDup (map getMetaMethName (metaMeths m))) by
                      noDupLtac;
                    assert (H2: NoDup (map getMetaRuleName (metaRules m))) by
                      noDupLtac;
                    constr:({| metaRegs := metaRegs m;
                               metaRules :=
                                 preR ++ RepRule strA goodFn getConstK goodFn2
                                      (fun ty => inlineGenGenDm (bdr ty) dm bdm)
                                      rn noDup :: sufR;
                                     metaMeths := metaMeths m |},
                            inlineGenGenDmToRule_traceRefines_NoFilt
                              strA goodFn getConstK goodFn2
                              bdm dmn preDm sufDm noDup eq_refl bdr rn preR
                              sufR eq_refl H1 H2,
                            inlineGenGenDmToRule_ModEquiv_NoFilt
                              mEquiv strA goodFn getConstK goodFn2
                              bdm dmn preDm sufDm noDup eq_refl bdr rn preR
                              sufR eq_refl H1 H2
                           )
              end
          end.

Ltac inlineSinDmGenRule_Filt m mEquiv dm r :=
  let dmTriple := eval simpl in (findDm dm nil (metaMeths m)) in
      let rTriple := eval simpl in (findR r nil (metaRules m)) in
          match dmTriple with
            | Some (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
              match rTriple with
                | Some (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                        ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                  let H1 := fresh in
                  let H2 := fresh in
                  let H3 := fresh in
                  let H4 := fresh in
                  let H5 := fresh in
                  let H6 := fresh in
                  let H7 := fresh in
                  let H8 := fresh in
                  assert (H1: NoDup (map getMetaMethName (metaMeths m))) by
                      noDupLtac;
                    assert (H2: NoDup (map getMetaRuleName (metaRules m))) by
                      noDupLtac;
                    assert (H3:
                              forall (B : Type) (strB : B -> string)
                                     (goodStrFnB : forall i j : B, strB i = strB j -> i = j) 
                                     (GenKB : Kind) (getConstKB : B -> ConstT GenKB)
                                     (goodStrFn2B : forall (si sj : string) (i j : B),
                                                      addIndexToStr strB i si =
                                                      addIndexToStr strB j sj ->
                                                      si = sj /\ i = j)
                                     (bgenB : GenAction GenKB Void)
                                     (rb : NameRec) (lsB : list B) (noDupLsB : NoDup lsB),
                                In
                                  (RepRule strB goodStrFnB getConstKB
                                           goodStrFn2B bgenB rb noDupLsB)
                                  (preR ++ sufR) ->
                                noCallDmSigGenA (bgenB typeUT)
                                                {| isRep := false; nameRec := dmn |}
                                                (projT1 dm) = true) by
                        (let isIn := fresh in
                         intros ? ? ? ? ? ? ? ? ? ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn);
                    assert (H4:
                              forall (B : Type) (strB : B -> string)
                                     (goodStrFnB : forall i j : B, strB i = strB j -> i = j) 
                                     (GenKB : Kind) (getConstKB : B -> ConstT GenKB)
                                     (goodStrFn2B : forall (si sj : string) (i j : B),
                                                      addIndexToStr strB i si =
                                                      addIndexToStr strB j sj ->
                                                      si = sj /\ i = j)
                                     (bgenB : sigT (GenMethodT GenKB))
                                     (rb : NameRec) (lsB : list B) (noDupLsB : NoDup lsB),
                                In
                                  (RepMeth strB goodStrFnB getConstKB
                                           goodStrFn2B bgenB rb noDupLsB)
                                  (metaMeths m) ->
                                noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                {| isRep := false; nameRec := dmn |}
                                                (projT1 dm) = true) by
                        (let isIn := fresh in
                         intros ? ? ? ? ? ? ? ? ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn);
                    assert
                      (H5: exists call : NameRecIdx,
                             In call (getCallsGenA (r typeUT)) /\
                             nameVal (nameRec call) = nameVal dmn /\ isRep call = false) by
                        (eexists {| isRep := false;
                                    nameRec := {| nameVal := nameVal dmn;
                                                  goodName := _ |} |};
                         split; [simpl; tauto | split; reflexivity]);
                    assert
                      (H6: ls <> nil) by
                        (unfold not; intros; discriminate);
                    assert
                      (H7: forall rbody rb, In (OneRule rbody rb) (metaRules m) ->
                                            noCallDmSigSinA (projT2 rbody typeUT tt)
                                                            dmn (projT1 dm) = true) by
                        (let isIn := fresh in
                         intros ? ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn);
                    assert
                      (H8: forall dbody db, In (OneMeth dbody db) (metaMeths m) ->
                                            noCallDmSigSinA (projT2 dbody typeUT tt)
                                                            dmn (projT1 dm) = true) by
                        (let isIn := fresh in
                         intros ? ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn);
                    constr:({| metaRegs := metaRegs m;
                               metaRules :=
                                 preR ++ RepRule strA goodFn getConstK goodFn2
                                      (fun ty => inlineGenSinDm (bdr ty) dm bdm)
                                      rn noDup :: sufR;
                                     metaMeths := preDm ++ sufDm |},
                            inlineGenSinDmToRule_traceRefines_Filt
                              mEquiv strA goodFn getConstK goodFn2
                              bdm dmn preDm sufDm H6 noDup eq_refl bdr rn preR
                              sufR eq_refl H1 H2 H7 H3 H8 H4 H5,
                            inlineGenSinDmToRule_ModEquiv_Filt
                              mEquiv strA goodFn getConstK goodFn2
                              bdm dmn preDm sufDm noDup eq_refl bdr rn preR
                              sufR eq_refl H1 H2 H8 H4
                           )
              end
          end.

Ltac inlineSinDmGenRule_NoFilt m mEquiv dm r :=
  let dmTriple := eval simpl in (findDm dm nil (metaMeths m)) in
      let rTriple := eval simpl in (findR r nil (metaRules m)) in
          match dmTriple with
            | Some (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
              match rTriple with
                | Some (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                        ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                  let H1 := fresh in
                  let H2 := fresh in
                  assert (H1: NoDup (map getMetaMethName (metaMeths m))) by
                      noDupLtac;
                    assert (H2: NoDup (map getMetaRuleName (metaRules m))) by
                      noDupLtac;
                    constr:({| metaRegs := metaRegs m;
                               metaRules :=
                                 preR ++ RepRule strA goodFn getConstK goodFn2
                                      (fun ty => inlineGenSinDm (bdr ty) dm bdm)
                                      rn noDup :: sufR;
                                     metaMeths := metaMeths m |},
                            inlineGenSinDmToRule_traceRefines_NoFilt
                              strA goodFn getConstK goodFn2
                              bdm dmn preDm sufDm noDup eq_refl bdr rn preR
                              sufR eq_refl H1 H2,
                            inlineGenSinDmToRule_ModEquiv_NoFilt
                              mEquiv strA goodFn getConstK goodFn2
                              bdm dmn preDm sufDm noDup eq_refl bdr rn preR
                              sufR eq_refl H1 H2
                           )
              end
          end.

Ltac inlineSinDmSinRule_Filt m mEquiv dm r :=
  let dmTriple := eval simpl in (findDm dm nil (metaMeths m)) in
      let rTriple := eval simpl in (findR r nil (metaRules m)) in
          match dmTriple with
            | Some (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
              match rTriple with
                | Some (?preR, @OneRule ?bdr ?rn, ?sufR) =>
                  let H1 := fresh in
                  let H2 := fresh in
                  let H3 := fresh in
                  let H4 := fresh in
                  let H5 := fresh in
                  let H7 := fresh in
                  let H8 := fresh in
                  assert (H1: NoDup (map getMetaMethName (metaMeths m))) by
                      noDupLtac;
                    assert (H2: NoDup (map getMetaRuleName (metaRules m))) by
                      noDupLtac;
                    assert (H3:
                              forall (B : Type) (strB : B -> string)
                                     (goodStrFnB : forall i j : B, strB i = strB j -> i = j) 
                                     (GenKB : Kind) (getConstKB : B -> ConstT GenKB)
                                     (goodStrFn2B : forall (si sj : string) (i j : B),
                                                      addIndexToStr strB i si =
                                                      addIndexToStr strB j sj ->
                                                      si = sj /\ i = j)
                                     (bgenB : GenAction GenKB Void)
                                     (rb : NameRec) (lsB : list B) (noDupLsB : NoDup lsB),
                                In
                                  (RepRule strB goodStrFnB getConstKB
                                           goodStrFn2B bgenB rb noDupLsB)
                                  (preR ++ sufR) ->
                                noCallDmSigGenA (bgenB typeUT)
                                                {| isRep := false; nameRec := dmn |}
                                                (projT1 dm) = true) by
                        (let isIn := fresh in
                         intros ? ? ? ? ? ? ? ? ? ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn);
                    assert (H4:
                              forall (B : Type) (strB : B -> string)
                                     (goodStrFnB : forall i j : B, strB i = strB j -> i = j) 
                                     (GenKB : Kind) (getConstKB : B -> ConstT GenKB)
                                     (goodStrFn2B : forall (si sj : string) (i j : B),
                                                      addIndexToStr strB i si =
                                                      addIndexToStr strB j sj ->
                                                      si = sj /\ i = j)
                                     (bgenB : sigT (GenMethodT GenKB))
                                     (rb : NameRec) (lsB : list B) (noDupLsB : NoDup lsB),
                                In
                                  (RepMeth strB goodStrFnB getConstKB
                                           goodStrFn2B bgenB rb noDupLsB)
                                  (metaMeths m) ->
                                noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                {| isRep := false; nameRec := dmn |}
                                                (projT1 dm) = true) by
                        (let isIn := fresh in
                         intros ? ? ? ? ? ? ? ? ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn);
                    assert
                      (H5: exists call : NameRec,
                             In call (getCallsGenA (r typeUT)) /\
                             nameVal call = nameVal dmn) by
                        (eexists {| nameVal := nameVal dmn;
                                    goodName := _ |};
                         split; [simpl; tauto | reflexivity]);
                    assert
                      (H7: forall rbody rb, In (OneRule rbody rb) (metaRules m) ->
                                            noCallDmSigSinA (projT2 rbody typeUT tt)
                                                            dmn (projT1 dm) = true) by
                        (let isIn := fresh in
                         intros ? ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn);
                    assert
                      (H8: forall dbody db, In (OneMeth dbody db) (metaMeths m) ->
                                            noCallDmSigSinA (projT2 dbody typeUT tt)
                                                            dmn (projT1 dm) = true) by
                        (let isIn := fresh in
                         intros ? ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn);
                    constr:({| metaRegs := metaRegs m;
                               metaRules :=
                                 preR ++ OneRule
                                      (fun ty => inlineSinSinDm (bdr ty) dm bdm)
                                      rn :: sufR;
                               metaMeths := preDm ++ sufDm |},
                            inlineSinSinDmToRule_traceRefines_Filt
                              mEquiv
                              bdm dmn preDm sufDm eq_refl bdr rn preR
                              sufR eq_refl H1 H2 H7 H3 H8 H4 H5,
                            inlineSinSinDmToRule_ModEquiv_Filt
                              mEquiv
                              bdm dmn preDm sufDm eq_refl bdr rn preR
                              sufR eq_refl H1 H2 H8 H4
                           )
              end
          end.

Ltac inlineSinDmSinRule_NoFilt m mEquiv dm r :=
  let dmTriple := eval simpl in (findDm dm nil (metaMeths m)) in
      let rTriple := eval simpl in (findR r nil (metaRules m)) in
          match dmTriple with
            | Some (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
              match rTriple with
                | Some (?preR, @OneRule ?bdr ?rn, ?sufR) =>
                  let H1 := fresh in
                  let H2 := fresh in
                  assert (H1: NoDup (map getMetaMethName (metaMeths m))) by
                      noDupLtac;
                    assert (H2: NoDup (map getMetaRuleName (metaRules m))) by
                      noDupLtac;
                    constr:({| metaRegs := metaRegs m;
                               metaRules :=
                                 preR ++ OneRule
                                      (fun ty => inlineSinSinDm (bdr ty) dm bdm)
                                      rn :: sufR;
                               metaMeths := metaMeths m |},
                            inlineSinSinDmToRule_traceRefines_NoFilt
                              bdm dmn preDm sufDm eq_refl bdr rn preR
                              sufR eq_refl H1 H2,
                            inlineSinSinDmToRule_ModEquiv_NoFilt
                              mEquiv
                              bdm dmn preDm sufDm eq_refl bdr rn preR
                              sufR eq_refl H1 H2
                           )
              end
          end.

