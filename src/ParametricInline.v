Require Import PartialInline
        PartialInline2 ParametricSyntax ParametricEquiv Syntax String List Semantics
        Lib.Struct Program.Equality Lib.CommonTactics Lib.Indexer Lib.StringExtension.

Section concat_app.
  Variable A: Type.
  Lemma concat_app: forall l1 l2: list (list A), concat (l1 ++ l2) = concat l1 ++ concat l2.
  Proof.
    induction l1; simpl in *; auto; intros.
    rewrite <- app_assoc.
    f_equal; auto.
  Qed.
End concat_app.

Section NoDup.
  Variable A: Type.
  Lemma noDupApp l1: forall l2, NoDup l1 -> NoDup l2 ->
                                (forall i: A, In i l1 -> ~ In i l2) ->
                                NoDup (l1 ++ l2).
  Proof.
    induction l1; simpl in *; intros.
    - intuition.
    - inv H.
      specialize (IHl1 _ H5 H0).
      assert (forall i, In i l1 -> ~ In i l2) by (intros; apply H1; intuition).
      specialize (IHl1 H).
      assert (~ In a l2) by (intros; apply H1; auto).
      constructor; auto.
      unfold not; intros K; apply in_app_or in K.
      destruct K; intuition auto.
  Qed.
End NoDup.

Section AboutConcat.
  Variable A: Type.

  Lemma in_concat_iff (ls: list (list A)):
    forall x,
      In x (concat ls) -> exists l, In l ls /\ In x l.
  Proof.
    induction ls; simpl in *; auto; intros; intuition auto.
    apply in_app_or in H.
    destruct H.
    exists a; intuition auto.
    specialize (IHls _ H); dest.
    exists x0; auto.
  Qed.

  Lemma in_concat_iff2 (ls: list (list A)):
    forall x,
      In x (concat ls) -> exists i, In x (nth i ls nil).
  Proof.
    induction ls; simpl in *; auto; intros; intuition auto.
    apply in_app_or in H.
    destruct H.
    exists 0; intuition auto.
    specialize (IHls _ H); dest.
    exists (S x0); auto.
  Qed.


  Variable B: Type.
  Variable f: A -> B.
  Lemma map_concat: forall (l: list (list A)) x, In x (map f (concat l)) ->
                                                 In x (concat (map (map f) l)).
  Proof.
    induction l; simpl in *; auto; intros.
    rewrite map_app in *.
    apply in_app_or in H.
    apply in_or_app.
    destruct H; auto.
  Qed.
End AboutConcat.

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
  Variable goodStrFn2: forall si sj i j, addIndexToStr strA i si = addIndexToStr strA j sj ->
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

  Lemma InlineGenGenDmToRule_traceRefines_NoFilt:
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

  Hypothesis HdmNoRule:
    forall r',
      In r' (preR ++ sufR) ->
      match r' with
        | OneRule a _ => noCallDmSigSinA (a typeUT) dmName (projT1 dm) = true
        | RepRule _ _ _ _ _ _ bgen _ _ _ =>
          noCallDmSigGenA (bgen typeUT) {| isRep := true; nameRec := dmName |} (projT1 dm) = true
      end.

  Hypothesis HdmNoMeth:
    forall d,
      In d (metaMeths m) ->
      match d with
        | OneMeth a _ => noCallDmSigSinA (projT2 a typeUT tt) dmName (projT1 dm) = true
        | RepMeth _ _ _ _ _ _ bgen _ _ _ =>
          noCallDmSigGenA (projT2 bgen typeUT tt) {| isRep := true; nameRec := dmName |}
                          (projT1 dm) = true
      end.

  Hypothesis HDmInR:
    In (nameVal dmName) (map (fun n => nameVal (nameRec n)) (getCallsGenA (r typeUT))).

  (*
  Lemma inlineGenGenDmToRule_traceRefines_2:
    makeModule m <<==
               makeModule
               {| metaRegs := metaRegs m;
                  metaRules :=
                    map (fun newr =>
                           if string_dec rName (getMetaRuleName newr)
                           then RepRule strA goodStrFn goodStrFn2
                                        (fun ty => inlineGenGenDm (r ty) dmName dm) rName ls
                           else newr) (metaRules m);
                  metaMeths :=
                    filter
                      (fun dm' =>
                         if string_dec dmName (getMetaMethName dm')
                         then false
                         else true) (metaMeths m) |}.
  Proof.
    admit.
  Qed.
*)
End GenGen.

(*
Section GenSin.
  Variable m: MetaModule.
  Variable mEquiv: forall ty, MetaModEquiv ty typeUT m.

  Variable A: Type.
  Variable strA: A -> string.
  Variable goodStrFn: forall i j, strA i = strA j -> i = j.
  Variable goodStrFn2: forall si sj i j, addIndexToStr strA i si = addIndexToStr strA j sj ->
                                         si = sj /\ i = j.
  Variable dm: sigT SinMethodT.
  Variable dmName: string.
  Variable ls: list A.

  Variable r: GenAction Void.
  Variable rName: string.

  Hypotheses (Hdm: In (OneMeth dm dmName) (metaMeths m))
             (HnoDupMeths: NoDup (map getMetaMethName (metaMeths m)))
             (HnoDupRules: NoDup (map getMetaRuleName (metaRules m))).
  Hypothesis Hrule: In (RepRule strA goodStrFn goodStrFn2 r rName ls) (metaRules m).

  Lemma InlineGenSinDmToRule_traceRefines_1:
    makeModule m <<==
               makeModule
               {| metaRegs := metaRegs m;
                  metaRules :=
                    map (fun newr =>
                           if string_dec rName (getMetaRuleName newr)
                           then RepRule strA goodStrFn goodStrFn2
                                        (fun ty => inlineGenSinDm (r ty) dmName dm) rName ls
                           else newr) (metaRules m);
                  metaMeths := metaMeths m |}.
  Proof.
    admit.
  Qed.

  Hypothesis HnoRuleCalls: forall rule,
                             In rule (metaRules m) ->
                             getMetaRuleName rule <> rName ->
                             ~ In dmName (map (fun n => nameVal (nameRec n))
                                              (getCallsMetaRule rule)).

  Hypothesis HnoMethCalls: forall meth,
                             In meth (metaMeths m) ->
                             getMetaMethName meth <> dmName ->
                             ~ In dmName (map (fun n => nameVal (nameRec n))
                                              (getCallsMetaMeth meth)).
  
  Lemma inlineGenSinDmToRule_traceRefines_2:
    makeModule m <<==
               makeModule
               {| metaRegs := metaRegs m;
                  metaRules :=
                    map (fun newr =>
                           if string_dec rName (getMetaRuleName newr)
                           then RepRule strA goodStrFn goodStrFn2
                                        (fun ty => inlineGenSinDm (r ty) dmName dm) rName ls
                           else newr) (metaRules m);
                  metaMeths :=
                    filter
                      (fun dm' =>
                         if string_dec dmName (getMetaMethName dm')
                         then false
                         else true) (metaMeths m) |}.
  Proof.
    admit.
  Qed.
End GenSin.
*)