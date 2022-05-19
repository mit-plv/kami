Require Import Bool String List Arith.Peano_dec Lia.
Require Import Lib.FMap Lib.Struct Lib.CommonTactics Lib.Indexer Lib.StringAsList Lib.StringEq.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.RefinementFacts Kami.Renaming Kami.Wf.

Require Import FunctionalExtensionality.
Require Import Compare_dec.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section SpecializeModule.
  Variable m: Modules.
  Variable i: nat.

  Fixpoint makeNoDup (l: list string) :=
    match l with
    | nil => nil
    | h :: t => let nt := makeNoDup t in
                if string_in h nt then nt else h :: nt
    end.

  Lemma makeNoDup_NoDup: forall l, NoDup (makeNoDup l).
  Proof.
    induction l; [auto|].
    simpl; remember (string_in a (makeNoDup l)) as sin; destruct sin; [auto|].
    apply string_in_dec_not_in in Heqsin.
    constructor; auto.
  Qed.

  Lemma makeNoDup_SubList_1: forall l, SubList (makeNoDup l) l.
  Proof.
    induction l; simpl; intros.
    - apply SubList_refl.
    - destruct (string_in _ _).
      + apply SubList_cons_right; auto.
      + unfold SubList; intros.
        inv H; [left; auto|right; auto].
  Qed.

  Lemma makeNoDup_SubList_2: forall l, SubList l (makeNoDup l).
  Proof.
    induction l; simpl; intros.
    - apply SubList_refl.
    - remember (string_in a (makeNoDup l)) as ain; destruct ain.
      + apply string_in_dec_in in Heqain.
        apply SubList_cons; auto.
      + apply SubList_cons; [left; auto|].
        apply SubList_cons_right; auto.
  Qed.

  Definition spDom := makeNoDup ((namesOf (getRegInits m))
                                   ++ (namesOf (getRules m))
                                   ++ (namesOf (getDefsBodies m))
                                   ++ (getCalls m)).

  Lemma spDom_regs:
    SubList (namesOf (getRegInits m)) spDom.
  Proof.
    unfold spDom.
    eapply SubList_trans; [|apply makeNoDup_SubList_2].
    apply SubList_app_1, SubList_refl.
  Qed.

  Lemma spDom_rules:
    SubList (namesOf (getRules m)) spDom.
  Proof.
    unfold spDom.
    eapply SubList_trans; [|apply makeNoDup_SubList_2].
    apply SubList_app_2, SubList_app_1, SubList_refl.
  Qed.

  Lemma spDom_defs:
    SubList (getDefs m) spDom.
  Proof.
    unfold spDom.
    eapply SubList_trans; [|apply makeNoDup_SubList_2].
    do 2 apply SubList_app_2.
    apply SubList_app_1, SubList_refl.
  Qed.

  Lemma spDom_calls:
    SubList (getCalls m) spDom.
  Proof.
    unfold spDom.
    eapply SubList_trans; [|apply makeNoDup_SubList_2].
    do 3 apply SubList_app_2.
    apply SubList_refl.
  Qed.

  Lemma spDom_getExtMeths:
    SubList (getExtMeths m) spDom.
  Proof.
    intros; eapply SubList_trans; [apply getExtMeths_meths|].
    apply SubList_app_3.
    - eapply SubList_trans; [|apply makeNoDup_SubList_2].
      do 2 apply SubList_app_2.
      apply SubList_app_1, SubList_refl.
    - eapply SubList_trans; [|apply makeNoDup_SubList_2].
      do 3 apply SubList_app_2.
      apply SubList_refl.
  Qed.

  Definition spf := fun e => e __ i.

  Lemma spf_onto: forall a1 a2, spf a1 = spf a2 -> a1 = a2.
  Proof.
    unfold spf; intros.
    rewrite withIndex_eq in H.
    eapply append_same; eauto.
  Qed.

  Lemma spf_in: forall a l, In (spf a) (map spf l) -> In a l.
  Proof.
    induction l; simpl; intros; [auto|].
    destruct H.
    - left; apply spf_onto; auto.
    - auto.
  Qed.

  Lemma spf_NoDup: forall l, NoDup l -> NoDup (map spf l).
  Proof.
    induction l; simpl; intros; [auto|].
    inv H; constructor; auto.
    intro; elim H2; apply spf_in; auto.
  Qed.

  Definition spImg := map spf spDom.

  Lemma sp_lengthEq: length spDom = length spImg.
  Proof. unfold spImg; rewrite map_length; auto. Qed.

  Lemma spImg_NoDup: NoDup spImg.
  Proof.
    unfold spImg.
    assert (NoDup spDom) by apply makeNoDup_NoDup.
    apply spf_NoDup; auto.
  Qed.

  Definition specializer := bijective spDom spImg.
  Definition specializeMod := renameModules specializer m.

  Hypothesis (HdisjDomImg: forall i, ~ (In i spDom /\ In i spImg)).

  Lemma specializer_bijective:
    forall x, specializer (specializer x) = x.
  Proof.
    intros; apply bijectiveCorrect; auto.
    - apply sp_lengthEq.
    - apply makeNoDup_NoDup.
    - apply spImg_NoDup.
  Qed.

  Lemma specializer_dom:
    forall k, In k spDom -> specializer k = spf k.
  Proof.
    intros; unfold specializer.
    assert (length spDom = length spImg) by apply sp_lengthEq.
    assert (NoDup spDom) by apply makeNoDup_NoDup.
    assert (NoDup spImg) by apply spImg_NoDup.
    unfold spImg in *.

    induction spDom; simpl; intros; [inv H|].
    simpl in *.
    inv H0; inv H1; inv H2.
    assert (forall i, ~ (In i l /\ In i (map spf l))).
    { intros; intro Hx; elim (HdisjDomImg i0); intuition. }

    destruct H; subst.
    - bijective_correct_tac.
    - specialize (IHl H0 H H4 H6 H7).
      bijective_correct_tac.
      exfalso; elim (HdisjDomImg (spf a)); intuition.
  Qed.

  Lemma specializer_dom_list:
    forall l, SubList l spDom -> map specializer l = map spf l.
  Proof.
    induction l; simpl; intros; auto.
    f_equal.
    - apply specializer_dom.
      apply H; left; auto.
    - apply IHl.
      eapply SubList_cons_inv; eauto.
  Qed.

  Lemma specializer_map:
    forall {A} (mp: M.t A),
      M.KeysSubset mp spDom ->
      renameMap specializer mp = renameMap spf mp.
  Proof.
    intros; M.mind mp; auto.

    unfold specializer, renameMap.
    rewrite M.F.P.fold_add; auto.
    - rewrite M.F.P.fold_add; auto.
      + f_equal.
        * apply M.KeysSubset_add_2 in H1.
          apply specializer_dom; auto.
        * apply H.
          eapply M.KeysSubset_add_1; eauto.
      + apply renameAdd_transpose_neqkey.
        apply spf_onto.
    - apply renameAdd_transpose_neqkey.
      intros.
      rewrite <-specializer_bijective with (x:= s1).
      rewrite <-specializer_bijective with (x:= s2).
      unfold specializer.
      rewrite H2; auto.
  Qed.

End SpecializeModule.

Section SpecializeFacts.

  Lemma spDom_concatMod_1:
    forall m1 m2, SubList (spDom m1) (spDom (m1 ++ m2)%kami).
  Proof.
    unfold SubList, spDom; intros.
    apply makeNoDup_SubList_1 in H.
    apply makeNoDup_SubList_2; simpl.
    unfold namesOf in *.
    repeat rewrite map_app.
    Opaque getCalls.
    repeat (apply in_app_or in H; destruct H).
    - apply in_or_app; left.
      apply in_or_app; left; auto.
    - apply in_or_app; right.
      apply in_or_app; left.
      apply in_or_app; left; auto.
    - apply in_or_app; right.
      apply in_or_app; right.
      apply in_or_app; left.
      apply in_or_app; left; auto.
    - apply in_or_app; right.
      apply in_or_app; right.
      apply in_or_app; right.
      apply getCalls_in_1; auto.
      Transparent getCalls.
  Qed.

  Lemma spDom_concatMod_2:
    forall m1 m2, SubList (spDom m2) (spDom (m1 ++ m2)%kami).
  Proof.
    unfold SubList, spDom; intros.
    apply makeNoDup_SubList_1 in H.
    apply makeNoDup_SubList_2; simpl.
    unfold namesOf in *.
    repeat rewrite map_app.
    Opaque getCalls.
    repeat (apply in_app_or in H; destruct H).
    - apply in_or_app; left.
      apply in_or_app; right; auto.
    - apply in_or_app; right.
      apply in_or_app; left.
      apply in_or_app; right; auto.
    - apply in_or_app; right.
      apply in_or_app; right.
      apply in_or_app; left.
      apply in_or_app; right; auto.
    - apply in_or_app; right.
      apply in_or_app; right.
      apply in_or_app; right.
      apply getCalls_in_2; auto.
      Transparent getCalls.
  Qed.

  Lemma spDom_in:
    forall m1 m2 s,
      In s (spDom (m1 ++ m2)%kami) ->
      In s (spDom m1) \/ In s (spDom m2).
  Proof.
    unfold spDom; intros.
    apply makeNoDup_SubList_1 in H.
    Opaque getCalls.
    repeat (apply in_app_or in H; destruct H).
    - simpl in H; unfold RegInitT in H; rewrite namesOf_app in H.
      apply in_app_or in H; destruct H.
      + left; apply makeNoDup_SubList_2.
        apply in_or_app; left; auto.
      + right; apply makeNoDup_SubList_2.
        apply in_or_app; left; auto.
    - simpl in H; rewrite namesOf_app in H.
      apply in_app_or in H; destruct H.
      + left; apply makeNoDup_SubList_2.
        apply in_or_app; right.
        apply in_or_app; left; auto.
      + right; apply makeNoDup_SubList_2.
        apply in_or_app; right.
        apply in_or_app; left; auto.
    - simpl in H; unfold DefMethT in H; rewrite namesOf_app in H.
      apply in_app_or in H; destruct H.
      + left; apply makeNoDup_SubList_2.
        do 2 (apply in_or_app; right).
        apply in_or_app; left; auto.
      + right; apply makeNoDup_SubList_2.
        do 2 (apply in_or_app; right).
        apply in_or_app; left; auto.
    - simpl in H; apply getCalls_in in H; destruct H.
      + left; apply makeNoDup_SubList_2.
        do 3 (apply in_or_app; right); auto.
      + right; apply makeNoDup_SubList_2.
        do 3 (apply in_or_app; right); auto.
        Transparent getCalls.
  Qed.
  
  Lemma spf_neq: forall a b i j, i <> j -> spf i a <> spf j b.
  Proof. intros; apply withIndex_neq; auto. Qed.

  Lemma renameAction_ActionEquiv:
    forall ty1 ty2 {retT} (ta: ActionT ty1 retT) (ua: ActionT ty2 retT),
      ActionEquiv ta ua ->
      forall f,
        ActionEquiv (renameAction f ta) (renameAction f ua).
  Proof.
    induction 1; simpl; intros; try (constructor; auto).
  Qed.
  
  Lemma renameRules_RulesEquiv:
    forall ty1 ty2 rules,
      RulesEquiv ty1 ty2 rules ->
      forall f,
        RulesEquiv ty1 ty2 (renameRules f rules).
  Proof.
    induction rules; simpl; intros; [constructor|].
    destruct a; constructor.
    - inv H; intros; apply renameAction_ActionEquiv; auto.
    - inv H; apply IHrules; auto.
  Qed.

  Lemma renameMeths_MethsEquiv:
    forall ty1 ty2 meths,
      MethsEquiv ty1 ty2 meths ->
      forall f,
        MethsEquiv ty1 ty2 (renameMeths f meths).
  Proof.
    induction meths; simpl; intros; [constructor|].
    destruct a; constructor.
    - unfold MethEquiv; inv H; destruct_existT; intros; apply renameAction_ActionEquiv; auto.
    - inv H; apply IHmeths; auto.
  Qed.

  Lemma renameAction_MethEquiv:
    forall ty1 ty2 meth,
      MethEquiv ty1 ty2 meth ->
      forall f, 
        MethEquiv ty1 ty2 (renameMeth f meth).
  Proof.
    intros.
    destruct meth.
    unfold MethEquiv.
    intros.
    specialize (H arg1 arg2).
    simpl in *.
    apply renameAction_ActionEquiv; auto.
  Qed.
  
  Lemma renameModules_ModEquiv:
    forall ty1 ty2 m,
      ModEquiv ty1 ty2 m ->
      forall f,
        ModEquiv ty1 ty2 (renameModules f m).
  Proof.
    induction m; simpl; intros.
    - inv H; simpl in *.
      constructor; simpl.
      + apply renameRules_RulesEquiv; auto.
      + apply renameMeths_MethsEquiv; auto.
    - inv H; simpl in *.
      constructor; simpl.
      + apply renameRules_RulesEquiv; auto.
      + apply renameMeths_MethsEquiv; auto.
    - apply ModEquiv_split in H; dest.
      apply ModEquiv_modular; auto.
  Qed.
  
  Lemma specializeMod_ModEquiv:
    forall ty1 ty2 i m,
      ModEquiv ty1 ty2 m ->
      ModEquiv ty1 ty2 (specializeMod m i).
  Proof.
    intros; apply renameModules_ModEquiv; auto.
  Qed.

  Lemma specializer_validRegsAction:
    forall m (regs: list RegInitT) {retT} (a: ActionT type retT) i,
        ValidRegsAction (namesOf regs) a ->
        ValidRegsAction (map (specializer m i) (namesOf regs))
                        (renameAction (specializer m i) a).
  Proof.
    induction 1; simpl; intros; try (constructor; auto; fail).
    - constructor; auto; apply in_map; auto.
    - constructor; auto; apply in_map; auto.
  Qed.

  Lemma specializer_validRegsRules:
    forall m (regs: list RegInitT) rules,
      SubList rules (getRules m) ->
      forall i,
        ValidRegsRules type (namesOf regs) rules ->
        ValidRegsRules type (namesOf (renameListAttr (specializer m i) regs))
                       (renameRules (specializer m i) rules).
  Proof.
    induction rules; simpl; intros; [constructor|].
    inv H0; destruct a as [rn rb]; simpl in *.
    constructor.
    - apply IHrules; auto.
      eapply SubList_cons_inv; eauto.
    - intros; rewrite renameListAttr_namesOf.
      apply specializer_validRegsAction; auto.
  Qed.

  Lemma specializer_validRegsDms:
    forall m (regs: list RegInitT) dms,
      SubList dms (getDefsBodies m) ->
      forall i,
        ValidRegsDms type (namesOf regs) dms ->
        ValidRegsDms type (namesOf (renameListAttr (specializer m i) regs))
                     (renameMeths (specializer m i) dms).
  Proof.
    induction dms; simpl; intros; [constructor|].
    inv H0; constructor.
    - apply IHdms; auto.
      eapply SubList_cons_inv; eauto.
    - intros; rewrite renameListAttr_namesOf.
      destruct a as [dmn [dsig dmb]]; simpl in *.
      apply specializer_validRegsAction; auto.
  Qed.

  Lemma specializeMod_validRegsModules_weakening:
    forall m1,
      ValidRegsModules type m1 ->
      forall m2 i,
        SubList (getRules m1) (getRules m2) ->
        SubList (getDefsBodies m1) (getDefsBodies m2) ->
        ValidRegsModules type (renameModules (specializer m2 i) m1).
  Proof.
    induction m1; simpl; intros.
    - dest; split.
      + apply specializer_validRegsRules; auto.
      + apply specializer_validRegsDms; auto.
    - dest; split.
      + apply specializer_validRegsRules; auto.
      + apply specializer_validRegsDms; auto.
    - dest; split.
      + apply IHm1_1; auto.
        * eapply SubList_app_4; eauto.
        * eapply SubList_app_4; eauto.
      + apply IHm1_2; auto.
        * eapply SubList_app_5; eauto.
        * eapply SubList_app_5; eauto.
  Qed.

  Lemma specializeMod_validRegsModules:
    forall m i,
      ValidRegsModules type m ->
      ValidRegsModules type (specializeMod m i).
  Proof.
    induction m; intros.
    - apply specializeMod_validRegsModules_weakening.
      + assumption.
      + apply SubList_refl.
      + apply SubList_refl.
    - simpl in *; dest; split.
      + apply specializer_validRegsRules; auto.
        apply SubList_refl.
      + apply specializer_validRegsDms; auto.
        apply SubList_refl.
    - simpl in *; dest; split.
      + apply specializeMod_validRegsModules_weakening; eauto.
        * simpl; apply SubList_app_1, SubList_refl.
        * simpl; apply SubList_app_1, SubList_refl.
      + apply specializeMod_validRegsModules_weakening; eauto.
        * simpl; apply SubList_app_2, SubList_refl.
        * simpl; apply SubList_app_2, SubList_refl.
  Qed.

  Lemma renameAction_spDom_weakening:
    forall f g ty {retT} (aty: ActionT ty retT)
           regs (Hvr: ValidRegsAction regs aty)
           au (Hequiv: ActionEquiv aty au),
      (forall s : string, In s (regs ++ (getCallsA au)) -> f s = g s) ->
      renameAction f aty = renameAction g aty.
  Proof.
    induction 2; simpl; intros; auto.
    - inv Hvr; destruct_existT.
      f_equal; auto.
      + apply H1, in_or_app; right; simpl; tauto.
      + extensionality v; eapply H0; [auto|].
        intros; apply H1; apply in_app_or in H2; destruct H2.
        * apply in_or_app; auto.
        * apply in_or_app; right; right; eauto.
    - inv Hvr; destruct_existT; f_equal; extensionality v; eauto.
    - inv Hvr; destruct_existT; f_equal; extensionality v; eauto.
    - inv Hvr; destruct_existT.
      f_equal; [|extensionality v; eauto].
      apply H1, in_or_app; auto.
    - inv Hvr; destruct_existT.
      f_equal; auto.
      apply H, in_or_app; auto.
    - inv Hvr; destruct_existT.
      f_equal.
      + apply IHHequiv1; intros; auto; apply H1.
        rewrite app_assoc; apply in_or_app; left; auto.
      + apply IHHequiv2; intros; auto; apply H1.
        apply in_app_or in H2; destruct H2.
        * apply in_or_app; auto.
        * do 2 (apply in_or_app; right).
          apply in_or_app; left; auto.
      + extensionality v.
        eapply H0; auto.
        intros; apply H1.
        apply in_app_or in H2; destruct H2.
        * apply in_or_app; auto.
        * do 3 (apply in_or_app; right); eauto.
    - inv Hvr; destruct_existT.
      f_equal; auto.
  Qed.

  Lemma renameModules_spDom_weakening:
    forall f g m
           (Hvr: forall ty, ValidRegsModules ty m)
           (Hequiv: forall ty, ModEquiv ty typeUT m),
      (forall s, In s (spDom m) -> f s = g s) ->
      renameModules f m = renameModules g m.
  Proof.
    induction m; simpl; intros.
    - do 2 f_equal.
      + assert (forall s, In s (namesOf (pm_regInits prim)) -> f s = g s)
          by (intros; apply H; apply spDom_regs; auto).
        clear -H0; induction (pm_regInits prim); simpl; auto.
        f_equal.
        * unfold renameAttr; f_equal.
          apply H0; simpl; tauto.
        * apply IHl; intros; apply H0; simpl; auto.
      + assert (forall s, In s (namesOf (pm_rules prim)) -> f s = g s)
          by (intros; apply H; apply spDom_rules; auto).
        assert (forall s, In s (namesOf (pm_regInits prim) ++ getCallsR (pm_rules prim)) ->
                          f s = g s).
        { intros; apply H.
          apply in_app_or in H1; destruct H1.
          { apply spDom_regs; auto. }
          { apply spDom_calls; apply in_or_app; auto. }
        }
        assert (forall ty, RulesEquiv ty typeUT (pm_rules prim))
          by (intros; specialize (Hequiv ty); inv Hequiv; auto).
        assert (forall ty, ValidRegsRules ty (namesOf (pm_regInits prim)) (pm_rules prim))
          by (intros; specialize (Hvr ty); dest; auto).
        clear -H0 H1 H2 H3; induction (pm_rules prim); simpl; auto.
        f_equal.
        * destruct a as [an ab]; f_equal.
          { apply H0; simpl; tauto. }
          { extensionality ty.
            specialize (H3 ty); inv H3.
            apply renameAction_spDom_weakening with
            (au:= ab typeUT) (regs:= namesOf (pm_regInits prim)).
            { auto. }
            { specialize (H2 ty); inv H2; auto. }
            { intros; apply H1.
              simpl; rewrite app_assoc; apply in_or_app; auto.
            }
          }
        * apply IHl; intros.
          { apply H0; simpl; auto. }
          { apply H1; simpl.
            apply in_app_or in H; destruct H.
            { apply in_or_app; auto. }
            { apply in_or_app; right; apply in_or_app; auto. }
          }
          { specialize (H2 ty); inv H2; auto. }
          { specialize (H3 ty); inv H3; auto. }
      + assert (forall s, In s (namesOf (pm_methods prim)) -> f s = g s)
          by (intros; apply H; apply spDom_defs; auto).
        assert (forall s, In s (namesOf (pm_regInits prim) ++ getCallsM (pm_methods prim)) ->
                          f s = g s).
        { intros; apply H.
          apply in_app_or in H1; destruct H1.
          { apply spDom_regs; auto. }
          { apply spDom_calls; apply in_or_app; auto. }
        }
        assert (forall ty, MethsEquiv ty typeUT (pm_methods prim))
          by (intros; specialize (Hequiv ty); inv Hequiv; auto).
        assert (forall ty, ValidRegsDms ty (namesOf (pm_regInits prim)) (pm_methods prim))
          by (intros; specialize (Hvr ty); dest; auto).
        clear -H0 H1 H2 H3; induction (pm_methods prim); simpl; auto.
        f_equal.
        * unfold renameMeth; destruct a as [an ab]; f_equal.
          { apply H0; simpl; tauto. }
          { f_equal.
            extensionality ty; extensionality v.
            specialize (H2 ty); inv H2.
            specialize (H3 ty); inv H3.
            simpl; eapply renameAction_spDom_weakening.
            { eapply H7. }
            { eapply H5. }
            { simpl in H1; intros; apply H1.
              rewrite app_assoc; apply in_or_app; eauto.
            }
          }
        * apply IHl; intros.
          { apply H0; simpl; auto. }
          { apply H1; simpl.
            apply in_app_or in H; destruct H.
            { apply in_or_app; auto. }
            { apply in_or_app; right; apply in_or_app; auto. }
          }
          { specialize (H2 ty); inv H2; auto. }
          { specialize (H3 ty); inv H3; auto. }

    - f_equal.
      + assert (forall s, In s (namesOf regs) -> f s = g s)
          by (intros; apply H; apply spDom_regs; auto).
        clear -H0; induction regs; simpl; auto.
        f_equal.
        * unfold renameAttr; f_equal.
          apply H0; simpl; tauto.
        * apply IHregs; intros; apply H0; simpl; auto.
      + assert (forall s, In s (namesOf rules) -> f s = g s)
          by (intros; apply H; apply spDom_rules; auto).
        assert (forall s, In s (namesOf regs ++ getCallsR rules) -> f s = g s).
        { intros; apply H.
          apply in_app_or in H1; destruct H1.
          { apply spDom_regs; auto. }
          { apply spDom_calls; apply in_or_app; auto. }
        }
        assert (forall ty, RulesEquiv ty typeUT rules)
          by (intros; specialize (Hequiv ty); inv Hequiv; auto).
        assert (forall ty, ValidRegsRules ty (namesOf regs) rules)
          by (intros; specialize (Hvr ty); dest; auto).
        clear -H0 H1 H2 H3; induction rules; simpl; auto.
        f_equal.
        * destruct a as [an ab]; f_equal.
          { apply H0; simpl; tauto. }
          { extensionality ty.
            specialize (H3 ty); inv H3.
            apply renameAction_spDom_weakening with
            (au:= ab typeUT) (regs:= namesOf regs).
            { auto. }
            { specialize (H2 ty); inv H2; auto. }
            { intros; apply H1.
              simpl; rewrite app_assoc; apply in_or_app; auto.
            }
          }
        * apply IHrules; intros.
          { apply H0; simpl; auto. }
          { apply H1; simpl.
            apply in_app_or in H; destruct H.
            { apply in_or_app; auto. }
            { apply in_or_app; right; apply in_or_app; auto. }
          }
          { specialize (H2 ty); inv H2; auto. }
          { specialize (H3 ty); inv H3; auto. }
      + assert (forall s, In s (namesOf dms) -> f s = g s)
          by (intros; apply H; apply spDom_defs; auto).
        assert (forall s, In s (namesOf regs ++ getCallsM dms) -> f s = g s).
        { intros; apply H.
          apply in_app_or in H1; destruct H1.
          { apply spDom_regs; auto. }
          { apply spDom_calls; apply in_or_app; auto. }
        }
        assert (forall ty, MethsEquiv ty typeUT dms)
          by (intros; specialize (Hequiv ty); inv Hequiv; auto).
        assert (forall ty, ValidRegsDms ty (namesOf regs) dms)
          by (intros; specialize (Hvr ty); dest; auto).
        clear -H0 H1 H2 H3; induction dms; simpl; auto.
        f_equal.
        * unfold renameMeth; destruct a as [an ab]; f_equal.
          { apply H0; simpl; tauto. }
          { f_equal.
            extensionality ty; extensionality v.
            specialize (H2 ty); inv H2.
            specialize (H3 ty); inv H3.
            simpl; eapply renameAction_spDom_weakening.
            { eapply H7. }
            { eapply H5. }
            { simpl in H1; intros; apply H1.
              rewrite app_assoc; apply in_or_app; eauto.
            }
          }
        * apply IHdms; intros.
          { apply H0; simpl; auto. }
          { apply H1; simpl.
            apply in_app_or in H; destruct H.
            { apply in_or_app; auto. }
            { apply in_or_app; right; apply in_or_app; auto. }
          }
          { specialize (H2 ty); inv H2; auto. }
          { specialize (H3 ty); inv H3; auto. }

    - f_equal.
      + apply IHm1; intros.
        { specialize (Hvr ty); dest; auto. }
        { specialize (Hequiv ty).
          apply ModEquiv_split in Hequiv; dest; auto.
        }
        { apply H; apply spDom_concatMod_1; auto. }
      + apply IHm2; intros.
        { specialize (Hvr ty); dest; auto. }
        { specialize (Hequiv ty).
          apply ModEquiv_split in Hequiv; dest; auto.
        }
        { apply H; apply spDom_concatMod_2; auto. }
  Qed.

End SpecializeFacts.

Section Specializable.

  Fixpoint hasNoIndex (l: list string) :=
    match l with
    | nil => true
    | h :: t =>
      match index 0 indexSymbol h with
      | Some _ => false
      | None => hasNoIndex t
      end
    end.

  Lemma hasNoIndex_in:
    forall l, hasNoIndex l = true ->
              forall a, In a l -> index 0 indexSymbol a = None.
  Proof.
    induction l; simpl; intros; [elim H0|].
    destruct H0; subst.
    - destruct (index _ _ _); intuition.
    - apply IHl; auto.
      destruct (index _ _ _); intuition.
  Qed.

  Lemma hasNoIndex_app:
    forall l1 l2,
      hasNoIndex l1 = true ->
      hasNoIndex l2 = true ->
      hasNoIndex (l1 ++ l2) = true.
  Proof.
    induction l1; simpl; intros; auto.
    destruct (index _ _ _); auto.
  Qed.

  Lemma hasNoIndex_app_inv:
    forall l1 l2,
      hasNoIndex (l1 ++ l2) = true ->
      hasNoIndex l1 = true /\ hasNoIndex l2 = true.
  Proof.
    induction l1; simpl; intros; auto.
    destruct (index _ _ _); auto; inv H.
  Qed.

  Lemma hasNoIndex_makeNoDup:
    forall l, hasNoIndex l = hasNoIndex (makeNoDup l).
  Proof.
    induction l; simpl; auto.
    remember (string_in a (makeNoDup l)) as al; destruct al; [|simpl; rewrite IHl; auto].
    apply string_in_dec_in in Heqal.
    destruct (hasNoIndex (makeNoDup l)).
    - rewrite (hasNoIndex_in _ IHl); auto.
      apply makeNoDup_SubList_1; auto.
    - rewrite IHl; destruct (index _ _ _); auto.
  Qed.

  Lemma hasNoIndex_SubList:
    forall l1 l2, SubList l1 l2 -> hasNoIndex l2 = true -> hasNoIndex l1 = true.
  Proof.
    induction l1; simpl; intros; auto.
    apply SubList_cons_inv in H; dest.
    rewrite hasNoIndex_in with (l:= l2) by assumption.
    eapply IHl1; eauto.
  Qed.

  Lemma hasNoIndex_disj_dom_img:
    forall l,
      hasNoIndex l = true ->
      forall i s,
        In s l ->
        In s (map (spf i) l) ->
        False.
  Proof.
    induction l; simpl; intros; auto.
    remember (index 0 indexSymbol a) as idx; destruct idx; [inv H|].
    destruct H0; [subst|].
    - destruct H1.
      + clear -H0.
        assert (String.length (spf i s) = String.length s) by (rewrite H0; auto).
        unfold spf in H; rewrite withIndex_eq in H.
        do 2 rewrite append_length in H; simpl in H.
        lia.
      + clear -Heqidx H0.
        apply in_map_iff in H0; dest; subst.
        unfold spf in Heqidx; rewrite withIndex_eq in Heqidx.
        apply eq_sym in Heqidx.
        apply index_correct3 with (m:= String.length x) in Heqidx.
        * rewrite substring_append_1 in Heqidx; simpl in Heqidx.
          rewrite substring_empty in Heqidx; auto.
        * discriminate.
        * lia.
    - destruct H1; [subst|].
      + clear -H H0; induction l; simpl; intros; auto.
        simpl in H.
        remember (index 0 indexSymbol a0) as idx; destruct idx; [inv H|].
        inv H0; auto.
        unfold spf in Heqidx; rewrite withIndex_eq in Heqidx.
        apply eq_sym in Heqidx.
        apply index_correct3 with (m:= String.length a) in Heqidx.
        * rewrite substring_append_1 in Heqidx; simpl in Heqidx.
          rewrite substring_empty in Heqidx; auto.
        * discriminate.
        * lia.
      + eauto.
  Qed.

  Lemma hasNoIndex_disj_imgs:
    forall l1 l2,
      hasNoIndex l1 = true ->
      hasNoIndex l2 = true ->
      forall i j s,
        i <> j ->
        In s (map (spf i) l1) ->
        In s (map (spf j) l2) ->
        False.
  Proof.
    induction l1; simpl; intros; auto.
    remember (index 0 indexSymbol a) as idx; destruct idx; [inv H|].
    destruct H2; [subst|].
    - apply in_map_iff in H3; dest.
      eapply spf_neq; eauto.
    - eapply IHl1; eauto.
  Qed.

  Definition Specializable (m: Modules) := hasNoIndex (spDom m) = true.

  Lemma specializable_concatMod:
    forall m1 m2,
      Specializable m1 ->
      Specializable m2 ->
      Specializable (m1 ++ m2)%kami.
  Proof.
    unfold Specializable, spDom, namesOf; intros.
    simpl; repeat rewrite map_app.
    rewrite <-hasNoIndex_makeNoDup in *.
    match type of H with
    | hasNoIndex ?i1 = true =>
      match type of H0 with
        | hasNoIndex ?i2 = true =>
          apply hasNoIndex_SubList with (l2 := (i1 ++ i2))
      end
    end.

    - Opaque getCalls.
      repeat apply SubList_app_3.
      + apply SubList_app_1, SubList_app_1, SubList_refl.
      + apply SubList_app_2, SubList_app_1, SubList_refl.
      + apply SubList_app_1, SubList_app_2, SubList_app_1, SubList_refl.
      + apply SubList_app_2, SubList_app_2, SubList_app_1, SubList_refl.
      + apply SubList_app_1, SubList_app_2, SubList_app_2, SubList_app_1, SubList_refl.
      + apply SubList_app_2, SubList_app_2, SubList_app_2, SubList_app_1, SubList_refl.
      + Transparent getCalls.
        clear; unfold SubList; intros.
        apply getCalls_in in H; destruct H.
        * apply in_or_app; left.
          do 3 (apply in_or_app; right); auto.
        * apply in_or_app; right.
          do 3 (apply in_or_app; right); auto.
    - apply hasNoIndex_app; auto.
  Qed.

  Variable (m: Modules).
  Hypothesis (Hsp: Specializable m).

  Lemma specializable_disj_dom_img:
    forall i s, ~ (In s (spDom m) /\ In s (spImg m i)).
  Proof.
    unfold spImg; intros; intro Hx; dest.
    unfold Specializable in H.
    eapply hasNoIndex_disj_dom_img; eauto.
  Qed.

  #[local] Hint Immediate specializable_disj_dom_img.

  Lemma specializeMod_regs:
    forall i,
      namesOf (getRegInits (specializeMod m i)) = map (spf i) (namesOf (getRegInits m)).
  Proof.
    intros; unfold specializeMod.
    rewrite renameGetRegInits.
    rewrite renameListAttr_namesOf.
    apply specializer_dom_list; auto.
    apply spDom_regs.
  Qed.

  Lemma specializeMod_rules:
    forall i,
      namesOf (getRules (specializeMod m i)) = map (spf i) (namesOf (getRules m)).
  Proof.
    intros; unfold specializeMod.
    rewrite renameGetRules.
    match goal with
    | [ |- ?lhs = _ ] =>
      assert (lhs = map (specializer m i) (namesOf (getRules m)))
    end.
    { generalize (getRules m); clear; induction l; simpl; auto.
      f_equal; auto; destruct a; auto.
    }
    rewrite H.
    apply specializer_dom_list; auto.
    apply spDom_rules.
  Qed.

  Lemma specializeMod_defs:
    forall i,
      getDefs (specializeMod m i) = map (spf i) (getDefs m).
  Proof.
    intros; unfold specializeMod.
    rewrite renameGetDefs.
    apply specializer_dom_list; auto.
    apply spDom_defs.
  Qed.

  Lemma specializeMod_calls:
    forall i,
      getCalls (specializeMod m i) = map (spf i) (getCalls m).
  Proof.
    intros; unfold specializeMod.
    rewrite renameGetCalls.
    apply specializer_dom_list; auto.
    apply spDom_calls.
  Qed.

  Lemma specializeMod_rules_in:
    forall rn rb i,
      In (rn :: rb)%struct (getRules m) ->
      In ((spf i rn) :: (fun ty => Renaming.renameAction (specializer m i) (rb ty)))%struct
         (getRules (specializeMod m i)).
  Proof.
    intros; unfold specializeMod.
    rewrite renameGetRules.
    rewrite <-specializer_dom with (m:= m); auto.
    - apply renameInRules; auto.
    - apply spDom_rules.
      apply in_map with (f:= @attrName _) in H; auto.
  Qed.

  Lemma specializeMod_dom_indexed:
    forall i s, In s (spDom (specializeMod m i)) ->
                exists t, s = t __ i.
  Proof.
    unfold spDom; intros.
    apply makeNoDup_SubList_1 in H.
    apply in_app_or in H; destruct H.
    - rewrite specializeMod_regs in H; auto.
      apply in_map_iff in H; dest; subst; eexists; reflexivity.
    - apply in_app_or in H; destruct H.
      + rewrite specializeMod_rules in H.
        apply in_map_iff in H; dest; subst; eexists; reflexivity.
      + apply in_app_or in H; destruct H.
        * fold (getDefs (specializeMod m i)) in H.
          rewrite specializeMod_defs in H.
          apply in_map_iff in H; dest; subst; eexists; reflexivity.
        * rewrite specializeMod_calls in H.
          apply in_map_iff in H; dest; subst; eexists; reflexivity.
  Qed.

  Lemma specializeMod_regs_NoDup:
    forall i,
      NoDup (namesOf (getRegInits m)) ->
      NoDup (namesOf (getRegInits (specializeMod m i))).
  Proof.
    intros; rewrite specializeMod_regs; auto.
    induction (namesOf (getRegInits m)); [simpl; auto|].
    inv H; simpl; constructor; auto.
    intro Hx; elim H2.
    apply in_map_iff in Hx; dest.
    apply spf_onto in H; subst; auto.
  Qed.

  Lemma specializable_disj_regs:
    forall i j,
      i <> j ->
      DisjList (namesOf (getRegInits (specializeMod m i)))
               (namesOf (getRegInits (specializeMod m j))).
  Proof.
    intros; do 2 rewrite specializeMod_regs.
    unfold DisjList; intros.
    destruct (in_dec string_dec e (map (spf i) (namesOf (getRegInits m))));
      destruct (in_dec string_dec e (map (spf j) (namesOf (getRegInits m))));
      intuition idtac.
    exfalso.
    eapply hasNoIndex_disj_imgs
    with (l1:= namesOf (getRegInits m)) (l2:= namesOf (getRegInits m)); eauto.
    - unfold Specializable in Hsp.
      eapply hasNoIndex_SubList; eauto.
      apply spDom_regs.
    - unfold Specializable in Hsp.
      eapply hasNoIndex_SubList; eauto.
      apply spDom_regs.
  Qed.

  Lemma specializable_disj_defs:
    forall i j,
      i <> j ->
      DisjList (getDefs (specializeMod m i))
               (getDefs (specializeMod m j)).
  Proof.
    intros; do 2 rewrite specializeMod_defs.
    unfold DisjList; intros.
    destruct (in_dec string_dec e (map (spf i) (getDefs m)));
      destruct (in_dec string_dec e (map (spf j) (getDefs m)));
      intuition idtac.
    exfalso.
    eapply hasNoIndex_disj_imgs with (l1:= getDefs m) (l2:= getDefs m); eauto.
    - unfold Specializable in Hsp.
      eapply hasNoIndex_SubList; eauto.
      apply spDom_defs.
    - unfold Specializable in Hsp.
      eapply hasNoIndex_SubList; eauto.
      apply spDom_defs.
  Qed.

  Lemma specializable_disj_calls:
    forall i j,
      i <> j ->
      DisjList (getCalls (specializeMod m i))
               (getCalls (specializeMod m j)).
  Proof.
    intros; do 2 rewrite specializeMod_calls.
    unfold DisjList; intros.
    destruct (in_dec string_dec e (map (spf i) (getCalls m)));
      destruct (in_dec string_dec e (map (spf j) (getCalls m)));
      intuition idtac.
    exfalso.
    eapply hasNoIndex_disj_imgs with (l1:= getCalls m) (l2:= getCalls m); eauto.
    - unfold Specializable in Hsp.
      eapply hasNoIndex_SubList; eauto.
      apply spDom_calls.
    - unfold Specializable in Hsp.
      eapply hasNoIndex_SubList; eauto.
      apply spDom_calls.
  Qed.

  Lemma specializable_noninteracting:
    forall i j,
      i <> j ->
      NonInteracting (specializeMod m i) (specializeMod m j).
  Proof.
    unfold NonInteracting; intros.
    do 2 rewrite specializeMod_calls.
    do 2 rewrite specializeMod_defs.
    unfold DisjList; split; intros.
    - destruct (in_dec string_dec e (map (spf i) (getDefs m)));
        destruct (in_dec string_dec e (map (spf j) (getCalls m)));
        intuition idtac.
      exfalso.
      eapply hasNoIndex_disj_imgs with (l1:= getDefs m) (l2:= getCalls m); eauto.
      + unfold Specializable in Hsp.
        eapply hasNoIndex_SubList; eauto.
        apply spDom_defs.
      + unfold Specializable in Hsp.
        eapply hasNoIndex_SubList; eauto.
        apply spDom_calls.
    - destruct (in_dec string_dec e (map (spf i) (getCalls m)));
        destruct (in_dec string_dec e (map (spf j) (getDefs m)));
        intuition idtac.
      exfalso.
      eapply hasNoIndex_disj_imgs with (l1:= getCalls m) (l2:= getDefs m); eauto.
      + unfold Specializable in Hsp.
        eapply hasNoIndex_SubList; eauto.
        apply spDom_calls.
      + unfold Specializable in Hsp.
        eapply hasNoIndex_SubList; eauto.
        apply spDom_defs.
  Qed.
  
End Specializable.

Lemma specializeMod_disj_regs_2:
  forall m1 m2,
    Specializable m1 ->
    Specializable m2 ->
    DisjList (namesOf (getRegInits m1))
             (namesOf (getRegInits m2)) ->
    forall i j,
      DisjList (namesOf (getRegInits (specializeMod m1 i)))
               (namesOf (getRegInits (specializeMod m2 j))).
Proof.
  intros; do 2 (rewrite specializeMod_regs; auto).
  unfold DisjList in *; intros.
  destruct (in_dec string_dec e (map (spf i) (namesOf (getRegInits m1)))); auto.
  destruct (in_dec string_dec e (map (spf j) (namesOf (getRegInits m2)))); auto.
  exfalso.
  apply in_map_iff in i0; apply in_map_iff in i1; dest.
  rewrite <-H2 in H4.
  destruct (string_dec x x0); subst.
  - specialize (H1 x0); destruct H1; auto.
  - destruct (dec_eq_nat i j); subst.
    + apply spf_onto in H4; auto.
    + apply spf_neq with (a:= x0) (b:= x) in H2; auto.
Qed.

Lemma specializeMod_disj_regs_different_indices:
  forall m1 m2 i j,
    Specializable m1 -> Specializable m2 ->
    i <> j ->
    DisjList (namesOf (getRegInits (specializeMod m1 i)))
             (namesOf (getRegInits (specializeMod m2 j))).
Proof.
  intros; do 2 (rewrite specializeMod_regs; auto).
  unfold DisjList in *; intros.
  destruct (in_dec string_dec e (map (spf i) (namesOf (getRegInits m1)))); auto.
  destruct (in_dec string_dec e (map (spf j) (namesOf (getRegInits m2)))); auto.
  exfalso.
  apply in_map_iff in i0; apply in_map_iff in i1; dest.
  rewrite <-H2 in H4.
  generalize H4; apply spf_neq; auto.
Qed.

Lemma specializeMod_disj_defs_different_indices:
  forall m1 m2 i j,
    Specializable m1 -> Specializable m2 ->
    i <> j ->
    DisjList (getDefs (specializeMod m1 i))
             (getDefs (specializeMod m2 j)).
Proof.
  intros; do 2 (rewrite specializeMod_defs; auto).
  unfold DisjList in *; intros.
  destruct (in_dec string_dec e (map (spf i) (getDefs m1))); auto.
  destruct (in_dec string_dec e (map (spf j) (getDefs m2))); auto.
  exfalso.
  apply in_map_iff in i0; apply in_map_iff in i1; dest.
  rewrite <-H2 in H4.
  generalize H4; apply spf_neq; auto.
Qed.

Lemma specializeMod_disj_calls_different_indices:
  forall m1 m2 i j,
    Specializable m1 -> Specializable m2 ->
    i <> j ->
    DisjList (getCalls (specializeMod m1 i))
             (getCalls (specializeMod m2 j)).
Proof.
  intros; do 2 (rewrite specializeMod_calls; auto).
  unfold DisjList in *; intros.
  destruct (in_dec string_dec e (map (spf i) (getCalls m1))); auto.
  destruct (in_dec string_dec e (map (spf j) (getCalls m2))); auto.
  exfalso.
  apply in_map_iff in i0; apply in_map_iff in i1; dest.
  rewrite <-H2 in H4.
  generalize H4; apply spf_neq; auto.
Qed.

Lemma specializable_noninteracting_2:
  forall m1 m2,
    Specializable m1 -> Specializable m2 ->
    forall i j,
      i <> j ->
      NonInteracting (specializeMod m1 i) (specializeMod m2 j).
Proof.
  unfold NonInteracting; intros.
  do 2 rewrite specializeMod_calls by assumption.
  do 2 rewrite specializeMod_defs by assumption.
  unfold DisjList; split; intros.
  - destruct (in_dec string_dec e (map (spf i) (getDefs m1)));
      destruct (in_dec string_dec e (map (spf j) (getCalls m2)));
      intuition idtac.
    exfalso.
    eapply hasNoIndex_disj_imgs with (l1:= getDefs m1) (l2:= getCalls m2); eauto.
    + unfold Specializable in H.
      eapply hasNoIndex_SubList with (l2:= spDom m1); eauto.
      apply spDom_defs.
    + unfold Specializable in H0.
      eapply hasNoIndex_SubList; eauto.
      apply spDom_calls.
  - destruct (in_dec string_dec e (map (spf i) (getCalls m1)));
      destruct (in_dec string_dec e (map (spf j) (getDefs m2)));
      intuition idtac.
    exfalso.
    eapply hasNoIndex_disj_imgs with (l1:= getCalls m1) (l2:= getDefs m2); eauto.
    + unfold Specializable in H.
      eapply hasNoIndex_SubList with (l2:= spDom m1); eauto.
      apply spDom_calls.
    + unfold Specializable in H0.
      eapply hasNoIndex_SubList; eauto.
      apply spDom_defs.
Qed.

Lemma specializeMod_concatMod:
  forall m1 m2
         (Hvr1: forall ty, ValidRegsModules ty m1)
         (Hvr2: forall ty, ValidRegsModules ty m2)
         (Hequiv1: forall ty, ModEquiv ty typeUT m1)
         (Hequiv2: forall ty, ModEquiv ty typeUT m2) i,
    Specializable m1 -> Specializable m2 ->
    specializeMod (m1 ++ m2)%kami i = ((specializeMod m1 i) ++ (specializeMod m2 i))%kami.
Proof.
  unfold specializeMod; intros.
  rewrite renameModulesConcat; f_equal.
  - apply renameModules_spDom_weakening; auto.
    intros.
    rewrite specializer_dom with (m:= (m1 ++ m2)%kami).
    + rewrite specializer_dom with (m:= m1); auto.
      apply specializable_disj_dom_img; auto.
    + apply specializable_disj_dom_img.
      apply specializable_concatMod; auto.
    + apply spDom_concatMod_1; auto.
  - apply renameModules_spDom_weakening; auto.
    intros.
    rewrite specializer_dom with (m:= (m1 ++ m2)%kami).
    + rewrite specializer_dom with (m:= m2); auto.
      apply specializable_disj_dom_img; auto.
    + apply specializable_disj_dom_img.
      apply specializable_concatMod; auto.
    + apply spDom_concatMod_2; auto.
Qed.

#[global] Hint Immediate specializable_disj_dom_img
     specializable_disj_regs
     specializable_disj_defs
     specializable_disj_calls.

Lemma renameAction_specializer_rules:
  forall regs rules dms i {ty} rn (a: Action Void),
    In (rn :: a)%struct rules ->
    Specializable (Mod regs rules dms) ->
    Wf.ValidRegsAction (namesOf regs) (a ty) ->
    ActionEquiv (a ty) (a typeUT) ->
    renameAction (specializer (Mod regs rules dms) i) (a ty) =
    renameAction (spf i) (a ty).
Proof.
  intros; apply renameAction_spDom_weakening with (regs:= namesOf regs) (au:= a typeUT); auto.
  intros; apply specializer_dom; auto.
  apply in_app_or in H3; destruct H3.
  - unfold spDom; apply makeNoDup_SubList_2.
    apply in_or_app; left; auto.
  - unfold spDom; apply makeNoDup_SubList_2.
    do 3 (apply in_or_app; right).
    apply in_or_app; left; simpl.

    clear -H H3; induction rules; [inv H|].
    inv H.
    + simpl; apply in_or_app; left; auto.
    + simpl; apply in_or_app; right; auto.
Qed.

Lemma renameAction_specializer_dms:
  forall regs rules dms i dmn (dm: sigT MethodT) ty v,
    In (dmn :: dm)%struct dms ->
    Specializable (Mod regs rules dms) ->
    Wf.ValidRegsAction (namesOf regs) (projT2 dm ty v) ->
    ActionEquiv (projT2 dm ty v) (projT2 dm typeUT tt) ->
    renameAction (specializer (Mod regs rules dms) i) (projT2 dm ty v) =
    renameAction (spf i) (projT2 dm ty v).
Proof.
  intros; apply renameAction_spDom_weakening with
          (regs:= namesOf regs) (au:= projT2 dm typeUT tt); auto.
  intros; apply specializer_dom; auto.
  apply in_app_or in H3; destruct H3.
  - unfold spDom; apply makeNoDup_SubList_2.
    apply in_or_app; left; auto.
  - unfold spDom; apply makeNoDup_SubList_2.
    do 4 (apply in_or_app; right); simpl.

    clear -H H3; induction dms; [inv H|].
    inv H.
    + simpl; apply in_or_app; left; auto.
    + simpl; apply in_or_app; right; auto.
Qed.

Section SpRefinement.
  Variables ma mb: Modules.
  Variable i: nat.
  Hypotheses (HspA: Specializable ma)
             (HspB: Specializable mb).

  Lemma specialized_1:
    forall rp,
      traceRefines rp ma mb ->
      traceRefines (liftPRename (specializer mb i) (specializer ma i) rp)
                   (specializeMod ma i) (specializeMod mb i).
  Proof.
    intros.
    eapply renameRefinement.
    - instantiate (1:= specializer ma i).
      apply specializer_bijective; auto.
    - apply specializer_bijective; auto.
    - instantiate (1:= specializer mb i).
      apply specializer_bijective; auto.
    - exact H.
    - reflexivity.
  Qed.

  Lemma specialized_2:
    forall rp,
      traceRefines (liftPRename (specializer mb i) (specializer ma i) rp) ma mb ->
      traceRefines rp (specializeMod ma i) (specializeMod mb i).
  Proof.
    intros.
    eapply renameRefinement.
    - instantiate (1:= specializer ma i).
      apply specializer_bijective; auto.
    - apply specializer_bijective; auto.
    - instantiate (1:= specializer mb i).
      apply specializer_bijective; auto.
    - exact H.
    - unfold liftPRename.
      extensionality dm.
      rewrite renameMapFInvG by (intros; apply specializer_bijective; auto).
      rewrite renameMapFInvG by (intros; apply specializer_bijective; auto).
      reflexivity.
  Qed.
  
End SpRefinement.

