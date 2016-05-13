Require Import Bool String List.
Require Import Lib.FMap Lib.Struct Lib.CommonTactics Lib.Indexer Lib.StringEq.
Require Import Syntax Semantics SemFacts Refinement Renaming Equiv Wf.

Require Import FunctionalExtensionality.
Require Import Compare_dec.

Set Implicit Arguments.

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

  Lemma makeNoDup_SubList: forall l, SubList l (makeNoDup l).
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
    eapply SubList_trans; [|apply makeNoDup_SubList].
    apply SubList_app_1, SubList_refl.
  Qed.

  Lemma spDom_rules:
    SubList (namesOf (getRules m)) spDom.
  Proof.
    unfold spDom.
    eapply SubList_trans; [|apply makeNoDup_SubList].
    apply SubList_app_2, SubList_app_1, SubList_refl.
  Qed.

  Lemma spDom_defs:
    SubList (getDefs m) spDom.
  Proof.
    unfold spDom.
    eapply SubList_trans; [|apply makeNoDup_SubList].
    do 2 apply SubList_app_2.
    apply SubList_app_1, SubList_refl.
  Qed.

  Lemma spDom_calls:
    SubList (getCalls m) spDom.
  Proof.
    unfold spDom.
    eapply SubList_trans; [|apply makeNoDup_SubList].
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
  
  Lemma spf_neq: forall a b i j, i <> j -> spf i a <> spf j b.
  Proof. intros; apply withIndex_neq; auto. Qed.

  Lemma renameAction_ActionEquiv:
    forall G {retT} (ta: ActionT type retT) (ua: ActionT typeUT retT),
      ActionEquiv G ta ua ->
      forall f,
        ActionEquiv G (renameAction f ta) (renameAction f ua).
  Proof.
    induction 1; simpl; intros; try (constructor; auto).
  Qed.

  Lemma renameRules_RulesEquiv:
    forall rules,
      RulesEquiv type typeUT rules ->
      forall f,
        RulesEquiv type typeUT (renameRules f rules).
  Proof.
    induction rules; simpl; intros; [constructor|].
    destruct a; constructor.
    - inv H; intros; apply renameAction_ActionEquiv; auto.
    - inv H; apply IHrules; auto.
  Qed.

  Lemma renameMeths_MethsEquiv:
    forall meths,
      MethsEquiv type typeUT meths ->
      forall f,
        MethsEquiv type typeUT (renameMeths f meths).
  Proof.
    induction meths; simpl; intros; [constructor|].
    destruct a; constructor.
    - inv H; destruct_existT; intros; apply renameAction_ActionEquiv; auto.
    - inv H; apply IHmeths; auto.
  Qed.
    
  Lemma renameModules_ModEquiv:
    forall m,
      ModEquiv type typeUT m ->
      forall f,
        ModEquiv type typeUT (renameModules f m).
  Proof.
    induction m; simpl; intros.
    - inv H; simpl in *.
      constructor; simpl.
      + apply renameRules_RulesEquiv; auto.
      + apply renameMeths_MethsEquiv; auto.
    - apply ModEquiv_split in H; dest.
      apply ModEquiv_modular; auto.
  Qed.
  
  Lemma specializeMod_ModEquiv:
    forall i m,
      ModEquiv type typeUT m ->
      ModEquiv type typeUT (specializeMod m i).
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
    induction m; simpl; intros.
    - dest; split.
      + apply specializer_validRegsRules; auto.
        apply SubList_refl.
      + apply specializer_validRegsDms; auto.
        apply SubList_refl.
    - dest; split.
      + apply specializeMod_validRegsModules_weakening; eauto.
        * simpl; apply SubList_app_1, SubList_refl.
        * simpl; apply SubList_app_1, SubList_refl.
      + apply specializeMod_validRegsModules_weakening; eauto.
        * simpl; apply SubList_app_2, SubList_refl.
        * simpl; apply SubList_app_2, SubList_refl.
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
        omega.
      + clear -Heqidx H0.
        apply in_map_iff in H0; dest; subst.
        unfold spf in Heqidx; rewrite withIndex_eq in Heqidx.
        apply eq_sym in Heqidx.
        apply index_correct3 with (m:= String.length x) in Heqidx; auto.
        * rewrite substring_append_1 in Heqidx; simpl in Heqidx.
          rewrite substring_empty in Heqidx; auto.
        * omega.
    - destruct H1; [subst|].
      + clear -H H0; induction l; simpl; intros; auto.
        simpl in H.
        remember (index 0 indexSymbol a0) as idx; destruct idx; [inv H|].
        inv H0; auto.
        unfold spf in Heqidx; rewrite withIndex_eq in Heqidx.
        apply eq_sym in Heqidx.
        apply index_correct3 with (m:= String.length a) in Heqidx; auto.
        * rewrite substring_append_1 in Heqidx; simpl in Heqidx.
          rewrite substring_empty in Heqidx; auto.
        * omega.
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

  Variable (m: Modules).
  Hypothesis (Hsp: Specializable m).

  Lemma specializable_disj_dom_img:
    forall i s, ~ (In s (spDom m) /\ In s (spImg m i)).
  Proof.
    unfold spImg; intros; intro Hx; dest.
    unfold Specializable in H.
    eapply hasNoIndex_disj_dom_img; eauto.
  Qed.

  Hint Immediate specializable_disj_dom_img.

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

Hint Immediate specializable_disj_dom_img
     specializable_disj_regs
     specializable_disj_defs
     specializable_disj_calls.

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

Section Duplicate.
  Variable m: Modules.

  Fixpoint duplicate n :=
    match n with
    | O => specializeMod m O
    | S n' => ConcatMod (specializeMod m n) (duplicate n')
    end.

End Duplicate.

Section DuplicateFacts.

  Lemma duplicate_ModEquiv:
    forall m n,
      ModEquiv type typeUT m ->
      ModEquiv type typeUT (duplicate m n).
  Proof.
    induction n; simpl; intros;
      [apply specializeMod_ModEquiv; auto|].
    apply ModEquiv_modular; auto.
    apply specializeMod_ModEquiv; auto.
  Qed.

  Lemma duplicate_validRegsModules:
    forall m n,
      ValidRegsModules type m ->
      ValidRegsModules type (duplicate m n).
  Proof.
    induction n; simpl; intros.
    - apply specializeMod_validRegsModules; auto.
    - split; auto.
      apply specializeMod_validRegsModules; auto.
  Qed.

  Lemma duplicate_disj_regs:
    forall m,
      Specializable m ->
      forall n ln,
        ln > n ->
        DisjList (namesOf (getRegInits (specializeMod m ln)))
                 (namesOf (getRegInits (duplicate m n))).
  Proof.
    induction n; simpl; intros.
    - apply specializable_disj_regs; auto; omega.
    - unfold namesOf in *.
      rewrite map_app.
      apply DisjList_comm, DisjList_app_4.
      + apply specializable_disj_regs; auto; omega.
      + apply DisjList_comm, IHn; omega.
  Qed.

  Lemma duplicate_disj_defs:
    forall m,
      Specializable m ->
      forall n ln,
        ln > n ->
        DisjList (getDefs (specializeMod m ln))
                 (getDefs (duplicate m n)).
  Proof.
    induction n; simpl; intros.
    - apply specializable_disj_defs; auto; omega.
    - apply DisjList_comm.
      apply DisjList_SubList with (l1:= app (getDefs (specializeMod m (S n)))
                                            (getDefs (duplicate m n))).
      + unfold SubList; intros.
        apply getDefs_in in H1; destruct H1;
          apply in_or_app; auto.
      + apply DisjList_app_4.
        * apply specializable_disj_defs; auto; omega.
        * apply DisjList_comm, IHn; omega.
  Qed.

  Lemma duplicate_disj_calls:
    forall m,
      Specializable m ->
      forall n ln,
        ln > n ->
        DisjList (getCalls (specializeMod m ln))
                 (getCalls (duplicate m n)).
  Proof.
    induction n; simpl; intros.
    - apply specializable_disj_calls; auto; omega.
    - apply DisjList_comm.
      apply DisjList_SubList with (l1:= app (getCalls (specializeMod m (S n)))
                                            (getCalls (duplicate m n))).
      + unfold SubList; intros.
        apply getCalls_in in H1; destruct H1;
          apply in_or_app; auto.
      + apply DisjList_app_4.
        * apply specializable_disj_calls; auto; omega.
        * apply DisjList_comm, IHn; omega.
  Qed.

  Lemma duplicate_noninteracting:
    forall m,
      Specializable m ->
      forall n ln,
        ln > n ->
        NonInteracting (specializeMod m ln)
                       (duplicate m n).
  Proof.
    induction n; simpl; intros.
    - apply specializable_noninteracting; auto; omega.
    - unfold NonInteracting in *.
      assert (ln > n) by omega; specialize (IHn _ H1); clear H1; dest.
      split.
      + apply DisjList_comm.
        apply DisjList_SubList with (l1:= app (getCalls (specializeMod m (S n)))
                                              (getCalls (duplicate m n))).
        * unfold SubList; intros.
          apply getCalls_in in H3.
          apply in_or_app; auto.
        * apply DisjList_app_4.
          { pose proof (specializable_noninteracting H).
            apply H3; omega.
          }
          { apply DisjList_comm; auto. }
      + apply DisjList_comm.
        apply DisjList_SubList with (l1:= app (getDefs (specializeMod m (S n)))
                                              (getDefs (duplicate m n))).
        * unfold SubList; intros.
          apply getDefs_in in H3.
          apply in_or_app; auto.
        * apply DisjList_app_4.
          { pose proof (specializable_noninteracting H).
            apply H3; omega.
          }
          { apply DisjList_comm; auto. }
  Qed.

  Section TwoModules.
    Variables (m1 m2: Modules).
    Hypotheses (Hsp1: Specializable m1)
               (Hsp2: Specializable m2)
               (Hequiv1: ModEquiv type typeUT m1)
               (Hequiv2: ModEquiv type typeUT m2)
               (Hvr1: ValidRegsModules type m1)
               (Hvr2: ValidRegsModules type m2)
               (Hexts: SubList (getExtMeths m1) (getExtMeths m2)).

    Lemma specializer_equiv:
      forall {A} (m: M.t A),
        M.KeysSubset m (spDom m1) ->
        M.KeysSubset m (spDom m2) ->
        forall i,
          renameMap (specializer m1 i) m = renameMap (specializer m2 i) m.
    Proof. intros; do 2 (rewrite specializer_map; auto). Qed.

    Lemma specializeMod_defCallSub:
      forall i,
        DefCallSub m1 m2 ->
        DefCallSub (specializeMod m1 i) (specializeMod m2 i).
    Proof.
      unfold DefCallSub; intros; dest; split.
      - do 2 rewrite specializeMod_defs by assumption.
        apply SubList_map; auto.
      - do 2 rewrite specializeMod_calls by assumption.
        apply SubList_map; auto.
    Qed.

    Lemma duplicate_defCallSub:
      forall n,
        DefCallSub m1 m2 ->
        DefCallSub (duplicate m1 n) (duplicate m2 n).
    Proof.
      induction n; simpl; intros.
      - apply specializeMod_defCallSub; auto.
      - apply DefCallSub_modular; auto.
        apply specializeMod_defCallSub; auto.
    Qed.

    Lemma specializer_two_comm:
      forall (m: MethsT),
        M.KeysSubset m (getExtMeths m1) ->
        forall i,
          m = renameMap (specializer m2 i) (renameMap (specializer m1 i) m).
    Proof.
      intros.
      replace (renameMap (specializer m1 i) m) with (renameMap (specializer m2 i) m).
      - rewrite renameMapFInvG; auto.
        + apply specializer_bijective.
          apply specializable_disj_dom_img; auto.
        + apply specializer_bijective.
          apply specializable_disj_dom_img; auto.
      - apply eq_sym, specializer_equiv.
        + eapply M.KeysSubset_SubList; eauto.
          pose proof (getExtMeths_meths m1).
          apply SubList_trans with (l2:= app (getDefs m1) (getCalls m1)); auto.
          apply SubList_app_3; [apply spDom_defs|apply spDom_calls].
        + apply M.KeysSubset_SubList with (d2:= getExtMeths m2) in H; auto.
          eapply M.KeysSubset_SubList; eauto.
          pose proof (getExtMeths_meths m2).
          apply SubList_trans with (l2:= app (getDefs m2) (getCalls m2)); auto.
          apply SubList_app_3; [apply spDom_defs|apply spDom_calls].
    Qed.

    Lemma duplicate_traceRefines:
      forall n,
        traceRefines (liftToMap1 (@idElementwise _)) m1 m2 ->
        traceRefines (liftToMap1 (@idElementwise _)) (duplicate m1 n) (duplicate m2 n).
    Proof.
      induction n; simpl; intros.
      - apply specialized_2 with (i:= O); auto.
        eapply traceRefines_label_map; eauto using H.
        clear; unfold EquivalentLabelMap; intros.
        rewrite idElementwiseId; unfold id; simpl.
        unfold liftPRename; simpl.
        apply specializer_two_comm; auto.

      - apply traceRefines_modular_noninteracting; auto.
        + apply specializeMod_ModEquiv; auto.
        + apply specializeMod_ModEquiv; auto.
        + apply duplicate_ModEquiv; auto.
        + apply duplicate_ModEquiv; auto.
        + apply duplicate_disj_regs; auto.
        + apply duplicate_disj_regs; auto.
        + pose proof (duplicate_validRegsModules m1 (S n) Hvr1); auto.
        + pose proof (duplicate_validRegsModules m2 (S n) Hvr2); auto.
        + apply duplicate_disj_defs; auto.
        + apply duplicate_disj_calls; auto.
        + apply duplicate_disj_defs; auto.
        + apply duplicate_disj_calls; auto.
        + apply duplicate_noninteracting; auto.
        + apply duplicate_noninteracting; auto.
        + apply specialized_2 with (i:= S n); auto.
          eapply traceRefines_label_map; eauto using H.
          clear; unfold EquivalentLabelMap; intros.
          rewrite idElementwiseId; unfold id; simpl.
          unfold liftPRename; simpl.
          apply specializer_two_comm; auto.
    Qed.

  End TwoModules.
      
End DuplicateFacts.

Require Import MetaSyntax.

Section DupRep.
  Variable m: Modules.
  Variable n: nat.

  Fixpoint regsToRep (regs: list RegInitT) :=
    match regs with
    | nil => nil
    | r :: rs =>
      (Rep (attrName r) (fun _ => (attrType r)) n)
        :: (regsToRep rs)
    end.

  Fixpoint rulesToRep (rules: list (Attribute (Action Void))) :=
    match rules with
    | nil => nil
    | r :: rs =>
      (Rep (attrName r) (fun i => (fun ty => renameAction (specializer m i) (attrType r ty))) n)
        :: (rulesToRep rs)
    end.

  Fixpoint methsToRep (meths: list DefMethT): list MetaMeth :=
    match meths with
    | nil => nil
    | dm :: dms =>
      (Rep (attrName dm) (fun i : nat =>
                            existT MethodT _ (fun ty arg =>
                                                renameAction (specializer m i)
                                                             (projT2 (attrType dm) ty arg))) n)
        :: (methsToRep dms)
    end.

  Definition duplicateByRep := 
    makeModule {| metaRegs := regsToRep (getRegInits m);
                  metaRules := rulesToRep (getRules m);
                  metaMeths := methsToRep (getDefsBodies m) |}.
  
  Lemma duplicate_refines_repeat:
    duplicate m n <<== makeModule {| metaRegs := regsToRep (getRegInits m);
                                     metaRules := rulesToRep (getRules m);
                                     metaMeths := methsToRep (getDefsBodies m) |}.
  Proof.
    unfold makeModule; simpl.
    rewrite idElementwiseId.
    apply traceRefines_same_module_structure; simpl.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Qed.

End DupRep.

Hint Unfold specializeMod duplicate: ModuleDefs.

