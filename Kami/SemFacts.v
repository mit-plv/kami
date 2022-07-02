Require Import Bool String List Program.Equality Program.Basics.
Require Import FunctionalExtensionality Classes.Morphisms.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct Lib.StringEq.
Require Import Kami.Syntax Kami.Semantics Kami.Wf.

Set Implicit Arguments.
Set Asymmetric Patterns.

Ltac specializeAll k :=
  repeat
    match goal with
    | [H: forall _, _ |- _] => specialize (H k)
    end.

Section LiftToMap.
  Variable A: Type.
  Variable p: M.key -> A -> option A.

  Lemma transpose_neqkey_rmModify:
    M.F.P.transpose_neqkey eq (rmModify p).
  Proof.
    unfold M.F.P.transpose_neqkey; intros.
    unfold rmModify.
    destruct (p k e), (p k' e'); intuition.
  Qed.

  Theorem liftToMap1_empty: liftToMap1 p (M.empty _) = M.empty _.
  Proof.
    unfold liftToMap1, M.fold; reflexivity.
  Qed.

  Theorem liftToMap1_MapsTo:
    forall m k v, M.MapsTo k v (liftToMap1 p m) <->
                  exists v', p k v' = Some v /\ M.MapsTo k v' m.
  Proof.
    intros m; M.mind m.
    - constructor; intros.
      + apply M.F.P.F.empty_mapsto_iff in H; intuition.
      + dest; subst.
        apply M.F.P.F.empty_mapsto_iff in H0; intuition.
    - constructor; intros.
      unfold liftToMap1 in H1.
      rewrite (M.F.P.fold_add (eqA := eq)) in H1; try apply transpose_neqkey_rmModify; intuition.
      fold (liftToMap1 p m) in H1.
      unfold rmModify in H1.
      case_eq (p k v); intros; subst.
      rewrite H2 in H1.
      + apply M.F.P.F.add_mapsto_iff in H1; dest.
        destruct H1; dest; subst.
        * exists v; intuition.
          apply M.F.P.F.add_mapsto_iff; intuition.
        * destruct (H k0 v0); dest; subst.
          specialize (H4 H3); dest; subst.
          exists x.
          intuition.
          apply M.F.P.F.add_mapsto_iff; intuition.
      + rewrite H2 in H1.
        destruct (H k0 v0); dest; subst.
        specialize (H3 H1); dest; subst.
        exists x.
        intuition.
        apply M.F.P.F.add_mapsto_iff; right; intuition.
        subst.
        apply M.MapsToIn1 in H5.
        intuition.
      + dest; subst.
        apply M.F.P.F.add_mapsto_iff in H2; dest.
        destruct H2; dest; try subst.
        * unfold liftToMap1.
          rewrite (M.F.P.fold_add (eqA := eq)); try apply transpose_neqkey_rmModify; intuition.
          unfold rmModify at 1.
          rewrite H1.
          apply M.F.P.F.add_mapsto_iff; intuition.
        * unfold liftToMap1.
          rewrite (M.F.P.fold_add (eqA := eq)); try apply transpose_neqkey_rmModify; intuition.
          unfold rmModify at 1.
          fold (liftToMap1 p m).
          specialize (H k0 v0).
          assert (sth: exists x, p k0 x = Some v0 /\ M.MapsTo k0 x m) by (eexists; eauto).
          apply H in sth.
          destruct (p k v); intuition.
          apply M.F.P.F.add_mapsto_iff; intuition.
  Qed.

  Lemma liftToMap1_DomainSubset s: M.DomainSubset (liftToMap1 p s) s.
  Proof.
    apply (M.map_induction (P := fun s => M.DomainSubset (liftToMap1 p s) s));
      unfold M.DomainSubset; intros.
    - rewrite liftToMap1_empty in *.
      intuition.
    - unfold liftToMap1 in H1.
      rewrite M.F.P.fold_add in H1; fold (liftToMap1 p m) in *; unfold rmModify.
      + apply M.F.P.F.add_in_iff.
        unfold rmModify in *.
        destruct (p k v).
        apply M.F.P.F.add_in_iff in H1.
        destruct H1; intuition.
        right; apply (H _ H1).
      + intuition.
      + clear; unfold Morphisms.Proper, Morphisms.respectful; intros; subst.
        apply M.leibniz in H1; subst.
        intuition.
      + clear; unfold M.F.P.transpose_neqkey; intros.
        unfold rmModify.
        destruct (p k e), (p k' e');
          try apply M.transpose_neqkey_Equal_add; intuition.
      + intuition.
  Qed.
        
  Theorem liftToMap1_add_one k v:
    liftToMap1 p (M.add k v (M.empty _)) =
    match p k v with
      | Some argRet => M.add k argRet (M.empty _)
      | None => M.empty _
    end.
  Proof.
    case_eq (p k v); unfold liftToMap1, rmModify, M.fold; simpl.
    intros a H.
    rewrite H; reflexivity.
    intros H.
    rewrite H; reflexivity.
  Qed.

  Lemma liftToMap1_find:
    forall (m: M.t A) k,
      M.find k (liftToMap1 p m) = match M.find k m with
                                   | Some v => p k v
                                   | None => None
                                   end.
  Proof.
    intros.
    case_eq (M.find k (liftToMap1 p m)); intros.
    - apply M.Facts.P.F.find_mapsto_iff in H.
      apply liftToMap1_MapsTo in H; dest; subst.
      apply M.F.P.F.find_mapsto_iff in H0.
      rewrite H0; auto.
    - apply M.F.P.F.not_find_in_iff in H.
      case_eq (M.find k m); intros; auto.
      apply M.Facts.P.F.find_mapsto_iff in H0.
      case_eq (p k a); intros; auto.
      assert (exists v', p k v' = Some a0 /\ M.MapsTo k v' m).
      { eexists; eauto. }
      apply liftToMap1_MapsTo in H2.
      elim H. 
      eapply M.MapsToIn1; eauto.
  Qed.

  Ltac liftToMap1_find_tac :=
    repeat
      match goal with
      | [H: context [M.find _ (liftToMap1 _ _)] |- _] =>
        rewrite liftToMap1_find in H
      | [ |- context [M.find _ (liftToMap1 _ _)] ] =>
        rewrite liftToMap1_find
      end.

  Lemma liftToMap1_union:
    forall (m1 m2: M.t A),
      M.Disj m1 m2 ->
      liftToMap1 p (M.union m1 m2) = M.union (liftToMap1 p m1) (liftToMap1 p m2).
  Proof.
    intros; M.ext y.
    findeq.
    findeq_custom liftToMap1_find_tac.
    destruct (p y a); auto.
  Qed.

  Lemma liftToMap1_subtractKV_1:
    forall (deceqA: forall x y : A, sumbool (x = y) (x <> y)) (m1 m2: M.t A),
      M.Disj m1 m2 ->
      M.subtractKV deceqA (liftToMap1 p m1) (liftToMap1 p m2) =
      liftToMap1 p (M.subtractKV deceqA m1 m2).
  Proof.
    intros; M.ext y.
    findeq.
    findeq_custom liftToMap1_find_tac.
    destruct (p y a); auto.
  Qed.

  Lemma liftToMap1_subtractKV_2:
    forall (deceqA: forall x y : A, sumbool (x = y) (x <> y)) (m1 m2: M.t A),
      (forall k v1 v2, M.find k m1 = Some v1 -> M.find k m2 = Some v2 -> v1 = v2) ->
      M.subtractKV deceqA (liftToMap1 p m1) (liftToMap1 p m2) =
      liftToMap1 p (M.subtractKV deceqA m1 m2).
  Proof.
    intros; M.ext y.
    findeq.
    findeq_custom liftToMap1_find_tac.
    - specialize (H _ _ _ (eq_sym Heqv) (eq_sym Heqv0)); subst.
      destruct (p y a0).
      + destruct (deceqA a a); [|elim f; reflexivity].
        destruct (deceqA a0 a0); [|elim f; reflexivity]; auto.
      + destruct (deceqA a0 a0); [|elim f; reflexivity]; auto.
    - destruct (p y a); auto.
  Qed.

End LiftToMap.

(* For global use *)
Ltac liftToMap1_find_tac :=
  repeat
    match goal with
    | [H: context [M.find _ (liftToMap1 _ _)] |- _] =>
      rewrite liftToMap1_find in H
    | [ |- context [M.find _ (liftToMap1 _ _)] ] =>
      rewrite liftToMap1_find
    end.

Lemma liftToMap1_idElementwise_add A m:
  forall k (v: A),
    liftToMap1 (@idElementwise _) (M.add k v m) =
    rmModify (@idElementwise _) k v (liftToMap1 (@idElementwise _) m).
Proof.
  intros; remember (M.find k m) as okm. destruct okm.
  - apply eq_sym, M.find_add_3 in Heqokm.
    destruct Heqokm as [sm [? ?]]; subst.
    rewrite M.add_idempotent.
    unfold liftToMap1.
    rewrite M.F.P.fold_add; auto.
    rewrite M.F.P.fold_add; auto.
    unfold rmModify; simpl in *.
    rewrite M.add_idempotent; reflexivity.
    + apply M.transpose_neqkey_eq_add; intuition.
    + apply M.transpose_neqkey_eq_add; intuition.
  - unfold liftToMap1, rmModify; simpl in *.
    rewrite M.F.P.fold_add; auto.
    apply M.F.P.F.not_find_in_iff; auto.
Qed.

Lemma liftToMap1_idElementwise_id A m:
  liftToMap1 (@idElementwise A) m = m.
Proof.
  M.mind m; simpl in *.
  - rewrite liftToMap1_empty; reflexivity.
  - rewrite liftToMap1_idElementwise_add.
    unfold rmModify; simpl in *.
    rewrite H.
    reflexivity.
Qed.

Lemma idElementwiseId A: liftToMap1 (@idElementwise A) = id.
Proof.
  apply functional_extensionality; intros.
  apply liftToMap1_idElementwise_id.
Qed.

Lemma wellHidden_find_1:
  forall m a (l: LabelT),
    In a (namesOf (getDefsBodies m)) ->
    wellHidden m (hide l) ->
    M.find a (calls l) = None \/ M.find a (defs l) = M.find a (calls l).
Proof.
  unfold wellHidden, hide; intros.
  destruct l as [rm dm cm]; simpl in *; dest.
  specialize (H1 _ H).
  findeq.
Qed.

Lemma wellHidden_find_2:
  forall m a (l: LabelT),
    In a (namesOf (getDefsBodies m)) ->
    In a (getCalls m) ->
    wellHidden m (hide l) ->
    M.find a (defs l) = M.find a (calls l).
Proof.
  unfold wellHidden, hide; intros.
  destruct l as [rm dm cm]; simpl in *; dest.
  specialize (H1 _ H0); specialize (H2 _ H).
  findeq.
Qed.

Lemma wellHidden_weakening:
  forall l m1 m2,
    SubList (getCalls m1) (getCalls m2) ->
    SubList (getDefs m1) (getDefs m2) ->
    wellHidden m2 l ->
    wellHidden m1 l.
Proof.
  unfold wellHidden; intros.
  dest; split.
  - eapply M.KeysDisj_SubList; eauto.
  - eapply M.KeysDisj_SubList; eauto.
Qed.

Lemma wellHidden_split:
  forall ma mb la lb,
    wellHidden (ConcatMod ma mb) (hide (mergeLabel la lb)) ->
    DisjList (getDefs ma) (getDefs mb) ->
    DisjList (getCalls ma) (getIntCalls mb) ->
    DisjList (getIntCalls ma) (getCalls mb) ->
    M.KeysSubset (calls la) (getCalls ma) ->
    M.KeysSubset (calls lb) (getCalls mb) ->
    M.KeysSubset (defs la) (getDefs ma) ->
    M.KeysSubset (defs lb) (getDefs mb) ->
    wellHidden ma (hide la) /\ wellHidden mb (hide lb).
Proof.
  intros.

  assert (M.Disj (defs la) (defs lb))
    by (eapply M.DisjList_KeysSubset_Disj with (d1:= getDefs ma); eauto).
  
  unfold wellHidden in *; dest.
  destruct la as [anna dsa csa], lb as [annb dsb csb].
  simpl in *; split; dest.

  - split.
    + clear H8; red in H1, H2.
      unfold M.KeysDisj, M.KeysSubset in *; intros.
      specializeAll k.
      specialize (H (getCalls_in_1 ma mb _ H8)).
      rewrite M.F.P.F.in_find_iff in *.
      intro Hx; elim H; clear H.
      findeq.
      apply H1.
      apply filter_In; split; [assumption|].
      unfold string_in; apply existsb_exists; exists k.
      split; [assumption|apply string_eq_true].
    + clear H; red in H0.
      unfold M.KeysDisj, M.KeysSubset in *; intros.
      specializeAll k.
      specialize (H8 (getDefs_in_1 ma mb _ H)).
      rewrite M.F.P.F.in_find_iff in *.
      intro Hx; elim H8; clear H8.
      findeq.
        
  - split.
    + clear H8; red in H1, H2.
      unfold M.KeysDisj, M.KeysSubset in *; intros.
      specializeAll k.
      specialize (H (getCalls_in_2 ma mb _ H8)).
      rewrite M.F.P.F.in_find_iff in *.
      intro Hx; elim H; clear H.
      findeq;
        try (remember (M.find k dsb) as v; destruct v;
             remember (M.find k csb) as v; destruct v; findeq).
      * apply H9.
        apply filter_In; split; [assumption|].
        unfold string_in; apply existsb_exists; exists k.
        split; [assumption|apply string_eq_true].
      * apply H9.
        apply filter_In; split; [assumption|].
        unfold string_in; apply existsb_exists; exists k.
        split; [assumption|apply string_eq_true].

    + clear H; red in H0.
      unfold M.KeysDisj, M.KeysSubset in *; intros.
      specializeAll k.
      specialize (H8 (getDefs_in_2 ma mb _ H)).
      rewrite M.F.P.F.in_find_iff in *.
      intro Hx; elim H8; clear H8.
      findeq;
        try (remember (M.find k csb) as v; destruct v;
             remember (M.find k dsb) as v; destruct v; findeq).
      * apply H9, H5; intros; discriminate.
      * specialize (H1 k); destruct H1.
        { elim H1; apply H3; intros; discriminate. }
        { elim H1.
          apply filter_In; split; [assumption|].
          unfold string_in; apply existsb_exists; exists k.
          split; [assumption|apply string_eq_true].
        }
Qed.

Lemma hide_mergeLabel_disj:
  forall la lb,
    M.Disj (defs la) (calls lb) ->
    M.Disj (defs lb) (calls la) ->
    hide (mergeLabel la lb) = mergeLabel (hide la) (hide lb).
Proof.
  unfold hide; destruct la as [anna dsa csa], lb as [annb dsb csb]; simpl; intros.
  f_equal; meq.
Qed.

Lemma hide_mergeLabel_idempotent:
  forall la lb,
    M.Disj (defs la) (defs lb) ->
    M.Disj (calls la) (calls lb) ->
    hide (mergeLabel la lb) = hide (mergeLabel (hide la) (hide lb)).
Proof.
  intros; destruct la as [anna dsa csa], lb as [annb dsb csb].
  simpl in *; unfold hide; simpl; f_equal; meq.
Qed.

Lemma wellHidden_combine:
  forall m la lb,
    wellHidden m la ->
    wellHidden m lb ->
    wellHidden m (mergeLabel la lb).
Proof.
  intros.
  destruct la as [anna dsa csa], lb as [annb dsb csb].
  unfold wellHidden in *; simpl in *; dest.
  split; unfold M.KeysDisj in *; intros.
  - specialize (H k H3); specialize (H0 k H3); findeq.
  - specialize (H2 k H3); specialize (H1 k H3); findeq.
Qed.

Lemma wellHidden_mergeLabel_hide:
  forall m la lb,
    wellHidden m (hide la) ->
    wellHidden m (hide lb) ->
    M.KeysSubset (defs la) (getDefs m) ->
    M.KeysSubset (calls la) (getCalls m) ->
    M.KeysSubset (defs lb) (getDefs m) ->
    M.KeysSubset (calls lb) (getCalls m) ->
    mergeLabel (hide la) (hide lb) = hide (mergeLabel la lb).
Proof.
  intros; destruct la as [anna dsa csa], lb as [annb dsb csb].
  unfold hide, wellHidden in *; simpl in *; dest.
  unfold M.KeysDisj, M.KeysSubset in *.
  f_equal.

  - meq; repeat
           match goal with
           | [H: forall _, _ |- _] => specialize (H y)
           end.
    + elim H0; [apply H4; findeq|findeq].
    + elim H0; [apply H2; findeq|findeq].
    + elim H; [apply H4; findeq|findeq].
    + elim H6; [apply H3; findeq|findeq].
    + elim H6; [apply H3; findeq|findeq].
    + elim H6; [apply H3; findeq|findeq].

  - meq; repeat
           match goal with
           | [H: forall _, _ |- _] => specialize (H y)
           end.
    + elim H0; [apply H4; findeq|findeq].
    + elim H5; [apply H1; findeq|findeq].
    + elim H6; [apply H3; findeq|findeq].
    + elim H; [apply H4; findeq|findeq].
    + elim H; [apply H4; findeq|findeq].
    + elim H; [apply H4; findeq|findeq].
Qed.

Lemma canCombine_CanCombineUL:
  forall m o u1 u2 ul1 ul2 cs1 cs2
         (Hss1: Substep m o u1 ul1 cs1)
         (Hss2: Substep m o u2 ul2 cs2),
    canCombine {| substep := Hss1 |} {| substep := Hss2 |} <->
    CanCombineUL u1 u2 (getLabel ul1 cs1) (getLabel ul2 cs2).
Proof.
  unfold canCombine, CanCombineUL, CanCombineLabel; simpl; intros; split; intros; dest.
  - repeat split; auto.
    + destruct ul1 as [[r1|]|[[dmn1 dmb1]|]], ul2 as [[r2|]|[[dmn2 dmb2]|]]; auto.
      specialize (H0 _ _ eq_refl eq_refl); simpl in H0.
      auto.
    + destruct ul1 as [[r1|]|[[dmn1 dmb1]|]], ul2 as [[r2|]|[[dmn2 dmb2]|]]; auto;
        try (destruct H1; discriminate; fail).
  - repeat split; auto.
    + intros; destruct ul1 as [[r1|]|[[dmn1 dmb1]|]], ul2 as [[r2|]|[[dmn2 dmb2]|]];
        try discriminate.
      inv H3; inv H4; simpl.
      intro Hx; subst.
      specialize (H0 dmn2); destruct H0; findeq.
    + intros; destruct ul1 as [[r1|]|[[dmn1 dmb1]|]], ul2 as [[r2|]|[[dmn2 dmb2]|]];
        eexists; intuition idtac.

      Unshelve.
      exact None.
      exact None.
      exact None.
      exact None.
Qed.
   
Lemma CanCombineLabel_hide:
  forall la lb,
    CanCombineLabel la lb ->
    CanCombineLabel (hide la) (hide lb).
Proof.
  intros; destruct la as [anna dsa csa], lb as [annb dsb csb].
  inv H; simpl in *; dest.
  repeat split; unfold hide; simpl in *; auto.
  - apply M.Disj_Sub with (m2:= dsa); [|apply M.subtractKV_sub].
    apply M.Disj_comm.
    apply M.Disj_Sub with (m2:= dsb); [|apply M.subtractKV_sub].
    auto.
  - apply M.Disj_Sub with (m2:= csa); [|apply M.subtractKV_sub].
    apply M.Disj_comm.
    apply M.Disj_Sub with (m2:= csb); [|apply M.subtractKV_sub].
    auto.
Qed.

Lemma equivalentLabelSeq_length:
  forall p lsa lsb,
    equivalentLabelSeq p lsa lsb ->
    List.length lsa = List.length lsb.
Proof. induction lsa; intros; inv H; simpl; auto. Qed.

Lemma equivalentLabelSeq_CanCombineLabelSeq:
  forall p (Hp: Proper (equivalentLabel p ==> equivalentLabel p ==> impl) CanCombineLabel)
         lsa lsb lsc lsd,
    equivalentLabelSeq p lsa lsb ->
    equivalentLabelSeq p lsc lsd ->
    CanCombineLabelSeq lsa lsc ->
    CanCombineLabelSeq lsb lsd.
Proof.
  ind lsa.
  - destruct lsc; intuition idtac.
    inv H; inv H0; constructor.
  - destruct lsc; intuition idtac.
    inv H; inv H0; constructor; [|eapply IHlsa; eauto].
    eapply Hp; eauto.
Qed.

Lemma hide_idempotent:
  forall (l: LabelT), hide l = hide (hide l).
Proof.
  intros; destruct l as [ann ds cs].
  unfold hide; simpl; f_equal;
  apply M.subtractKV_idempotent.
Qed.

Lemma hide_empty:
  forall a,
    hide {| annot := a; defs := []%fmap; calls := []%fmap |} =
    {| annot := a; defs := []%fmap; calls := []%fmap |}.
Proof. reflexivity. Qed.

Lemma step_empty:
  forall m o a,
    (a = None \/ a = Some None) ->
    Step m o []%fmap {| annot := a; defs := []%fmap; calls := []%fmap |}.
Proof.
  intros; apply step_consistent.
  rewrite <-hide_empty.
  constructor; [|unfold wellHidden; cbn; split; apply M.KeysDisj_empty].

  destruct H; subst.
  - constructor.
  - eapply SubstepsCons.
    + apply SubstepsNil.
    + apply EmptyRule.
    + repeat split; auto.
    + reflexivity.
    + reflexivity.
Qed.

Lemma step_hide:
  forall m o u l,
    Step m o u l -> hide l = l.
Proof.
  intros; apply step_consistent in H; inv H.
  rewrite <-hide_idempotent; auto.
Qed.

Inductive HiddenLabelSeq: LabelSeqT -> Prop :=
| HLSNil: HiddenLabelSeq nil
| HLSCons:
    forall l ll,
      HiddenLabelSeq ll ->
      hide l = l ->
      HiddenLabelSeq (l :: ll).

Lemma behavior_hide:
  forall m n ll,
    Behavior m n ll -> HiddenLabelSeq ll.
Proof.
  intros; inv H.
  induction HMultistepBeh; [constructor|].
  constructor; auto.
  eapply step_hide; eauto.
Qed.

Section EmptyDefs.
  Variable m: Modules.
  Variable o: RegsT.
  Variable defsZero: getDefsBodies m = nil.
  
  Theorem substepsInd_zero u l:
    SubstepsInd m o u l ->
    defs l = M.empty _ /\
    Substep m o u match annot l with
                    | None => Meth None
                    | Some r => Rle r
                  end (calls l).
  Proof.
    intros si.
    dependent induction si.
    - constructor; econstructor; eauto.
    - dest; destruct l; subst.
      inv H; simpl in *; repeat rewrite M.union_empty_L; constructor; auto;
      repeat rewrite M.union_empty_R; unfold CanCombineUUL in *; simpl in *; dest.
      + destruct annot; intuition.
        inversion H4.
        econstructor; eauto.
      + destruct annot; auto.
      + destruct annot.
        * intuition.
        * inversion H4.
          rewrite M.union_empty_L, M.union_empty_R.
          econstructor; eauto.
      + rewrite defsZero in *.
        intuition.
      + rewrite defsZero in *.
        intuition.
  Qed.

  Theorem substepsInd_zero_hide u l:
    SubstepsInd m o u l ->
    hide l = l.
  Proof.
    intros si.
    apply substepsInd_zero in si; dest.
    unfold hide; destruct l; simpl in *; subst.
    rewrite M.subtractKV_empty_1.
    rewrite M.subtractKV_empty_2.
    reflexivity.
  Qed.

  Theorem step_zero u l:
    Step m o u l ->
    defs l = M.empty _ /\
    Substep m o u match annot l with
                    | None => Meth None
                    | Some r => Rle r
                  end (calls l).
  Proof.
    intros si.
    apply step_consistent in si.
    inv si.
    apply substepsInd_zero.
    rewrite substepsInd_zero_hide with (u := u); auto.
  Qed.

  Theorem substepZero_imp_step u a cs:
    Substep m o u a cs ->
    Step m o u (getLabel a cs).
  Proof.
    intros si.
    assert (sth: substepsComb ({| substep := si |} :: nil)).
    { constructor 2.
      constructor.
      intuition.
    }
    pose proof (StepIntro sth); simpl in *.
    unfold addLabelLeft in H;
      unfold getSLabel in H.
    assert (ua: unitAnnot
                  {| upd := u; unitAnnot := a; cms := cs; substep := si |} = a) by reflexivity.
    rewrite ua in H.
    assert (ub: cms
                  {| upd := u; unitAnnot := a; cms := cs; substep := si |} = cs) by reflexivity.
    rewrite ub in H.
    clear ua ub.
    assert (st: mergeLabel (getLabel a cs) {| annot := None;
                                          defs := M.empty _;
                                          calls := M.empty _ |} = getLabel a cs).
    { simpl.
      destruct a.
      - repeat rewrite M.union_empty_L, M.union_empty_R.
        reflexivity.
      - destruct o0;
        try destruct a; repeat rewrite M.union_empty_L; repeat rewrite M.union_empty_R;
        try reflexivity.
    }
    rewrite st in H; clear st.
    rewrite M.union_empty_L in H.
    assert (s: hide (getLabel a cs) = getLabel a cs).
    { clear H sth.
      unfold hide.
      simpl.
      destruct a; destruct o0; try destruct a; repeat rewrite M.subtractKV_empty_1;
      repeat rewrite M.subtractKV_empty_2; try reflexivity.
      inv si.
      rewrite defsZero in HIn.
      intuition.
    }
    rewrite s in *; clear s.
    assert (t: wellHidden m (getLabel a cs)).
    { clear sth H.
      unfold wellHidden.
      simpl in *.
      unfold getDefs.
      rewrite defsZero.
      simpl in *.
      destruct a;
      constructor;
      destruct o0; try destruct a;
      try apply M.KeysDisj_empty; try apply M.KeysDisj_nil.
      inversion si.
      rewrite defsZero in HIn.
      intuition.
    }
    apply H; intuition.
  Qed.

End EmptyDefs.

Lemma DisjList_string_cons:
  forall l1 l2 (e: string),
    ~ In e l2 -> DisjList l1 l2 -> DisjList (e :: l1) l2.
Proof.
  unfold DisjList; intros.
  destruct (string_dec e e0); subst; auto.
  pose proof (H0 e0); clear H0.
  inv H1; auto.
  left; intro Hx; inv Hx; auto.
Qed.

Lemma isLeaf_implies_disj:
  forall {retK} (a: ActionT typeUT retK) calls,
    true = isLeaf a calls -> DisjList (getCallsA a) calls.
Proof.
  induction a; simpl; intros; auto.
  - apply eq_sym, andb_true_iff in H0; dest.
    remember (string_in _ _) as sin; destruct sin; [inv H0|].
    apply string_in_dec_not_in in Heqsin.
    apply DisjList_string_cons; auto.
  - apply eq_sym, andb_true_iff in H0; dest.
    apply andb_true_iff in H0; dest.
    apply DisjList_app_4; auto.
    apply DisjList_app_4; auto.
  - apply DisjList_nil_1.
Qed.

Lemma noCallsRules_implies_disj:
  forall calls rules,
    noCallsRules rules calls = true ->
    DisjList (getCallsR rules) calls.
Proof.
  induction rules; simpl; intros; [apply DisjList_nil_1|].
  remember (isLeaf (attrType a typeUT) calls) as blf; destruct blf; [|discriminate].
  apply DisjList_app_4.
  - apply isLeaf_implies_disj; auto.
  - apply IHrules; auto.
Qed.

Lemma noCallsDms_implies_disj:
  forall calls dms,
    noCallsDms dms calls = true ->
    DisjList (getCallsM dms) calls.
Proof.
  induction dms; simpl; intros; [apply DisjList_nil_1|].
  remember (isLeaf (projT2 (attrType a) typeUT tt) calls) as blf; destruct blf; [|discriminate].
  apply DisjList_app_4.
  - apply isLeaf_implies_disj; auto.
  - apply IHdms; auto.
Qed.

Lemma noInternalCalls_implies_disj:
  forall m,
    noInternalCalls m = true ->
    DisjList (getCalls m) (getDefs m).
Proof.
  unfold noInternalCalls, noCalls, getCalls, getDefs; simpl; intros.
  apply andb_true_iff in H; dest.
  apply DisjList_app_4.
  - apply noCallsRules_implies_disj; auto.
  - apply noCallsDms_implies_disj; auto.
Qed.

Section Calls.
  Variable m: Modules.
  Variable mEquiv: ModEquiv type typeUT m.

  Lemma callsA_subset k (a1: ActionT type k) (a2: ActionT typeUT k):
    ActionEquiv a1 a2 ->
    forall o u cs r,
      SemAction o a1 u cs r ->
      forall x, M.In x cs -> In x (getCallsA a2).
  Proof.
    intro ae.
    induction ae; fold type in *; fold typeUT in *; subst; intros.
    - dependent destruction H1.
      apply M.F.P.F.add_in_iff in H2.
      specialize (@H0 _ tt _ _ _ _ H1 x).
      simpl in *.
      destruct H2; subst; intuition.
    - dependent destruction H1.
      specialize (H0 (evalExpr e1)).
      apply (H0 _ _ _ _ _ H1 x H2).
    - dependent destruction H1.
      apply (H0 _ _ _ _ _ _ H1 x H2).
    - dependent destruction H1.
      apply (H0 _ _ _ _ _ _ H1 x H2).
    - dependent destruction H.
      apply (@IHae _ _ _ _ H x H0).
    - dependent destruction H1.
      apply M.union_In in H2.
      simpl in *.
      specialize (IHae1 _ _ _ _ H1_ x).
      specialize (H0 _ tt _ _ _ _ H1_0 x).
      destruct H2.
      + apply in_or_app.
        intuition.
      + apply in_or_app; right; apply in_or_app.
        intuition.
      + specialize (IHae2 _ _ _ _ H1_ x).
        specialize (H0 _ tt _ _ _ _ H1_0 x).
        simpl in *.
        apply M.union_In in H2.
        destruct H2;
          apply in_or_app; right; apply in_or_app;
            intuition.
    - dependent destruction H.
      apply (IHae _ _ _ _ H x H0).
    - dependent destruction H.
      apply M.F.P.F.empty_in_iff in H0; intuition.
  Qed.

  Lemma callsR_subset:
    forall o u rName cs,
      Substep m o u (Rle (Some rName)) cs ->
      forall x, M.In x cs -> exists a, In (rName :: a)%struct (getRules m) /\
                                       In x (getCallsA (a typeUT)).
  Proof.
    destruct mEquiv.
    clear mEquiv H0.
    intros.
    dependent destruction H0.
    exists a.
    constructor.
    intuition.
    pose proof (proj1 (RulesEquiv_in type typeUT (getRules m)) H _ HInRules).
    apply (callsA_subset H0 HAction); intuition.
  Qed.

  Lemma callsM_subset:
    forall o u mName argRet cs,
      Substep m o u (Meth (Some (mName :: argRet)%struct)) cs ->
      forall x, M.In x cs -> exists a, In (mName :: a)%struct (getDefsBodies m) /\
                                      In x (getCallsA (projT2 a typeUT tt)).
  Proof.
    destruct mEquiv.
    clear mEquiv H.
    intros.
    dependent destruction H.
    destruct f.
    exists attrType.
    constructor.
    intuition.
    pose proof (proj1 (MethsEquiv_in type typeUT (getDefsBodies m)) H0  _ HIn argV tt).
    apply (callsA_subset H HAction); intuition.
  Qed.

  Lemma getCalls_rules_subset (a: Action Void) rName:
    forall x,
      In x (getCallsA (a typeUT)) ->
      In (rName :: a)%struct (getRules m) ->
      In x (getCalls m).
  Proof.
    intros.
    unfold getCalls.
    apply in_or_app.
    left.
    induction (getRules m).
    - intuition.
    - simpl in *.
      destruct H0; subst; apply in_or_app; intuition.
  Qed.

  Lemma getCalls_meths_subset (a: sigT MethodT) mName:
    forall x,
      In x (getCallsA (projT2 a typeUT tt)) ->
      In (mName :: a)%struct (getDefsBodies m) ->
      In x (getCalls m).
  Proof.
    intros.
    unfold getCalls.
    apply in_or_app.
    right.
    induction (getDefsBodies m).
    - intuition.
    - simpl in *.
      destruct H0; subst; apply in_or_app; intuition.
  Qed.

  Theorem getCalls_substep o u rm cs:
    Substep m o u rm cs ->
    forall f, M.In f cs -> In f (getCalls m).
  Proof.
    dependent induction rm; dependent induction o0; intros.
    - eapply callsR_subset in H; dest; subst;
        try eapply getCalls_rules_subset in H1; eauto.
    - dependent destruction H.
      apply M.F.P.F.empty_in_iff in H0; intuition.
    - destruct a.
      eapply callsM_subset  in H; dest; subst;
        try eapply getCalls_meths_subset in H1; eauto.
    - dependent destruction H.
      apply M.F.P.F.empty_in_iff in H0; intuition.
  Qed.

  Theorem getCalls_substeps o ss:
    forall f, M.In f (calls (foldSSLabel (m := m) (o := o) ss)) -> In f (getCalls m).
  Proof.
    intros.
    induction ss; simpl in *.
    - exfalso.
      apply (proj1 (M.F.P.F.empty_in_iff _ _) H).
    - unfold addLabelLeft, mergeLabel in *.
      destruct a.
      simpl in *.
      destruct unitAnnot.
      + destruct (foldSSLabel ss); simpl in *.
        pose proof (M.union_In H) as sth.
        destruct sth.
        * apply (getCalls_substep substep); intuition.
        * intuition.
      + destruct (foldSSLabel ss); simpl in *.
        dependent destruction o0; simpl in *.
        * dependent destruction a; simpl in *.
          pose proof (M.union_In H) as sth.
          { destruct sth.
            - apply (getCalls_substep substep); intuition.
            - intuition.
          }
        * pose proof (M.union_In H) as sth.
          { destruct sth.
            - apply (getCalls_substep substep); intuition.
            - intuition.
          }
  Qed.

End Calls.

Theorem getDefs_substep m o u far cs:
  Substep m o u (Meth (Some far)) cs ->
  List.In (attrName far) (getDefs m).
Proof.
  intros.
  dependent induction H; simpl in *.
  unfold getDefs in *.
  clear - HIn.
  induction (getDefsBodies m).
  - intuition.
  - simpl in *.
    destruct HIn.
    + subst.
      left; intuition.
    + right; intuition.
Qed.

Theorem getDefs_substepsInd m o u l:
  SubstepsInd m o u l ->
  forall x, M.In x (defs l) -> List.In x (getDefs m).
Proof.
  intros.
  dependent induction H; simpl in *.
  - apply M.F.P.F.empty_in_iff in H0; intuition.
  - destruct sul.
    destruct l.
    destruct annot; simpl in *; subst; simpl in *;
    rewrite M.union_empty_L in H4; simpl in *; apply IHSubstepsInd; intuition.
    destruct l.
    destruct o0.
    + destruct a.
      destruct ll.
      simpl in *.
      inv H3.
      apply M.union_In in H4.
      destruct H4.
      * apply M.F.P.F.add_in_iff in H2.
        { destruct H2; subst.
          - apply getDefs_substep in H0.
            assumption.
          - apply M.F.P.F.empty_in_iff in H2; intuition.
        }
      * apply IHSubstepsInd; intuition.
    + destruct ll.
      simpl in *.
      rewrite M.union_empty_L in H3.
      inv H3.
      apply IHSubstepsInd; intuition.
Qed.

Theorem getDefs_substeps m o ss:
  forall f, M.In f (defs (foldSSLabel (m := m) (o := o) ss)) -> In f (getDefs m).
Proof.
  intros.
  induction ss; simpl in *.
  - exfalso.
    apply (proj1 (M.F.P.F.empty_in_iff _ _) H).
  - unfold addLabelLeft, mergeLabel in *.
    destruct a.
    simpl in *.
    destruct unitAnnot.
    + destruct (foldSSLabel ss); simpl in *.
      rewrite M.union_empty_L in H.
      intuition.
    + destruct (foldSSLabel ss); simpl in *.
      dependent destruction o0; simpl in *.
      * dependent destruction a; simpl in *.
        pose proof (M.union_In H) as sth.
        { destruct sth.
          - apply M.F.P.F.add_in_iff in H0.
            destruct H0.
            + subst.
              apply (getDefs_substep substep).
            + exfalso; apply ((proj1 (M.F.P.F.empty_in_iff _ _)) H0).
          - intuition.
        }
      * rewrite M.union_empty_L in H.
        intuition.
Qed.

Lemma mergeLabel_assoc:
  forall l1 l2 l3,
    mergeLabel (mergeLabel l1 l2) l3 = mergeLabel l1 (mergeLabel l2 l3).
Proof.
  intros; destruct l1 as [[[|]|] ? ?], l2 as [[[|]|] ? ?], l3 as [[[|]|] ? ?];
    unfold mergeLabel; try reflexivity; try (f_equal; auto).
Qed.

Lemma substepsInd_defs_sig:
  forall m dm,
    NoDup (getDefs m) ->
    In dm (getDefsBodies m) ->
    forall o u l,
      SubstepsInd m o u l ->
      forall s,
        Some s = M.find (elt:=sigT SignT) (attrName dm) (defs l) ->
        projT1 s = projT1 (attrType dm).
Proof.
  induction 3; simpl; intros; [mred|].
  subst; destruct sul as [|odm].

  - apply IHSubstepsInd.
    destruct l as [ann ds cs]; simpl in *; findeq.

  - destruct odm as [dm'|].
    + destruct dm as [dmn dmb], dm' as [dmn' dmb'], l as [ann ds cs]; simpl in *.
      destruct (string_dec dmn dmn').
      * subst; mred.
        inv H2; inv Hsig; simpl in *.
        destruct f as [fn fb]; simpl in *.
        f_equal.
        assert ((fn :: fb)%struct = (fn :: dmb)%struct).
        { eapply in_NoDup_attr; eauto. }
        inv H2; auto.
      * apply IHSubstepsInd; findeq.
    + apply IHSubstepsInd.
      destruct l as [ann ds cs]; simpl in *; findeq.
Qed.

Lemma substepsInd_defs_in:
  forall m or u l,
    SubstepsInd m or u l -> M.KeysSubset (defs l) (getDefs m).
Proof.
  induction 1; simpl; [apply M.KeysSubset_empty|].
  subst; destruct l as [ann ds cs]; simpl in *.
  apply M.KeysSubset_union; auto.
  destruct sul as [|[[dmn dmv]|]]; try (apply M.KeysSubset_empty).
  apply M.KeysSubset_add; [apply M.KeysSubset_empty|].
  pose proof (getDefs_substep H0); auto.
Qed.

Lemma substepsInd_calls_in:
  forall m (Hequiv: ModEquiv type typeUT m) or u l,
    SubstepsInd m or u l -> M.KeysSubset (calls l) (getCalls m).
Proof.
  induction 2; simpl; [apply M.KeysSubset_empty|].
  subst; destruct l as [ann ds cs]; simpl in *.
  apply M.KeysSubset_union; auto.
  pose proof (getCalls_substep Hequiv H0); auto.
Qed.

Lemma step_defs_in:
  forall m or u l,
    Step m or u l -> M.KeysSubset (defs l) (getDefs m).
Proof.
  intros; apply step_consistent in H; inv H.
  apply substepsInd_defs_in in HSubSteps; auto.
  destruct l0 as [ann ds cs]; unfold hide in *; simpl in *.
  eapply M.KeysSubset_Sub; eauto.
  apply M.subtractKV_sub.
Qed.

Lemma step_calls_in:
  forall m (Hequiv: ModEquiv type typeUT m) or u l,
    Step m or u l -> M.KeysSubset (calls l) (getCalls m).
Proof.
  intros; apply step_consistent in H; inv H.
  apply substepsInd_calls_in in HSubSteps; auto.
  destruct l0 as [ann ds cs]; unfold hide in *; simpl in *.
  eapply M.KeysSubset_Sub; eauto.
  apply M.subtractKV_sub.
Qed.

Lemma multistep_defs_in:
  forall m or ll u,
    Multistep m or u ll -> Forall (fun l => M.KeysSubset (defs l) (getDefs m)) ll.
Proof.
  induction ll; intros; auto.
  inv H; constructor; eauto.
  eapply step_defs_in; eauto.
Qed.

Lemma multistep_calls_in:
  forall m (Hequiv: ModEquiv type typeUT m) or ll u,
    Multistep m or u ll -> Forall (fun l => M.KeysSubset (calls l) (getCalls m)) ll.
Proof.
  induction ll; intros; auto.
  inv H; constructor; eauto.
  eapply step_calls_in; eauto.
Qed.

Lemma behavior_defs_in:
  forall m ll u,
    Behavior m u ll -> Forall (fun l => M.KeysSubset (defs l) (getDefs m)) ll.
Proof.
  intros; inv H.
  eapply multistep_defs_in; eauto.
Qed.

Lemma behavior_calls_in:
  forall m (Hequiv: ModEquiv type typeUT m) ll u,
    Behavior m u ll -> Forall (fun l => M.KeysSubset (calls l) (getCalls m)) ll.
Proof.
  intros; inv H.
  eapply multistep_calls_in; eauto.
Qed.
      
Lemma step_defs_disj:
  forall m or u l,
    Step m or u l -> M.KeysDisj (defs l) (getCalls m).
Proof.
  intros; apply step_consistent in H.
  inv H; destruct l0 as [ann ds cs].
  unfold wellHidden, hide in *; simpl in *; dest; auto.
Qed.

Lemma step_calls_disj:
  forall m or u l,
    Step m or u l -> M.KeysDisj (calls l) (getDefs m).
Proof.
  intros; apply step_consistent in H.
  inv H; destruct l0 as [ann ds cs].
  unfold wellHidden, hide in *; simpl in *; dest; auto.
Qed.

Lemma multistep_defs_disj:
  forall m or ll u,
    Multistep m or u ll ->
    Forall (fun l => M.KeysDisj (defs l) (getCalls m)) ll.
Proof.
  induction ll; intros; auto.
  inv H; constructor.
  - eapply step_defs_disj; eauto.
  - eapply IHll; eauto.
Qed.

Lemma multistep_calls_disj:
  forall m or ll u,
    Multistep m or u ll ->
    Forall (fun l => M.KeysDisj (calls l) (getDefs m)) ll.
Proof.
  induction ll; intros; auto.
  inv H; constructor.
  - eapply step_calls_disj; eauto.
  - eapply IHll; eauto.
Qed.

Lemma behavior_defs_disj:
  forall m ll n,
    Behavior m n ll ->
    Forall (fun l => M.KeysDisj (defs l) (getCalls m)) ll.
Proof.
  induction ll; intros; auto.
  inv H; inv HMultistepBeh; constructor.
  - eapply step_defs_disj; eauto.
  - eapply IHll.
    econstructor; eauto.
Qed.

Lemma behavior_calls_disj:
  forall m ll n,
    Behavior m n ll ->
    Forall (fun l => M.KeysDisj (calls l) (getDefs m)) ll.
Proof.
  induction ll; intros; auto.
  inv H; inv HMultistepBeh; constructor.
  - eapply step_calls_disj; eauto.
  - eapply IHll.
    econstructor; eauto.
Qed.

Lemma step_defs_extDefs_in:
  forall m (Hequiv: ModEquiv type typeUT m) o u l,
    Step m o u l ->
    M.KeysSubset (defs l) (getExtDefs m).
Proof.
  intros.
  pose proof (step_defs_in H).
  pose proof (step_defs_disj H).

  unfold M.KeysSubset, M.KeysDisj in *; intros.
  specialize (H0 k H2).
  specialize (H1 k).
  destruct (in_dec string_dec k (getCalls m)); intuition idtac.
  apply filter_In; split; auto.
  apply negb_true_iff.
  remember (string_in k (getCalls m)) as kin; destruct kin; auto.
  apply string_in_dec_in in Heqkin; elim n; auto.
Qed.

Lemma step_defs_ext_in:
  forall m (Hequiv: ModEquiv type typeUT m) o u l,
    Step m o u l ->
    M.KeysSubset (defs l) (getExtMeths m).
Proof.
  intros.
  pose proof (step_defs_extDefs_in Hequiv H).
  eapply M.KeysSubset_SubList; eauto.
  apply SubList_app_1, SubList_refl.
Qed.

Lemma step_calls_extCalls_in:
  forall m (Hequiv: ModEquiv type typeUT m) o u l,
    Step m o u l ->
    M.KeysSubset (calls l) (getExtCalls m).
Proof.
  intros.
  pose proof (step_calls_in Hequiv H).
  pose proof (step_calls_disj H).

  unfold M.KeysSubset, M.KeysDisj in *; intros.
  specialize (H0 k H2).
  specialize (H1 k).
  destruct (in_dec string_dec k (getDefs m)); intuition idtac.
  apply filter_In; split; auto.
  apply negb_true_iff.
  remember (string_in k (getDefs m)) as kin; destruct kin; auto.
  apply string_in_dec_in in Heqkin; elim n; auto.
Qed.

Lemma step_calls_ext_in:
  forall m (Hequiv: ModEquiv type typeUT m) o u l,
    Step m o u l ->
    M.KeysSubset (calls l) (getExtMeths m).
Proof.
  intros.
  pose proof (step_calls_extCalls_in Hequiv H).
  eapply M.KeysSubset_SubList; eauto.
  apply SubList_app_2, SubList_refl.
Qed.

Lemma multistep_defs_extDefs_in:
  forall m (Hequiv: ModEquiv type typeUT m) or ll u,
    Multistep m or u ll -> Forall (fun l => M.KeysSubset (defs l) (getExtDefs m)) ll.
Proof.
  induction ll; intros; auto.
  inv H; constructor; eauto.
  eapply step_defs_extDefs_in; eauto.
Qed.

Lemma multistep_calls_extCalls_in:
  forall m (Hequiv: ModEquiv type typeUT m) or ll u,
    Multistep m or u ll -> Forall (fun l => M.KeysSubset (calls l) (getExtCalls m)) ll.
Proof.
  induction ll; intros; auto.
  inv H; constructor; eauto.
  eapply step_calls_extCalls_in; eauto.
Qed.

Lemma multistep_defs_ext_in:
  forall m (Hequiv: ModEquiv type typeUT m) or ll u,
    Multistep m or u ll -> Forall (fun l => M.KeysSubset (defs l) (getExtMeths m)) ll.
Proof.
  induction ll; intros; auto.
  inv H; constructor; eauto.
  apply M.KeysSubset_SubList with (d1:= getExtDefs m).
  - eapply step_defs_extDefs_in; eauto.
  - apply SubList_app_1, SubList_refl.
Qed.

Lemma multistep_calls_ext_in:
  forall m (Hequiv: ModEquiv type typeUT m) or ll u,
    Multistep m or u ll -> Forall (fun l => M.KeysSubset (calls l) (getExtMeths m)) ll.
Proof.
  induction ll; intros; auto.
  inv H; constructor; eauto.
  apply M.KeysSubset_SubList with (d1:= getExtCalls m).
  - eapply step_calls_extCalls_in; eauto.
  - apply SubList_app_2, SubList_refl.
Qed.

Lemma behavior_defs_extDefs_in:
  forall m (Hequiv: ModEquiv type typeUT m) ll u,
    Behavior m u ll -> Forall (fun l => M.KeysSubset (defs l) (getExtDefs m)) ll.
Proof.
  intros; inv H.
  eapply multistep_defs_extDefs_in; eauto.
Qed.

Lemma behavior_calls_extCalls_in:
  forall m (Hequiv: ModEquiv type typeUT m) ll u,
    Behavior m u ll -> Forall (fun l => M.KeysSubset (calls l) (getExtCalls m)) ll.
Proof.
  intros; inv H.
  eapply multistep_calls_extCalls_in; eauto.
Qed.

Lemma behavior_defs_ext_in:
  forall m (Hequiv: ModEquiv type typeUT m) ll u,
    Behavior m u ll -> Forall (fun l => M.KeysSubset (defs l) (getExtMeths m)) ll.
Proof.
  intros; inv H.
  eapply multistep_defs_ext_in; eauto.
Qed.

Lemma behavior_calls_ext_in:
  forall m (Hequiv: ModEquiv type typeUT m) ll u,
    Behavior m u ll -> Forall (fun l => M.KeysSubset (calls l) (getExtMeths m)) ll.
Proof.
  intros; inv H.
  eapply multistep_calls_ext_in; eauto.
Qed.

Lemma substepsInd_rule_split:
  forall m o u l,
    SubstepsInd m o u l ->
    forall or,
      annot l = Some or ->
      exists ru rcs pu pl,
        Substep m o ru (Rle or) rcs /\
        SubstepsInd m o pu pl /\
        CanCombineUUL pu pl ru rcs (Rle or) /\
        u = M.union pu ru /\
        l = mergeLabel (getLabel (Rle or) rcs) pl.
Proof.
  induction 1; simpl; intros; [inv H|].

  subst; destruct sul as [|].

  - clear IHSubstepsInd.
    exists su, scs, u, l.

    destruct l as [ann ds cs]; inv H1; dest; simpl in *.
    destruct ann; [inv H3|].
    inv H4.
    repeat split; auto.

  - clear H.
    destruct l as [ann ds cs]; simpl in *; subst.
    specialize (IHSubstepsInd _ eq_refl).
    destruct IHSubstepsInd as [ru [rcs [pu [pl ?]]]]; dest; subst.

    exists ru, rcs, (M.union pu su), (mergeLabel (getLabel (Meth o0) scs) pl).
    
    destruct pl as [pann pds pcs]; inv H1; inv H3; dest; simpl in *.
    destruct pann as [|]; [inv H7|]; inv H5.

    repeat split; auto.
    + econstructor.
      * exact H2.
      * exact H0.
      * repeat split; auto.
      * reflexivity.
      * reflexivity.
    + simpl; auto.
    + f_equal; auto.
      
Qed.

Lemma substep_filterDm:
  forall regs rules dms o u ul cs dmn,
    Substep (Mod regs rules dms) o u ul cs ->
    (forall s, ul <> Meth (Some (dmn :: s)%struct)) ->
    Substep (Mod regs rules (filterDm dms dmn)) o u ul cs.
Proof.
  intros; inv H; try (econstructor; eauto; fail).
  destruct f as [fn fb]; simpl in *.
  destruct (string_dec fn dmn).

  - subst; exfalso; eapply H0; eauto.
  - econstructor.
    + simpl; apply filter_In; split.
      * exact HIn.
      * simpl; destruct (string_dec _ _); [elim n; auto|]; auto.
    + simpl; eassumption.
    + reflexivity.
Qed.

Lemma substepsInd_filterDm:
  forall regs rules dms o u l dmn,
    SubstepsInd (Mod regs rules dms) o u l ->
    M.find dmn (defs l) = None ->
    SubstepsInd (Mod regs rules (filterDm dms dmn)) o u l.
Proof.
  induction 1; simpl; intros; [constructor|].

  subst; econstructor.
  - apply IHSubstepsInd.
    destruct l as [ann ds cs]; simpl in *; findeq.
  - apply substep_filterDm; eauto.
    intros.
    destruct sul as [|]; [discriminate|].
    destruct o0 as [[dmn' dmb]|]; [|discriminate].
    destruct (string_dec dmn dmn').
    + subst; destruct l as [ann ds cs]; simpl in *; mred.
    + intro Hx; elim n; clear n.
      inv Hx; reflexivity.
  - assumption.
  - reflexivity.
  - reflexivity.
Qed.

Lemma filterDms_getCalls:
  forall regs rules dms filt,
    SubList (getCalls (Mod regs rules (filterDms dms filt)))
            (getCalls (Mod regs rules dms)).
Proof.
  unfold getCalls; simpl; intros.
  apply SubList_app_3; [apply SubList_app_1, SubList_refl|].
  apply SubList_app_2.

  clear.
  induction dms; simpl; [apply SubList_nil|].
  destruct (string_in _ _).
  - apply SubList_app_2; auto.
  - apply SubList_app_3.
    + apply SubList_app_1, SubList_refl.
    + apply SubList_app_2; auto.
Qed.

Lemma filterDms_wellHidden:
  forall regs rules dms l,
    wellHidden (Mod regs rules dms) (hide l) ->
    forall filt,
      wellHidden (Mod regs rules (filterDms dms filt)) (hide l).
Proof.
  unfold wellHidden, hide; simpl; intros; dest.
  split.
  - eapply M.KeysDisj_SubList; eauto.
    apply filterDms_getCalls.
  - unfold getDefs in *; simpl in *.
    eapply M.KeysDisj_SubList; eauto.

    clear.
    induction dms; simpl; auto.
    + apply SubList_nil.
    + destruct (string_in _ _).
      * apply SubList_cons_right; auto.
      * simpl; apply SubList_cons; intuition.
        apply SubList_cons_right; auto.
Qed.

Lemma module_structure_indep_substep:
  forall m1 m2 or u ul cs,
    SubList (getRules m1) (getRules m2) ->
    SubList (getDefsBodies m1) (getDefsBodies m2) ->
    Substep m1 or u ul cs ->
    Substep m2 or u ul cs.
Proof.
  induction 3; simpl; intros; try (econstructor; eauto).
Qed.

Lemma module_structure_indep_substepsInd:
  forall m1 m2 or u l,
    SubList (getRules m1) (getRules m2) ->
    SubList (getDefsBodies m1) (getDefsBodies m2) ->
    SubstepsInd m1 or u l ->
    SubstepsInd m2 or u l.
Proof.
  induction 3; simpl; intros; [constructor|].
  subst; econstructor; eauto.
  eapply module_structure_indep_substep; eauto.
Qed.

Lemma module_structure_indep_step:
  forall m1 m2 or u l,
    EquivList (getRules m1) (getRules m2) ->
    EquivList (getDefsBodies m1) (getDefsBodies m2) ->
    Step m1 or u l ->
    Step m2 or u l.
Proof.
  intros.
  apply step_consistent in H1.
  apply step_consistent.
  inv H1; constructor.
  - inv H; inv H0.
    eapply module_structure_indep_substepsInd; eauto.
  - destruct (hide l0) as [a d c].
    unfold wellHidden in *; simpl in *.
    inv H; inv H0.
    pose proof (module_structure_indep_getCalls _ _ H2 H3); dest; split.
    + eapply M.KeysDisj_SubList; eauto.
    + eapply M.KeysDisj_SubList; eauto.
      apply SubList_map; auto.
Qed.

Lemma flatten_preserves_substep:
  forall m or u ul cs,
    Substep m or u ul cs ->
    Substep (Mod (getRegInits m) (getRules m) (getDefsBodies m)) or u ul cs.
Proof.
  intros; apply module_structure_indep_substep with (m1:= m);
    auto; apply SubList_refl.
Qed.

Lemma flatten_preserves_substepsInd:
  forall m or u l,
    SubstepsInd m or u l ->
    SubstepsInd (Mod (getRegInits m) (getRules m) (getDefsBodies m)) or u l.
Proof.
  intros; apply module_structure_indep_substepsInd with (m1:= m);
    auto; apply SubList_refl.
Qed.

Lemma flatten_preserves_step:
  forall m or nr l,
    Step m or nr l ->
    Step (Mod (getRegInits m) (getRules m) (getDefsBodies m)) or nr l.
Proof.
  intros; apply module_structure_indep_step with (m1:= m);
    auto; apply EquivList_refl.
Qed.

Lemma substep_dm_weakening:
  forall regs rules dms dmn o u ul cs,
    Substep (Mod regs rules dms) o u ul cs ->
    None = M.find (elt:=sigT SignT) dmn (defs (getLabel ul cs)) ->
    None = M.find (elt:=sigT SignT) dmn (calls (getLabel ul cs)) ->
    Substep (Mod regs rules (filterDm dms dmn)) o u ul cs.
Proof.
  induction 1; simpl; intros; try (econstructor; eauto; fail).

  econstructor; eauto.
  simpl; apply filter_In; split; auto.
  destruct (string_dec _ _); subst; auto.
  mred.
Qed.

Lemma substepsInd_dm_weakening:
  forall regs rules dms dmn o u l,
    SubstepsInd (Mod regs rules dms) o u l ->
    None = M.find (elt:=sigT SignT) dmn (defs l) ->
    None = M.find (elt:=sigT SignT) dmn (calls l) ->
    SubstepsInd (Mod regs rules (filterDm dms dmn)) o u l.
Proof.
  induction 1; simpl; intros; [constructor|subst].

  destruct l as [a d c]; simpl in *.
  econstructor.
  - apply IHSubstepsInd.
    + rewrite M.find_union in H4.
      match goal with
      | [H: None = match M.find dmn ?lm with Some _ => _ | None => _ end |- _] =>
        destruct (M.find dmn lm); [inv H|]
      end.
      auto.
    + rewrite M.find_union in H5.
      destruct (M.find dmn scs); [inv H5|]; auto.
  - apply substep_dm_weakening; eauto.
    + rewrite M.find_union in H4; simpl.
      match goal with
      | [H: None = match M.find dmn ?lm with Some _ => _ | None => _ end |- _] =>
        destruct (M.find dmn lm); [inv H|]
      end.
      auto.
    + simpl; findeq.
  - inv H1; dest; simpl in *.
    repeat split; auto.
  - reflexivity.
  - reflexivity.
Qed.

Lemma filterDm_wellHidden:
  forall regs rules dms dmn l,
    wellHidden (Mod regs rules dms) l ->
    wellHidden (Mod regs rules (filterDm dms dmn)) l.
Proof.
  intros; eapply wellHidden_weakening; eauto.
  - apply SubList_app_3.
    + apply SubList_app_1, SubList_refl.
    + apply SubList_app_2; simpl.
      clear; induction dms; simpl; [apply SubList_nil|].
      destruct (string_dec _ _).
      * apply SubList_app_2; auto.
      * simpl; apply SubList_app_3.
        { apply SubList_app_1, SubList_refl. }
        { apply SubList_app_2; auto. }
  - unfold getDefs; simpl.
    apply SubList_map.
    unfold SubList; intros.
    unfold filterDm in H0; apply filter_In in H0; dest; auto.
Qed.

Lemma substep_dms_weakening:
  forall regs rules dms or u ul cs,
    Substep (Mod regs rules dms) or u ul cs ->
    forall filt,
      M.KeysDisj (defs (getLabel ul cs)) filt ->
      Substep (Mod regs rules (filterDms dms filt)) or u ul cs.
Proof.
  induction 1; simpl; intros; try (econstructor; eauto; fail).

  eapply SingleMeth; eauto; subst.
  clear -H HIn; simpl in *.
  specialize (H (attrName f)).
  apply filter_In.
  remember (string_in _ _) as sin; destruct sin; auto.
  apply string_in_dec_in in Heqsin.
  elim H; auto.
  apply M.F.P.F.add_in_iff; auto.
Qed.

Lemma substepInd_dms_weakening:
  forall regs rules dms or u l,
    SubstepsInd (Mod regs rules dms) or u l ->
    forall filt,
      M.KeysDisj (defs l) filt ->
      SubstepsInd (Mod regs rules (filterDms dms filt)) or u l.
Proof.
  induction 1; intros; subst; simpl; [constructor|].
  eapply SubstepsCons; eauto.
  - apply IHSubstepsInd.
    clear -H4.
    destruct (getLabel sul scs) as [ann ds cs], l as [lann lds lcs].
    simpl in *; eapply M.KeysDisj_union_2; eauto.
  - apply substep_dms_weakening; auto.
    clear -H4.
    destruct (getLabel sul scs) as [ann ds cs], l as [lann lds lcs].
    simpl in *; eapply M.KeysDisj_union_1; eauto.
Qed.

Lemma substepsInd_meths_disj:
  forall regs rules dms
    (mEquiv: ModEquiv type typeUT (Mod regs rules dms)),
    DisjList (getCalls (Mod regs rules dms)) (getDefs (Mod regs rules dms)) ->
    forall or u l,
      SubstepsInd (Mod regs rules dms) or u l ->
      M.Disj (calls l) (defs l).
Proof.
  intros.
  pose proof (substepsInd_calls_in mEquiv H0).
  pose proof (substepsInd_defs_in H0).
  eapply M.DisjList_KeysSubset_Disj; eauto.
Qed.

Lemma substepsInd_hide_void:
  forall regs rules dms
    (mEquiv: ModEquiv type typeUT (Mod regs rules dms)),
    DisjList (getCalls (Mod regs rules dms)) (getDefs (Mod regs rules dms)) ->
    forall or u l,
      SubstepsInd (Mod regs rules dms) or u l ->
      hide l = l.
Proof.
  intros; destruct l as [ann ds cs].
  pose proof (substepsInd_meths_disj mEquiv H H0).
  unfold hide; simpl in *; f_equal; apply M.subtractKV_disj_invalid; mdisj.
Qed.

Lemma stepInd_dms_weakening:
  forall regs rules dms or u l
         (mEquiv: ModEquiv type typeUT (Mod regs rules dms)),
    DisjList (getCalls (Mod regs rules dms)) (getDefs (Mod regs rules dms)) ->
    StepInd (Mod regs rules dms) or u l ->
    forall filt,
      M.KeysDisj (defs l) filt ->
      StepInd (Mod regs rules (filterDms dms filt)) or u l.
Proof.
  induction 3; intros.
  constructor.
  - erewrite substepsInd_hide_void in H0; eauto.
    apply substepInd_dms_weakening; auto.
  - apply filterDms_wellHidden; auto.
Qed.

Lemma step_dms_weakening:
  forall regs rules dms or u l,
    ModEquiv type typeUT (Mod regs rules dms) ->
    DisjList (getCalls (Mod regs rules dms))
             (getDefs (Mod regs rules dms)) ->
    Step (Mod regs rules dms) or u l ->
    forall filt,
      M.KeysDisj (defs l) filt ->
      Step (Mod regs rules (filterDms dms filt)) or u l.
Proof.
  intros; subst; simpl.
  apply step_consistent.
  apply step_consistent in H1.
  apply stepInd_dms_weakening; auto.
Qed.

Definition IsChild (c p: Modules) :=
  (exists c', p = ConcatMod c c' \/ p = ConcatMod c' c).
#[global] Hint Unfold IsChild.

Lemma substep_modules_weakening:
  forall mc o u ul cs,
    Substep mc o u ul cs ->
    forall mp,
      IsChild mc mp ->
      Substep mp o u ul cs.
Proof.
  induction 1; simpl; intros; subst; try (constructor; auto; fail).
  - eapply SingleRule; eauto.
    inv H; inv H0; apply in_or_app; auto.
  - eapply SingleMeth; eauto.
    inv H; inv H0; apply in_or_app; auto.
Qed.

Lemma substepsInd_modules_weakening:
  forall mc o u l,
    SubstepsInd mc o u l ->
    forall mp,
      IsChild mc mp ->
      SubstepsInd mp o u l.
Proof.
  induction 1; simpl; intros; subst; [constructor|].
  eapply SubstepsCons; eauto.
  eapply substep_modules_weakening; eauto.
Qed.

Lemma semAction_oldRegs_weakening:
  forall o {retK} retv (a: ActionT type retK) u cs,
    SemAction o a u cs retv ->
    forall so,
      M.Sub o so ->
      SemAction so a u cs retv.
Proof.
  induction 1; simpl; intros; subst.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply SemIfElseTrue; eauto.
  - eapply SemIfElseFalse; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma substep_oldRegs_weakening:
  forall m o u ul cs,
    Substep m o u ul cs ->
    forall so,
      M.Sub o so ->
      Substep m so u ul cs.
Proof.
  induction 1; simpl; intros; subst; try (constructor; auto; fail).
  - eapply SingleRule; eauto.
    eapply semAction_oldRegs_weakening; eauto.
  - eapply SingleMeth; eauto.
    eapply semAction_oldRegs_weakening; eauto.
Qed.

Lemma substepsInd_oldRegs_weakening:
  forall m o u l,
    SubstepsInd m o u l ->
    forall so,
      M.Sub o so ->
      SubstepsInd m so u l.
Proof.
  induction 1; simpl; intros; subst; [constructor|].
  eapply SubstepsCons; eauto.
  eapply substep_oldRegs_weakening; eauto.
Qed.

Definition ValidLabel (m: Modules) (l: LabelT) :=
  M.KeysSubset (defs l) (getDefs m) /\ M.KeysSubset (calls l) (getCalls m).

Lemma validLabel_wellHidden_getExtDefs:
  forall m l, ValidLabel m l -> wellHidden m l -> M.KeysSubset (defs l) (getExtDefs m).
Proof.
  unfold ValidLabel, wellHidden; intros; dest.
  clear H1 H2.
  unfold M.KeysSubset, M.KeysDisj in *; intros.
  specialize (H k H1).
  specialize (H0 k).
  destruct (in_dec string_dec k (getCalls m)); intuition idtac.
  apply filter_In; split; auto.
  apply negb_true_iff.
  remember (string_in k (getCalls m)) as kin; destruct kin; auto.
  apply string_in_dec_in in Heqkin; elim n; auto.
Qed.

Lemma validLabel_wellHidden_getExtCalls:
  forall m l, ValidLabel m l -> wellHidden m l -> M.KeysSubset (calls l) (getExtCalls m).
Proof.
  unfold ValidLabel, wellHidden; intros; dest.
  clear H H0.
  unfold M.KeysSubset, M.KeysDisj in *; intros.
  specialize (H2 k H).
  specialize (H1 k).
  destruct (in_dec string_dec k (getDefs m)); intuition idtac.
  apply filter_In; split; auto.
  apply negb_true_iff.
  remember (string_in k (getDefs m)) as kin; destruct kin; auto.
  apply string_in_dec_in in Heqkin; elim n; auto.
Qed.

Lemma extDefs_calls_disj:
  forall m, DisjList (getExtDefs m) (getCalls m).
Proof.
  unfold DisjList; intros.
  destruct (in_dec string_dec e (getExtDefs m)) as [Hin|Hin].
  - right; intro Hx; unfold getExtDefs in *.
    apply filter_In in Hin; dest.
    apply negb_true_iff, eq_sym, string_in_dec_not_in in H0; auto.
  - left; auto.
Qed.

Lemma extCalls_defs_disj:
  forall m, DisjList (getExtCalls m) (getDefs m).
Proof.
  unfold DisjList; intros.
  destruct (in_dec string_dec e (getExtCalls m)) as [Hin|Hin].
  - right; intro Hx; unfold getExtCalls in *.
    apply filter_In in Hin; dest.
    apply negb_true_iff, eq_sym, string_in_dec_not_in in H0; auto.
  - left; auto.
Qed.

Lemma extDefs_extCalls_disj:
  forall m, DisjList (getExtDefs m) (getExtCalls m).
Proof.
  intros; apply DisjList_comm, DisjList_SubList with (l1:= getCalls m).
  - apply getExtCalls_getCalls.
  - apply DisjList_comm, extDefs_calls_disj.
Qed.

Lemma validLabel_wellHidden_disj:
  forall m l, ValidLabel m l -> wellHidden m l -> M.Disj (defs l) (calls l).
Proof.
  intros.
  pose proof (validLabel_wellHidden_getExtCalls H H0).
  pose proof (validLabel_wellHidden_getExtDefs H H0).
  pose proof (extDefs_extCalls_disj m).
  eauto using M.DisjList_KeysSubset_Disj.
Qed.

Lemma getCalls_not_getDefs_getExtCalls:
  forall m k, In k (getCalls m) -> ~ In k (getDefs m) -> In k (getExtCalls m).
Proof.
  intros; unfold getExtCalls.
  apply filter_In; split; auto.
  remember (string_in k (getDefs m)) as kin; destruct kin; auto.
  apply string_in_dec_in in Heqkin; auto.
Qed.

Lemma getDefs_not_getCalls_getExtDefs:
  forall m k, In k (getDefs m) -> ~ In k (getCalls m) -> In k (getExtDefs m).
Proof.
  intros; unfold getExtCalls.
  apply filter_In; split; auto.
  remember (string_in k (getCalls m)) as kin; destruct kin; auto.
  apply string_in_dec_in in Heqkin; auto.
Qed.

Lemma step_wellHidden: forall m o u l, Step m o u l -> wellHidden m l.
Proof. intros; inv H; auto. Qed.

Lemma multistep_wellHidden:
  forall m o ll n, Multistep m o n ll -> Forall (fun l => wellHidden m l) ll.
Proof.
  induction ll; simpl; intros; constructor; auto; inv H; eauto.
  eapply step_wellHidden; eauto.
Qed.

Lemma behavior_wellHidden:
  forall m ll n, Behavior m n ll -> Forall (fun l => wellHidden m l) ll.
Proof.
  intros; inv H; eapply multistep_wellHidden; eauto.
Qed.

Lemma multistep_app:
  forall m ll1 ll2 o n,
    Multistep m o n (ll1 ++ ll2) ->
    exists n', Multistep m o n' ll2 /\ Multistep m n' n ll1.
Proof.
  induction ll1; simpl; intros.
  - eexists; split; eauto.
    constructor; auto.
  - inv H; specialize (IHll1 _ _ _ HMultistep); dest.
    eexists; split; eauto.
    constructor; auto.
Qed.

Lemma multistep_app_inv:
  forall m ll1 ll2 o n n',
    Multistep m o n' ll2 ->
    Multistep m n' n ll1 ->
    Multistep m o n (ll1 ++ ll2).
Proof.
  induction ll1; simpl; intros.
  - inv H0; auto.
  - inv H0; constructor; eauto.
Qed.

Lemma reachable_init:
  forall m, reachable (initRegs (getRegInits m)) m.
Proof.
  intros; repeat econstructor.
Qed.

Lemma reachable_multistep:
  forall m o n ll,
    reachable o m ->
    Multistep m o n ll ->
    reachable n m.
Proof.
  intros.
  inversion_clear H.
  inversion_clear H1.
  do 2 econstructor.
  eapply multistep_app_inv; eassumption.
Qed.

Section NoRules.
  Variable m: Modules.
  Hypothesis (Hrules: getRules m = nil).

  Lemma substep_getRules_nil:
    forall o u ul cs,
      Substep m o u ul cs -> ul = Rle None \/ exists d, ul = Meth d.
  Proof.
    destruct 1; auto.
    - right; eexists; auto.
    - rewrite Hrules in HInRules; inv HInRules.
    - right; eexists; auto.
  Qed.

  Lemma substepsInd_getRules_nil:
    forall o u l,
      SubstepsInd m o u l -> annot l = Some None \/ annot l = None.
  Proof.
    induction 1; auto.
    apply substep_getRules_nil in H0; destruct H0; dest; subst.
    - destruct l as [a d c]; simpl in *.
      destruct IHSubstepsInd; subst; simpl; auto.
    - destruct l as [a d c]; simpl in *; auto.
  Qed.

  Lemma step_getRules_nil:
    forall o u l,
      Step m o u l -> annot l = Some None \/ annot l = None.
  Proof.
    intros; apply step_consistent in H.
    inv H; apply substepsInd_getRules_nil in HSubSteps.
    destruct l0 as [a d c]; simpl in *; auto.
  Qed.

  Lemma substepsInd_rule_annot_1:
    forall o u ds cs,
      SubstepsInd m o u {| annot := None; defs := ds; calls := cs |} ->
      SubstepsInd m o u {| annot := Some None; defs := ds; calls := cs |}.
  Proof.
    intros.
    econstructor.
    - eassumption.
    - apply EmptyRule.
    - repeat split; auto.
    - auto.
    - reflexivity.
  Qed.

  Lemma substepsInd_rule_annot_2:
    forall o u l,
      SubstepsInd m o u l ->
      forall ds cs,
        l = {| annot := Some None; defs := ds; calls := cs |} ->
        SubstepsInd m o u {| annot := None; defs := ds; calls := cs |}.
  Proof.
    induction 1; simpl; intros; [inv H|].
    subst; inv H0.
    - mred; replace {| annot := None; defs := ds; calls := cs |} with l; auto.
      destruct l as [ann d c]; inv H1; simpl in *; dest; inv H4.
      destruct ann; intuition idtac.
    - destruct l as [ann d c]; inv H1; simpl in *; dest; inv H4.
      mred; auto.
    - rewrite Hrules in HInRules; inv HInRules.
    - destruct l as [ann d c]; inv H1; simpl in *; dest; inv H4.
      econstructor.
      + apply IHSubstepsInd; auto.
      + eapply SingleMeth; eauto.
      + repeat split; auto.
      + auto.
      + reflexivity.
  Qed.

  Lemma step_rule_annot_1:
    forall o u ds cs,
      Step m o u {| annot := None; defs := ds; calls := cs |} ->
      Step m o u {| annot := Some None; defs := ds; calls := cs |}.
  Proof.
    intros.
    apply step_consistent; apply step_consistent in H.
    inv H.
    destruct l as [a d c]; simpl in *; subst.
    change {| annot := _; defs := _; calls := _ |}
    with (hide {| annot := Some None; defs := d; calls := c |}).
    constructor; auto.
    apply substepsInd_rule_annot_1; auto.
  Qed.

  Lemma step_rule_annot_2:
    forall o u ds cs,
      Step m o u {| annot := Some None; defs := ds; calls := cs |} ->
      Step m o u {| annot := None; defs := ds; calls := cs |}.
  Proof.
    intros.
    apply step_consistent; apply step_consistent in H.
    inv H.
    destruct l as [a d c]; simpl in *; subst.
    change {| annot := _; defs := _; calls := _ |}
    with (hide {| annot := None; defs := d; calls := c |}).
    constructor; auto.
    eapply substepsInd_rule_annot_2; eauto.
  Qed.

End NoRules.

