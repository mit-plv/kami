Require Import Bool String List Arith.Peano_dec.
Require Import Lib.FMap Lib.Struct Lib.CommonTactics Lib.Indexer Lib.StringEq.
Require Import Syntax Semantics SemFacts Refinement Renaming Equiv Wf.
Require Import Specialize MetaSyntax.

Require Import FunctionalExtensionality.
Require Import Compare_dec.

Set Implicit Arguments.

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
    forall ty1 ty2 m n,
      ModEquiv ty1 ty2 m ->
      ModEquiv ty1 ty2 (duplicate m n).
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

  Lemma duplicate_specializeMod_disj_regs:
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

  Lemma duplicate_specializeMod_disj_defs:
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

  Lemma duplicate_specializeMod_disj_calls:
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
  
  Lemma duplicate_disj_regs:
    forall m1 m2,
      Specializable m1 ->
      Specializable m2 ->
      DisjList (namesOf (getRegInits m1))
               (namesOf (getRegInits m2)) ->
      forall n,
        DisjList (namesOf (getRegInits (duplicate m1 n)))
                 (namesOf (getRegInits (duplicate m2 n))).
  Proof.
    induction n; simpl; intros.
    - apply specializeMod_disj_regs_2; auto.
    - unfold namesOf; do 2 rewrite map_app; apply DisjList_app_4.
      + apply DisjList_comm, DisjList_app_4.
        * apply DisjList_comm, specializeMod_disj_regs_2; auto.
        * clear IHn; generalize (S n); intros; induction n; simpl.
          { apply DisjList_comm, specializeMod_disj_regs_2; auto. }
          { rewrite map_app; apply DisjList_app_4; auto.
            apply DisjList_comm, specializeMod_disj_regs_2; auto.
          }
      + apply DisjList_comm, DisjList_app_4.
        * clear IHn; generalize (S n); intros; induction n; simpl.
          { apply DisjList_comm, specializeMod_disj_regs_2; auto. }
          { rewrite map_app; apply DisjList_comm, DisjList_app_4.
            { apply specializeMod_disj_regs_2; auto. }
            { apply DisjList_comm; auto. }
          }
        * apply DisjList_comm; auto.
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

  Lemma duplicate_regs_NoDup:
    forall m (Hsp: Specializable m) n,
      NoDup (namesOf (getRegInits m)) ->
      NoDup (namesOf (getRegInits (duplicate m n))).
  Proof.
    induction n; simpl; intros; [apply specializeMod_regs_NoDup; auto|].
    unfold namesOf in *; simpl in *.
    rewrite map_app; apply NoDup_DisjList; auto.
    - apply specializeMod_regs_NoDup; auto.
    - apply duplicate_specializeMod_disj_regs; auto.
  Qed.

  Section TwoModules1.
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
        + apply duplicate_specializeMod_disj_regs; auto.
        + apply duplicate_specializeMod_disj_regs; auto.
        + pose proof (duplicate_validRegsModules m1 (S n) Hvr1); auto.
        + pose proof (duplicate_validRegsModules m2 (S n) Hvr2); auto.
        + apply duplicate_specializeMod_disj_defs; auto.
        + apply duplicate_specializeMod_disj_calls; auto.
        + apply duplicate_specializeMod_disj_defs; auto.
        + apply duplicate_specializeMod_disj_calls; auto.
        + apply duplicate_noninteracting; auto.
        + apply duplicate_noninteracting; auto.
        + apply specialized_2 with (i:= S n); auto.
          eapply traceRefines_label_map; eauto using H.
          clear; unfold EquivalentLabelMap; intros.
          rewrite idElementwiseId; unfold id; simpl.
          unfold liftPRename; simpl.
          apply specializer_two_comm; auto.
    Qed.

  End TwoModules1.

  Section TwoModules2.
    Variables (m1 m2: Modules).
    Hypotheses (Hequiv1: forall ty, ModEquiv ty typeUT m1)
               (Hequiv2: forall ty, ModEquiv ty typeUT m2)
               (Hvr1: forall ty, ValidRegsModules ty m1)
               (Hvr2: forall ty, ValidRegsModules ty m2)
               (Hsp1: Specializable m1)
               (Hsp2: Specializable m2).

    Lemma duplicate_regs_ConcatMod_1:
      forall n,
        SubList (getRegInits (duplicate (m1 ++ m2)%kami n))
                (getRegInits (duplicate m1 n ++ duplicate m2 n)%kami).
    Proof.
      Opaque specializeMod.
      induction n; intros.
      - unfold duplicate.
        rewrite specializeMod_concatMod; auto.
        apply SubList_refl.
      - simpl in *; apply SubList_app_3.
        + rewrite specializeMod_concatMod; auto.
          simpl; apply SubList_app_3.
          * do 2 apply SubList_app_1; apply SubList_refl.
          * apply SubList_app_2, SubList_app_1, SubList_refl.
        + unfold SubList in *; intros.
          specialize (IHn e H).
          apply in_app_or in IHn; destruct IHn.
          * apply in_or_app; left; apply in_or_app; auto.
          * apply in_or_app; right; apply in_or_app; auto.
            Transparent specializeMod.
    Qed.

    Lemma duplicate_regs_ConcatMod_2:
      forall n,
        SubList (getRegInits (duplicate m1 n ++ duplicate m2 n)%kami)
                (getRegInits (duplicate (m1 ++ m2)%kami n)).
    Proof.
      Opaque specializeMod.
      induction n; intros.
      - unfold duplicate.
        rewrite specializeMod_concatMod; auto.
        apply SubList_refl.
      - simpl in *; apply SubList_app_3.
        + rewrite specializeMod_concatMod; auto.
          simpl; apply SubList_app_3.
          * do 2 apply SubList_app_1; apply SubList_refl.
          * apply SubList_app_2; apply SubList_app_4 in IHn; auto.
        + rewrite specializeMod_concatMod; auto.
          simpl; apply SubList_app_3.
          * apply SubList_app_1, SubList_app_2, SubList_refl.
          * apply SubList_app_2; apply SubList_app_5 in IHn; auto.
            Transparent specializeMod.
    Qed.

    Lemma duplicate_regs_NoDup_2:
      NoDup (namesOf (getRegInits (m1 ++ m2)%kami)) ->
      forall n,
        NoDup (namesOf (getRegInits (duplicate m1 n ++ duplicate m2 n)%kami)).
    Proof.
      Opaque specializeMod.
      intros.
      pose proof H; apply duplicate_regs_NoDup with (n:= n) in H0.
      induction n; simpl; intros.
      - simpl in *; rewrite specializeMod_concatMod in H0; auto.
      - assert (NoDup (namesOf (getRegInits (duplicate (m1 ++ m2)%kami n)))).
        { apply duplicate_regs_NoDup; auto.
          apply specializable_concatMod; auto.
        }
        specialize (IHn H1); clear H1.
        unfold namesOf; repeat rewrite map_app.
        rewrite app_assoc.
        rewrite <-app_assoc with (l:= map (attrName (Kind:=sigT ConstFullT))
                                          (getRegInits (specializeMod m1 (S n)))).
        rewrite <-app_assoc with (l:= map (attrName (Kind:=sigT ConstFullT))
                                          (getRegInits (specializeMod m1 (S n)))).
        apply NoDup_app_comm_ext.
        rewrite app_assoc.
        rewrite app_assoc.
        rewrite <-app_assoc with (n:= map (attrName (Kind:=sigT ConstFullT))
                                          (getRegInits (duplicate m2 n))).
        apply NoDup_DisjList.
        + apply specializeMod_regs_NoDup with (i:= S n) in H;
            [|apply specializable_concatMod; auto].
          rewrite specializeMod_concatMod in H; auto.
          rewrite <-map_app; auto.
        + rewrite <-map_app; auto.
        + do 2 rewrite <-map_app.
          pose proof (duplicate_regs_ConcatMod_2 n).
          apply SubList_map with (f:= @attrName _) in H1.
          eapply DisjList_comm, DisjList_SubList; eauto.
          pose proof (specializeMod_concatMod Hvr1 Hvr2 Hequiv1 Hequiv2 (S n) Hsp1 Hsp2).
          change (getRegInits (specializeMod m1 (S n)) ++ getRegInits (specializeMod m2 (S n)))
          with (getRegInits (specializeMod m1 (S n) ++ (specializeMod m2 (S n)))%kami).
          rewrite <-H2.
          apply DisjList_comm, duplicate_specializeMod_disj_regs; auto.
          apply specializable_concatMod; auto.
      - apply specializable_concatMod; auto.
    Qed.

    Lemma duplicate_rules_ConcatMod_1:
      forall n,
        SubList (getRules (duplicate (m1 ++ m2)%kami n))
                (getRules (duplicate m1 n ++ duplicate m2 n)%kami).
    Proof.
      Opaque specializeMod.
      induction n; intros.
      - unfold duplicate.
        rewrite specializeMod_concatMod; auto.
        apply SubList_refl.
      - simpl in *; apply SubList_app_3.
        + rewrite specializeMod_concatMod; auto.
          simpl; apply SubList_app_3.
          * do 2 apply SubList_app_1; apply SubList_refl.
          * apply SubList_app_2, SubList_app_1, SubList_refl.
        + unfold SubList in *; intros.
          specialize (IHn e H).
          apply in_app_or in IHn; destruct IHn.
          * apply in_or_app; left; apply in_or_app; auto.
          * apply in_or_app; right; apply in_or_app; auto.
            Transparent specializeMod.
    Qed.

    Lemma duplicate_rules_ConcatMod_2:
      forall n,
        SubList (getRules (duplicate m1 n ++ duplicate m2 n)%kami)
                (getRules (duplicate (m1 ++ m2)%kami n)).
    Proof.
      Opaque specializeMod.
      induction n; intros.
      - unfold duplicate.
        rewrite specializeMod_concatMod; auto.
        apply SubList_refl.
      - simpl in *; apply SubList_app_3.
        + rewrite specializeMod_concatMod; auto.
          simpl; apply SubList_app_3.
          * do 2 apply SubList_app_1; apply SubList_refl.
          * apply SubList_app_2; apply SubList_app_4 in IHn; auto.
        + rewrite specializeMod_concatMod; auto.
          simpl; apply SubList_app_3.
          * apply SubList_app_1, SubList_app_2, SubList_refl.
          * apply SubList_app_2; apply SubList_app_5 in IHn; auto.
            Transparent specializeMod.
    Qed.

    Lemma duplicate_defs_ConcatMod_1:
      forall n,
        SubList (getDefsBodies (duplicate (m1 ++ m2)%kami n))
                (getDefsBodies (duplicate m1 n ++ duplicate m2 n)%kami).
    Proof.
      Opaque specializeMod.
      induction n; intros.
      - unfold duplicate.
        rewrite specializeMod_concatMod; auto.
        apply SubList_refl.
      - simpl in *; apply SubList_app_3.
        + rewrite specializeMod_concatMod; auto.
          simpl; apply SubList_app_3.
          * do 2 apply SubList_app_1; apply SubList_refl.
          * apply SubList_app_2, SubList_app_1, SubList_refl.
        + unfold SubList in *; intros.
          specialize (IHn e H).
          apply in_app_or in IHn; destruct IHn.
          * apply in_or_app; left; apply in_or_app; auto.
          * apply in_or_app; right; apply in_or_app; auto.
            Transparent specializeMod.
    Qed.

    Lemma duplicate_defs_ConcatMod_2:
      forall n,
        SubList (getDefsBodies (duplicate m1 n ++ duplicate m2 n)%kami)
                (getDefsBodies (duplicate (m1 ++ m2)%kami n)).
    Proof.
      Opaque specializeMod.
      induction n; intros.
      - unfold duplicate.
        rewrite specializeMod_concatMod; auto.
        apply SubList_refl.
      - simpl in *; apply SubList_app_3.
        + rewrite specializeMod_concatMod; auto.
          simpl; apply SubList_app_3.
          * do 2 apply SubList_app_1; apply SubList_refl.
          * apply SubList_app_2; apply SubList_app_4 in IHn; auto.
        + rewrite specializeMod_concatMod; auto.
          simpl; apply SubList_app_3.
          * apply SubList_app_1, SubList_app_2, SubList_refl.
          * apply SubList_app_2; apply SubList_app_5 in IHn; auto.
            Transparent specializeMod.
    Qed.

  End TwoModules2.

  Section TwoModules3.
    Variables (m1 m2: Modules).
    Hypotheses (Hsp1: Specializable m1)
               (Hsp2: Specializable m2)
               (Hvr1: forall ty, ValidRegsModules ty m1)
               (Hvr2: forall ty, ValidRegsModules ty m2)
               (Hequiv1: forall ty, ModEquiv ty typeUT m1)
               (Hequiv2: forall ty, ModEquiv ty typeUT m2)
               (HnoDup: NoDup (namesOf (getRegInits (m1 ++ m2)%kami))).

    Lemma duplicate_concatMod_comm_1:
      forall n,
        duplicate (m1 ++ m2)%kami n <<== ((duplicate m1 n) ++ (duplicate m2 n))%kami.
    Proof.
      intros; rewrite idElementwiseId.
      apply traceRefines_same_module_structure.
      - apply duplicate_regs_NoDup; auto.
        apply specializable_concatMod; auto.
      - apply duplicate_regs_NoDup_2; auto.
      - apply duplicate_regs_ConcatMod_1; auto.
      - apply duplicate_regs_ConcatMod_2; auto.
      - apply duplicate_rules_ConcatMod_1; auto.
      - apply duplicate_rules_ConcatMod_2; auto.
      - apply duplicate_defs_ConcatMod_1; auto.
      - apply duplicate_defs_ConcatMod_2; auto.
    Qed.

    Lemma duplicate_concatMod_comm_2:
      forall n,
        ((duplicate m1 n) ++ (duplicate m2 n))%kami <<== duplicate (m1 ++ m2)%kami n.
    Proof.
      intros; rewrite idElementwiseId.
      apply traceRefines_same_module_structure.
      - apply duplicate_regs_NoDup_2; auto.
      - apply duplicate_regs_NoDup; auto.
        apply specializable_concatMod; auto.
      - apply duplicate_regs_ConcatMod_2; auto.
      - apply duplicate_regs_ConcatMod_1; auto.
      - apply duplicate_rules_ConcatMod_2; auto.
      - apply duplicate_rules_ConcatMod_1; auto.
      - apply duplicate_defs_ConcatMod_2; auto.
      - apply duplicate_defs_ConcatMod_1; auto.
    Qed.

  End TwoModules3.

End DuplicateFacts.

Lemma duplicate_meta_disj_regs_one:
  forall m s r,
    (forall i, DisjList (namesOf (getRegInits (specializeMod m i))) [s]) ->
    forall mrules mmeths n,
      DisjList (namesOf (getRegInits (duplicate m n)))
               (namesOf (getRegInits (makeModule (Build_MetaModule [One (s :: r)%struct]
                                                                   mrules mmeths)))).
Proof.
  induction n; simpl; [auto|].
  unfold namesOf in *; simpl in *.
  rewrite map_app.
  apply DisjList_app_4; auto.
Qed.

Lemma duplicate_meta_disj_defs_rep:
  forall m s,
    (forall i j, DisjList (getDefs (specializeMod m i)) [s __ j]) ->
    forall mregs mrules mf n,
      DisjList (getDefs (duplicate m n))
               (getDefs (makeModule (Build_MetaModule mregs mrules [Rep s mf n]))).
Proof.
  induction n; [unfold getDefs in *; simpl in *; auto|].

  unfold getDefs in *; simpl in *.
  apply DisjList_comm, SemFacts.DisjList_string_cons.

  - clear IHn.
    unfold namesOf in *; simpl in *.
    rewrite map_app; intro Hx; apply in_app_or in Hx; destruct Hx.
    + specialize (H (S n) (S n) (s __ (S n))); destruct H; auto.
      elim H; simpl; tauto.
    + remember (S n); clear Heqn0.
      induction n.
      * specialize (H 0 n0 (s __ n0)); destruct H; auto.
        elim H; simpl; tauto.
      * simpl in H0; rewrite map_app in H0.
        apply in_app_or in H0; destruct H0; auto.
        specialize (H (S n) n0 (s __ n0)); destruct H; auto.
        elim H; simpl; tauto.

  - rewrite app_nil_r in *.
    match goal with
    | [ |- context[namesOf (?l ++ ?r)] ] =>
      replace (namesOf (l ++ r)) with (namesOf l ++ namesOf r)
        by (unfold namesOf; rewrite map_app; reflexivity)
    end.
    apply DisjList_comm, DisjList_app_4; [|auto].
    clear IHn; generalize (S n); intros.
    induction n; simpl; [auto|].
    apply DisjList_comm, SemFacts.DisjList_string_cons.
    + specialize (H n0 (S n) (s __ (S n))); destruct H; auto.
      elim H; simpl; tauto.
    + apply DisjList_comm; auto.
Qed.

Lemma duplicate_meta_disj_meth_calls_rep:
  forall m mregso mregs mn mf,
    (forall i j, DisjList (getCalls (specializeMod m i))
                          (getCalls (makeModule (Build_MetaModule
                                                   mregso
                                                   nil
                                                   [One (mn __ j :: (mf j))%struct])))) ->
    forall n,
      DisjList (getCalls (duplicate m n))
               (getCalls (makeModule (Build_MetaModule mregs nil [Rep mn mf n]))).
Proof.
  induction n; [unfold getCalls in *; simpl in *; auto|].
  unfold getCalls in *; simpl in *.
  apply DisjList_comm, DisjList_app_4; apply DisjList_comm.

  - apply DisjList_app_4.
    + rewrite getCallsR_app; apply DisjList_app_4.
      * specialize (H (S n) (S n)); rewrite app_nil_r in *.
        apply DisjList_comm, DisjList_app_1, DisjList_comm in H; auto.
      * generalize (S n); intros; clear -H; induction n.
        { specialize (H 0 n0); rewrite app_nil_r in *.
          apply DisjList_comm, DisjList_app_1, DisjList_comm in H; auto.
        }
        { simpl; rewrite getCallsR_app.
          apply DisjList_app_4; [|auto].
          specialize (H (S n) n0); rewrite app_nil_r in *.
          apply DisjList_comm, DisjList_app_1, DisjList_comm in H; auto.
        }
    + rewrite getCallsM_app; apply DisjList_app_4.
      * specialize (H (S n) (S n)); rewrite app_nil_r in *.
        apply DisjList_comm, DisjList_app_2, DisjList_comm in H; auto.
      * generalize (S n); intros; clear -H; induction n.
        { specialize (H 0 n0); rewrite app_nil_r in *.
          apply DisjList_comm, DisjList_app_2, DisjList_comm in H; auto.
        }
        { simpl; rewrite getCallsM_app.
          apply DisjList_app_4; [|auto].
          specialize (H (S n) n0); rewrite app_nil_r in *.
          apply DisjList_comm, DisjList_app_2, DisjList_comm in H; auto.
        }

  - assert (DisjList (getCallsR (getRules (specializeMod m (S n)))
                                ++ getCallsM (getDefsBodies (specializeMod m (S n))))
                     (getCallsM (getListFromRep mn mf n ++ nil))).
    { clear -H; generalize (S n); intros; induction n; [simpl; auto|].
      simpl; apply DisjList_comm, DisjList_app_4; apply DisjList_comm; [|auto].
      specialize (H n0 (S n)); rewrite app_nil_r in *; auto.
    }

    apply DisjList_app_3 in IHn; apply DisjList_app_3 in H0; dest.
    apply DisjList_app_4.
    + rewrite getCallsR_app; apply DisjList_app_4; auto.
    + rewrite getCallsM_app; apply DisjList_app_4; auto.
Qed.

Section DupRep.
  Variable m: Modules.
  Hypothesis (Hmregs: NoDup (namesOf (getRegInits m))).
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

  Lemma rulesToRep_RulesEquiv:
    forall ty1 ty2 rules,
      RulesEquiv ty1 ty2 rules ->
      RulesEquiv ty1 ty2 (getFullListFromMeta (rulesToRep rules)).
  Proof.
    induction rules; simpl; intros; [constructor|].
    inv H; simpl.
    apply RulesEquiv_app; auto.
    clear -H2.

    induction n; simpl.
    - constructor; [|constructor].
      intros; apply renameAction_ActionEquiv; auto.
    - constructor; auto.
      intros; apply renameAction_ActionEquiv; auto.
  Qed.

  Lemma methsToRep_MethsEquiv:
    forall ty1 ty2 meths,
      MethsEquiv ty1 ty2 meths ->
      MethsEquiv ty1 ty2 (getFullListFromMeta (methsToRep meths)).
  Proof.
    induction meths; simpl; intros; [constructor|].
    inv H; simpl.
    apply MethsEquiv_app; auto.
    clear -H2.

    induction n; simpl.
    - constructor; [|constructor].
      intros; apply renameAction_ActionEquiv; auto.
    - constructor; auto.
      intros; apply renameAction_ActionEquiv; auto.
  Qed.
    
  Lemma duplicateByRep_ModEquiv:
    forall ty1 ty2,
      ModEquiv ty1 ty2 m ->
      ModEquiv ty1 ty2 duplicateByRep.
  Proof.
    unfold duplicateByRep, regsToRep, rulesToRep, methsToRep.
    unfold makeModule; simpl; intros.
    inv H; constructor.
    - apply rulesToRep_RulesEquiv; auto.
    - apply methsToRep_MethsEquiv; auto.
  Qed.

  Hypothesis (Hsp: Specializable m).
  
  Lemma duplicate_duplicateByRep_same_structure:
    NoDup (namesOf (getRegInits (duplicate m n))) /\
    NoDup (namesOf (getRegInits duplicateByRep)) /\
    SubList (getRegInits (duplicate m n)) (getRegInits duplicateByRep) /\
    SubList (getRegInits duplicateByRep) (getRegInits (duplicate m n)) /\
    SubList (getRules (duplicate m n)) (getRules duplicateByRep) /\
    SubList (getRules duplicateByRep) (getRules (duplicate m n)) /\
    SubList (getDefsBodies (duplicate m n)) (getDefsBodies duplicateByRep) /\
    SubList (getDefsBodies duplicateByRep) (getDefsBodies (duplicate m n)).
  Proof.
    admit.
  Qed.
      
  Lemma duplicate_refines_repeat:
    duplicate m n <<== duplicateByRep.
  Proof.
    pose proof duplicate_duplicateByRep_same_structure; dest.
    rewrite idElementwiseId.
    apply traceRefines_same_module_structure; auto.
  Qed.

End DupRep.

Hint Unfold specializeMod duplicate: ModuleDefs.
Hint Unfold regsToRep rulesToRep methsToRep duplicateByRep: ModuleDefs.

