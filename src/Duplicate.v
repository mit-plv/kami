Require Import Bool String List Arith.Peano_dec Omega.
Require Import Lib.FMap Lib.Struct Lib.CommonTactics Lib.Indexer Lib.StringEq Lib.ListSupport.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Specialize.

Require Import FunctionalExtensionality.
Require Import Compare_dec.

Set Implicit Arguments.
Set Asymmetric Patterns.

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

  Lemma duplicate_dom_indexed:
    forall m,
      Specializable m ->
      forall s n,
        In s (spDom (duplicate m n)) ->
        exists t i, s = t __ i /\ i < S n.
  Proof.
    induction n; simpl; intros.
    - pose proof (specializeMod_dom_indexed H _ _ H0); dest; subst.
      do 2 eexists; eauto.
    - apply spDom_in in H0; destruct H0.
      + pose proof (specializeMod_dom_indexed H _ _ H0); dest; subst.
        do 2 eexists; eauto.
      + specialize (IHn H0); dest; subst.
        do 2 eexists; eauto.
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

  Lemma getRegInits_duplicate_nil:
    forall m n,
      Specializable m -> getRegInits m = nil -> getRegInits (duplicate m n) = nil.
  Proof.
    intros.
    match goal with
    | [ |- ?P ] => assert (namesOf (getRegInits (duplicate m n)) = nil -> P) as Hm
    end.
    { intros; unfold namesOf in H1; eapply map_eq_nil; eauto. }
    apply Hm; clear Hm.
    
    induction n.
    - simpl; rewrite specializeMod_regs; auto.
      rewrite H0; reflexivity.
    - simpl; rewrite namesOf_app.
      rewrite IHn; rewrite app_nil_r.
      rewrite specializeMod_regs; auto.
      rewrite H0; reflexivity.
  Qed.

  Lemma getDefs_duplicate_nil:
    forall m n, Specializable m -> getDefs m = nil -> getDefs (duplicate m n) = nil.
  Proof.
    intros; induction n; simpl.
    - rewrite specializeMod_defs; auto.
      rewrite H0; reflexivity.
    - rewrite getDefs_app.
      rewrite IHn; rewrite app_nil_r.
      rewrite specializeMod_defs; auto.
      rewrite H0; reflexivity.
  Qed.

  Lemma getDefsBodies_duplicate_nil:
    forall m n, Specializable m -> getDefsBodies m = nil -> getDefsBodies (duplicate m n) = nil.
  Proof.
    intros.
    assert (getDefs m = nil) by (unfold getDefs; rewrite H0; reflexivity).
    apply getDefs_duplicate_nil with (n:= n) in H1; auto.
    eapply map_eq_nil with (f:= @attrName _); eauto.
  Qed.

  Lemma getRules_duplicate_in:
    forall m rn rb i n,
      Specializable m ->
      In (rn :: rb)%struct (getRules m) ->
      le i n ->
      In ((rn __ i) :: (fun ty => (Renaming.renameAction (specializer m i) (rb ty))))%struct
         (getRules (duplicate m n)).
  Proof.
    induction n; simpl; intros.
    - inv H1; apply specializeMod_rules_in; auto.
    - inv H1; [|apply in_or_app; right; auto].
      apply in_or_app; left.
      apply specializeMod_rules_in; auto.
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
        clear - Hsp1 Hsp2 Hexts; unfold EquivalentLabelMap; intros.
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
          clear - Hsp1 Hsp2 Hexts; unfold EquivalentLabelMap; intros.
          rewrite idElementwiseId; unfold id; simpl.
          unfold liftPRename; simpl.
          apply specializer_two_comm; auto.
    Qed.

  End TwoModules1.

  Section TwoModules2.
    Variables (m1 m2: Modules).
    Hypotheses (Hsp1: Specializable m1)
               (Hsp2: Specializable m2)
               (Hequiv1: ModEquiv type typeUT m1)
               (Hequiv2: ModEquiv type typeUT m2)
               (Hvr1: ValidRegsModules type m1)
               (Hvr2: ValidRegsModules type m2).

    Variable (ds: string). (* a single label to drop *)

    Hypothesis (Hexts: SubList (filter (fun s => negb (string_eq s ds)) (getExtMeths m1))
                               (getExtMeths m2)).

    Lemma specializeMod_traceRefines_drop:
      forall i,
        (m1 <<=[dropP ds] m2) ->
        (specializeMod m1 i <<=[dropI ds i] specializeMod m2 i).
    Proof.
      intros.
      apply specialized_2; auto.
      apply traceRefines_label_map with (p:= liftToMap1 (dropP ds)); auto.

      clear -Hsp1 Hsp2 Hexts.
      unfold EquivalentLabelMap; intros.

      unfold liftPRename.

      assert (renameMap (specializer m2 i) ((liftToMap1 (dropP ds)) m) =
              liftToMap1 (dropI ds i) (renameMap (specializer m1 i) m)).
      { rewrite specializer_map with (m:= m1); auto;
        [|eapply M.KeysSubset_SubList; eauto; apply spDom_getExtMeths].
        rewrite specializer_map with (m:= m2); auto;
          [|apply M.KeysSubset_SubList with (d1:= getExtMeths m2); [|apply spDom_getExtMeths];
            eapply M.KeysSubset_SubList; eauto;
            apply dropP_KeysSubset; auto].

        clear; M.ext y.
        rewrite liftToMap1_find.
        remember (M.find y (renameMap (spf i) m)) as yiv; destruct yiv.
        - apply eq_sym, renameFind2' in Heqyiv; [|apply spf_onto].
          dest; subst; rewrite <-renameMapFind; [|apply spf_onto].
          rewrite liftToMap1_find, H0.
          unfold dropP, dropI.
          remember (string_eq x ds) as xds; destruct xds.
          + apply string_eq_dec_eq in Heqxds; subst.
            rewrite string_eq_true; reflexivity.
          + apply string_eq_dec_neq in Heqxds.
            remember (string_eq (spf i x) (ds __ i)) as xdsi; destruct xdsi; auto.
            apply string_eq_dec_eq, spf_onto in Heqxdsi.
            elim Heqxds; auto.
        - remember (M.find y (renameMap (spf i) (liftToMap1 (dropP ds) m))) as ypv;
            destruct ypv; auto.
          exfalso; apply eq_sym, renameFind2' in Heqypv; [|apply spf_onto].
          dest; subst.
          rewrite <-renameMapFind in Heqyiv; [|apply spf_onto].
          rewrite liftToMap1_find in H0.
          rewrite <-Heqyiv in H0; inv H0.
      }

      rewrite <-H0.
      rewrite <-specializer_two_comm with (m1:= m2) (m2:= m2) (i:= i); auto.
      - apply SubList_refl.
      - eapply M.KeysSubset_SubList; eauto.
        apply dropP_KeysSubset; auto.
    Qed.

    Lemma equivalentLabelMapElem_dropI_dropN:
      forall n t (Ht: t > n),
        EquivalentLabelMapElem (dropI ds t) (compLabelMaps (dropI ds t) (dropN ds n))
                               (getExtMeths (specializeMod m1 t)).
    Proof.
      unfold EquivalentLabelMapElem; intros.
      induction n.
      - simpl; unfold compLabelMaps, dropI.
        destruct (string_eq _ (ds __ t)).
        + destruct (string_eq _ (ds __ 0)); auto.
        + remember (string_eq _ _) as sv; destruct sv; auto.
          exfalso; apply string_eq_dec_eq in Heqsv; subst.
          apply spDom_getExtMeths in H.
          apply specializeMod_dom_indexed in H; auto; dest.
          apply withIndex_index_eq in H; dest; omega.
      - simpl; assert (t > n) by omega; specialize (IHn H0); clear H0.
        rewrite IHn; clear IHn.
        unfold dropI, compLabelMaps.
        remember (dropN ds n s v) as nv; destruct nv; auto.
        destruct (string_eq s (ds __ t)).
        + destruct (string_eq _ _); auto.
        + remember (string_eq _ _) as sn; destruct sn; auto.
          exfalso; apply string_eq_dec_eq in Heqsn; subst.
          apply spDom_getExtMeths in H.
          apply specializeMod_dom_indexed in H; auto; dest.
          apply withIndex_index_eq in H; dest; omega.
    Qed.

    Lemma equivalentLabelMapElem_dropN_dropI:
      forall n t (Ht: t > n),
        EquivalentLabelMapElem (dropN ds n) (compLabelMaps (dropI ds t) (dropN ds n))
                               (getExtMeths (duplicate m1 n)).
    Proof.
      unfold EquivalentLabelMapElem; intros.
      induction n.
      - simpl; unfold compLabelMaps, dropI.
        destruct (string_eq _ (ds __ 0)); auto.
        remember (string_eq _ _) as st; destruct st; auto.
        apply string_eq_dec_eq in Heqst; subst.
        simpl in H.
        apply spDom_getExtMeths in H.
        apply specializeMod_dom_indexed in H; auto; dest.
        apply withIndex_index_eq in H; dest; omega.
      - simpl; assert (t > n) by omega; specialize (IHn H0); clear H0.
        simpl in H.
        apply getExtMeths_in in H; destruct H.
        + clear IHn.
          unfold dropI, compLabelMaps.
          destruct (dropN ds n s v); auto.
          destruct (string_eq _ (ds __ (S n))); auto.
          remember (string_eq _ _) as st; destruct st; auto.
          exfalso; apply string_eq_dec_eq in Heqst; subst.
          apply spDom_getExtMeths in H.
          apply specializeMod_dom_indexed in H; auto; dest.
          apply withIndex_index_eq in H; dest; omega.
        + specialize (IHn H).
          unfold compLabelMaps.
          rewrite IHn; clear IHn.
          unfold compLabelMaps.
          destruct (dropN ds n s v); auto.
          destruct (dropI ds t s s0); auto.
          destruct (dropI ds (S n) s s1); auto.
          unfold dropI; remember (string_eq _ _) as st; destruct st; auto.
          exfalso; apply string_eq_dec_eq in Heqst; subst.
          apply spDom_getExtMeths in H.
          apply duplicate_dom_indexed in H; auto; dest.
          apply withIndex_index_eq in H; dest; omega.
    Qed.

    Lemma duplicate_traceRefines_drop:
      forall n,
        (m1 <<=[dropP ds] m2) ->
        (duplicate m1 n <<=[dropN ds n] duplicate m2 n).
    Proof.
      induction n; simpl; intros.

      - apply specializeMod_traceRefines_drop; auto.

      - apply traceRefines_modular_noninteracting_p; auto.
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
        + split.
          * apply equivalentLabelMapElem_dropI_dropN; omega.
          * apply equivalentLabelMapElem_dropN_dropI; omega.
        + apply duplicate_noninteracting; auto.
        + apply duplicate_noninteracting; auto.
        + apply specializeMod_traceRefines_drop; auto.
    Qed.

  End TwoModules2.

  Section TwoModules3.
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

    Corollary duplicate_regs_ConcatMod:
      forall n,
        EquivList (getRegInits (duplicate m1 n ++ duplicate m2 n)%kami)
                  (getRegInits (duplicate (m1 ++ m2)%kami n)).
    Proof.
      intros; split.
      - apply duplicate_regs_ConcatMod_2.
      - apply duplicate_regs_ConcatMod_1.
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
        rewrite <-app_assoc with (l:= map (@attrName _) (getRegInits (specializeMod m1 (S n)))).
        rewrite <-app_assoc with (l:= map (@attrName _) (getRegInits (specializeMod m1 (S n)))).
        apply NoDup_app_comm_ext.
        rewrite app_assoc.
        rewrite app_assoc.
        rewrite <-app_assoc with (n:= map (@attrName _) (getRegInits (duplicate m2 n))).
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

    Corollary duplicate_rules_ConcatMod:
      forall n,
        EquivList (getRules (duplicate m1 n ++ duplicate m2 n)%kami)
                  (getRules (duplicate (m1 ++ m2)%kami n)).
    Proof.
      intros; split.
      - apply duplicate_rules_ConcatMod_2.
      - apply duplicate_rules_ConcatMod_1.
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

    Lemma duplicate_defs_ConcatMod:
      forall n,
        EquivList (getDefsBodies (duplicate m1 n ++ duplicate m2 n)%kami)
                  (getDefsBodies (duplicate (m1 ++ m2)%kami n)).
    Proof.
      intros; split.
      - apply duplicate_defs_ConcatMod_2.
      - apply duplicate_defs_ConcatMod_1.
    Qed.

  End TwoModules3.

  Section TwoModules4.
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
      - split.
        + apply duplicate_regs_ConcatMod_1; auto.
        + apply duplicate_regs_ConcatMod_2; auto.
      - split.
        + apply duplicate_rules_ConcatMod_1; auto.
        + apply duplicate_rules_ConcatMod_2; auto.
      - split.
        + apply duplicate_defs_ConcatMod_1; auto.
        + apply duplicate_defs_ConcatMod_2; auto.
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
      - split.
        + apply duplicate_regs_ConcatMod_2; auto.
        + apply duplicate_regs_ConcatMod_1; auto.
      - split.
        + apply duplicate_rules_ConcatMod_2; auto.
        + apply duplicate_rules_ConcatMod_1; auto.
      - split.
        + apply duplicate_defs_ConcatMod_2; auto.
        + apply duplicate_defs_ConcatMod_1; auto.
    Qed.

  End TwoModules4.

End DuplicateFacts.

Hint Unfold specializeMod duplicate: ModuleDefs.

