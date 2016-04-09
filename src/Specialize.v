Require Import Bool String List.
Require Import Lib.FMap Lib.Struct Lib.CommonTactics Lib.StringEq.
Require Import Syntax Semantics SemFacts Refinement Renaming Equiv Wf.

Require Import FunctionalExtensionality.

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

  Definition spf := fun e => e __ i.

  Lemma prepend_same: forall x a b, (x ++ a)%string = (x ++ b)%string -> a = b.
  Proof.
    induction x; intros; intuition.
    inv H; auto.
  Qed.

  Lemma spf_onto: forall a1 a2, spf a1 = spf a2 -> a1 = a2.
  Proof.
    unfold spf; intros.
    rewrite withIndex_eq in H.
    eapply prepend_same; eauto.
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

End SpecializeModule.

Section SpecializeFacts.

  Lemma specializer_equiv:
    forall m1 m2 {A} (m: M.t A),
      M.KeysSubset m (spDom m1) ->
      M.KeysSubset m (spDom m2) ->
      forall i,
        renameMap (specializer m1 i) m = renameMap (specializer m2 i) m.
  Proof.
    admit.
  Qed.

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

  Lemma specializeMod_validRegsModules:
    forall m i,
      ValidRegsModules type m ->
      ValidRegsModules type (specializeMod m i).
  Proof.
    admit.
  Qed.

  Lemma specializeMod_defCallSub:
    forall m1 m2 i,
      DefCallSub m1 m2 ->
      DefCallSub (specializeMod m1 i) (specializeMod m2 i).
  Proof.
    admit.
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

  Lemma append_length:
    forall s1 s2,
      String.length (s1 ++ s2) = String.length s1 + String.length s2.
  Proof. induction s1; simpl; intros; auto. Qed.

  Lemma substring_append_1:
    forall s1 s2 n,
      substring (String.length s1) n (s1 ++ s2) = substring 0 n s2.
  Proof. induction s1; simpl; intros; auto. Qed.

  Lemma substring_empty:
    forall s, substring 0 0 s = ""%string.
  Proof. induction s; simpl; intros; auto. Qed.

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
        apply index_correct3 with (m:= String.length (string_of_nat i)) in Heqidx; auto.
        * rewrite <-string_append_assoc in Heqidx.
          rewrite substring_append_1 in Heqidx; simpl in Heqidx.
          rewrite substring_empty in Heqidx; auto.
        * omega.
    - destruct H1; [subst|].
      + clear -H H0; induction l; simpl; intros; auto.
        simpl in H.
        remember (index 0 indexSymbol a0) as idx; destruct idx; [inv H|].
        inv H0; auto.
        unfold spf in Heqidx; rewrite withIndex_eq in Heqidx.
        apply eq_sym in Heqidx.
        apply index_correct3 with (m:= String.length (string_of_nat i)) in Heqidx; auto.
        * rewrite <-string_append_assoc in Heqidx.
          rewrite substring_append_1 in Heqidx; simpl in Heqidx.
          rewrite substring_empty in Heqidx; auto.
        * omega.
      + eauto.
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

  Lemma specializable_disj_regs:
    forall i j,
      i <> j ->
      DisjList (namesOf (getRegInits (specializeMod m i)))
               (namesOf (getRegInits (specializeMod m j))).
  Proof.
    admit.
  Qed.

  Lemma specializable_disj_defs:
    forall i j,
      i <> j ->
      DisjList (getDefs (specializeMod m i))
               (getDefs (specializeMod m j)).
  Proof.
    admit.
  Qed.

  Lemma specializable_disj_calls:
    forall i j,
      i <> j ->
      DisjList (getCalls (specializeMod m i))
               (getCalls (specializeMod m j)).
  Proof.
    admit.
  Qed.

  Lemma specializable_noninteracting:
    forall i j,
      i <> j ->
      NonInteracting (specializeMod m i) (specializeMod m j).
  Proof.
    admit.
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
      apply DisjList_SubList with (l1:= (getDefs (specializeMod m (S n)))
                                          ++ (getDefs (duplicate m n))).
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
      apply DisjList_SubList with (l1:= (getCalls (specializeMod m (S n)))
                                          ++ (getCalls (duplicate m n))).
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
    - apply specializable_noninteracting; omega.
    - unfold NonInteracting in *.
      assert (ln > n) by omega; specialize (IHn _ H1); clear H1; dest.
      split.
      + apply DisjList_comm.
        apply DisjList_SubList with (l1:= (getCalls (specializeMod m (S n)))
                                            ++ (getCalls (duplicate m n))).
        * unfold SubList; intros.
          apply getCalls_in in H3.
          apply in_or_app; auto.
        * apply DisjList_app_4.
          { pose proof (specializable_noninteracting m).
            apply H3; omega.
          }
          { apply DisjList_comm; auto. }
      + apply DisjList_comm.
        apply DisjList_SubList with (l1:= (getDefs (specializeMod m (S n)))
                                            ++ (getDefs (duplicate m n))).
        * unfold SubList; intros.
          apply getDefs_in in H3.
          apply in_or_app; auto.
        * apply DisjList_app_4.
          { pose proof (specializable_noninteracting m).
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
      - apply specializer_equiv.
        + apply M.KeysSubset_SubList with (d2:= getExtMeths m2) in H; auto.
          eapply M.KeysSubset_SubList; eauto.
          pose proof (getExtMeths_meths m2).
          apply SubList_trans with (l2:= getDefs m2 ++ getCalls m2); auto.
          unfold spDom.
          eapply SubList_trans; [|eapply makeNoDup_SubList].
          apply SubList_app_3.
          * do 2 apply SubList_app_2.
            apply SubList_app_1, SubList_refl.
          * do 3 apply SubList_app_2.
            apply SubList_refl.
        + eapply M.KeysSubset_SubList; eauto.
          pose proof (getExtMeths_meths m1).
          apply SubList_trans with (l2:= getDefs m1 ++ getCalls m1); auto.
          unfold spDom.
          eapply SubList_trans; [|eapply makeNoDup_SubList].
          apply SubList_app_3.
          * do 2 apply SubList_app_2.
            apply SubList_app_1, SubList_refl.
          * do 3 apply SubList_app_2.
            apply SubList_refl.
    Qed.

    Lemma duplicate_traceRefines:
      forall n,
        (* TODO: requires a number of conditions *)
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

Hint Unfold specializeMod duplicate: ModuleDefs.

