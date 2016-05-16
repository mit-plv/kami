Require Import Bool String List.
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

  Lemma duplicate_NoDup_regs:
    forall m n,
      NoDup (namesOf (getRegInits m)) ->
      NoDup (namesOf (getRegInits (duplicate m n))).
  Proof.
    admit.
  Qed.

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

  Lemma regsToRep_regs_equiv:
    SubList (getRegInits (duplicate m n)) (getFullListFromMeta (regsToRep (getRegInits m))) /\
    SubList (getFullListFromMeta (regsToRep (getRegInits m))) (getRegInits (duplicate m n)).
  Proof.
    admit.
  Qed.

  Definition duplicateByRep := 
    makeModule {| metaRegs := regsToRep (getRegInits m);
                  metaRules := rulesToRep (getRules m);
                  metaMeths := methsToRep (getDefsBodies m) |}.
  
  Lemma duplicate_refines_repeat:
    duplicate m n <<== duplicateByRep.
  Proof.
    unfold makeModule; simpl.
    rewrite idElementwiseId.
    apply traceRefines_same_module_structure; simpl; auto; admit.
    (* - apply duplicate_NoDup_regs; auto. *)
    (* - apply regsToRep_regs_equiv. *)
    (* - apply regsToRep_regs_equiv. *)
  Qed.

End DupRep.

Hint Unfold specializeMod duplicate: ModuleDefs.
Hint Unfold regsToRep rulesToRep methsToRep duplicateByRep: ModuleDefs.

