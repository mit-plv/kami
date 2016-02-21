Require Import String List Program.Equality Program.Basics Classes.Morphisms.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct.
Require Import Syntax Semantics.

Set Implicit Arguments.

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

Theorem staticDynCallsRules m o name a u cs r:
  In (name :: a)%struct (getRules m) ->
  SemAction o (a type) u cs r ->
  forall f, M.In f cs -> In f (getCalls m).
Proof.
  admit.
Qed.

Theorem staticDynCallsMeths m o name a u cs r:
  In (name :: a)%struct (getDefsBodies m) ->
  forall argument,
    SemAction o (projT2 a type argument) u cs r ->
    forall f, M.In f cs -> In f (getCalls m).
Proof.
  admit.
Qed.

Theorem staticDynCallsSubstep m o u rm cs:
  Substep m o u rm cs ->
  forall f, M.In f cs -> In f (getCalls m).
Proof.
  intro H.
  dependent induction H; simpl in *; intros.
  - apply (M.F.P.F.empty_in_iff) in H; intuition.
  - apply (M.F.P.F.empty_in_iff) in H; intuition.
  - eapply staticDynCallsRules; eauto.
  - destruct f as [name a]; simpl in *.
    eapply staticDynCallsMeths; eauto.
Qed.

Theorem staticDynDefsSubstep m o u far cs:
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

Theorem staticDynCallsSubsteps m o ss:
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
      * apply (staticDynCallsSubstep substep); intuition.
      * intuition.
    + destruct (foldSSLabel ss); simpl in *.
      dependent destruction o0; simpl in *.
      * dependent destruction a; simpl in *.
        pose proof (M.union_In H) as sth.
        { destruct sth.
          - apply (staticDynCallsSubstep substep); intuition.
          - intuition.
        }
      * pose proof (M.union_In H) as sth.
        { destruct sth.
          - apply (staticDynCallsSubstep substep); intuition.
          - intuition.
        }
Qed.

Theorem staticDynDefsSubsteps m o ss:
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
              apply (staticDynDefsSubstep substep).
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

Lemma substepsInd_defs_in:
  forall m or u l,
    SubstepsInd m or u l -> M.KeysSubset (defs l) (getDefs m).
Proof.
  induction 1; simpl; [apply M.KeysSubset_empty|].
  subst; destruct l as [ann ds cs]; simpl in *.
  apply M.KeysSubset_union; auto.
  destruct sul as [|[[dmn dmv]|]]; try (apply M.KeysSubset_empty).
  apply M.KeysSubset_add; [apply M.KeysSubset_empty|].
  pose proof (staticDynDefsSubstep H0); auto.
Qed.

Lemma substepsInd_calls_in:
  forall m or u l,
    SubstepsInd m or u l -> M.KeysSubset (calls l) (getCalls m).
Proof.
  induction 1; simpl; [apply M.KeysSubset_empty|].
  subst; destruct l as [ann ds cs]; simpl in *.
  apply M.KeysSubset_union; auto.
  pose proof (staticDynCallsSubstep H0); auto.
Qed.

Lemma hide_idempotent:
  forall (l: LabelT), hide l = hide (hide l).
Proof.
  intros; destruct l as [ann ds cs].
  unfold hide; simpl; f_equal;
  apply M.subtractKV_idempotent.
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
  destruct (in_dec _ _ _).
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
    + destruct (in_dec _ _ _).
      * apply SubList_cons_right; auto.
      * simpl; apply SubList_cons; intuition.
        apply SubList_cons_right; auto.
Qed.

Lemma merge_preserves_substep:
  forall m or u ul cs,
    Substep m or u ul cs ->
    Substep (Mod (getRegInits m) (getRules m) (getDefsBodies m)) or u ul cs.
Proof. induction 1; simpl; intros; try (econstructor; eauto). Qed.

Lemma merge_preserves_substepsInd:
  forall m or u l,
    SubstepsInd m or u l ->
    SubstepsInd (Mod (getRegInits m) (getRules m) (getDefsBodies m)) or u l.
Proof.
  induction 1; intros; [constructor|].
  subst; eapply SubstepsCons; eauto.
  apply merge_preserves_substep; auto.
Qed.

Lemma merge_preserves_stepInd:
  forall m or nr l,
    StepInd m or nr l ->
    StepInd (Mod (getRegInits m) (getRules m) (getDefsBodies m)) or nr l.
Proof.
  intros; inv H.
  constructor; auto.
  apply merge_preserves_substepsInd; auto.
Qed.

Lemma merge_preserves_step:
  forall m or nr l,
    Step m or nr l ->
    Step (Mod (getRegInits m) (getRules m) (getDefsBodies m)) or nr l.
Proof.
  intros; apply step_consistent; apply step_consistent in H.
  apply merge_preserves_stepInd; auto.
Qed.

Lemma substep_dms_weakening:
  forall regs rules dms or u ul cs,
    Substep (Mod regs rules dms) or u ul cs ->
    forall filt,
      M.KeysDisj (defs (getLabel ul cs)) filt ->
      Substep (Mod regs rules (filterDms dms filt)) or u ul cs.
Proof.
  induction 1; simpl; intros; try (econstructor; eauto; fail).

  eapply SingleMeth; eauto.
  clear -H HIn; simpl in *.
  specialize (H f).
  apply filter_In.
  destruct (in_dec string_dec f filt); auto.
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
  forall regs rules dms,
    DisjList (getCalls (Mod regs rules dms)) (getDefs (Mod regs rules dms)) ->
    forall or u l,
      SubstepsInd (Mod regs rules dms) or u l ->
      M.Disj (calls l) (defs l).
Proof.
  intros.
  pose proof (substepsInd_calls_in H0).
  pose proof (substepsInd_defs_in H0).
  eapply M.DisjList_KeysSubset_Disj; eauto.
Qed.

Lemma substepsInd_hide_void:
  forall regs rules dms,
    DisjList (getCalls (Mod regs rules dms)) (getDefs (Mod regs rules dms)) ->
    forall or u l,
      SubstepsInd (Mod regs rules dms) or u l ->
      hide l = l.
Proof.
  intros; destruct l as [ann ds cs].
  pose proof (substepsInd_meths_disj H H0).
  unfold hide; simpl in *; f_equal; apply M.subtractKV_disj; mdisj.
Qed.

Lemma stepInd_dms_weakening:
  forall regs rules dms or u l,
    DisjList (getCalls (Mod regs rules dms)) (getDefs (Mod regs rules dms)) ->
    StepInd (Mod regs rules dms) or u l ->
    forall filt,
      M.KeysDisj (defs l) filt ->
      StepInd (Mod regs rules (filterDms dms filt)) or u l.
Proof.
  induction 2; intros.
  constructor.
  - erewrite substepsInd_hide_void in H0; eauto.
    apply substepInd_dms_weakening; auto.
  - apply filterDms_wellHidden; auto.
Qed.

Lemma step_dms_weakening:
  forall regs rules dms or u l,
    DisjList (getCalls (Mod regs rules dms))
             (getDefs (Mod regs rules dms)) ->
    Step (Mod regs rules dms) or u l ->
    forall filt,
      M.KeysDisj (defs l) filt ->
      Step (Mod regs rules (filterDms dms filt)) or u l.
Proof.
  intros; subst; simpl.
  apply step_consistent; apply step_consistent in H0.
  apply stepInd_dms_weakening; auto.
Qed.

Definition IsChild (c p: Modules) :=
  (exists c', p = ConcatMod c c' \/ p = ConcatMod c' c).
Hint Unfold IsChild.

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
  - eapply SemIfElseTrue; eauto.
  - eapply SemIfElseFalse; eauto.
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

