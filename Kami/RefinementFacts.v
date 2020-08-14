Require Import Bool List String Lia.
Require Import Program.Equality Program.Basics Classes.Morphisms.
Require Import Lib.CommonTactics Lib.Indexer Lib.FMap Lib.Struct Lib.StringEq Lib.ListSupport.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.ModularFacts Kami.Wf.
Require Import FunctionalExtensionality.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section LabelMapComposition.
  Definition compLabelMaps (p q: M.key -> sigT SignT -> option (sigT SignT)) :=
    fun s v =>
      match q s v with
      | Some qv => p s qv
      | None => None
      end.

  Lemma compLabelMaps_id_left:
    forall p, p = compLabelMaps (@idElementwise _) p.
  Proof.
    intros; extensionality k; extensionality v.
    unfold compLabelMaps.
    destruct (p k v); auto.
  Qed.

  Lemma compLabelMaps_id_right:
    forall p, p = compLabelMaps p (@idElementwise _).
  Proof. auto. Qed.
  
End LabelMapComposition.

Section EquivalentLabelMapElem.

  Definition EquivalentLabelMapElem (p q: M.key -> sigT SignT -> option (sigT SignT))
             (d: list string) :=
    forall s, In s d -> forall v, p s v = q s v.

  Lemma equivalentLabelMapElem_id_left:
    forall p d, EquivalentLabelMapElem p (compLabelMaps (@idElementwise _) p) d.
  Proof.
    unfold EquivalentLabelMapElem; intros.
    unfold compLabelMaps; destruct (p s v); auto.
  Qed.

  Lemma equivalentLabelMapElem_id_right:
    forall p d, EquivalentLabelMapElem p (compLabelMaps p (@idElementwise _)) d.
  Proof.
    unfold EquivalentLabelMapElem; intros; reflexivity.
  Qed.

End EquivalentLabelMapElem.

Section DisjLabelMap.
  Variable (vp vq: M.key -> sigT SignT -> option (sigT SignT)).

  Definition DisjLabelMap (dp dq: list string) :=
    EquivalentLabelMapElem vp (compLabelMaps vp vq) dp /\
    EquivalentLabelMapElem vq (compLabelMaps vp vq) dq.

End DisjLabelMap.

Section LabelDrop.

  Definition dropP (ds: string) (s: M.key) (v: sigT SignT): option (sigT SignT) :=
    if string_eq s ds then None else Some v.

  Definition dropI (ds: string) (i: nat) (s: M.key) (v: sigT SignT): option (sigT SignT) :=
    if string_eq s (ds __ i) then None else Some v.

  Fixpoint dropN (ds: string) (n: nat) :=
    match n with
    | O => dropI ds O
    | S n' => compLabelMaps (dropI ds n) (dropN ds n')
    end.

  Lemma dropP_KeysSubset:
    forall ds m d,
      M.KeysSubset m d -> M.KeysSubset (liftToMap1 (dropP ds) m)
                                       (filter (fun s => negb (string_eq s ds)) d).
  Proof.
    unfold M.KeysSubset; intros.
    apply filter_In; split.
    - apply H; rewrite M.F.P.F.in_find_iff in *.
      intro Hx; elim H0; clear H0.
      rewrite liftToMap1_find; rewrite Hx; auto.
    - apply negb_true_iff.
      apply string_eq_dec_false.
      apply M.F.P.F.in_find_iff in H0.
      intro Hx; elim H0; clear H0; subst.
      rewrite liftToMap1_find.
      destruct (M.find ds m); auto.
      unfold dropP; rewrite string_eq_true; auto.
  Qed.

  Fixpoint dropPs (ds: list string): M.key -> sigT SignT -> option (sigT SignT) :=
    match ds with
    | nil => fun _ v => Some v
    | d :: ds' => fun s v => if string_eq s d then None else dropPs ds' s v
    end.

  Lemma dropPs_nil_idElementwise: dropPs nil = idElementwise (A:= sigT SignT).
  Proof. reflexivity. Qed.

  Lemma dropPs_None: forall s v ds, dropPs ds s v = None -> In s ds.
  Proof.
    induction ds; simpl; intros; [inv H|].
    remember (string_eq s a) as sa; destruct sa; auto.
    apply string_eq_dec_eq in Heqsa; auto.
  Qed.

  Lemma dropPs_None_inv: forall s v ds, In s ds -> dropPs ds s v = None.
  Proof.
    induction ds; simpl; intros; [inv H|].
    destruct H; subst.
    - rewrite string_eq_true; auto.
    - destruct (string_eq s a); auto.
  Qed.

  Lemma dropPs_Some: forall s v v' ds, dropPs ds s v = Some v' -> v = v' /\ ~ In s ds.
  Proof.
    induction ds; simpl; intros; [inv H; auto|].
    remember (string_eq s a) as sa; destruct sa; [inv H|].
    specialize (IHds H); dest; split; auto.
    apply string_eq_dec_neq in Heqsa; intuition.
  Qed.

  Lemma dropPs_Some_inv: forall s v ds, ~ In s ds -> dropPs ds s v = Some v.
  Proof.
    induction ds; simpl; intros; auto.
    remember (string_eq s a) as sa; destruct sa; auto.
    apply string_eq_dec_eq in Heqsa; subst.
    intuition.
  Qed.

  Fixpoint duplicateElt (ds: string) (n: nat) :=
    match n with
    | O => [ds __ 0]
    | S n' => (ds __ n) :: (duplicateElt ds n')
    end.

  Lemma duplicateElt_In:
    forall e p n,
      In e (duplicateElt p n) -> exists t, e = p __ t.
  Proof.
    induction n; simpl; intros.
    - destruct H; [|inv H]; subst; eexists; eauto.
    - destruct H; [subst; eexists; eauto|auto].
  Qed.

  Lemma duplicateElt_In_inv:
    forall p x n, x <= n -> In (p __ x) (duplicateElt p n).
  Proof.
    induction n; simpl; intros.
    - assert (x = 0) by lia; subst; intuition.
    - inv H; intuition.
  Qed.

  Lemma duplicateElt_not_In:
    forall p' p x n, p <> p' -> ~ In (p' __ x) (duplicateElt p n).
  Proof.
    induction n; simpl; intros.
    - intro Hx; destruct Hx; auto.
      apply withIndex_index_eq in H0; intuition.
    - intro Hx; destruct Hx.
      + apply withIndex_index_eq in H0; intuition.
      + intuition.
  Qed.

  Lemma duplicateElt_DisjList:
    forall p1 p2 n, p1 <> p2 -> DisjList (duplicateElt p1 n) (duplicateElt p2 n).
  Proof.
    unfold DisjList; intros.
    destruct (in_dec string_dec e (duplicateElt p1 n)); auto.
    destruct (in_dec string_dec e (duplicateElt p2 n)); auto.
    exfalso; apply duplicateElt_In in i; apply duplicateElt_In in i0; dest.
    subst; apply withIndex_index_eq in H0; intuition.
  Qed.

  Lemma dropN_dropPs: forall ds n, dropN ds n = dropPs (duplicateElt ds n).
  Proof.
    induction n; simpl; intros; auto.
    rewrite IHn; unfold compLabelMaps.
    extensionality s; extensionality v.
    remember (string_eq s (ds __ (S n))) as sn; destruct sn.
    - destruct (dropPs _ _ _); auto.
      apply string_eq_dec_eq in Heqsn; subst.
      unfold dropI; rewrite string_eq_true; auto.
    - destruct (dropPs _ _ _); auto.
      apply string_eq_dec_neq in Heqsn.
      unfold dropI; rewrite string_eq_dec_false; auto.
  Qed.

  Lemma dropPs_disj:
    forall ds1 ds2 dom1 dom2,
      DisjList dom1 ds2 -> DisjList dom2 ds1 ->
      DisjLabelMap (dropPs ds1) (dropPs ds2) dom1 dom2.
  Proof.
    unfold DisjLabelMap; intros; split;
      unfold EquivalentLabelMapElem, compLabelMaps; intros.
    - remember (dropPs ds2 s v) as dv; destruct dv.
      + apply eq_sym, dropPs_Some in Heqdv; dest; subst; auto.
      + exfalso; apply eq_sym, dropPs_None in Heqdv.
        specialize (H s); destruct H; auto.
    - remember (dropPs ds2 s v) as dv; destruct dv; auto.
      apply eq_sym, dropPs_Some in Heqdv; dest; subst.
      remember (dropPs ds1 s s0) as ds; destruct ds.
      + apply eq_sym, dropPs_Some in Heqds; dest; subst; auto.
      + exfalso; apply eq_sym, dropPs_None in Heqds.
        specialize (H0 s); destruct H0; auto.
  Qed.

End LabelDrop.

Section StepToRefinement.
  Variable imp spec: Modules.
  Variable p: MethsT -> MethsT.
  Variable ruleMap: RegsT -> string -> option string.
  Variable theta: RegsT -> RegsT.
  Variable thetaInit: theta (initRegs (getRegInits imp)) = initRegs (getRegInits spec).

  Definition liftPLabel o l :=
    match l with
    | {| annot := a; defs := dfs; calls := clls |} =>
      {| annot := match a with
                  | Some (Some r) => Some (ruleMap o r)
                  | Some None => Some None
                  | None => None
                  end;
         defs := p dfs;
         calls := p clls |}
    end.

  Variable stepMap:
    forall o u l,
      reachable o imp ->
      Step imp o u l ->
      exists uspec, Step spec (theta o) uspec (liftPLabel o l) /\
                    theta (M.union u o) = M.union uspec (theta o).

  Theorem stepRefinement':
    forall s sig, Behavior imp s sig ->
                  exists sigSpec, Behavior spec (theta s) sigSpec /\
                                  equivalentLabelSeq p sig sigSpec.
  Proof.
    intros.
    dependent induction H.
    dependent induction HMultistepBeh; subst.
    - exists nil; rewrite thetaInit; repeat constructor.
    - specialize (IHHMultistepBeh thetaInit stepMap eq_refl).
      assert (reachable n imp) by (eexists; constructor; eauto).
      pose proof (stepMap H HStep) as [uSpec [stepSpec upd]].
      destruct IHHMultistepBeh as [sigSpec [behSpec eqv]].
      inversion behSpec; subst.
      pose proof (BehaviorIntro (Multi HMultistepBeh0 stepSpec)) as sth.
      rewrite <- upd in sth.
      exists (liftPLabel n l :: sigSpec).
      constructor.
      + intuition.
      + constructor.
        * unfold equivalentLabel, liftPLabel; simpl.
          destruct l; destruct annot; simpl; intuition.
          destruct o; simpl; intuition.
        * intuition.
  Qed.

  Theorem stepRefinement: traceRefines p imp spec.
  Proof.
    unfold traceRefines; intros.
    pose proof (stepRefinement' H) as [sigSpec beh].
    exists (theta s1); exists sigSpec.
    intuition.
  Qed.
End StepToRefinement.

Section StepToRefinementR.
  Variable imp spec: Modules.
  Variable p: MethsT -> MethsT.
  Variable thetaR: RegsT -> RegsT -> Prop.
  Hypothesis (HthetaInit:
                thetaR (initRegs (getRegInits imp)) (initRegs (getRegInits spec))).

  Definition labelR il sa :=
    match il with
    | {| annot := ia; defs := ids; calls := ics |} =>
      {| annot := match ia with
                  | None => None
                  | Some _ => Some sa
                  end; defs := p ids; calls := p ics |}
    end.

  Variable stepMapR:
    forall o u l,
      reachable o imp ->
      Step imp o u l ->
      forall so,
        thetaR o so ->
        exists sa su,
          Step spec so su (labelR l sa) /\
          thetaR (M.union u o) (M.union su so).

  Lemma stepRefinementR':
    forall o s sig,
      o = initRegs (getRegInits imp) ->
      Multistep imp o s sig ->
      forall os,
        thetaR o os ->
        exists ss ssig,
          thetaR s ss /\
          Multistep spec os ss ssig /\ 
          equivalentLabelSeq p sig ssig.
  Proof.
    induction 2; simpl; intros.
    - repeat subst; do 2 eexists; repeat split; eauto.
      + constructor; auto.
      + constructor.
    - specialize (IHMultistep H _ H1); dest.
      apply stepMapR with (so:= x) in HStep; auto;
        [|subst; eexists; constructor; eauto].
      dest.
      
      do 2 eexists; repeat split; eauto.
      + econstructor 2; eauto.
      + econstructor; eauto.
        destruct l as [ann ds cs]; unfold equivalentLabel, liftPLabel; simpl.
        repeat split.
        destruct ann as [[|]|]; auto.
  Qed.

  Theorem stepRefinementR: traceRefines p imp spec.
  Proof.
    unfold traceRefines; intros.
    inv H.
    apply stepRefinementR' with (os:= initRegs (getRegInits spec)) in HMultistepBeh; auto.
    dest; do 2 eexists; split; eauto.
    constructor; eauto.
  Qed.

End StepToRefinementR.

Lemma liftPLabel_mergeLabel:
  forall ruleMap o p l1 l2,
    CanCombineLabel l1 l2 ->
    liftPLabel (liftToMap1 p) ruleMap o (mergeLabel l1 l2) =
    mergeLabel (liftPLabel (liftToMap1 p) ruleMap o l1)
               (liftPLabel (liftToMap1 p) ruleMap o l2).
Proof.
  intros; destruct l1 as [a1 d1 c1], l2 as [a2 d2 c2]; simpl in *; f_equal.

  - destruct a1 as [[|]|], a2 as [[|]|]; reflexivity.
  - inv H; dest; simpl in *.
    apply liftToMap1_union; auto.
  - inv H; dest; simpl in *.
    apply liftToMap1_union; auto.
Qed.

Lemma liftPLabel_hide:
  forall imp ruleMap o p l,
    M.KeysSubset (defs l) (getDefs imp) ->
    M.KeysSubset (calls l) (getCalls imp) ->
    wellHidden imp (hide l) ->
    liftPLabel (liftToMap1 p) ruleMap o (hide l) =
    hide (liftPLabel (liftToMap1 p) ruleMap o l).
Proof.
  intros; destruct l as [a d c].
  unfold hide in *; simpl in *.
  f_equal; auto.
  - apply eq_sym, liftToMap1_subtractKV_2.
    intros; unfold wellHidden in H1; dest; simpl in *.
    apply M.subtractKV_not_In_find with (deceqA:= signIsEq) (m2:= c) in H2.
    + rewrite H2 in H3; inv H3; reflexivity.
    + apply H1, H0.
      apply M.F.P.F.in_find_iff; rewrite H3; discriminate.
  - apply eq_sym, liftToMap1_subtractKV_2.
    intros; unfold wellHidden in H1; dest; simpl in *.
    apply M.subtractKV_not_In_find with (deceqA:= signIsEq) (m2:= c) in H3.
    + rewrite H2 in H3; inv H3; reflexivity.
    + apply H1, H0.
      apply M.F.P.F.in_find_iff; rewrite H2; discriminate.
Qed.

Lemma liftPLabel_wellHidden:
  forall imp spec ruleMap o p l
         (HdefSubset: forall f, In f (getDefs spec) -> In f (getDefs imp))
         (HcallSubset: forall f, In f (getCalls spec) -> In f (getCalls imp)),
    wellHidden imp l ->
    wellHidden spec (liftPLabel (liftToMap1 p) ruleMap o l).
Proof.
  intros; unfold wellHidden in *.
  destruct l; simpl in *; dest; split.
  - clear -H HcallSubset.
    unfold M.KeysDisj in *; intros.
    specialize (H k (HcallSubset _ H0)).
    clear -H; findeq.
    rewrite liftToMap1_find, H; auto.
  - clear -H0 HdefSubset.
    unfold M.KeysDisj in *; intros.
    specialize (H0 k (HdefSubset _ H)).
    clear -H0; findeq.
    rewrite liftToMap1_find, H0; auto.
Qed.

Lemma vp_equivalentLabel_CanCombineLabel_proper:
  forall vp,
    Proper (equivalentLabel (liftToMap1 vp) ==> equivalentLabel (liftToMap1 vp) ==> impl)
           CanCombineLabel.
Proof.
  unfold Proper, respectful, impl; intros.
  destruct x as [annx dsx csx], y as [anny dsy csy].
  destruct x0 as [annx0 dsx0 csx0], y0 as [anny0 dsy0 csy0]; simpl in *.
  inv H; inv H0; inv H1; dest; simpl in *; subst.
  repeat split; simpl; auto.
  - apply M.DomainSubset_Disj with (m2:= dsx); [|apply liftToMap1_DomainSubset].
    apply M.Disj_comm.
    apply M.DomainSubset_Disj with (m2:= dsx0); [|apply liftToMap1_DomainSubset].
    auto.
  - apply M.DomainSubset_Disj with (m2:= csx); [|apply liftToMap1_DomainSubset].
    apply M.Disj_comm.
    apply M.DomainSubset_Disj with (m2:= csx0); [|apply liftToMap1_DomainSubset].
    auto.
  - destruct annx, annx0, anny, anny0; auto.
Qed.

Lemma traceRefines_refl:
  forall m, traceRefines id m m.
Proof.
  unfold traceRefines; intros.
  exists s1, sig1; split; auto.
  clear; induction sig1; constructor; auto.
  clear; repeat split.
  destruct (annot a); auto.
Qed.

Lemma traceRefines_trans:
  forall ma mb mc p q,
    traceRefines p ma mb ->
    traceRefines q mb mc ->
    traceRefines (fun f => q (p f)) ma mc.
Proof.
  unfold traceRefines; intros.
  specialize (H _ _ H1); destruct H as [s2 [sig2 ?]]; dest.
  specialize (H0 _ _ H); destruct H0 as [s3 [sig3 ?]]; dest.
  exists s3, sig3; split; auto.
  clear -H2 H3.
  generalize dependent sig2; generalize dependent sig3.
  induction sig1; intros.
  - inv H2; inv H3; constructor.
  - inv H2; inv H3; constructor; eauto.
    clear -H1 H2.
    inv H1; inv H2; dest.
    repeat split; auto.
    + rewrite H; auto.
    + rewrite H0; auto.
    + destruct (annot y), (annot y0), (annot a); auto.
Qed.

Corollary traceRefines_trans_elem:
  forall m1 m2 m3: Modules,
    (m1 <<== m2) -> (m2 <<== m3) -> (m1 <<== m3).
Proof.
  intros; unfold MethsT in *; rewrite idElementwiseId in *.
  eapply traceRefines_trans; eauto.
Qed.

Corollary traceRefines_trans_elem_left_p:
  forall (m1 m2 m3: Modules) p,
    (m1 <<=[p] m2) -> (m2 <<== m3) -> (m1 <<=[p] m3).
Proof.
  intros; unfold MethsT in *; rewrite idElementwiseId in *.
  eapply traceRefines_trans with (q:= id); eauto.
Qed.

Corollary traceRefines_trans_elem_right_p:
  forall (m1 m2 m3: Modules) p,
    (m1 <<== m2) -> (m2 <<=[p] m3) -> (m1 <<=[p] m3).
Proof.
  intros; unfold MethsT in *; rewrite idElementwiseId in *.
  eapply traceRefines_trans; eauto.
Qed.

Corollary traceRefines_trans_conj:
  forall ma mb mc p q,
    traceRefines p ma mb /\
    traceRefines q mb mc ->
    traceRefines (fun f => q (p f)) ma mc.
Proof.
  intros; dest; eapply traceRefines_trans; eauto.
Qed.

Lemma traceRefines_labelMap_weakening:
  forall ma (Hequiv: ModEquiv type typeUT ma) mb vp,
    (ma <<=[vp] mb) ->
    forall vq,
      EquivalentLabelMapElem vp vq (getExtMeths ma) ->
      (ma <<=[vq] mb).
Proof.
  unfold traceRefines; intros.
  specialize (H _ _ H1).
  destruct H as [s2 [sig2 ?]]; dest.
  exists s2, sig2; split; auto.
  pose proof (behavior_defs_ext_in Hequiv H1).
  pose proof (behavior_calls_ext_in Hequiv H1).
  clear -H0 H2 H3 H4.

  generalize dependent sig2; induction sig1; simpl; intros;
    [inv H2; constructor|].
  destruct sig2; [inv H2|].
  inv H2; inv H3; inv H4; constructor; auto.
  clear -H0 H2 H3 H6.

  unfold equivalentLabel in *; dest; repeat split; auto; clear H4.
  - rewrite <-H; clear -H0 H2.
    M.ext y; do 2 rewrite liftToMap1_find.
    remember (M.find y (defs a)) as yv; destruct yv; auto.
    apply eq_sym, H0.
    apply H2; findeq.
  - rewrite <-H1; clear -H0 H3.
    M.ext y; do 2 rewrite liftToMap1_find.
    remember (M.find y (calls a)) as yv; destruct yv; auto.
    apply eq_sym, H0.
    apply H3; findeq.
Qed.

Lemma traceRefines_same_module_structure:
  forall ma mb,
    NoDup (namesOf (getRegInits ma)) ->
    NoDup (namesOf (getRegInits mb)) ->
    EquivList (getRegInits ma) (getRegInits mb) ->
    EquivList (getRules ma) (getRules mb) ->
    EquivList (getDefsBodies ma) (getDefsBodies mb) ->
    traceRefines id ma mb.
Proof.
  unfold traceRefines; intros.
  pose proof (initRegs_eq H H0 H1).
  exists s1, sig1; split.
  - inv H4; constructor.
    remember (initRegs (getRegInits ma)).
    induction HMultistepBeh.
    + subst; constructor.
      rewrite <-H5; auto.
    + constructor; auto.
      apply module_structure_indep_step with (m1:= ma); auto.
  - clear; induction sig1; constructor; auto.
    constructor; destruct (annot a); auto.
Qed.

Lemma traceRefines_same_module_structure_modular_1:
  forall ma mb mc,
    NoDup (namesOf (getRegInits ma)) ->
    NoDup (namesOf (getRegInits mb)) ->
    NoDup (namesOf (getRegInits mc)) ->
    DisjList (namesOf (getRegInits ma)) (namesOf (getRegInits mc)) ->
    DisjList (namesOf (getRegInits mb)) (namesOf (getRegInits mc)) ->
    EquivList (getRegInits ma) (getRegInits mb) ->
    EquivList (getRules ma) (getRules mb) ->
    EquivList (getDefsBodies ma) (getDefsBodies mb) ->
    traceRefines id (ma ++ mc)%kami (mb ++ mc)%kami.
Proof.
  intros; apply traceRefines_same_module_structure; auto.
  - simpl; unfold RegInitT; rewrite namesOf_app.
    apply NoDup_DisjList; auto.
  - simpl; unfold RegInitT; rewrite namesOf_app.
    apply NoDup_DisjList; auto.
  - apply EquivList_app; [auto|apply EquivList_refl].
  - apply EquivList_app; [auto|apply EquivList_refl].
  - apply EquivList_app; [auto|apply EquivList_refl].
Qed.

Lemma traceRefines_same_module_structure_modular_2:
  forall ma mb mc,
    NoDup (namesOf (getRegInits ma)) ->
    NoDup (namesOf (getRegInits mb)) ->
    NoDup (namesOf (getRegInits mc)) ->
    DisjList (namesOf (getRegInits ma)) (namesOf (getRegInits mc)) ->
    DisjList (namesOf (getRegInits mb)) (namesOf (getRegInits mc)) ->
    EquivList (getRegInits ma) (getRegInits mb) ->
    EquivList (getRules ma) (getRules mb) ->
    EquivList (getDefsBodies ma) (getDefsBodies mb) ->
    traceRefines id (mc ++ ma)%kami (mc ++ mb)%kami.
Proof.
  intros; apply traceRefines_same_module_structure; auto.
  - simpl; unfold RegInitT; rewrite namesOf_app.
    apply NoDup_DisjList; auto.
    apply DisjList_comm; auto.
  - simpl; unfold RegInitT; rewrite namesOf_app.
    apply NoDup_DisjList; auto.
    apply DisjList_comm; auto.
  - apply EquivList_app; [apply EquivList_refl|auto].
  - apply EquivList_app; [apply EquivList_refl|auto].
  - apply EquivList_app; [apply EquivList_refl|auto].
Qed.

Lemma traceRefines_comm:
  forall ma mb,
    NoDup (namesOf (getRegInits (ma ++ mb)%kami)) ->
    traceRefines id (ma ++ mb)%kami (mb ++ ma)%kami.
Proof.
  intros; apply traceRefines_same_module_structure; auto.
  - unfold namesOf in *; simpl in *; rewrite map_app in *.
    apply NoDup_app_comm; auto.
  - apply EquivList_app_comm.
  - apply EquivList_app_comm.
  - apply EquivList_app_comm.
Qed.

Lemma traceRefines_assoc_1:
  forall ma mb mc,
    traceRefines id ((ma ++ mb) ++ mc)%kami (ma ++ (mb ++ mc))%kami.
Proof.
  unfold traceRefines; intros.
  exists s1, sig1; split.
  - inv H; constructor.
    remember (initRegs (getRegInits ((ma ++ mb) ++ mc)%kami)).
    induction HMultistepBeh.
    + subst; constructor.
      f_equal.
      simpl; rewrite app_assoc; auto.
    + constructor; auto.
      clear -HStep.
      apply module_structure_indep_step with (m1:= ((ma ++ mb) ++ mc)%kami); auto;
        simpl; split; rewrite app_assoc; apply SubList_refl.
      
  - clear; induction sig1; constructor; auto.
    constructor; destruct (annot a); auto.
Qed.

Lemma traceRefines_assoc_2:
  forall ma mb mc,
    traceRefines id (ma ++ (mb ++ mc))%kami ((ma ++ mb) ++ mc)%kami.
Proof.
  unfold traceRefines; intros.
  exists s1, sig1; split.
  - inv H; constructor.
    remember (initRegs (getRegInits (ma ++ mb ++ mc)%kami)).
    induction HMultistepBeh.
    + subst; constructor.
      f_equal.
      simpl; rewrite app_assoc; auto.
    + constructor; auto.
      clear -HStep.
      apply module_structure_indep_step with (m1:= (ma ++ mb ++ mc)%kami); auto;
        simpl; split; rewrite app_assoc; apply SubList_refl.
      
  - clear; induction sig1; constructor; auto.
    constructor; destruct (annot a); auto.
Qed.    

Definition EquivalentLabelMap (p q: MethsT -> MethsT) (dom: list M.key) :=
  forall m, M.KeysSubset m dom -> p m = q m.

Lemma equivalentLabelMap_elem:
  forall vp vq d,
    EquivalentLabelMapElem vp vq d ->
    EquivalentLabelMap (liftToMap1 vp) (liftToMap1 vq) d.
Proof.
  unfold EquivalentLabelMap, EquivalentLabelMapElem; intros.
  M.ext y; rewrite !liftToMap1_find.
  remember (M.find y m) as yv; destruct yv; auto.
  apply H, H0; findeq.
Qed.

Lemma step_label_map:
  forall m (Hequiv: ModEquiv type typeUT m) p q,
    EquivalentLabelMap p q (getExtMeths m) ->
    forall o u l1,
      Step m o u l1 ->
      forall l2,
        equivalentLabel p l1 l2 ->
        equivalentLabel q l1 l2.
Proof.
  intros. destruct H1 as [? [? ?]].
  repeat split; auto; clear H3.
  - rewrite <-H1.
    apply eq_sym, H.
    eapply step_defs_ext_in; eauto.
  - rewrite <-H2.
    apply eq_sym, H.
    eapply step_calls_ext_in; eauto.
Qed.

Lemma multistep_label_map:
  forall m (Hequiv: ModEquiv type typeUT m) p q,
    EquivalentLabelMap p q (getExtMeths m) ->
    forall o s ll1,
      Multistep m o s ll1 ->
      forall ll2,
        equivalentLabelSeq p ll1 ll2 ->
        equivalentLabelSeq q ll1 ll2.
Proof.
  induction 3; simpl; intros; [inv H1; constructor|].
  destruct ll2; [inv H1|].
  inv H1; constructor; auto.
  eapply step_label_map; eauto.
Qed.

Lemma behavior_label_map:
  forall m (Hequiv: ModEquiv type typeUT m) p q,
    EquivalentLabelMap p q (getExtMeths m) ->
    forall s ll1,
      Behavior m s ll1 ->
      forall ll2,
        equivalentLabelSeq p ll1 ll2 ->
        equivalentLabelSeq q ll1 ll2.
Proof.
  intros; inv H0.
  eapply multistep_label_map; eauto.
Qed.

Lemma traceRefines_label_map:
  forall ma (Hequiv: ModEquiv type typeUT ma) mb p q,
    EquivalentLabelMap p q (getExtMeths ma) ->
    traceRefines p ma mb ->
    traceRefines q ma mb.
Proof.
  unfold traceRefines; intros.
  specialize (H0 _ _ H1); destruct H0 as [s2 [sig2 ?]]; dest.
  exists s2, sig2; split; auto.
  eapply behavior_label_map; eauto.
Qed.

Definition NonInteracting (m1 m2: Modules) :=
  DisjList (getDefs m1) (getCalls m2) /\
  DisjList (getCalls m1) (getDefs m2).

Lemma nonInteracting_implies_wellHiddenModular:
  forall ma mb,
    NonInteracting ma mb ->
    forall la lb,
      WellHiddenModular ma mb la lb.
Proof.
  unfold NonInteracting, WellHiddenModular, ValidLabel, wellHidden; intros; dest.
  destruct la as [anna dsa csa], lb as [annb dsb csb]; simpl in *.
  split.

  - unfold M.KeysDisj in *; intros.
    apply M.F.P.F.not_find_in_iff.
    specializeAll k.
    apply getCalls_in in H9; destruct H9.
    + specialize (H2 H9); clear H3 H4 H5.
      apply M.F.P.F.not_find_in_iff in H2.
      findeq;
        try (destruct (H8 k); [elim H3; auto|elim H3; apply H1; findeq]).
    + specialize (H3 H9); clear H2 H4 H5.
      apply M.F.P.F.not_find_in_iff in H3.
      findeq; findeq_more;
        try (destruct (H k); elim H2; [apply H0; findeq|apply H6; findeq]; fail).
      destruct (H8 k); elim H2; [apply H7; findeq|apply H1; findeq].
  - unfold M.KeysDisj in *; intros.
    apply M.F.P.F.not_find_in_iff.
    specializeAll k.
    apply getDefs_in in H9; destruct H9.
    + specialize (H5 H9); clear H2 H3 H4.
      apply M.F.P.F.not_find_in_iff in H5.
      findeq;
        try (destruct (H k); elim H2; [apply H0; findeq|apply H6; findeq]).
    + specialize (H4 H9); clear H2 H3 H5.
      apply M.F.P.F.not_find_in_iff in H4.
      findeq; findeq_more;
        try (destruct (H k); elim H2; [apply H0; findeq|apply H6; findeq]; fail);
        try (destruct (H8 k); elim H2; [apply H7; findeq|apply H1; findeq]; fail).
Qed.

Lemma nonInteracting_implies_wellHiddenModularSeq:
  forall ma mb,
    NonInteracting ma mb ->
    forall lsa lsb,
      List.length lsa = List.length lsb ->
      WellHiddenModularSeq ma mb lsa lsb.
Proof.
  induction lsa; intros.
  - destruct lsb; [constructor|inv H0].
  - destruct lsb; [inv H0|].
    constructor; auto.
    apply nonInteracting_implies_wellHiddenModular; auto.
Qed.

Lemma equivalentLabel_mergeLabel:
  forall la lb vp,
    equivalentLabel (liftToMap1 vp) la lb ->
    forall lc ld,
      CanCombineLabel la lc ->
      equivalentLabel (liftToMap1 vp) lc ld ->
      equivalentLabel (liftToMap1 vp) (mergeLabel la lc) (mergeLabel lb ld).
Proof.
  intros.
  destruct la as [anna dsa csa], lb as [annb dsb csb].
  destruct lc as [annc dsc csc], ld as [annd dsd csd].
  inv H; inv H0; inv H1; dest; simpl in *; subst.
  repeat split.
  - apply liftToMap1_union; auto.
  - apply liftToMap1_union; auto.
  - destruct anna, annb, annc, annd; auto.
Qed.

Definition NonInteractingLabel (l1 l2: LabelT) :=
  hide l1 = l1 /\ hide l2 = l2 /\
  M.Disj (defs l1) (calls l2) /\ M.Disj (calls l1) (defs l2).

Lemma NonInteractingLabel_mergeLabel_hide:
  forall l1 l2,
    CanCombineLabel l1 l2 ->
    NonInteractingLabel l1 l2 ->
    hide (mergeLabel l1 l2) = mergeLabel l1 l2.
Proof.
  intros; inv H; dest.
  unfold NonInteractingLabel in H0; dest.
  destruct l1 as [ann1 ds1 cs1], l2 as [ann2 ds2 cs2].
  unfold hide in *; simpl in *.
  f_equal.
  - rewrite M.subtractKV_disj_union_1 by assumption.
    do 2 (rewrite M.subtractKV_disj_union_2 by assumption).
    rewrite M.subtractKV_disj_invalid with (m1:= ds2) by auto.
    remember (M.subtractKV _ ds1 cs1) as dcs1; clear Heqdcs1.
    remember (M.subtractKV _ cs1 ds1) as cds1; clear Heqcds1.
    remember (M.subtractKV _ ds2 cs2) as dcs2; clear Heqdcs2.
    remember (M.subtractKV _ cs2 ds2) as cds2; clear Heqcds2.
    inv H0; inv H3.
    rewrite M.subtractKV_disj_invalid by auto.
    reflexivity.
  - rewrite M.subtractKV_disj_union_1 by assumption.
    do 2 (rewrite M.subtractKV_disj_union_2 by assumption).
    rewrite M.subtractKV_disj_invalid with (m1:= cs2) by auto.
    remember (M.subtractKV _ ds1 cs1) as dcs1; clear Heqdcs1.
    remember (M.subtractKV _ cs1 ds1) as cds1; clear Heqcds1.
    remember (M.subtractKV _ ds2 cs2) as dcs2; clear Heqdcs2.
    remember (M.subtractKV _ cs2 ds2) as cds2; clear Heqcds2.
    inv H0; inv H3.
    rewrite M.subtractKV_disj_invalid by auto.
    reflexivity.
Qed.

Inductive NonInteractingLabelSeq: LabelSeqT -> LabelSeqT -> Prop :=
| NILSNil: NonInteractingLabelSeq nil nil
| NILSCons:
    forall l1 l2 ll1 ll2,
      NonInteractingLabelSeq ll1 ll2 ->
      NonInteractingLabel l1 l2 ->
      NonInteractingLabelSeq (l1 :: ll1) (l2 :: ll2).

Lemma nonInteracting_to_labels:
  forall (m1 m2: Modules)
         (Hequiv1: ModEquiv type typeUT m1)
         (Hequiv2: ModEquiv type typeUT m2)
         (ll1 ll2: LabelSeqT) o1 o2,
    NonInteracting m1 m2 ->
    Behavior m1 o1 ll1 ->
    Behavior m2 o2 ll2 ->
    List.length ll1 = List.length ll2 ->
    NonInteractingLabelSeq ll1 ll2.
Proof.
  induction ll1; simpl; intros;
    [destruct ll2; [|inv H2]; constructor|].

  destruct ll2; [inv H2|].
  constructor.
  - inv H0; inv HMultistepBeh; inv H1; inv HMultistepBeh; eapply IHll1; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
  - inv H0; inv HMultistepBeh; inv H1; inv HMultistepBeh.
    clear -Hequiv1 Hequiv2 HStep HStep0 H.
    pose proof (step_defs_in HStep).
    pose proof (step_calls_in Hequiv1 HStep).
    pose proof (step_defs_in HStep0).
    pose proof (step_calls_in Hequiv2 HStep0).
    inv H; repeat split.
    + eapply step_hide; eauto.
    + eapply step_hide; eauto.
    + apply (M.DisjList_KeysSubset_Disj H4); auto.
    + apply (M.DisjList_KeysSubset_Disj H5); auto.
Qed.

Lemma composeLabels_modular:
  forall vp lsa lsb,
    equivalentLabelSeq (liftToMap1 vp) lsa lsb ->
    forall lsc lsd,
      CanCombineLabelSeq lsa lsc ->
      CanCombineLabelSeq lsb lsd ->
      NonInteractingLabelSeq lsa lsc ->
      NonInteractingLabelSeq lsb lsd ->
      equivalentLabelSeq (liftToMap1 vp) lsc lsd ->
      equivalentLabelSeq (liftToMap1 vp) (composeLabels lsa lsc) (composeLabels lsb lsd).
Proof.
  induction 1; simpl; intros; [constructor|].
  destruct lsc, lsd; [constructor|inv H5|inv H5|].
  inv H1; inv H2; inv H3; inv H4; inv H5;
    constructor; [|apply IHequivalentLabelSeq; auto].
  clear IHequivalentLabelSeq H0 H7 H8 H10 H11 H15.
  rewrite NonInteractingLabel_mergeLabel_hide by assumption.
  rewrite NonInteractingLabel_mergeLabel_hide by assumption.
  apply equivalentLabel_mergeLabel; auto.
Qed.

Definition Interacting (m1 m2: Modules)
           (vp: M.key -> sigT SignT -> option (sigT SignT)) :=
  (forall k, In k (getCalls m1) -> ~ In k (getDefs m2) ->
             forall v, vp k v = Some v) /\
  (forall k, In k (getDefs m1) -> ~ In k (getCalls m2) ->
             forall v, vp k v = Some v) /\
  (forall k, In k (getCalls m2) -> ~ In k (getDefs m1) ->
             forall v, vp k v = Some v) /\
  (forall k, In k (getDefs m2) -> ~ In k (getCalls m1) ->
             forall v, vp k v = Some v).

Lemma hide_mergeLabel_labelMap_domainSubset:
  forall vp la lb lc ld,
    M.Disj (defs la) (defs lc) ->
    M.Disj (calls la) (calls lc) ->
    calls lb = liftToMap1 vp (calls la) ->
    calls ld = liftToMap1 vp (calls lc) ->
    defs lb = liftToMap1 vp (defs la) ->
    defs ld = liftToMap1 vp (defs lc) ->
    M.DomainSubset (defs (hide (mergeLabel lb ld))) (defs (hide (mergeLabel la lc))) /\
    M.DomainSubset (calls (hide (mergeLabel lb ld))) (calls (hide (mergeLabel la lc))).
Proof.
  intros.
  destruct la as [anna dsa csa], lc as [annc dsc csc].
  destruct lb as [annb dsb csb], ld as [annd dsd csd].
  simpl in *; subst; split.

  - unfold M.DomainSubset; intros.
    specialize (H k).
    rewrite !M.F.P.F.not_find_in_iff in *.
    rewrite !M.F.P.F.in_find_iff in *.
    intro Hx; elim H1; clear H1.

    rewrite !M.subtractKV_find; rewrite !M.subtractKV_find in Hx.
    rewrite !M.find_union; rewrite !M.find_union in Hx.
    rewrite !liftToMap1_find.

    remember (M.find k dsa) as kda; destruct kda.
    + remember (M.find k csa) as kca; destruct kca.
      * destruct (signIsEq s s0); [|inv Hx]; subst.
        destruct (vp k s0); [destruct (signIsEq s s); [auto|elim n; auto]|].
        remember (M.find k dsc) as kdc; destruct kdc; auto.
        destruct H; discriminate.
      * remember (M.find k csc) as kcc; destruct kcc; [|inv Hx].
        destruct (signIsEq s s0); [|inv Hx]; subst.
        destruct (vp k s0); [destruct (signIsEq s s); [auto|elim n; auto]|].
        remember (M.find k dsc) as kdc; destruct kdc; auto.
        destruct H; discriminate.
    + remember (M.find k dsc) as kdc; destruct kdc; auto.
      remember (M.find k csa) as kca; destruct kca.
      * destruct (signIsEq s s0); [|inv Hx]; subst.
        destruct (vp k s0); auto.
        destruct (signIsEq s s); [auto|elim n; auto].
      * remember (M.find k csc) as kcc; destruct kcc; [|inv Hx].
        destruct (signIsEq s s0); [|inv Hx]; subst.
        destruct (vp k s0); auto.
        destruct (signIsEq s s); [auto|elim n; auto].

  - unfold M.DomainSubset; intros.
    specialize (H0 k).
    rewrite !M.F.P.F.not_find_in_iff in *.
    rewrite !M.F.P.F.in_find_iff in *.
    intro Hx; elim H1; clear H1.

    rewrite !M.subtractKV_find; rewrite !M.subtractKV_find in Hx.
    rewrite !M.find_union; rewrite !M.find_union in Hx.
    rewrite !liftToMap1_find.

    remember (M.find k csa) as kca; destruct kca.
    + remember (M.find k dsa) as kda; destruct kda.
      * destruct (signIsEq s s0); [|inv Hx]; subst.
        destruct (vp k s0); [destruct (signIsEq s s); [auto|elim n; auto]|].
        remember (M.find k csc) as kcc; destruct kcc; auto.
        destruct H0; discriminate.
      * remember (M.find k dsc) as kdc; destruct kdc; [|inv Hx].
        destruct (signIsEq s s0); [|inv Hx]; subst.
        destruct (vp k s0); [destruct (signIsEq s s); [auto|elim n; auto]|].
        remember (M.find k csc) as kcc; destruct kcc; auto.
        destruct H0; discriminate.
    + remember (M.find k csc) as kcc; destruct kcc; auto.
      remember (M.find k dsa) as kda; destruct kda.
      * destruct (signIsEq s s0); [|inv Hx]; subst.
        destruct (vp k s0); auto.
        destruct (signIsEq s s); [auto|elim n; auto].
      * remember (M.find k dsc) as kdc; destruct kdc; [|inv Hx].
        destruct (signIsEq s s0); [|inv Hx]; subst.
        destruct (vp k s0); auto.
        destruct (signIsEq s s); [auto|elim n; auto].
Qed.

Lemma KeysSubset_KeysDisj_filter:
  forall {A} (m: M.t A) sd dd,
    M.KeysSubset m sd -> M.KeysDisj m dd ->
    M.KeysSubset m (filter (fun d => negb (string_in d dd)) sd).
Proof.
  unfold M.KeysSubset, M.KeysDisj; intros.
  apply filter_In; split; auto.
  apply negb_true_iff.
  remember (string_in k dd) as kin; destruct kin; auto.
  exfalso; apply string_in_dec_in in Heqkin.
  elim (H0 k Heqkin); auto.
Qed.

Lemma DomainSubset_KeysDisj:
  forall {A} (m1 m2: M.t A) d, M.KeysDisj m1 d -> M.DomainSubset m2 m1 -> M.KeysDisj m2 d.
Proof.
  unfold M.KeysDisj, M.DomainSubset; intros.
  specialize (H k H1); rewrite !M.F.P.F.not_find_in_iff in *.
  specialize (H0 k); rewrite !M.F.P.F.in_find_iff in *.
  findeq; exfalso; apply H0; auto; intros; discriminate.
Qed.

Lemma DisjList_KeysSubset_KeysDisj:
  forall {A} (m: M.t A) d1 d2,
    DisjList d1 d2 -> M.KeysSubset m d1 -> M.KeysDisj m d2.
Proof.
  unfold DisjList, M.KeysSubset, M.KeysDisj; intros.
  specializeAll k; destruct H; auto.
Qed.

Lemma interacting_implies_wellHiddenModular:
  forall ma mb mc md vp,
    DisjList (getExtDefs (ma ++ mc)%kami) (getCalls (mb ++ md)%kami) ->
    DisjList (getExtCalls (ma ++ mc)%kami) (getDefs (mb ++ md)%kami) ->
    forall la lb lc ld,
      ValidLabel ma la -> ValidLabel mc lc ->
      CanCombineLabel la lc ->
      WellHiddenConcat ma mc la lc ->
      equivalentLabel (liftToMap1 vp) la lb ->
      equivalentLabel (liftToMap1 vp) lc ld ->
      WellHiddenConcat mb md lb ld.
Proof.
  unfold WellHiddenConcat, WellHiddenModular; intros.
  pose proof (hide_mergeLabel_labelMap_domainSubset vp la lb lc ld).

  destruct la as [anna dsa csa], lc as [annc dsc csc].
  destruct lb as [annb dsb csb], ld as [annd dsd csd].
  unfold wellHidden, hide in *; simpl in *; dest.
  inv H1; inv H2; inv H3; inv H5; inv H6; dest; simpl in *; clear H14 H15 H16.
  split.

  - apply DomainSubset_KeysDisj with
    (m1:= M.subtractKV signIsEq (M.union dsa dsc) (M.union csa csc)); [|apply H7; auto].
    apply DisjList_KeysSubset_KeysDisj with (d1:= getExtDefs (ma ++ mc)%kami); auto.
    apply KeysSubset_KeysDisj_filter; auto.
    apply M.KeysSubset_subtractKV.
    rewrite getDefs_app; apply M.KeysSubset_union_app; auto.

  - apply DomainSubset_KeysDisj with
    (m1:= M.subtractKV signIsEq (M.union csa csc) (M.union dsa dsc)); [|apply H7; auto].
    apply DisjList_KeysSubset_KeysDisj with (d1:= getExtCalls (ma ++ mc)%kami); auto.
    apply KeysSubset_KeysDisj_filter; auto.
    apply M.KeysSubset_subtractKV.
    apply M.KeysSubset_SubList with (d1:= getCalls ma ++ getCalls mc).
    + apply M.KeysSubset_union_app; auto.
    + apply getCalls_subList_1.
Qed.

Lemma interacting_implies_wellHiddenModularSeq:
  forall ma mb mc md vp,
    DisjList (getExtDefs (ma ++ mc)%kami) (getCalls (mb ++ md)%kami) ->
    DisjList (getExtCalls (ma ++ mc)%kami) (getDefs (mb ++ md)%kami) ->
    forall la lb lc ld,
      Forall (fun l => ValidLabel ma l) la ->
      Forall (fun l => ValidLabel mc l) lc ->
      CanCombineLabelSeq la lc ->
      WellHiddenConcatSeq ma mc la lc ->
      equivalentLabelSeq (liftToMap1 vp) la lb ->
      equivalentLabelSeq (liftToMap1 vp) lc ld ->
      WellHiddenConcatSeq mb md lb ld.
Proof.
  induction la; intros.
  - inv H5; inv H4; inv H6; constructor.
  - inv H1; inv H4; inv H5; inv H6; inv H2; inv H3; constructor.
    + eapply IHla; eauto.
    + eapply interacting_implies_wellHiddenModular; eauto.
Qed.

Lemma interacting_implies_id:
  forall ma mc vp,
    Interacting ma mc vp ->
    forall la lb lc ld,
      ValidLabel ma la -> ValidLabel mc lc ->
      CanCombineLabel la lc ->
      equivalentLabel (liftToMap1 vp) la lb ->
      equivalentLabel (liftToMap1 vp) lc ld ->
      WellHiddenConcat ma mc la lc ->
      equivalentLabel (liftToMap1 (@idElementwise _))
                      (hide (mergeLabel la lc)) (hide (mergeLabel lb ld)).
Proof.
  intros.
  assert (equivalentLabel (liftToMap1 vp) (mergeLabel la lc) (mergeLabel lb ld)).
  { clear -H2 H3 H4.
    destruct la as [anna dsa csa], lb as [annb dsb csb].
    destruct lc as [annc dsc csc], ld as [annd dsd csd].
    inv H2; unfold equivalentLabel in *; simpl in *; dest.
    repeat split; [| |destruct anna, annb, annc, annd; auto];
      clear H1 H5 H7; subst.
    { apply liftToMap1_union; auto. }
    { apply liftToMap1_union; auto. }
  }

  assert (M.KeysSubset (defs (mergeLabel la lc)) (getDefs (ConcatMod ma mc))).
  { inv H0; inv H1.
    destruct la as [anna dsa csa], lc as [annc dsc csc]; simpl in *.
    apply M.KeysSubset_union.
    { unfold M.KeysSubset in *; intros.
      apply getDefs_in_1; auto.
    }
    { unfold M.KeysSubset in *; intros.
      apply getDefs_in_2; auto.
    }
  }
  assert (M.KeysSubset (calls (mergeLabel la lc)) (getCalls (ConcatMod ma mc))).
  { inv H0; inv H1.
    destruct la as [anna dsa csa], lc as [annc dsc csc]; simpl in *.
    apply M.KeysSubset_union.
    { unfold M.KeysSubset in *; intros.
      apply getCalls_in_1; auto.
    }
    { unfold M.KeysSubset in *; intros.
      apply getCalls_in_2; auto.
    }
  }
  
  inv H5.
  remember (mergeLabel la lc) as lac; clear Heqlac.
  remember (mergeLabel lb ld) as lbd; clear Heqlbd.
  clear -H H6 H7 H8 H9 H10.

  inv H6; dest.
  repeat split; auto; clear H2; unfold id.

  - destruct lac as [anna dsa csa], lbd as [annb dsb csb]; simpl in *; subst.
    M.ext y.
    unfold M.KeysSubset, M.KeysDisj in *; inv H; dest.
    specializeAll y.
    rewrite M.F.P.F.not_find_in_iff in *.
    rewrite M.F.P.F.in_find_iff in *.
    repeat rewrite M.subtractKV_find.
    repeat rewrite liftToMap1_find.
    findeq.
    
    + destruct (vp y s); auto.
      destruct (signIsEq _ _); auto.
      elim n; auto.
    + specialize (H7 (opt_discr _)).
      specialize (H10 H7).
      inv H10.
    + specialize (H7 (opt_discr _)).
      destruct (in_dec string_dec y (getCalls (ConcatMod ma mc)));
        [specialize (H9 i); inv H9|].
      apply getDefs_in in H7; destruct H7.
      * rewrite H; auto.
        intro; elim n; apply getCalls_in_2; auto.
      * rewrite H2; auto.
        intro; elim n; apply getCalls_in_1; auto.

  - destruct lac as [anna dsa csa], lbd as [annb dsb csb]; simpl in *; subst.
    M.ext y.
    unfold M.KeysSubset, M.KeysDisj in *; inv H; dest.
    specializeAll y.
    rewrite M.F.P.F.not_find_in_iff in *.
    rewrite M.F.P.F.in_find_iff in *.
    repeat rewrite M.subtractKV_find.
    repeat rewrite liftToMap1_find.
    findeq.
    
    + destruct (vp y s0); auto.
      destruct (signIsEq _ _); auto.
      elim n; auto.
    + specialize (H7 (opt_discr _)).
      specialize (H10 H7).
      inv H10.
    + specialize (H8 (opt_discr _)).
      destruct (in_dec string_dec y (getDefs (ConcatMod ma mc)));
        [specialize (H10 i); inv H10|].
      apply getCalls_in in H8; destruct H8.
      * rewrite H0; auto.
        intro; elim n; apply getDefs_in_2; auto.
      * rewrite H1; auto.
        intro; elim n; apply getDefs_in_1; auto.
Qed.

Lemma interacting_seq_implies_id:
  forall ma mc vp,
    Interacting ma mc vp ->
    forall lsa lsb lsc lsd,
      Forall (fun l => ValidLabel ma l) lsa ->
      Forall (fun l => ValidLabel mc l) lsc ->
      CanCombineLabelSeq lsa lsc ->
      equivalentLabelSeq (liftToMap1 vp) lsa lsb ->
      equivalentLabelSeq (liftToMap1 vp) lsc lsd ->
      WellHiddenConcatSeq ma mc lsa lsc ->
      equivalentLabelSeq (liftToMap1 (@idElementwise _))
                         (composeLabels lsa lsc) (composeLabels lsb lsd).
Proof.
  induction lsa; simpl; intros; [inv H3; constructor|].
  inv H3; destruct lsc.
  - inv H5; constructor.
  - simpl; destruct lsd.
    + inv H4.
    + inv H0; inv H1; inv H5; dest.
      inv H4; constructor; auto.
      eapply interacting_implies_id; eauto.
Qed.

Lemma behavior_ValidLabel:
  forall m (Hequiv: ModEquiv type typeUT m) ll u,
    Behavior m u ll ->
    Forall (fun l => ValidLabel m l) ll.
Proof.
  intros.
  pose proof (behavior_defs_in H).
  pose proof (behavior_calls_in Hequiv H).
  clear H u.
  induction ll; simpl; intros; auto.
  inv H0; inv H1; constructor; auto.
  split; auto.
Qed.

Section Modularity.
  Variables (ma mb mc md: Modules).

  Hypotheses (HmaEquiv: ModEquiv type typeUT ma)
             (HmbEquiv: ModEquiv type typeUT mb)
             (HmcEquiv: ModEquiv type typeUT mc)
             (HmdEquiv: ModEquiv type typeUT md).

  Hypotheses (Hacregs: DisjList (namesOf (getRegInits ma))
                                (namesOf (getRegInits mc)))
             (Hbdregs: DisjList (namesOf (getRegInits mb))
                                (namesOf (getRegInits md)))
             (Hacval: ValidRegsModules type (ConcatMod ma mc))
             (Hbdval: ValidRegsModules type (ConcatMod mb md)).

  Hypotheses (Hacdefs: DisjList (getDefs ma) (getDefs mc))
             (Haccalls1: DisjList (getCalls ma) (getIntCalls mc))
             (Haccalls2: DisjList (getIntCalls ma) (getCalls mc))
             (Hbddefs: DisjList (getDefs mb) (getDefs md))
             (Hbdcalls1: DisjList (getCalls mb) (getIntCalls md))
             (Hbdcalls2: DisjList (getIntCalls mb) (getCalls md)).
  
  Section NonInteracting.
    Variable (vp: M.key -> sigT SignT -> option (sigT SignT)).

    Lemma traceRefines_modular_noninteracting:
      NonInteracting ma mc ->
      NonInteracting mb md ->
      (ma <<=[vp] mb) -> (mc <<=[vp] md) ->
      ((ma ++ mc)%kami <<=[vp] (mb ++ md)%kami).
    Proof.
      unfold traceRefines; intros.
      apply behavior_split in H3; auto.
      destruct H3 as [sa [lsa [sc [lsc ?]]]]; dest; subst.
      specialize (H1 _ _ H3).
      destruct H1 as [sb [lsb [? ?]]].
      specialize (H2 _ _ H4).
      destruct H2 as [sd [lsd [? ?]]].

      exists (M.union sb sd).
      exists (composeLabels lsb lsd).
      split; auto.
      - apply behavior_modular; auto.
        + eapply equivalentLabelSeq_CanCombineLabelSeq; eauto.
          apply vp_equivalentLabel_CanCombineLabel_proper.
        + apply nonInteracting_implies_wellHiddenModularSeq; auto.
          apply equivalentLabelSeq_length in H6.
          apply equivalentLabelSeq_length in H9.
          apply wellHiddenConcatSeq_length in H8.
          intuition.
      - apply composeLabels_modular; auto.
        + eapply equivalentLabelSeq_CanCombineLabelSeq; eauto.
          apply vp_equivalentLabel_CanCombineLabel_proper.
        + eapply nonInteracting_to_labels with (m1:= ma) (m2:= mc); eauto.
          eapply wellHiddenConcatSeq_length; eauto.
        + eapply nonInteracting_to_labels with (m1:= mb) (m2:= md); eauto.
          apply equivalentLabelSeq_length in H6.
          apply equivalentLabelSeq_length in H9.
          apply wellHiddenConcatSeq_length in H8.
          intuition.
    Qed.

  End NonInteracting.

  Section NonInteractingP.
    Variable (vp vq: M.key -> sigT SignT -> option (sigT SignT)).
    Hypothesis (Hdisjl: DisjLabelMap vp vq (getExtMeths ma) (getExtMeths mc)).
    
    Corollary traceRefines_modular_noninteracting_p:
      NonInteracting ma mc ->
      NonInteracting mb md ->
      (ma <<=[vp] mb) ->
      (mc <<=[vq] md) ->
      ((ma ++ mc)%kami <<=[compLabelMaps vp vq] (mb ++ md)%kami).
    Proof.
      intros; destruct Hdisjl.
      eapply traceRefines_labelMap_weakening in H1; eauto.
      eapply traceRefines_labelMap_weakening in H2; eauto.
      apply traceRefines_modular_noninteracting; auto.
    Qed.

  End NonInteractingP.

  Section Interacting.
    Variable (vp: M.key -> sigT SignT -> option (sigT SignT)).

    Hypotheses (Hdisj1: DisjList (getExtDefs (ma ++ mc)%kami) (getCalls (mb ++ md)%kami))
               (Hdisj2: DisjList (getExtCalls (ma ++ mc)%kami) (getDefs (mb ++ md)%kami)).

    Lemma traceRefines_modular_interacting:
      Interacting ma mc vp ->
      (ma <<=[vp] mb) -> (mc <<=[vp] md) ->
      ((ma ++ mc)%kami <<== (mb ++ md)%kami).
    Proof.
      unfold traceRefines; intros.
      apply behavior_split in H2; auto.
      destruct H2 as [sa [lsa [sc [lsc ?]]]]; dest; subst.
      specialize (H0 _ _ H2).
      destruct H0 as [sb [lsb [? ?]]].
      specialize (H1 _ _ H3).
      destruct H1 as [sd [lsd [? ?]]].

      exists (M.union sb sd).
      exists (composeLabels lsb lsd).
      split; auto.
      - apply behavior_modular; auto.
        + eapply equivalentLabelSeq_CanCombineLabelSeq; eauto.
          apply vp_equivalentLabel_CanCombineLabel_proper.
        + apply wellHidden_concat_modular_seq.
          eapply interacting_implies_wellHiddenModularSeq; try eassumption;
            eapply behavior_ValidLabel; eauto.
      - eapply interacting_seq_implies_id; eauto;
          eapply behavior_ValidLabel; eauto.
    Qed.

  End Interacting.

End Modularity.

Lemma flatten_traceRefines: forall m, m <<== Mod (getRegInits m) (getRules m)
                                        (getDefsBodies m).
Proof.
  intros.
  apply stepRefinement with (ruleMap := fun _ s => Some s) (theta := id); eauto; simpl in *.
  unfold id; simpl in *; intros.
  exists u; constructor; auto.
  apply flatten_preserves_step.
  rewrite idElementwiseId.
  unfold liftPLabel.
  destruct l; destruct annot; try destruct o0; auto.
Qed.

Lemma flatten_traceRefines_inv: forall m, Mod (getRegInits m) (getRules m)
                                              (getDefsBodies m) <<== m.
Proof.
  intros.
  apply stepRefinement with (ruleMap := fun _ s => Some s) (theta := id); eauto; simpl in *.
  unfold id; simpl in *; intros.
  exists u; constructor; auto.
  apply module_structure_indep_step
  with (m1:= Mod (getRegInits m) (getRules m) (getDefsBodies m)).
  - apply EquivList_refl.
  - apply EquivList_refl.
  - rewrite idElementwiseId.
    unfold liftPLabel.
    destruct l; destruct annot; try destruct o0; auto.
Qed.

Lemma deflatten_traceRefines:
  forall regs1 regs2 rules1 rules2 dms1 dms2,
    Mod (regs1 ++ regs2) (rules1 ++ rules2) (dms1 ++ dms2)
        <<== ConcatMod (Mod regs1 rules1 dms1) (Mod regs2 rules2 dms2).
Proof.
  unfold traceRefines; intros.
  exists s1, sig1; split.
  - inv H; constructor; simpl in *.
    remember (initRegs (regs1 ++ regs2)).
    induction HMultistepBeh.
    + subst; constructor.
      f_equal.
    + constructor; auto.
      clear -HStep.
      apply module_structure_indep_step with
      (m1:= Mod (regs1 ++ regs2) (rules1 ++ rules2) (dms1 ++ dms2)); auto;
        simpl; apply EquivList_refl.
  - clear; induction sig1; constructor; auto.
    rewrite idElementwiseId.
    constructor; destruct (annot a); auto.
Qed.

