Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct Lib.StringBound Lib.ilist Lib.Word Lib.FMap.
Require Import Syntax Semantics Wf Equiv Inline InlineFacts_1.

Require Import FunctionalExtensionality.

Section SubtractKVD.
  Context {A: Type}.
  Hypothesis deceqA : forall x y : A, sumbool (x = y) (x <> y).

  Definition subtractKVD (m1 m2 : M.t A) (dom: list string): M.t A :=
    M.fold (fun k2 v2 m1' =>
              match M.find k2 m1' with
                | None => m1'
                | Some v1 => if deceqA v1 v2 then
                               if in_dec string_dec k2 dom then
                                 M.remove k2 m1'
                               else m1'
                             else m1'
              end) m2 m1.

  Lemma transpose_neqkey_Equal_subtractKVD:
    forall dom,
      M.F.P.transpose_neqkey
        eq
        (fun k2 v2 m1' =>
           match M.find k2 m1' with
             | Some v1 =>
               if deceqA v1 v2
               then
                 if in_dec string_dec k2 dom
                 then M.remove k2 m1'
                 else m1'
               else m1'
             | None => m1'
           end).
  Proof.
    simpl; unfold M.F.P.transpose_neqkey; intros.

    repeat
      match goal with
        | [ |- context [in_dec string_dec ?k ?l] ] =>
          destruct (in_dec string_dec k l)
        | [ |- context [M.find ?k ?m] ] =>
          let okv := fresh "okv" in
          remember (M.find k m) as okv; destruct okv
        | [H: _ = M.find _ _ |- _] => rewrite <-H
        | [ |- context [deceqA ?a1 ?a2] ] =>
          destruct (deceqA a1 a2); [subst|]
        | [ |- context [M.remove ?k ?m] ] =>
          try rewrite M.remove_find_None by auto
      end;
      repeat
        match goal with
          | [H1: ?v1 = M.find ?k ?m, H2: ?v2 = M.find ?k ?m |- _] =>
            rewrite <-H1 in H2
          | [H: Some ?v1 = Some ?v2 |- _] => inv H
          | [H: Some _ = None |- _] => discriminate
          | [H: ?a = ?a -> False |- _] => elim H; auto
          | [H: context [M.find ?k (M.remove ?k _)] |- _] =>
            rewrite M.F.P.F.remove_eq_o in H; auto
          | [H: context [M.find ?k1 (M.remove ?k2 _)] |- _] =>
            try (rewrite M.F.P.F.remove_neq_o in H; auto)
        end; try reflexivity; try discriminate;
      meq.
  Qed.

  Lemma subtractKVD_nil:
    forall (m1 m2: M.t A), subtractKVD m1 m2 nil = m1.
  Proof.
    intros; unfold subtractKVD; rewrite M.fold_1.
    induction (M.elements m2); auto.
    simpl in *.
    destruct (M.find (fst a) m1); auto.
    destruct (deceqA a0 (snd a)); auto.
  Qed.

  Lemma subtractKVD_cons_1:
    forall dom d (m1 m2: M.t A),
      M.find d m1 = None \/ M.find d m2 = None \/ M.find d m1 <> M.find d m2 ->
      subtractKVD m1 m2 (d :: dom) = subtractKVD m1 m2 dom.
  Proof.
    admit.
  Qed.

  Lemma subtractKVD_cons_2:
    forall dom d (m1 m2: M.t A),
      M.find d m1 <> None ->
      M.find d m1 = M.find d m2 ->
      subtractKVD m1 m2 (d :: dom) = subtractKVD (M.remove d m1) (M.remove d m2) dom.
  Proof.
    admit.
  Qed.
    
  Lemma subtractKVD_empty_1:
    forall dom (m: M.t A), subtractKVD (M.empty _) m dom = M.empty _.
  Proof.
    intros; unfold subtractKVD; rewrite M.fold_1.
    induction (M.elements m); auto.
  Qed.

  Lemma subtractKVD_empty_2:
    forall dom (m: M.t A), subtractKVD m (M.empty _) dom = m.
  Proof.
    intros; unfold subtractKVD; rewrite M.fold_1.
    induction (M.elements m); auto.
  Qed.

  Lemma subtractKV_subtractKVD_1:
    forall dom (m1 m2: M.t A),
      M.KeysSubset m1 dom ->
      M.subtractKV deceqA m1 m2 = subtractKVD m1 m2 dom.
  Proof.
    intros; unfold M.subtractKV, subtractKVD.
    do 2 rewrite M.fold_1.
    generalize dependent m1.
    induction (M.elements m2); intros; [reflexivity|].
    unfold M.subtractKVf; simpl.
    destruct a as [ak av]; simpl in *.
    remember (M.find ak m1) as ov1; destruct ov1.
    - destruct (deceqA a av); [subst|].
      + destruct (in_dec string_dec ak dom).
        * apply IHl.
          unfold M.KeysSubset; intros.
          apply M.F.P.F.remove_in_iff in H0; dest.
          apply H; auto.
        * exfalso; elim n.
          apply H, M.F.P.F.in_find_iff.
          rewrite <-Heqov1; discriminate.
      + apply IHl; auto.
    - apply IHl; auto.
  Qed.

  Lemma subtractKV_subtractKVD_2:
    forall (m1 m2: M.t A) dom,
      M.KeysSubset m2 dom ->
      M.subtractKV deceqA m1 m2 = subtractKVD m1 m2 dom.
  Proof.
    intros; unfold M.subtractKV, subtractKVD.
    do 2 rewrite M.fold_1.
    apply M.KeysSubset_elements in H.
    
    generalize dependent m1.
    induction (M.elements m2); intros; [reflexivity|].
    unfold M.subtractKVf; simpl.
    destruct a as [ak av]; simpl in *.
    assert (SubList (map (fun e => fst e) l) dom)
      by (apply SubList_cons_inv in H; intuition).
    specialize (IHl H0).

    remember (M.find ak m1) as ov1; destruct ov1.
    - destruct (deceqA a av); [subst|].
      + destruct (in_dec string_dec ak dom).
        * apply IHl.
        * exfalso; elim n; apply H; auto.
      + apply IHl; auto.
    - apply IHl; auto.
  Qed.

End SubtractKVD.

Hint Immediate transpose_neqkey_Equal_subtractKVD.

Section HideExts.
  Definition hideMeth (l: LabelT) (dmn: string): LabelT :=
    match M.find dmn (defs l), M.find dmn (calls l) with
      | Some v1, Some v2 =>
        match signIsEq v1 v2 with
          | left _ => {| annot := annot l;
                         defs := M.remove dmn (defs l);
                         calls := M.remove dmn (calls l) |}
          | _ => l
        end
      | _, _ => l
    end.

  Lemma hideMeth_preserves_hide:
    forall (l: LabelT ) dm,
      hide (hideMeth l dm) = hide l.
  Proof.
    intros; destruct l as [rm dms cms].
    unfold hide, hideMeth; simpl.
    remember (M.find dm dms) as odm; destruct odm; [|reflexivity].
    remember (M.find dm cms) as ocm; destruct ocm; [|reflexivity].
    destruct (signIsEq s s0); [|reflexivity].
    subst; f_equal; auto; apply M.subtractKV_remove; rewrite <-Heqodm, <-Heqocm; auto.
  Qed.

  Definition hideMeths (l: LabelT) (dms: list string): LabelT :=
    {| annot := annot l;
       defs := subtractKVD signIsEq (defs l) (calls l) dms;
       calls := subtractKVD signIsEq (calls l) (defs l) dms |}.

  Lemma hideMeths_nil:
    forall l, hideMeths l nil = l.
  Proof.
    intros; destruct l as [ann ds cs].
    unfold hideMeths; f_equal; simpl; apply subtractKVD_nil.
  Qed.

  Lemma hideMeths_hideMeth:
    forall l d dom, hideMeths l (d :: dom) =
                    hideMeths (hideMeth l d) dom.
  Proof.
    destruct l as [ann ds cs].
    intros; unfold hideMeths; f_equal; simpl.

    - unfold hideMeth; simpl.
      destruct (M.find d ds);
        try destruct (M.find d cs);
        try destruct (signIsEq _ _); reflexivity.

    - unfold hideMeth; simpl.
      remember (M.find d ds) as odv; destruct odv; simpl; [|apply subtractKVD_cons_1; auto].
      remember (M.find d cs) as ocv; destruct ocv; simpl; [|apply subtractKVD_cons_1; auto].
      destruct (signIsEq s s0); simpl.
      + subst; apply subtractKVD_cons_2; auto.
        * rewrite <-Heqodv; discriminate.
        * rewrite <-Heqocv, <-Heqodv; reflexivity.
      + apply subtractKVD_cons_1.
        right; right.
        rewrite <-Heqocv, <-Heqodv.
        intro Hx; elim n; inv Hx; auto.

    - unfold hideMeth; simpl.
      remember (M.find d ds) as odv; destruct odv; simpl; [|apply subtractKVD_cons_1; auto].
      remember (M.find d cs) as ocv; destruct ocv; simpl; [|apply subtractKVD_cons_1; auto].
      destruct (signIsEq s s0); simpl.
      + subst; apply subtractKVD_cons_2; auto.
        * rewrite <-Heqocv; discriminate.
        * rewrite <-Heqocv, <-Heqodv; reflexivity.
      + apply subtractKVD_cons_1.
        right; right.
        rewrite <-Heqocv, <-Heqodv.
        intro Hx; elim n; inv Hx; auto.
  Qed.

End HideExts.

Section SubstepFacts.
  Variable m: Modules.
  Hypotheses (Hwf: WfModules type m)
             (Hequiv: ModEquiv typeUT type m)
             (Hdefs: NoDup (namesOf (getDefsBodies m))).
  Variable dm: DefMethT.
  Hypothesis (Hdm: noCallDm dm dm = true).
  
  Lemma inlineDmToMod_correct_Substep:
    forall or u1 u2 cs1 cs2 argV retV ul2,
      Substep m or u2 ul2 cs2 ->
      SemAction or (projT2 (attrType dm) type argV) u1 cs1 retV ->
      M.Disj u1 u2 -> M.Disj cs1 cs2 ->
      Some (existT _ (projT1 (attrType dm)) (argV, retV)) = M.find dm cs2 ->
      Substep (Mod (getRegInits m) (inlineDmToRules (getRules m) dm)
                   (inlineDmToDms (getDefsBodies m) dm))
              or (M.union u1 u2) ul2 (M.union cs1 (M.remove dm cs2)).
  Proof.
    induction 1; intros; simpl in *; try (inv H2).

    - eapply SingleRule with (a:= attrType (inlineDmToRule (k :: a)%struct dm)); eauto.
      + apply in_map with (f:= fun r => inlineDmToRule r dm) in HInRules; auto.
      + simpl; eapply inlineDm_correct_SemAction; eauto.
        inv Hwf; eapply wfRules_rule; eauto.

    - apply SingleMeth with (f:= inlineDmToDm f dm); auto.
      + apply in_map with (f:= fun d => inlineDmToDm d dm) in HIn; auto.
      + simpl; eapply inlineDm_correct_SemAction; eauto.
        inv Hwf; eapply wfDms_dms; eauto.
  Qed.  

  Lemma inlineDmToMod_Substep_intact:
    forall or u ul cs (dmn: string),
      Substep m or u ul cs ->
      None = M.find dm cs ->
      dmn = dm ->
      Substep (Mod (getRegInits m) (inlineDmToRules (getRules m) dm)
                   (inlineDmToDms (getDefsBodies m) dm))
              or u ul cs.
  Proof.
    induction 1; intros; simpl in *; try (constructor; auto; fail).

    - apply SingleRule with (a:= attrType (inlineDmToRule (k :: a)%struct dm)); auto.
      + apply in_map with (f:= fun r => inlineDmToRule r dm) in HInRules; auto.
      + simpl; destruct dm; apply inlineDm_SemAction_intact; auto.

    - apply SingleMeth with (f:= inlineDmToDm f dm); auto.
      + apply in_map with (f:= fun d => inlineDmToDm d dm) in HIn; auto.
      + simpl; destruct dm; apply inlineDm_SemAction_intact; auto.
  Qed.

End SubstepFacts.

Lemma hideMeths_hide:
  forall dmsAll (l: LabelT),
    M.KeysSubset (defs l) dmsAll ->
    hideMeths l dmsAll = hide l.
Proof.
  intros.
  unfold hide, hideMeths; f_equal.
  - rewrite <-subtractKV_subtractKVD_1; auto.
  - rewrite <-subtractKV_subtractKVD_2; auto.
Qed.

Lemma inlineDmToMod_getDmsMod:
  forall m a,
    getDefs (fst (inlineDmToMod m a)) = getDefs m.
Proof.
  intros; unfold inlineDmToMod.
  destruct (wfModules _); [|auto].
  destruct (getAttribute _ _); [|auto].
  destruct (noCallDm _ _); [|auto].
  simpl.

  clear; induction m; unfold getDefs in *; simpl in *.
  - clear; induction dms; [auto|].
    simpl; f_equal; auto.
  - apply inlineDmToDms_names.
Qed.

Lemma inlineDm_calls:
  forall {retK} dm dms,
    In dm dms ->
    forall (a: ActionT typeUT retK),
      SubList (getCallsA (inlineDm a dm))
              (getCallsA a ++ getCallsM dms).
Proof.
  induction a; simpl; intros; eauto.

  - unfold getBody.
    destruct (string_dec _ _).
    + subst; destruct (SignatureT_dec _ _).
      * subst; simpl.
        rewrite getCallsA_appendAction.
        apply SubList_app_3.
        { apply SubList_cons_right, SubList_app_2.
          clear H0; induction dms; [inv H|].
          simpl; inv H.
          { apply SubList_app_1, SubList_refl. }
          { apply SubList_app_2; auto. }
        }          
        { apply SubList_cons_right; auto. }
      * simpl; apply SubList_cons; auto.
        apply SubList_cons_right; eauto.
    + simpl; apply SubList_cons; auto.
      apply SubList_cons_right; eauto.
  - apply SubList_app_3.
    + apply SubList_app_comm.
      rewrite app_assoc.
      apply SubList_app_1, SubList_app_comm; eauto.
    + apply SubList_app_3.
      * rewrite <-app_assoc.
        apply SubList_app_comm, SubList_app_1.
        apply SubList_app_comm.
        rewrite app_assoc.
        apply SubList_app_1, SubList_app_comm; eauto.
      * rewrite <-app_assoc.
        apply SubList_app_comm, SubList_app_1.
        rewrite <-app_assoc.
        apply SubList_app_2; eauto.
  - apply SubList_nil.
Qed.

Lemma inlineDmToRule_calls:
  forall rules dms dm,
    In dm dms ->
    SubList (getCallsR (inlineDmToRules rules dm))
            (getCallsR rules ++ getCallsM dms).
Proof.
  induction rules; simpl; intros; [apply SubList_nil|].
  apply SubList_app_3.
  - apply SubList_app_comm.
    rewrite app_assoc.
    apply SubList_app_1, SubList_app_comm.
    eapply inlineDm_calls; eauto.
  - rewrite <-app_assoc.
    apply SubList_app_2.
    eapply IHrules; eauto.
Qed.

Lemma inlineDmToDms_calls':
  forall dm dms2 dms1,
    In dm dms2 ->
    (forall d : DefMethT,
       In d dms1 ->
       SubList (getCallsA (projT2 (attrType (inlineDmToDm d dm))
                                  typeUT tt))
               (getCallsA (projT2 (attrType d) typeUT tt)
                          ++ getCallsM dms2)) ->
    SubList (getCallsM (inlineDmToDms dms1 dm))
            (getCallsM dms1 ++ getCallsM dms2).
Proof.
  induction dms1; simpl; intros; [apply SubList_nil|].
  apply SubList_app_3.
  - rewrite <-app_assoc.
    apply SubList_app_comm.
    rewrite <-app_assoc.
    apply SubList_app_2, SubList_app_comm; auto.
  - rewrite <-app_assoc.
    apply SubList_app_2.
    simpl in *; auto.
Qed.

Lemma inlineDmToDms_calls:
  forall dms dm,
    In dm dms ->
    SubList (getCallsM (inlineDmToDms dms dm))
            (getCallsM dms).
Proof.
  intros.
  assert (SubList (getCallsM (inlineDmToDms dms dm))
                  (getCallsM dms ++ getCallsM dms)).
  { intros; apply inlineDmToDms_calls'; auto; intros.
    simpl; apply inlineDm_calls; auto.
  }
  apply SubList_app_idempotent; auto.
Qed.

Lemma inlineDmToMod_calls:
  forall m a,
    SubList (Syntax.getCalls (fst (inlineDmToMod m a)))
            (Syntax.getCalls m).
Proof.
  intros; unfold inlineDmToMod.
  destruct (wfModules _); [|apply SubList_refl].
  remember (getAttribute _ _) as odm; destruct odm;
  [|apply SubList_refl].
  destruct (noCallDm _ _); [|apply SubList_refl].
  unfold Syntax.getCalls; simpl.
  apply SubList_app_3.
  - eapply inlineDmToRule_calls; eauto.
    eapply getAttribute_Some_body; eauto.
  - apply SubList_app_2.
    eapply inlineDmToDms_calls; eauto.
    eapply getAttribute_Some_body; eauto.
Qed.

Lemma inlineDmToMod_wellHidden:
  forall m (l: LabelT) a,
    wellHidden m l ->
    wellHidden (fst (inlineDmToMod m a)) l.
Proof.
  unfold wellHidden; intros.
  rewrite inlineDmToMod_getDmsMod.
  dest; split; auto.
  apply M.KeysDisj_SubList with (d1:= Syntax.getCalls m); auto.
  apply inlineDmToMod_calls.
Qed.

Lemma inlineDms_wellHidden:
  forall m (l: LabelT),
    wellHidden m l ->
    wellHidden (fst (inlineDms m)) l.
Proof.
  intros; unfold inlineDms.
  remember (namesOf (getDefsBodies m)) as dms; clear Heqdms.
  generalize dependent m; induction dms; intros; [assumption|].
  simpl; remember (inlineDmToMod m a) as imb; destruct imb; simpl.
  destruct b.
  - apply IHdms; auto.
    replace m0 with (fst (inlineDmToMod m a)) by (rewrite <-Heqimb; reflexivity).
    apply inlineDmToMod_wellHidden; auto.
  - unfold inlineDmToMod in Heqimb.
    destruct (wfModules _); [|inv Heqimb; assumption].
    destruct (getAttribute _ _); [|inv Heqimb; assumption].
    destruct (noCallDm _ _); [|inv Heqimb; assumption].
    inv Heqimb.
Qed.

Lemma hideMeths_Substeps_hide:
  forall m or nr l,
    SubstepsInd m or nr l ->
    hideMeths l (namesOf (getDefsBodies m)) = hide l.
Proof.
  intros; apply hideMeths_hide.

  (* NOTE: better to extract a lemma *)
  induction H; [apply M.KeysSubset_empty|].
  subst; destruct l as [ann ds cs].
  inv H1; dest; simpl in *.
  destruct ann; destruct sul as [|[|]]; auto; destruct a as [an ab].
  - apply M.KeysSubset_union; auto.
    apply M.KeysSubset_add.
    + apply M.KeysSubset_empty.
    + pose proof (staticDynDefsSubstep H0); auto.
  - apply M.KeysSubset_union; auto.
    apply M.KeysSubset_add.
    + apply M.KeysSubset_empty.
    + pose proof (staticDynDefsSubstep H0); auto.
Qed.

Lemma inlineDm_ActionEquiv:
  forall type1 type2 {retT} G
         (aU: ActionT type1 retT) (aT: ActionT type2 retT) (dm: DefMethT),
    (forall (argV1: ft1 type1 (SyntaxKind _))
            (argV2: ft2 type2 (SyntaxKind _)),
       ActionEquiv (vars (argV1, argV2) :: nil)
                   (projT2 (attrType dm) type1 argV1) (projT2 (attrType dm) type2 argV2)) ->
    ActionEquiv G aU aT ->
    ActionEquiv G (inlineDm aU dm) (inlineDm aT dm).
Proof.
  induction 2; intros; try (constructor; auto).

  simpl; remember (getBody n dm s) as dmb; destruct dmb; [|constructor; auto].

  unfold getBody in Heqdmb.
  destruct (string_dec n dm); [subst|discriminate].
  destruct (SignatureT_dec _ _); [subst|discriminate].
  inv Heqdmb; simpl.

  constructor; intros.
  apply actionEquiv_appendAction.
  + eapply ActionEquiv_ctxt; eauto.
    unfold SubList; intros; inv H2; intuition.
  + intros.
    eapply ActionEquiv_ctxt; eauto.
    unfold SubList; intros; inv H2; intuition.
Qed.

Lemma inlineDmToRules_RulesEquiv:
  forall {type1 type2} rules (dm: DefMethT),
    (forall (argV1: ft1 type1 (SyntaxKind _))
            (argV2: ft2 type2 (SyntaxKind _)),
       ActionEquiv (vars (argV1, argV2) :: nil)
                   (projT2 (attrType dm) type1 argV1) (projT2 (attrType dm) type2 argV2)) ->
    RulesEquiv type1 type2 rules ->
    RulesEquiv type1 type2 (inlineDmToRules rules dm).
Proof.
  induction 2; intros; simpl in *; constructor; auto.
  intros; simpl; apply inlineDm_ActionEquiv; auto.
Qed.

Lemma inlineDmToDms_MethsEquiv:
  forall {type1 type2} dms (dm: DefMethT),
    (forall (argV1: ft1 type1 (SyntaxKind _))
            (argV2: ft2 type2 (SyntaxKind _)),
       ActionEquiv (vars (argV1, argV2) :: nil)
                   (projT2 (attrType dm) type1 argV1) (projT2 (attrType dm) type2 argV2)) ->
    MethsEquiv type1 type2 dms ->
    MethsEquiv type1 type2 (inlineDmToDms dms dm).
Proof.
  induction 2; intros; simpl in *; constructor; auto.
  intros; simpl in *; apply inlineDm_ActionEquiv; auto.
Qed.

Lemma inlineDmToMod_ModEquiv:
  forall m dm,
    ModEquiv typeUT type m ->
    ModEquiv typeUT type (fst (inlineDmToMod m dm)).
Proof.
  intros.
  unfold inlineDmToMod.
  destruct (wfModules _); [|auto].
  remember (getAttribute _ _) as oattr; destruct oattr; [|auto].
  simpl in Heqoattr.
  apply getAttribute_Some_body in Heqoattr.
  destruct (noCallDm _ _); [|auto].
  simpl; inv H.
  pose proof (MethsEquiv_in _ H1 Heqoattr).
  constructor.
  - apply inlineDmToRules_RulesEquiv; auto.
  - apply inlineDmToDms_MethsEquiv; auto.
Qed.

Lemma inlineDmToMod_dms_names:
  forall m a,
    namesOf (getDefsBodies (fst (inlineDmToMod m a))) =
    namesOf (getDefsBodies m).
Proof.
  destruct m; intros; simpl in *.
  - unfold inlineDmToMod.
    destruct (wfModules _); try destruct (getAttribute _ _); try destruct (noCallDm _ _);
    try (reflexivity; fail).
    simpl; clear.

    induction dms; auto.
    simpl; f_equal; auto.

  - unfold inlineDmToMod.
    destruct (wfModules _); try destruct (getAttribute _ _); try destruct (noCallDm _ _);
    try reflexivity.
    apply inlineDmToDms_names.
Qed.

Lemma inlineDmToMod_correct_Substeps:
  forall m (Hequiv: ModEquiv typeUT type m)
         or nr l dm,
    NoDup (namesOf (getDefsBodies m)) ->
    SubstepsInd m or nr l ->
    M.find dm (calls l) = None \/ M.find dm (defs l) = M.find dm (calls l) ->
    snd (inlineDmToMod m dm) = true ->
    SubstepsInd (fst (inlineDmToMod m dm)) or nr (hideMeth l dm).
Proof.
  induction 3; intros; [constructor|].

  subst; unfold inlineDmToMod in *.
  remember (wfModules _) as owf; destruct owf; [|inv H6].
  remember (getAttribute _ _) as odm; destruct odm; [|inv H6].
  remember (noCallDm _ _) as onc; destruct onc; [|inv H6].
  destruct l as [ann ds cs]; simpl in *.

  pose proof (getAttribute_Some_name _ _ Heqodm); subst.
  apply getAttribute_Some_body in Heqodm.
  inv H2; dest; simpl in *.

  unfold hideMeth in *; simpl in *.
  remember (M.find a (M.union scs cs)) as ocmv; destruct ocmv.

  - destruct H5; [discriminate|].
    rewrite H5 in *.
    rewrite M.find_union in Heqocmv.
    remember (M.find a scs) as oscmv; destruct oscmv.
    + inv Heqocmv.
      admit. (* TODO *)

    + rewrite <-Heqocmv in IHSubstepsInd.
      match goal with
        | [H: M.find ?a (M.union ?lm _) = Some _ |- _] =>
          rewrite M.find_union in H;
            remember (M.find a lm) as odmv; destruct odmv
      end.

      * admit. (* TODO *)

      * rewrite H5 in IHSubstepsInd.
        destruct (signIsEq s s); [clear e|elim n; auto].

        eapply SubstepsCons; eauto.
        { eapply inlineDmToMod_Substep_intact; eauto. }
        { repeat split; simpl; auto.
          { apply M.Disj_comm; apply M.Disj_remove_1; apply M.Disj_comm; auto. }
          { destruct ann; destruct sul as [|[|]]; auto;
            intro Hx; elim H4; eapply M.F.P.F.remove_in_iff; eauto.
          }
        }
        { unfold mergeLabel, getSLabel, getLabel; f_equal.
          { destruct sul as [|[|]]; destruct ann; try destruct o; auto; destruct a0;
            meq; try (rewrite <-Heqodmv; auto; fail); try(inv Heqv; auto; fail).
            (* TODO: strengthen meq to deal with following "try"s *)
          }
          { meq. }
        }

  - rewrite M.find_union in Heqocmv.
    remember (M.find a scs) as oscmv; destruct oscmv; [inv Heqocmv|].
    rewrite <-Heqocmv in IHSubstepsInd.
    match goal with
      | [ |- SubstepsInd _ _ _ ?ll] =>
        match ll with
          | (match ?c with Some _ => ?l | None => ?l end) =>
            replace ll with l by (destruct c; reflexivity)
        end
    end.

    eapply SubstepsCons; eauto.
    + eapply inlineDmToMod_Substep_intact; eauto.
    + destruct (M.find a ds); repeat split; simpl; auto.
    + destruct (M.find a ds); reflexivity.
Qed.

Lemma wellHidden_find:
  forall m a (l: LabelT),
    In a (namesOf (getDefsBodies m)) ->
    wellHidden m (hide l) ->
    M.find a (calls l) = None \/ M.find a (defs l) = M.find a (calls l).
Proof.
  unfold wellHidden, hide; intros.
  destruct l as [rm dm cm]; simpl in *; dest.

  specialize (H1 _ H).
  remember (M.find a cm) as ocm; destruct ocm; auto.
  right; eapply M.subtractKV_not_In_find; eauto.
Qed.

Lemma inlineDms'_correct_Substeps:
  forall cdms m (Hequiv: ModEquiv typeUT type m)
         (Hdms: NoDup (namesOf (getDefsBodies m)))
         (Hcdms: SubList cdms (namesOf (getDefsBodies m)))
         or nr l,
    SubstepsInd m or nr l ->
    wellHidden m (hide l) ->
    snd (inlineDms' m cdms) = true ->
    SubstepsInd (fst (inlineDms' m cdms)) or nr (hideMeths l cdms).
Proof.
  induction cdms; [intros; simpl; rewrite hideMeths_nil; auto|].
  
  intros; simpl.
  rewrite hideMeths_hideMeth.
  apply SubList_cons_inv in Hcdms; dest.
  remember (inlineDmToMod m a) as imb; destruct imb as [im ib]; simpl.
  destruct ib.

  - assert (im = fst (inlineDmToMod m a)) by (rewrite <-Heqimb; reflexivity); subst.
    apply IHcdms; auto.
    + apply inlineDmToMod_ModEquiv; auto.
    + rewrite inlineDmToMod_dms_names; auto.
    + rewrite inlineDmToMod_dms_names; auto.
    + apply inlineDmToMod_correct_Substeps; auto.
      * eapply wellHidden_find; eauto.
      * simpl in H0; destruct (inlineDmToMod m a); simpl in *.
        destruct b; [auto|inv Heqimb].
    + apply inlineDmToMod_wellHidden.
      rewrite hideMeth_preserves_hide; auto.
    + simpl in H1; destruct (inlineDmToMod m a); simpl in *.
      destruct b; [auto|inv Heqimb].

  - simpl in *; unfold inlineDmToMod in *.
    destruct (wfModules m); [|discriminate].
    destruct (getAttribute _ _); [|discriminate].
    destruct (noCallDm _ _); [|discriminate].
    destruct m; [|discriminate].
    inv Heqimb.
Qed.

Lemma inlineDms_correct_SubstepsInd:
  forall m (Hequiv: ModEquiv typeUT type m)
         (Hdms: NoDup (namesOf (getDefsBodies m))) or u l,
    SubstepsInd m or u l ->
    snd (inlineDms m) = true ->
    wellHidden m (hide l) ->
    SubstepsInd (fst (inlineDms m)) or u (hide l).
Proof.
  intros.
  erewrite <-hideMeths_Substeps_hide; eauto.
  apply inlineDms'_correct_Substeps; auto.
  apply SubList_refl.
Qed.

Lemma hide_idempotent:
  forall (l: LabelT), hide l = hide (hide l).
Proof.
  intros; destruct l as [ann ds cs].
  unfold hide; simpl; f_equal;
  apply M.subtractKV_idempotent.
Qed.

Lemma inlineDms_correct:
  forall m (Hequiv: ModEquiv typeUT type m)
         (Hdms: NoDup (namesOf (getDefsBodies m)))
         (Hin: snd (inlineDms m) = true)
         or nr l,
    StepInd m or nr l ->
    StepInd (fst (inlineDms m)) or nr l.
Proof.
  intros; inv H.
  rewrite hide_idempotent.
  constructor.
  - apply inlineDms_correct_SubstepsInd; auto.
  - rewrite <-hide_idempotent.
    apply inlineDms_wellHidden; auto.
Qed.

(* Instead of filter, use below *)
Lemma step_dms_hidden:
  forall m or nr l,
    Step m or nr l ->
    M.KeysDisj (defs l) (Syntax.getCalls m).
Proof.
  intros; inv H.
  unfold wellHidden in HWellHidden.
  destruct (hide _); simpl in *; intuition.
Qed.

Theorem inline_correct:
  forall m (Hequiv: ModEquiv typeUT type m)
         (Hdms: NoDup (namesOf (getDefsBodies m)))
         (Hin: snd (inline m) = true)
         or nr l,
    Step m or nr l ->
    Step (fst (inline m)) or nr l.
Proof.
  intros; unfold inline.
  apply step_consistent; apply step_consistent in H.
  apply inlineDms_correct; auto.
Qed.

