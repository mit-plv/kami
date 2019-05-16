Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct.
Require Import Lib.ilist Lib.Word Lib.FMap Lib.StringEq.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts.
Require Import Kami.Wf Kami.Inline.
Require Import Kami.RefinementFacts.

Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Asymmetric Patterns.

Lemma inlineDm_SemAction_intact:
  forall {retK} or a nr calls (retV: type retK),
    SemAction or a nr calls retV ->
    forall dmn dmb,
      None = M.find dmn calls ->
      SemAction or (inlineDm a (dmn :: dmb)%struct) nr calls retV.
Proof.
  induction 1; intros.

  - simpl.
    remember (getBody meth (dmn :: dmb)%struct s) as omb;
      destruct omb.
    + exfalso; subst.
      unfold getBody in Heqomb.
      remember (string_eq _ _) as seq; destruct seq; [|discriminate].
      apply string_eq_dec_eq in Heqseq.
      subst; rewrite M.find_add_1 in H0; inv H0.
    + subst.
      unfold getBody in Heqomb.
      remember (string_eq _ _) as seq; destruct seq.
      * apply string_eq_dec_eq in Heqseq.
        subst; rewrite M.find_add_1 in H0; inv H0.
      * apply string_eq_dec_neq in Heqseq.
        rewrite M.find_add_2 in H0 by intuition auto.
        econstructor; eauto.

  - simpl; constructor; auto.
  - simpl; econstructor; eauto.
  - simpl; econstructor; eauto.
  - simpl; econstructor; eauto.

  - subst; eapply SemIfElseTrue; eauto.
    + apply IHSemAction1.
      rewrite M.find_union in H1.
      destruct (M.find dmn calls1); auto.
    + apply IHSemAction2.
      rewrite M.find_union in H1.
      destruct (M.find dmn calls1); auto; inv H1.

  - subst; eapply SemIfElseFalse; eauto.
    + apply IHSemAction1.
      rewrite M.find_union in H1.
      destruct (M.find dmn calls1); auto.
    + apply IHSemAction2.
      rewrite M.find_union in H1.
      destruct (M.find dmn calls1); auto; inv H1.

  - simpl; constructor; auto.
  - simpl; constructor; auto.
  - simpl; constructor; auto.
Qed.

Lemma inlineDm_correct_SemAction:
  forall (meth: DefMethT) or u1 cm1 argV retV1,
    SemAction or (projT2 (attrType meth) type argV) u1 cm1 retV1 ->
    forall {retK2} a
           u2 cm2 (retV2: type retK2),
      M.Disj u1 u2 -> M.Disj cm1 cm2 ->
      Some (existT _ (projT1 (attrType meth))
                   (argV, retV1)) =
      M.find (attrName meth) cm2 ->
      SemAction or a u2 cm2 retV2 ->
      SemAction or (inlineDm a meth) (M.union u1 u2)
                (M.union cm1 (M.remove (attrName meth) cm2))
                retV2.
Proof.
  induction a; intros; simpl in *.

  - inv H4; destruct_existT.
    remember (getBody meth0 meth s) as ob; destruct ob.
    + unfold getBody in Heqob.
      remember (string_eq _ _) as seq; destruct seq; [|inv Heqob].
      apply string_eq_dec_eq in Heqseq; subst.
      destruct (SignatureT_dec _ _); [|inv Heqob].
      generalize dependent HSemAction; inv Heqob; intros.
      rewrite M.find_add_1 in H3.
      inv H3; destruct_existT.
      simpl; constructor.

      eapply appendAction_SemAction; eauto.
      
      rewrite M.remove_add.
      rewrite M.remove_find_None by assumption.

      destruct meth; apply inlineDm_SemAction_intact; auto.

    + unfold getBody in Heqob.
      remember (string_eq _ _) as seq; destruct seq.

      * apply string_eq_dec_eq in Heqseq; subst.
        destruct (SignatureT_dec _ _); [inv Heqob|].

        { constructor 1 with
          (mret := mret)
            (calls := M.union cm1 (M.remove (attrName meth) calls)).
          - apply M.F.P.F.not_find_in_iff.
            unfold not; intros.
            apply M.F.P.F.not_find_in_iff in HDisjCalls.
            apply M.union_In in H4.
            dest_disj.
            destruct H4; auto.
            rewrite M.F.P.F.remove_in_iff in H4; intuition.
          - meq; clear - n H3; inv H3; destruct_existT; intuition auto.
          - apply H0; auto.
            elim n.
            rewrite M.find_add_1 in H3.
            clear -H3; inv H3; destruct_existT; auto.
        }

      * apply string_eq_dec_neq in Heqseq; subst.
        { constructor 1 with
          (mret := mret)
            (calls := M.union cm1 (M.remove (attrName meth) calls)).
          - apply M.F.P.F.not_find_in_iff.
            unfold not; intros.
            apply M.F.P.F.not_find_in_iff in HDisjCalls.
            apply M.union_In in H4.
            dest_disj.
            destruct H4; auto.
            rewrite M.F.P.F.remove_in_iff in H4; intuition.
          - meq; clear - n H3; inv H3; destruct_existT; intuition auto.
          - apply H0; auto.
            rewrite M.find_add_2 in H3; auto.
        } 
        
  - inv H4; destruct_existT.
    constructor; auto.
  - inv H4; destruct_existT.
    econstructor; eauto.
  - inv H4; destruct_existT.
    econstructor; eauto.
  - inv H3; destruct_existT.
    constructor 5 with (newRegs := M.union u1 newRegs).
    + apply M.F.P.F.not_find_in_iff.
      apply M.F.P.F.not_find_in_iff in HDisjRegs.
      unfold not; intros.
      apply M.union_In in H3.
      dest_disj.
      intuition.
    + meq.
    + apply IHa; auto.

  - inv H4; destruct_existT.
    + rewrite M.find_union in H3.
      remember (M.find (attrName meth) calls1) as omv1; destruct omv1.
      * remember (M.find (attrName meth) calls2) as omv2; destruct omv2.
        { exfalso.
          specialize (HDisjCalls (attrName meth)); destruct HDisjCalls; elim H4.
          { apply M.F.P.F.in_find_iff; rewrite <-Heqomv1; discriminate. }
          { apply M.F.P.F.in_find_iff; rewrite <-Heqomv2; discriminate. }
        }
        { inv H3.
          rewrite M.union_assoc, M.remove_union, M.union_assoc.
          eapply SemIfElseTrue with
          (newRegs1 := M.union u1 newRegs1)
            (calls1 := M.union cm1 (M.Map.remove (attrName meth) calls1)); eauto.
          { dest_disj; solve_disj. }
          { dest_disj.
            apply M.Disj_remove_2.
            solve_disj.
          }
          { rewrite M.remove_find_None by auto.
            destruct meth; apply inlineDm_SemAction_intact; auto.
          }
        }
      * assert (M.union u1 (M.union newRegs1 newRegs2) =
                M.union newRegs1 (M.union u1 newRegs2)).
        { rewrite M.union_assoc.
          rewrite M.union_comm with (m1:= u1); [|eapply M.Disj_union_1; eauto].
          rewrite <-M.union_assoc; auto.
        }
        rewrite H4; clear H4.

        assert (M.union cm1 (M.remove (attrName meth) (M.union calls1 calls2)) =
                M.union (M.remove (attrName meth) calls1)
                        (M.union cm1 (M.remove (attrName meth) calls2))).
        { rewrite M.remove_union, M.union_assoc.
          rewrite M.union_comm with (m1:= cm1);
            [|apply M.Disj_remove_2; eapply M.Disj_union_1; eauto].
          rewrite <-M.union_assoc; auto.
        }
        rewrite H4; clear H4.
        eapply SemIfElseTrue with
        (newRegs1 := newRegs1)
          (newRegs2 := M.union u1 newRegs2)
          (calls1 := M.remove (attrName meth) calls1)
          (calls2 := M.union cm1 (M.remove (attrName meth) calls2)); eauto.
        rewrite M.remove_find_None by auto.
        destruct meth; eapply inlineDm_SemAction_intact; eauto.

    + rewrite M.find_union in H3.
      remember (M.find (attrName meth) calls1) as omv1; destruct omv1.
      * remember (M.find (attrName meth) calls2) as omv2; destruct omv2.
        { exfalso.
          specialize (HDisjCalls (attrName meth)); destruct HDisjCalls; elim H4.
          { apply M.F.P.F.in_find_iff; rewrite <-Heqomv1; discriminate. }
          { apply M.F.P.F.in_find_iff; rewrite <-Heqomv2; discriminate. }
        }
        { inv H3.
          rewrite M.union_assoc, M.remove_union, M.union_assoc.
          eapply SemIfElseFalse with
          (newRegs1 := M.union u1 newRegs1)
            (calls1 := M.union cm1 (M.Map.remove (attrName meth) calls1)); eauto.
          { dest_disj; solve_disj. }
          { dest_disj.
            apply M.Disj_remove_2.
            solve_disj.
          }
          { rewrite M.remove_find_None by auto.
            destruct meth; apply inlineDm_SemAction_intact; auto.
          }
        }
      * assert (M.union u1 (M.union newRegs1 newRegs2) =
                M.union newRegs1 (M.union u1 newRegs2)).
        { rewrite M.union_assoc.
          rewrite M.union_comm with (m1:= u1); [|eapply M.Disj_union_1; eauto].
          rewrite <-M.union_assoc; auto.
        }
        rewrite H4; clear H4.

        assert (M.union cm1 (M.remove (attrName meth) (M.union calls1 calls2)) =
                M.union (M.remove (attrName meth) calls1)
                        (M.union cm1 (M.remove (attrName meth) calls2))).
        { rewrite M.remove_union, M.union_assoc.
          rewrite M.union_comm with (m1:= cm1);
            [|apply M.Disj_remove_2; eapply M.Disj_union_1; eauto].
          rewrite <-M.union_assoc; auto.
        }
        rewrite H4; clear H4.
        eapply SemIfElseFalse with
        (newRegs1 := newRegs1)
          (newRegs2 := M.union u1 newRegs2)
          (calls1 := M.remove (attrName meth) calls1)
          (calls2 := M.union cm1 (M.remove (attrName meth) calls2)); eauto.
        rewrite M.remove_find_None by auto.
        destruct meth; eapply inlineDm_SemAction_intact; eauto.

  - inv H3; destruct_existT.
    constructor; auto.

  - inv H3; destruct_existT.
    constructor; auto.

  - inv H3; destruct_existT.
    rewrite M.find_empty in H2; inv H2.
Qed.

Lemma isLeaf_SemAction_calls:
  forall {retK} aU aT,
    ActionEquiv (k:= retK) aT aU ->
    forall lcalls or nr calls retV,
      isLeaf aU lcalls = true ->
      SemAction or aT nr calls retV ->
      forall lc,
        In lc lcalls ->
        M.find lc calls = None.
Proof.
  induction 1; intros.

  - inv H2; destruct_existT.
    destruct (string_dec lc n).
    + subst; simpl in H1.
      apply andb_true_iff in H1; dest.
      remember (string_in _ _) as sin; destruct sin; [inv H1|].
      apply string_in_dec_not_in in Heqsin; elim Heqsin; auto.
    + simpl in H1.
      apply andb_true_iff in H1; dest.
      remember (string_in _ _) as sin; destruct sin; [inv H1|].
      apply string_in_dec_not_in in Heqsin.
      rewrite M.find_add_2 by assumption.
      eapply H0; eauto.

  - inv H2; destruct_existT.
    simpl in H1.
    eapply H0; eauto.
  - inv H2; destruct_existT.
    simpl in H1.
    eapply H0; eauto.
  - inv H2; destruct_existT.
    simpl in H1.
    eapply H0; eauto.
  - inv H1; destruct_existT.
    simpl in H0.
    eapply IHActionEquiv; eauto.
  - inv H3.
    apply andb_true_iff in H7; dest.
    apply andb_true_iff in H3; dest.
    inv H4; destruct_existT; rewrite M.find_union.
    + erewrite IHActionEquiv1; eauto.
    + erewrite IHActionEquiv2; eauto.
  - inv H1; destruct_existT.
    simpl in H0.
    eapply IHActionEquiv; eauto.
  - inv H0; destruct_existT.
    rewrite M.find_empty; auto.
Qed.

Lemma noCallDm_SemAction_calls:
  forall mn (mb: sigT MethodT) or nr calls argV retV
         (Hmb: ActionEquiv (projT2 mb type argV) (projT2 mb typeUT tt)),
    noCallDm (mn :: mb)%struct (mn :: mb)%struct = true ->
    SemAction or (projT2 mb type argV) nr calls retV ->
    M.find (elt:=sigT SignT) mn calls = None.
Proof.
  intros; unfold noCallDm in H; simpl in H.
  eapply isLeaf_SemAction_calls; eauto.
  intuition.
Qed.

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

  Fixpoint hideMeths (l: LabelT) (dms: list string): LabelT :=
    match dms with
      | nil => l
      | dm :: dms' => hideMeths (hideMeth l dm) dms'
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

End HideExts.

Section SubstepFacts.
  Variable m: Modules.
  Hypotheses (Hequiv: ModEquiv type typeUT m)
             (Hdefs: NoDup (namesOf (getDefsBodies m))).
  Variable dm: DefMethT.
  
  Lemma inlineDmToMod_correct_Substep:
    forall or u1 u2 cs1 cs2 argV retV ul2,
      Substep m or u2 ul2 cs2 ->
      SemAction or (projT2 (attrType dm) type argV) u1 cs1 retV ->
      M.Disj u1 u2 -> M.Disj cs1 cs2 ->
      Some (existT _ (projT1 (attrType dm)) (argV, retV)) = M.find (attrName dm) cs2 ->
      Substep (Mod (getRegInits m) (inlineDmToRules (getRules m) dm)
                   (inlineDmToDms (getDefsBodies m) dm))
              or (M.union u1 u2) ul2 (M.union cs1 (M.remove (attrName dm) cs2)).
  Proof.
    induction 1; intros; simpl in *; try (inv H2).

    - eapply SingleRule with (a:= attrType (inlineDmToRule (k :: a)%struct dm)); eauto.
      + apply in_map with (f:= fun r => inlineDmToRule r dm) in HInRules; auto.
      + simpl; eapply inlineDm_correct_SemAction; eauto.

    - eapply SingleMeth with (f:= inlineDmToDm f dm); eauto.
      + apply in_map with (f:= fun d => inlineDmToDm d dm) in HIn; auto.
      + simpl; eapply inlineDm_correct_SemAction; eauto.
  Qed.  

  Lemma inlineDmToMod_Substep_intact:
    forall or u ul cs (dmn: string),
      Substep m or u ul cs ->
      None = M.find (attrName dm) cs ->
      dmn = attrName dm ->
      Substep (Mod (getRegInits m) (inlineDmToRules (getRules m) dm)
                   (inlineDmToDms (getDefsBodies m) dm))
              or u ul cs.
  Proof.
    induction 1; intros; simpl in *; try (constructor; auto; fail).

    - apply SingleRule with (a:= attrType (inlineDmToRule (k :: a)%struct dm)); auto.
      + apply in_map with (f:= fun r => inlineDmToRule r dm) in HInRules; auto.
      + simpl; destruct dm; apply inlineDm_SemAction_intact; auto.

    - eapply SingleMeth with (f:= inlineDmToDm f dm); eauto.
      + apply in_map with (f:= fun d => inlineDmToDm d dm) in HIn; auto.
      + simpl; destruct dm; apply inlineDm_SemAction_intact; auto.
  Qed.

End SubstepFacts.

Lemma hideMeths_subtractKVD:
  forall dmsAll (l: LabelT),
    hideMeths l dmsAll = {| annot := annot l;
                            defs := M.subtractKVD signIsEq (defs l) (calls l) dmsAll;
                            calls := M.subtractKVD signIsEq (calls l) (defs l) dmsAll |}.
Proof.
  induction dmsAll; intros; destruct l as [ann ds cs]; simpl in *;
    [do 2 rewrite M.subtractKVD_nil; auto|].

  unfold hideMeth; simpl in *.
  do 2 rewrite M.subtractKVD_cons.
  remember (M.find a ds) as odv; destruct odv.
  - remember (M.find a cs) as ocv; destruct ocv; [|apply IHdmsAll].
    destruct (signIsEq s s0); [|destruct (signIsEq _ _); intuition; apply IHdmsAll].
    subst; destruct (signIsEq s0 s0); intuition auto.
    rewrite IHdmsAll; simpl in *.
    clear; f_equal.
  - destruct (M.find a cs); apply IHdmsAll.
Qed.

Lemma hideMeths_hide:
  forall dmsAll (l: LabelT),
    M.KeysSubset (defs l) dmsAll ->
    hideMeths l dmsAll = hide l.
Proof.
  intros; rewrite hideMeths_subtractKVD.
  unfold hide; f_equal.
  - rewrite <-M.subtractKV_subtractKVD_1; auto.
  - rewrite <-M.subtractKV_subtractKVD_2; auto.
Qed.

Lemma inlineDmToMod_getDmsMod:
  forall m a,
    getDefs (fst (inlineDmToMod m a)) = getDefs m.
Proof.
  intros; unfold inlineDmToMod; simpl.
  destruct (getAttribute _ _); [|auto].
  simpl.

  clear; induction m; unfold getDefs in *; simpl in *.
  - clear; induction (pm_methods prim); [auto|].
    simpl; f_equal; auto.
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
    destruct (string_eq _ _).
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
      * simpl; apply SubList_cons; intuition.
        apply SubList_cons_right; eauto.
    + simpl; apply SubList_cons; intuition.
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
    SubList (getCalls (fst (inlineDmToMod m a)))
            (getCalls m).
Proof.
  intros; unfold inlineDmToMod; simpl.
  remember (getAttribute _ _) as odm; destruct odm;
  [|apply SubList_refl]; simpl.
  unfold getCalls; simpl.
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
  apply M.KeysDisj_SubList with (d1:= getCalls m); auto.
  apply inlineDmToMod_calls.
Qed.

Lemma inlineDms_wellHidden:
  forall m (l: LabelT),
    wellHidden m l ->
    wellHidden (fst (inlineDms m)) l.
Proof.
  intros; unfold inlineDms.
  remember (namesOf (getDefsBodies m)) as dms; clear Heqdms.
  generalize dependent m; induction dms; intros; [assumption|]; simpl.
  pose proof (inlineDmToMod_wellHidden a H) as iwh.
  simpl; remember (inlineDmToMod m a) as imb; destruct imb; simpl in *.
  pose proof (IHdms _ iwh) as sth.
  remember (inlineDms' m0 dms) as imb'; destruct imb'; simpl in *.
  intuition.
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
    + pose proof (getDefs_substep H0); auto.
  - apply M.KeysSubset_union; auto.
    apply M.KeysSubset_add.
    + apply M.KeysSubset_empty.
    + pose proof (getDefs_substep H0); auto.
Qed.

Lemma inlineDm_ActionEquiv:
  forall type1 type2 {retT}
         (aU: ActionT type1 retT) (aT: ActionT type2 retT) (dm: DefMethT),
    (forall (argV1: ft1 type1 (SyntaxKind _))
            (argV2: ft2 type2 (SyntaxKind _)),
       ActionEquiv (projT2 (attrType dm) type1 argV1) (projT2 (attrType dm) type2 argV2)) ->
    ActionEquiv aU aT ->
    ActionEquiv (inlineDm aU dm) (inlineDm aT dm).
Proof.
  induction 2; intros; try (constructor; auto).

  simpl; remember (getBody n dm s) as dmb; destruct dmb; [|constructor; auto].

  unfold getBody in Heqdmb.
  remember (string_eq _ _) as seq; destruct seq; [|discriminate].
  apply string_eq_dec_eq in Heqseq; subst.
  destruct (SignatureT_dec _ _); [subst|discriminate].
  inv Heqdmb; simpl.

  constructor; intros.
  apply actionEquiv_appendAction.
  + apply H; auto.
  + intros.
    apply H1; auto.
Qed.

Lemma inlineDmToRules_RulesEquiv:
  forall {type1 type2} rules (dm: DefMethT),
    (forall (argV1: ft1 type1 (SyntaxKind _))
            (argV2: ft2 type2 (SyntaxKind _)),
       ActionEquiv (projT2 (attrType dm) type1 argV1) (projT2 (attrType dm) type2 argV2)) ->
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
       ActionEquiv (projT2 (attrType dm) type1 argV1) (projT2 (attrType dm) type2 argV2)) ->
    MethsEquiv type1 type2 dms ->
    MethsEquiv type1 type2 (inlineDmToDms dms dm).
Proof.
  induction 2; intros; unfold MethEquiv in *; simpl in *; constructor; auto.
  unfold MethEquiv in *.
  intros; simpl in *; apply inlineDm_ActionEquiv; auto.
Qed.

Lemma inlineDmToMod_ModEquiv:
  forall m dm,
    ModEquiv type typeUT m ->
    ModEquiv type typeUT (fst (inlineDmToMod m dm)).
Proof.
  intros.
  unfold inlineDmToMod.
  remember (getAttribute _ _) as oattr; destruct oattr; [|auto].
  simpl in Heqoattr.
  apply getAttribute_Some_body in Heqoattr.
  simpl; inv H.
  pose proof (proj1 (MethsEquiv_in type typeUT (getDefsBodies m)) H1 _ Heqoattr).
  constructor.
  - apply inlineDmToRules_RulesEquiv; auto.
  - apply inlineDmToDms_MethsEquiv; auto.
Qed.

Lemma inlineDms'_ModEquiv:
  forall dms m,
    ModEquiv type typeUT m ->
    ModEquiv type typeUT (fst (inlineDms' m dms)).
Proof.
  induction dms; simpl; intros; auto.
  case_eq (inlineDmToMod m a); intros.
  case_eq (inlineDms' m0 dms); intros; simpl.
  replace m1 with (fst (inlineDms' m0 dms)) by (rewrite H1; auto).
  apply IHdms.
  replace m0 with (fst (inlineDmToMod m a)) by (rewrite H0; auto).
  apply inlineDmToMod_ModEquiv; auto.
Qed.

Lemma inlineDms_ModEquiv:
  forall m,
    ModEquiv type typeUT m ->
    ModEquiv type typeUT (fst (inlineDms m)).
Proof. intros; apply inlineDms'_ModEquiv; auto. Qed.

Lemma inline_ModEquiv:
  forall m,
    ModEquiv type typeUT m ->
    ModEquiv type typeUT (fst (inline m)).
Proof. intros; apply inlineDms_ModEquiv; auto. Qed.

Lemma inlineDmToMod_dms_names:
  forall m a,
    namesOf (getDefsBodies (fst (inlineDmToMod m a))) =
    namesOf (getDefsBodies m).
Proof.
  destruct m; intros; simpl in *.
  - unfold inlineDmToMod.
    try destruct (getAttribute _ _);
    try (reflexivity; fail).
    simpl; clear.
    induction (pm_methods prim); auto.
    simpl; f_equal; auto.

  - unfold inlineDmToMod.
    try destruct (getAttribute _ _);
    try (reflexivity; fail).
    simpl; clear.
    induction dms; auto.
    simpl; f_equal; auto.

  - unfold inlineDmToMod.
    try destruct (getAttribute _ _);
    try reflexivity.
    apply inlineDmToDms_names.
Qed.

Section SubstepsFacts.
  Variable m: Modules.
  Hypotheses (Hequiv: ModEquiv type typeUT m)
             (Hdefs: NoDup (namesOf (getDefsBodies m))).
  Variable dm: DefMethT.
  Hypotheses (Hdm: In dm (getDefsBodies m)).

  Lemma inlineDmToMod_Substeps_intact:
    forall or u l,
      SubstepsInd m or u l ->
      forall ann ds cs,
        l = {| annot := ann; defs := ds; calls := cs |} ->
        None = M.find (attrName dm) cs ->
        SubstepsInd
          (Mod (getRegInits m) (inlineDmToRules (getRules m) dm)
               (inlineDmToDms (getDefsBodies m) dm)) or u l.
  Proof.
    induction 1; simpl; intros; [constructor|].

    subst; destruct l as [pann pds pcs].
    eapply SubstepsCons; eauto.
    - eapply IHSubstepsInd.
      + reflexivity.
      + inv H4.
        rewrite M.find_union in H5.
        destruct (M.find (attrName dm) pcs); auto.
        destruct (M.find (attrName dm) scs); inv H5.
    - eapply inlineDmToMod_Substep_intact; eauto.
      inv H4.
      rewrite M.find_union in H5.
      destruct (M.find (attrName dm) scs); auto.
  Qed.

  Lemma inlineDmToMod_correct_Substeps_called_rule:
    forall or su sr scs u l s,
      Substep m or su (Rle sr) scs ->
      SubstepsInd m or u l ->
      forall ds cs,
        l = {| annot := None; defs := ds; calls := cs |} ->
        Some s = M.find (attrName dm) scs ->
        Some s = M.find (attrName dm) ds ->
        M.Disj su u ->
        M.Disj scs cs ->
        SubstepsInd
          (Mod (getRegInits m) (inlineDmToRules (getRules m) dm)
               (inlineDmToDms (getDefsBodies m) dm)) or (M.union u su)
          {| annot := Some sr;
             defs := M.remove (attrName dm) (M.union (M.empty (sigT SignT)) ds);
             calls := M.remove (attrName dm) (M.union scs cs) |}.
  Proof.
    induction 2; simpl; intros; [inv H0; mcontra|].
    destruct l as [pann pds pcs]; simpl in *; subst.
    assert (pann = None); subst.
    { destruct pann; [destruct sul; discriminate|reflexivity]. }

    destruct sul as [psr|[[pdmn pdmv]|]]; inv H5.

    - M.cmp (attrName dm) pdmn; mred.
      + inv H2; dest; simpl in *.
        eapply SubstepsCons.
        * eapply inlineDmToMod_Substeps_intact; eauto; findeq.
        * inv H1; inv Hsig.
          assert (f = dm) by (eapply in_NoDup_attr; eauto); subst.
          eapply inlineDmToMod_correct_Substep; eauto.
        * repeat split; simpl; auto.
        * auto.
        * simpl; f_equal; auto.
      + eapply SubstepsCons.
        * eapply IHSubstepsInd; eauto.
        * eapply inlineDmToMod_Substep_intact; eauto; findeq.
        * inv H2; dest; simpl in *.
          repeat split; simpl; auto.
          findeq.
        * auto.
        * simpl; f_equal; auto.
      
    - eapply SubstepsCons.
      + apply IHSubstepsInd; eauto.
      + eapply inlineDmToMod_Substep_intact; eauto; findeq.
      + inv H2; dest; simpl in *.
        repeat split; simpl; auto.
      + auto.
      + simpl; f_equal; auto.
  Qed.

  Lemma inlineDmToMod_correct_Substeps_called_meth:
    forall or su smn smv scs u l,
      Substep m or su (Meth (Some (smn :: smv)%struct)) scs ->
      SubstepsInd m or u l ->
      forall ann ds cs s,
        l = {| annot := ann; defs := ds; calls := cs |} ->
        Some s = M.find (attrName dm) scs ->
        Some s = M.find (attrName dm) ds ->
        M.Disj su u ->
        M.Disj scs cs ->
        ~ M.In smn ds ->
        SubstepsInd
          (Mod (getRegInits m) (inlineDmToRules (getRules m) dm)
               (inlineDmToDms (getDefsBodies m) dm)) or (M.union u su)
          {|
            annot := ann;
            defs := M.remove (attrName dm) (M.union (M.add smn smv (M.empty (sigT SignT))) ds);
            calls := M.remove (attrName dm) (M.union scs cs) |}.
  Proof.
    induction 2; simpl; intros; [inv H0; mcontra|].
    destruct l as [pann pds pcs]; simpl in *; subst.

    destruct sul as [psr|[[pdmn pdmv]|]]; inv H5.

    - mred; eapply SubstepsCons.
      + eapply IHSubstepsInd; eauto.
      + eapply inlineDmToMod_Substep_intact; eauto; findeq.
      + inv H2; dest; simpl in *.
        repeat split; simpl; auto.
      + auto.
      + simpl; f_equal; auto.

    - M.cmp (attrName dm) pdmn; mred.
      + inv H2; dest; simpl in *.
        eapply SubstepsCons.
        * eapply inlineDmToMod_Substeps_intact; eauto; findeq.
        * inv H1; inv Hsig.
          assert (f = dm) by (eapply in_NoDup_attr; eauto); subst.
          eapply inlineDmToMod_correct_Substep; eauto.
        * repeat split; simpl; auto.
          destruct ann; M.cmp smn (attrName dm); findeq.
        * auto.
        * simpl; f_equal; auto.
          destruct ann; meq.
      + eapply SubstepsCons.
        * eapply IHSubstepsInd; eauto.
          M.cmp smn pdmn; findeq.
        * eapply inlineDmToMod_Substep_intact; eauto; findeq.
        * inv H2; dest; simpl in *.
          repeat split; simpl; auto.
          destruct ann; M.cmp pdmn smn; findeq.
        * auto.
        * simpl; f_equal; auto.

    - mred; eapply SubstepsCons.
      + eapply IHSubstepsInd; eauto.
      + eapply inlineDmToMod_Substep_intact; eauto; findeq.
      + inv H2; dest; simpl in *.
        repeat split; simpl; auto.
      + auto.
      + simpl; f_equal; auto.
  Qed.

  Lemma inlineDmToMod_correct_Substeps_calling:
    forall or su scs u l sdmv,
      Substep m or su (Meth (Some ((attrName dm) :: sdmv)%struct)) scs ->
      SubstepsInd m or u l ->
      forall ann ds cs,
        l = {| annot := ann; defs := ds; calls := cs |} ->
        M.Disj su u ->
        M.Disj scs cs ->
        Some sdmv = M.Map.find (elt:=sigT SignT) (attrName dm) cs ->
        ~ M.In (attrName dm) ds ->
        SubstepsInd
          (Mod (getRegInits m) (inlineDmToRules (getRules m) dm)
               (inlineDmToDms (getDefsBodies m) dm)) or (M.union u su)
          {| annot := ann;
             defs := M.remove (elt:=sigT SignT) (attrName dm)
                              (M.union (M.add (attrName dm) sdmv (M.empty (sigT SignT))) ds);
             calls := M.remove (elt:=sigT SignT) (attrName dm) (M.union scs cs) |}.
  Proof.
    induction 2; simpl; intros; [inv H0; mcontra|].
    subst; destruct l as [pann pds pcs].
    inv H5; mred.
    remember (M.find (attrName dm) scs0) as osdm; destruct osdm.

    - inv H8; inv H2; dest; simpl in *.
      eapply SubstepsCons.
      + eapply inlineDmToMod_Substeps_intact; eauto; findeq.
      + inv H; inv Hsig.
        assert (f = dm) by (eapply in_NoDup_attr; eauto); subst.
        eapply inlineDmToMod_correct_Substep; eauto.
      + repeat split; simpl; auto.
      + auto.
      + simpl; f_equal; auto.
        destruct sul as [|[[? ?]|]]; auto.

    - inv H2; dest; simpl in *.
      eapply SubstepsCons.
      + apply IHSubstepsInd; auto.
        destruct sul as [|[[pdmn pdmv]|]]; findeq.
      + eapply inlineDmToMod_Substep_intact; eauto.
      + repeat split; simpl; auto.
        destruct pann; destruct sul as [|[[pdmn pdmv]|]]; auto;
          findeq; auto.
      + auto.
      + simpl; f_equal; auto.
        destruct sul as [|[[pdmn pdmv]|]]; auto.
  Qed.

End SubstepsFacts.

Lemma inlineDmToMod_correct_Substeps:
  forall m (Hequiv: ModEquiv type typeUT m)
         or nr l dm,
    NoDup (namesOf (getDefsBodies m)) ->
    SubstepsInd m or nr l ->
    M.find dm (calls l) = None \/ M.find dm (defs l) = M.find dm (calls l) ->
    snd (inlineDmToMod m dm) = true ->
    SubstepsInd (fst (inlineDmToMod m dm)) or nr (hideMeth l dm).
Proof.
  induction 3; intros; [constructor|].

  subst; unfold inlineDmToMod in *.
  remember (getAttribute _ _) as odm; destruct odm; [|inv H6].
  remember (noCallDm _ _) as onc; destruct onc; [|inv H6].
  destruct l as [ann ds cs]; simpl in *.

  pose proof (getAttribute_Some_name _ _ Heqodm); subst.
  apply getAttribute_Some_body in Heqodm.
  inv H2; dest; simpl in *.

  unfold hideMeth in *; simpl in *.

  (* inline target called? *)
  remember (M.find (attrName a) (M.union scs cs)) as ocmv; destruct ocmv.

  - destruct H5; [discriminate|].
    rewrite H5 in *; mred.

    (* by Substep? *)
    remember (M.find (attrName a) scs) as oscmv; destruct oscmv.
    + inv Heqocmv.
      assert (None = M.find (attrName a) cs) by findeq.
      rewrite <-H7 in IHSubstepsInd.
      destruct (signIsEq s0 s0); [clear e|elim n; auto].
      specialize (IHSubstepsInd (or_introl eq_refl) eq_refl).

      destruct sul as [sr|[[sdmn sdmv]|]].

      * mred.
        rewrite H5 in IHSubstepsInd.
        destruct ann; [intuition idtac|].
        eapply inlineDmToMod_correct_Substeps_called_rule; eauto.
      * M.cmp (attrName a) sdmn.
        { (* Substep(head)-inlined: impossible *)
          mred; exfalso.
          inv H1; inv Hsig.
          assert (f = a) by (apply in_NoDup_attr with (attrs:= getDefsBodies m); auto);
            subst.
          assert (M.find (attrName a) scs = None).
          { eapply noCallDm_SemAction_calls; eauto.
            eapply MethsEquiv_in; eauto.
            inv Hequiv; auto.
          }
          rewrite H1 in Heqoscmv; discriminate.
        }
        { mred.
          rewrite H5 in IHSubstepsInd.
          assert (~ M.In sdmn ds)
            by (destruct ann; auto).
          eapply inlineDmToMod_correct_Substeps_called_meth; eauto.
        }
      * exfalso; inv H1; mred.

    + rewrite <-Heqocmv in IHSubstepsInd.
      match goal with
        | [H: match (M.find ?a ?lm) with | Some _ => _ | None => _ end = Some _ |- _] =>
          remember (M.find a lm) as odmv; destruct odmv
      end.

      * inv H5; destruct (signIsEq s s); [clear e|elim n; auto].
        destruct sul as [sr|[[sdmn sdmv]|]].
        { mred; mcontra. }
        { M.cmp (attrName a) sdmn; [|mred; mcontra].
          mred.
          assert (~ M.In (attrName a) ds)
            by (destruct ann; auto).
          eapply inlineDmToMod_correct_Substeps_calling; eauto.
        }
        { mred; mcontra. }

      * rewrite H5 in IHSubstepsInd.
        destruct (signIsEq s s); [clear e|elim n; auto].

        eapply SubstepsCons; eauto.
        { eapply inlineDmToMod_Substep_intact; eauto. }
        { repeat split; simpl; auto.
          destruct ann; destruct sul as [|[|]]; auto;
          intro Hx; elim H4; eapply M.F.P.F.remove_in_iff; eauto.
        }
        { simpl; f_equal; auto. }

  - rewrite M.find_union in Heqocmv.
    remember (M.find (attrName a) scs) as oscmv; destruct oscmv; [inv Heqocmv|].
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
    + destruct (M.find (attrName a) ds); repeat split; simpl; auto.
    + destruct (M.find (attrName a) ds); reflexivity.
Qed.

Lemma inlineDms'_correct_Substeps:
  forall cdms m (Hequiv: ModEquiv type typeUT m)
         (Hdms: NoDup (namesOf (getDefsBodies m)))
         (Hcdms: SubList cdms (namesOf (getDefsBodies m)))
         or nr l,
    SubstepsInd m or nr l ->
    wellHidden m (hide l) ->
    snd (inlineDms' m cdms) = true ->
    SubstepsInd (fst (inlineDms' m cdms)) or nr (hideMeths l cdms).
Proof.
  induction cdms; intros; simpl; [apply flatten_preserves_substepsInd; auto|].
  apply SubList_cons_inv in Hcdms; dest.
  remember (inlineDmToMod m a) as imb; destruct imb as [im ib]; simpl.
  remember (inlineDms' im cdms) as imc; destruct imc as [im' ib']; simpl.
  destruct ib; simpl in *.
  - assert (im' = fst (inlineDms' im cdms)) by (rewrite <- Heqimc; reflexivity); subst; simpl in *.
    assert (im = fst (inlineDmToMod m a)) by (rewrite <-Heqimb; reflexivity); subst; simpl in *.
    apply IHcdms; auto.
    + apply inlineDmToMod_ModEquiv; auto.
    + rewrite inlineDmToMod_dms_names; auto.
    + rewrite inlineDmToMod_dms_names; auto.
    + apply inlineDmToMod_correct_Substeps; auto.
      * eapply wellHidden_find_1; eauto.
      * simpl in H0; destruct (inlineDmToMod m a); simpl in *.
        destruct b; [auto|inv Heqimb].
    + apply inlineDmToMod_wellHidden.
      rewrite hideMeth_preserves_hide; auto.
    + simpl in H1; destruct (inlineDmToMod m a); simpl in *.
      destruct (inlineDms' m0 cdms); simpl in *.
      destruct b; [auto|inv Heqimb].
  - destruct (inlineDmToMod m a).
    destruct (inlineDms' m0 cdms); simpl in *.
    inversion Heqimb; subst.
    simpl in *.
    discriminate.
Qed.

Lemma inlineDms_correct_SubstepsInd:
  forall m (Hequiv: ModEquiv type typeUT m)
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

Lemma inlineDms_correct:
  forall m (Hequiv: ModEquiv type typeUT m)
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

Lemma step_dms_hidden:
  forall m or nr l,
    Step m or nr l ->
    M.KeysDisj (defs l) (getCalls m).
Proof.
  intros; inv H.
  unfold wellHidden in HWellHidden.
  destruct (hide _); simpl in *; intuition.
Qed.

Lemma inline_correct_Step:
  forall m (Hequiv: ModEquiv type typeUT m)
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

Lemma inlineF_correct_Step:
  forall m (Hequiv: ModEquiv type typeUT m)
         (Hdms: NoDup (namesOf (getDefsBodies m)))
         (Hin: snd (inlineF m) = true)
         or nr l,
    Step m or nr l ->
    Step (fst (inlineF m)) or nr l.
Proof.
  unfold inlineF; intros.
  remember (inline m) as imb; destruct imb as [im ib]; subst.
  simpl; remember (noInternalCalls im) as imc.
  destruct imc; [|inv Hin].
  assert (Hit: snd (inline m) = true)
    by (rewrite <-Heqimb; inv Hin; auto).
  pose proof (inline_correct_Step Hequiv Hdms Hit H).
  rewrite <-Heqimb in H0; simpl in H0.
  pose proof (step_dms_hidden H).
  apply step_dms_weakening; auto.
  - replace im with (fst (inline m)) by (rewrite <-Heqimb; auto).
    apply inline_ModEquiv; auto.
  - apply noInternalCalls_implies_disj; auto.
  - apply flatten_preserves_step; auto.
Qed.
  
Lemma inlineDms'_preserves_regInits:
  forall dms m, getRegInits m = getRegInits (fst (inlineDms' m dms)).
Proof.
  induction dms; [reflexivity|].
  intros; simpl; remember (inlineDmToMod m a) as ima; destruct ima.
  remember (inlineDms' m0 dms) as imb; destruct imb; simpl in *.
  specialize (IHdms m0).
  destruct (inlineDms' m0 dms).
  simpl in *.
  inv Heqimb.
  unfold inlineDmToMod in *.
  destruct (getAttribute _ _);
  inv Heqima; simpl in *; intuition.
Qed.

Lemma inline_preserves_regInits:
  forall m, getRegInits m = getRegInits (fst (inline m)).
Proof. intros; apply inlineDms'_preserves_regInits. Qed.

Lemma inlineF_preserves_regInits:
  forall m, getRegInits m = getRegInits (fst (inlineF m)).
Proof.
  intros; unfold inlineF.
  remember (inline m) as imb; destruct imb as [im ib]; simpl.
  replace im with (fst (inline m)) by (rewrite <-Heqimb; auto).
  apply inlineDms'_preserves_regInits.
Qed.

Theorem inline_refines:
  forall m (Hequiv: ModEquiv type typeUT m)
         (Hdms: NoDup (namesOf (getDefsBodies m)))
         (Hin: snd (inline m) = true),
    traceRefines id m (fst (inline m)).
Proof.
  intros.
  apply stepRefinement with (ruleMap:= fun o r => Some r) (theta:= id).
  - erewrite inlineDms'_preserves_regInits; reflexivity.
  - intros.
    apply inline_correct_Step in H0; unfold id in *; auto.
    exists u; split; auto.
    destruct l as [ann ds cs]; simpl in *.
    destruct ann as [[|]|]; auto.
Qed.

Theorem inlineF_refines:
  forall m (Hequiv: ModEquiv type typeUT m)
         (Hdms: NoDup (namesOf (getDefsBodies m))),
    let im := inlineF m in
    snd im = true -> traceRefines id m (fst im).
Proof.
  intros.
  apply stepRefinement with (ruleMap:= fun o r => Some r) (theta:= id).
  - rewrite inlineF_preserves_regInits; reflexivity.
  - intros; eapply inlineF_correct_Step in H; unfold id in *; eauto.
    destruct l as [ann ds cs]; simpl in *.
    destruct ann as [[|]|]; auto.
Qed.

(** Interface lemmas and ltacs *)
Lemma traceRefines_inlining_left:
  forall ma
         (Hequiv: ModEquiv type typeUT ma)
         (Hdup: NoDup (namesOf (getDefsBodies ma)))
         mb p,
    traceRefines p (fst (inlineF ma)) mb /\ snd (inlineF ma) = true ->
    traceRefines p ma mb.
Proof.
  intros; dest; apply traceRefines_trans with (mb:= fst (inlineF ma)).
  - apply inlineF_refines; auto.
  - auto.
Qed.


(** Now for fine-grained partial inlining *)
Section NoCallDmSig.
  Fixpoint noCallDmSigA {retT} (a: ActionT typeUT retT) (dmn: string) (dsig: SignatureT) :=
    match a with
    | MCall name sig _ cont =>
      ((negb (string_eq name dmn))
       || (if SignatureT_dec sig dsig then false else true))
        && (noCallDmSigA (cont tt) dmn dsig)
    | Let_ _ ar cont => noCallDmSigA (cont (getUT _)) dmn dsig
    | ReadNondet k cont => noCallDmSigA (cont (getUT _)) dmn dsig
    | ReadReg reg k cont => noCallDmSigA (cont (getUT _)) dmn dsig
    | WriteReg reg _ e cont => noCallDmSigA cont dmn dsig
    | IfElse ce _ ta fa cont =>
      (noCallDmSigA ta dmn dsig) && (noCallDmSigA fa dmn dsig) && (noCallDmSigA (cont tt) dmn dsig)
    | Assert_ ae cont => noCallDmSigA cont dmn dsig
    | Displ ls cont => noCallDmSigA cont dmn dsig
    | Return e => true
    end.

  Definition noCallDmSigDms (dms: list DefMethT) (ndm: DefMethT) :=
    Forall (fun dm: DefMethT =>
              noCallDmSigA (projT2 (attrType dm) typeUT tt) (attrName ndm)
                           (projT1 (attrType ndm)) = true) dms.

  Definition noCallDmSigRules (rules: list (Attribute (Action Void))) (ndm: DefMethT) :=
    Forall (fun r: Attribute (Action Void) =>
              noCallDmSigA (attrType r typeUT) (attrName ndm)
                           (projT1 (attrType ndm)) = true) rules.

  Definition noCallDmSig (m: Modules) (ndm: DefMethT) :=
    (noCallDmSigRules (getRules m) ndm) /\ (noCallDmSigDms (getDefsBodies m) ndm).

End NoCallDmSig.

Lemma noCallDmSigA_semAction_calls:
  forall {retK} (aty: ActionT type retK) aut (Hequiv: ActionEquiv aty aut)
         (dm: DefMethT),
    noCallDmSigA aut (attrName dm) (projT1 (attrType dm)) = true ->
    forall s o u cs retv,
      SemAction o aty u cs retv ->
      Some s = M.find (attrName dm) cs ->
      projT1 s = projT1 (attrType dm) ->
      False.
Proof.
  induction 1; simpl; intros; auto.

  - inv H2; destruct_existT.
    apply andb_true_iff in H1; dest.
    remember (string_eq n (attrName dm)) as ndeq; destruct ndeq.
    + apply string_eq_dec_eq in Heqndeq; subst; mred.
    + apply string_eq_dec_neq in Heqndeq.
      rewrite M.find_add_2 in H3 by intuition.
      eapply H0; eauto.

  - inv H2; destruct_existT; eapply H0; eauto.
  - inv H2; destruct_existT; eapply H0; eauto.
  - inv H2; destruct_existT; eapply H0; eauto.
  - inv H0; destruct_existT; eapply IHHequiv; eauto.
  - apply andb_true_iff in H1; dest.
    apply andb_true_iff in H1; dest.
    inv H2; destruct_existT.
    + rewrite M.find_union in H3.
      remember (M.find (attrName dm) calls1) as odc1; destruct odc1.
      * inv H3; eapply IHHequiv1; eauto.
      * eapply H0; eauto.
    + rewrite M.find_union in H3.
      remember (M.find (attrName dm) calls1) as odc1; destruct odc1.
      * inv H3; eapply IHHequiv2; eauto.
      * eapply H0; eauto.
  - inv H0; destruct_existT; eapply IHHequiv; eauto.
  - inv H0; destruct_existT; mred.
Qed.

Lemma appendAction_noCallDmSigA:
  forall {retK1 retK2} (a1: ActionT typeUT retK1)
         (a2: typeUT retK1 -> ActionT typeUT retK2) dmn dsig,
    noCallDmSigA (appendAction a1 a2) dmn dsig =
    noCallDmSigA a1 dmn dsig && noCallDmSigA (a2 tt) dmn dsig.
Proof.
  induction a1; simpl; intros; auto.
  - rewrite <-andb_assoc; f_equal; auto.
  - do 3 rewrite <-andb_assoc; repeat f_equal; auto.
Qed.

Lemma noCallDm_noCallDmSigA:
  forall tdm dm,
    noCallDm tdm dm = true ->
    noCallDmSigA (projT2 (attrType tdm) typeUT tt)
                 (attrName dm) (projT1 (attrType dm)) = true.
Proof.
  unfold noCallDm; intros.
  generalize dependent (projT2 (attrType tdm) typeUT tt).
  clear; intros.
  induction a; simpl; intros; auto; simpl in *.
  - apply andb_true_iff in H; dest.
    apply andb_true_iff; split; auto.
    remember (string_eq meth (attrName dm)) as md; destruct md.
    + apply string_eq_dec_eq in Heqmd; subst.
      exfalso; rewrite string_eq_true in H.
      inv H.
    + auto.
  - apply andb_true_iff in H; dest.
    apply andb_true_iff in H; dest.
    apply andb_true_iff; split; auto.
    apply andb_true_iff; split; auto.
Qed.

Lemma noCalls_noCallDmSigATrue:
  forall k (a: ActionT typeUT k) dmName dmBody,
    ~ In dmName (getCallsA a) -> noCallDmSigA a dmName dmBody = true.
Proof.
  induction a; simpl in *; auto; intros.
  - assert (sth1: meth <> dmName) by intuition auto.
    assert (sth2: ~ In dmName (getCallsA (a tt))) by intuition auto.
    unfold negb, orb, andb.
    case_eq (string_eq meth dmName); intros.
    + apply eq_sym in H1; apply string_eq_dec_eq in H1; subst; intuition.
    + apply H; auto.
  - rewrite IHa1, IHa2, H; auto; unfold not; intros.
    + assert (In dmName (getCallsA a1 ++ getCallsA a2 ++ getCallsA (a3 tt)))
        by (apply in_or_app; right; apply in_or_app; right; intuition auto).
      auto.
    + assert (In dmName (getCallsA a1 ++ getCallsA a2 ++ getCallsA (a3 tt)))
        by (apply in_or_app; right; apply in_or_app; left; intuition auto).
      auto.
    + assert (In dmName (getCallsA a1 ++ getCallsA a2 ++ getCallsA (a3 tt)))
        by (apply in_or_app; left; intuition auto).
      auto.
Qed.

Lemma inlineDm_noCallDmSigA:
  forall (dm: DefMethT)
         (Hdm: noCallDmSigA (projT2 (attrType dm) typeUT tt)
                            (attrName dm) (projT1 (attrType dm)) = true)
         {retK} (a: ActionT typeUT retK),
    noCallDmSigA (inlineDm a dm) (attrName dm) (projT1 (attrType dm)) = true.
Proof.
  induction a; simpl; intros; auto;
    [|do 2 (apply andb_true_iff; split; auto)].

  unfold getBody.
  remember (string_eq meth (attrName dm)) as md; destruct md;
    [|simpl; rewrite <-Heqmd; simpl; auto].
  destruct (SignatureT_dec _ _).
  - simpl; rewrite appendAction_noCallDmSigA.
    apply andb_true_iff; split; auto.
    subst; simpl.
    assumption.
  - simpl; rewrite <-Heqmd; simpl.
    destruct (SignatureT_dec _ _); [elim n; auto|].
    simpl; auto.
Qed.

Lemma inlineDmToRule_noCallDmSigA:
  forall (dm: DefMethT)
         (Hdm: noCallDmSigA (projT2 (attrType dm) typeUT tt)
                            (attrName dm) (projT1 (attrType dm)) = true) r,
    noCallDmSigA (attrType (inlineDmToRule r dm) typeUT)
                 (attrName dm) (projT1 (attrType dm)) = true.
Proof.
  intros; apply inlineDm_noCallDmSigA; auto.
Qed.

Lemma noCallDmSig_substep_calls:
  forall m o u ul cs,
    ModEquiv type typeUT m ->
    Substep m o u ul cs ->
    forall dm s,
      noCallDmSig m dm ->
      Some s = M.find (elt:=sigT SignT) (attrName dm) cs ->
      projT1 s = projT1 (attrType dm) ->
      False.
Proof.
  intros; inv H0; try (mred; fail).

  - inv H; rewrite RulesEquiv_in in H0.
    specialize (H0 _ HInRules); unfold RuleEquiv in H0; simpl in H0.
    unfold noCallDmSig in H1; dest.
    unfold noCallDmSigRules in H; rewrite Forall_forall in H.
    specialize (H _ HInRules); simpl in H.
    eapply noCallDmSigA_semAction_calls; eauto.

  - inv H; rewrite MethsEquiv_in in H4.
    specialize (H4 _ HIn); unfold MethEquiv in H4; simpl in H4.
    unfold noCallDmSig in H1; dest.
    unfold noCallDmSigDms in H1; rewrite Forall_forall in H1.
    specialize (H1 _ HIn); simpl in H1.
    eapply noCallDmSigA_semAction_calls; eauto.
Qed.

Lemma noCallDmSig_substepsInd_calls:
  forall m o u l,
    ModEquiv type typeUT m ->
    SubstepsInd m o u l ->
    forall dm s,
      noCallDmSig m dm ->
      Some s = M.find (elt:=sigT SignT) (attrName dm) (calls l) ->
      projT1 s = projT1 (attrType dm) ->
      False.
Proof.
  induction 2; simpl; intros; [mred|].
  subst; destruct l as [ann ds cs]; simpl in *.
  rewrite M.find_union in H6.
  remember (M.find (attrName dm) scs) as odsc; destruct odsc.
  - inv H6; apply noCallDmSig_substep_calls with (dm:= dm) (s:= s0) in H1; auto.
  - eapply IHSubstepsInd; eauto.
Qed.

Lemma stepInd_filterDm:
  forall regs rules dms o u l,
    ModEquiv type typeUT (Mod regs rules dms) ->
    NoDup (getDefs (Mod regs rules dms)) ->
    StepInd (Mod regs rules dms) o u l ->
    forall (dm: DefMethT),
      In dm dms ->
      M.find (attrName dm) (defs l) = None ->
      noCallDmSig (Mod regs rules dms) dm ->
      StepInd (Mod regs rules (filterDm dms (attrName dm))) o u l.
Proof.
  intros; inv H1; constructor; [|apply filterDm_wellHidden; auto].

  remember (M.find (attrName dm) (defs l0)) as odl; destruct odl.

  - pose proof (substepsInd_defs_sig _ H0 H2 HSubSteps Heqodl).
    remember (M.find (attrName dm) (calls l0)) as ocl; destruct ocl.

    + assert (s = s0); subst.
      { clear -H3 Heqodl Heqocl.
        destruct l0 as [ann ds cs]; simpl in *.
        findeq.
      }
      exfalso; eapply noCallDmSig_substepsInd_calls; eauto.

    + exfalso; clear -H3 Heqodl Heqocl.
      destruct l0 as [ann ds cs]; simpl in *.
      findeq.

  - assert (None = M.find (attrName dm) (calls l0)).
    { apply wellHidden_find_1 with (a:= attrName dm) in HWellHidden.
      { destruct HWellHidden; auto.
        rewrite Heqodl; auto.
      }
      { simpl; apply in_map; auto. }
    }
    apply substepsInd_dm_weakening; auto.
Qed.

(* Partial inlining interfaces *)
Section Partial.
  Variable m: Modules.

  Variable dm: DefMethT. (* a method to be inlined *)
  Hypotheses (Hdm: In dm (getDefsBodies m))
             (HnoDupMeths: NoDup (namesOf (getDefsBodies m))).
  Variable r: Attribute (Action Void). (* a rule calling dm *)
  Hypothesis Hrule: In r (getRules m).

  Lemma inlineDmToRule_substepsInd_intact_1:
    forall o u l,
      SubstepsInd m o u l ->
      ~ (annot l = Some (Some (attrName r)) /\ M.find (attrName dm) (calls l) <> None) ->
      SubstepsInd
        (Mod (getRegInits m)
             (map
                (fun newr =>
                   if string_dec (attrName r) (attrName newr)
                   then inlineDmToRule newr dm
                   else newr) (getRules m)) (getDefsBodies m)) o u l.
  Proof.
    induction 1; intros; [constructor|].
    subst; econstructor.

    - apply IHSubstepsInd.
      intro Hx; elim H4; clear H4; dest; split.
      + clear -H1 H2.
        inv H1; dest.
        destruct l as [ann ds cs], sul as [|];
          simpl in *; subst; intuition idtac.
      + intro Hx; elim H3; clear H3.
        destruct l as [ann ds cs]; simpl in *; findeq.

    - instantiate (1:= scs); instantiate (1:= sul); instantiate (1:= su).
      clear -H0 H4.
      inv H0; try constructor.

      + destruct (string_dec (attrName r) k); subst.
        * remember (M.find (attrName dm) scs) as ods; destruct ods.
          { elim H4; clear H4; split.
            { destruct l as [ann ds cs]; simpl; destruct ann; reflexivity. }
            { destruct l as [ann ds cs]; simpl.
              rewrite M.find_union, <-Heqods; discriminate.
            }
          }
          { econstructor.
            { simpl.
              apply in_map with (f:= fun newr =>
                                       if string_dec (attrName r) (attrName newr)
                                       then inlineDmToRule newr dm
                                       else newr) in HInRules.
              simpl in HInRules.
              destruct (string_dec (attrName r) (attrName r)); [clear e|elim n; reflexivity].
              eauto.
            }
            { simpl; destruct dm as [dmn dmb].
              apply inlineDm_SemAction_intact; auto.
            }
          }
        * econstructor.
          { simpl.
            apply in_map with (f:= fun newr =>
                                     if string_dec (attrName r) (attrName newr)
                                     then inlineDmToRule newr dm
                                     else newr) in HInRules.
            simpl in HInRules.
            destruct (string_dec (attrName r) k); [elim n; auto|].
            eauto.
          }
          { auto. }

      + econstructor; eauto.

    - auto.
    - auto.
    - auto.

  Qed.

  Lemma inlineDmToRule_substepsInd_intact_2:
    forall o pu pds pcs,
      SubstepsInd m o pu {| annot := None; defs := pds; calls := pcs |} ->
      forall ru rcs,
        Substep m o ru (Rle (Some (attrName r))) rcs ->
        None = M.find (elt:=sigT SignT) (attrName dm) rcs ->
        (* Some s = M.find (elt:=sigT SignT) (attrName dm) pcs -> *)
        M.Disj ru pu -> M.Disj rcs pcs ->
        SubstepsInd
          (Mod (getRegInits m)
               (map
                  (fun newr =>
                     if string_dec (attrName r) (attrName newr)
                     then inlineDmToRule newr dm else newr)
                  (getRules m)) (getDefsBodies m)) o (M.union pu ru)
          {| annot := Some (Some (attrName r)); defs := pds; calls := M.union rcs pcs |}.
  Proof.
    intros; econstructor.

    - apply inlineDmToRule_substepsInd_intact_1.
      + eassumption.
      + simpl; intro Hx; dest; discriminate.

    - instantiate (1:= rcs).
      instantiate (1:= Rle (Some (attrName r))).
      instantiate (1:= ru).
      inv H0.

      econstructor.
      + simpl.
        apply in_map with (f:= fun newr =>
                                 if string_dec (attrName r) (attrName newr)
                                 then inlineDmToRule newr dm
                                 else newr) in HInRules.
        simpl in HInRules.
        destruct (string_dec (attrName r) (attrName r)); [clear e|elim n; reflexivity].
        eauto.
      + simpl; destruct dm as [dmn dmb].
        apply inlineDm_SemAction_intact; auto.

    - repeat split; auto.
    - reflexivity.
    - reflexivity.

  Qed.

  Lemma inlineDmToRule_substepsInd_sub:
    forall o u su scs s l,
      Substep m o su (Rle (Some (attrName r))) scs ->
      M.find (elt:=sigT SignT) (attrName dm) scs = Some s ->
      SubstepsInd m o u l ->
      forall ds cs,
        l = {| annot := None; defs:= ds; calls := cs |} ->
        M.Disj su u -> M.Disj scs cs ->
        M.find (elt:=sigT SignT) (attrName dm) ds = Some s ->
        SubstepsInd
          (Mod (getRegInits m)
               (map
                  (fun newr =>
                     if string_dec (attrName r) (attrName newr)
                     then inlineDmToRule newr dm else newr)
                  (getRules m)) (getDefsBodies m)) o (M.union u su)
          (hideMeth 
             {| annot := Some (Some (attrName r));
                defs := ds;
                calls := M.union scs cs |} (attrName dm)).
  Proof.
    induction 3; simpl; intros; [exfalso; inv H1; mred|].

    subst; destruct l as [pann pds pcs].
    destruct pann as [|]; [exfalso; destruct sul; inv H6|].
    specialize (IHSubstepsInd _ _ eq_refl).

    remember (M.find (attrName dm) pds) as odp; destruct odp.

    - assert (s = s0); subst.
      { clear -Heqodp H3 H6 H9.
        inv H3; dest; simpl in *.
        inv H6.
        destruct sul as [|[[dmn dmb]|]]; simpl in *; findeq.
        destruct (string_dec (attrName dm) dmn).
        { subst; exfalso; mcontra. }
        { mred. }
      }

      econstructor.
      + apply IHSubstepsInd; auto.
        inv H6; auto.
      + instantiate (1:= scs0); instantiate (1:= sul); instantiate (1:= su0).
        destruct sul as [|]; [exfalso; inv H6|].
        clear -H2.
        inv H2; [constructor|].
        econstructor; eauto.
      + inv H6; inv H3; dest; simpl in *.
        unfold hideMeth; simpl.
        rewrite <-Heqodp.
        rewrite M.find_union, H0.
        destruct (signIsEq _ _); [|elim n; reflexivity].
        repeat split; simpl; auto.
        destruct sul as [|[|]]; auto.
        * inv H5.
        * findeq; auto.
      + meq.
      + unfold hideMeth at 1; simpl.
        rewrite H9.
        rewrite M.find_union, H0.
        destruct (signIsEq _ _); [clear e|elim n; reflexivity].
        unfold hideMeth; simpl.
        rewrite <-Heqodp.
        rewrite M.find_union, H0.
        destruct (signIsEq _ _); [clear e|elim n; reflexivity].
        f_equal.
        * inv H6; destruct sul as [|[|]]; auto; inv H5.
        * inv H6; inv H3; dest; simpl in *.
          destruct sul as [|[[dmn dmb]|]]; auto.
          destruct (string_dec (attrName dm) dmn); auto.
          subst; meq.
          simpl in H6; mcontra.
        * inv H6; inv H3; dest; simpl in *.
          apply eq_sym in H0; meq.
          
    - clear IHSubstepsInd.
      assert (sul = Meth (Some (attrName dm :: s)%struct)); subst.
      { destruct sul as [|]; inv H6.
        destruct o0 as [[dmn dmb]|]; [|mred].
        destruct (string_dec (attrName dm) dmn); subst; mred.
      }
      inv H3; inv H6; dest; simpl in *; clear H5 H9.

      econstructor.
      + apply inlineDmToRule_substepsInd_intact_1.
        * eassumption.
        * simpl; intro Hx; dest; discriminate.
      + instantiate (1:= M.remove (attrName dm) (M.union scs scs0)).
        instantiate (1:= Rle (Some (attrName r))).
        instantiate (1:= M.union su su0).

        inv H; inv H2.
        econstructor.
        * simpl.
          apply in_map with (f:= fun newr =>
                                   if string_dec (attrName r) (attrName newr)
                                   then inlineDmToRule newr dm
                                   else newr) in HInRules.
          simpl in HInRules.
          destruct (string_dec _ _); [|elim n; reflexivity].
          eauto.
        * simpl; inv Hsig.
          assert (dm = f) by (eapply in_NoDup_attr; eauto); subst.
          rewrite M.union_comm with (m1:= su) by auto.
          replace (M.remove (attrName f) (M.union scs scs0)) with
          (M.union scs0 (M.remove (attrName f) scs))
            by (meq; apply eq_sym in H0; mcontra).
          eapply inlineDm_correct_SemAction; eauto.

      + repeat split; auto.
      + meq.
      + unfold hideMeth; simpl; mred.
        simpl; f_equal; meq.

  Qed.

  Lemma inlineDmToRule_wellHidden:
    forall l,
      wellHidden m l ->
      wellHidden
        (Mod (getRegInits m)
             (map
                (fun newr =>
                   if string_dec (attrName r) (attrName newr)
                   then inlineDmToRule newr dm else newr)
                (getRules m)) (getDefsBodies m)) l.
  Proof.
    intros; apply wellHidden_weakening with (m2:= m); auto.
    - unfold getCalls; simpl.
      apply SubList_app_3; [|apply SubList_app_2, SubList_refl].
      clear -Hdm.
      induction (getRules m); [apply SubList_nil|].
      apply SubList_app_3.
      + destruct (string_dec _ _).
        * simpl.
          pose proof (inlineDm_calls _ _ Hdm (attrType a typeUT)).
          apply SubList_trans with (l2:= getCallsA (attrType a typeUT)
                                                   ++ getCallsM (getDefsBodies m)); auto.
          apply SubList_app_3.
          { apply SubList_app_1, SubList_app_1, SubList_refl. }
          { apply SubList_app_2, SubList_refl. }
        * simpl.
          apply SubList_app_1, SubList_app_1, SubList_refl.
      + fold getCallsR.
        apply SubList_trans with (l2:= getCallsR l ++ getCallsM (getDefsBodies m)); auto.
        apply SubList_app_3.
        * apply SubList_app_1, SubList_app_2, SubList_refl.
        * apply SubList_app_2, SubList_refl.
    - apply SubList_refl.
  Qed.

  Lemma inlineDmToRule_stepInd:
    forall o u l,
      StepInd m o u l ->
      StepInd
        (Mod (getRegInits m)
             (map
                (fun newr =>
                   if string_dec (attrName r) (attrName newr)
                   then inlineDmToRule newr dm else newr)
                (getRules m)) (getDefsBodies m)) o u l.
  Proof.
    intros; inv H.

    destruct l0 as [ann ds cs].
    assert (ann = Some (Some (attrName r)) \/ ~ ann = Some (Some (attrName r))).
    { destruct ann; [|right; discriminate].
      destruct o0; [|right; discriminate].
      destruct (string_dec s (attrName r)).
      { subst; left; reflexivity. }
      { right; intro Hx; inv Hx; elim n; reflexivity. }
    }

    destruct H.

    - subst.
      pose proof (substepsInd_rule_split HSubSteps) as Hsp.
      clear HSubSteps.
      specialize (Hsp _ eq_refl).
      destruct Hsp as [ru [rcs [pu [pl ?]]]]; dest; subst.

      remember (M.find (attrName dm) rcs) as odr; destruct odr.

      + rewrite <-hideMeth_preserves_hide with (dm:= attrName dm).
        constructor.
        * destruct pl as [pann pds pcs]; inv H3.
          inv H1; dest; simpl in *; mred.
          destruct pann; [inv H3|].
          eapply inlineDmToRule_substepsInd_sub; eauto.

          clear -Hdm Heqodr HWellHidden.
          apply wellHidden_find_1 with (a:= attrName dm) in HWellHidden.
          { simpl in *; destruct HWellHidden; mred. }
          { apply in_map; auto. }
          
        * rewrite hideMeth_preserves_hide.
          apply inlineDmToRule_wellHidden; auto.

      + destruct pl as [pann pds pcs]; simpl in *.
        remember (M.find (attrName dm) pcs) as odp; destruct odp.

        * econstructor.
          { mred; inv H3; clear H4.
            inv H1; dest; simpl in *.
            destruct pann; [inv H3|].
            apply inlineDmToRule_substepsInd_intact_2; auto.
          }
          { apply inlineDmToRule_wellHidden; auto. }

        * econstructor.
          { apply inlineDmToRule_substepsInd_intact_1; auto.
            { econstructor; eauto. }
            { simpl; intro Hx; dest.
              elim H4; clear H4.
              inv H3; findeq.
            }
          }
          { apply inlineDmToRule_wellHidden; auto. }

    - econstructor.
      + apply inlineDmToRule_substepsInd_intact_1; auto.
        simpl; intro Hx; dest; elim H; auto.
      + apply inlineDmToRule_wellHidden; auto.

  Qed.

  Lemma inlineDmToRule_traceRefines_1:
    m <<== (Mod (getRegInits m)
                (map (fun newr =>
                        if string_dec (attrName r) (attrName newr)
                        then inlineDmToRule newr dm
                        else newr) (getRules m))
                (getDefsBodies m)).
  Proof.
    apply stepRefinement with (ruleMap:= fun _ s => Some s) (theta:= id); auto.
    intros; exists u; split; auto.

    rewrite idElementwiseId.
    replace (liftPLabel _ _ _ _) with l; [|destruct l as [[[|]|] ? ?]; simpl; f_equal].
    unfold id.

    clear H.
    apply step_consistent; apply step_consistent in H0.
    apply inlineDmToRule_stepInd; auto.
  Qed.

  Hypotheses (Hequiv: ModEquiv type typeUT m)
             (HrCalls: In (attrName dm) (getCallsA (attrType r typeUT)))
             (HnoRuleCalls: forall rule,
                 In rule (getRules m) ->
                 attrName rule <> attrName r ->
                 noCallDmSigA (attrType rule typeUT)
                              (attrName dm) (projT1 (attrType dm)) = true)
             (HnoMethCalls: forall meth,
                 In meth (getDefsBodies m) ->
                 noCallDmSigA (projT2 (attrType meth) typeUT tt)
                              (attrName dm) (projT1 (attrType dm)) = true).

  Lemma getCallsA_getCalls_In:
    In (attrName dm) (getCalls m).
  Proof.
    unfold getCalls.
    apply in_or_app; left.
    clear -Hrule HrCalls.
    induction (getRules m); auto.
    destruct Hrule; [subst|].
    - simpl; apply in_or_app; left; auto.
    - simpl; apply in_or_app; right; auto.
  Qed.

  Lemma inlineDmToRule_noDup:
    NoDup (namesOf (getDefsBodies (Mod (getRegInits m)
                                       (map
                                          (fun newr =>
                                             if string_dec (attrName r) (attrName newr)
                                             then inlineDmToRule newr dm else newr)
                                          (getRules m))
                                       (getDefsBodies m)))).
  Proof. simpl; auto. Qed.

  Lemma inlineDmToRule_In:
    In dm (getDefsBodies (Mod (getRegInits m)
                              (map
                                 (fun newr =>
                                    if string_dec (attrName r) (attrName newr)
                                    then inlineDmToRule newr dm else newr)
                                 (getRules m))
                              (getDefsBodies m))).
  Proof. simpl; auto. Qed.

  Lemma inlineDmToRule_ModEquiv:
    ModEquiv type typeUT (Mod (getRegInits m)
                              (map (fun newr =>
                                      if string_dec (attrName r) (attrName newr)
                                      then inlineDmToRule newr dm
                                      else newr) (getRules m))
                              (getDefsBodies m)).
  Proof.
    clear -Hequiv Hdm.
    assert (MethEquiv type typeUT dm).
    { inv Hequiv.
      rewrite MethsEquiv_in in H0.
      apply H0; auto.
    }
    inv Hequiv.
    constructor; simpl; auto; clear H1.
    induction H0; simpl; [constructor|].
    constructor; auto.
    destruct (string_dec _ _); auto.
    apply inlineDm_ActionEquiv; auto.
  Qed.

  Lemma inlineDmToRule_traceRefines_2:
    m <<== (Mod (getRegInits m)
                (map (fun newr =>
                        if string_dec (attrName r) (attrName newr)
                        then inlineDmToRule newr dm
                        else newr) (getRules m))
                (filterDm (getDefsBodies m) (attrName dm))).
  Proof.
    apply stepRefinement with (ruleMap:= fun _ s => Some s) (theta:= id); auto.
    intros; exists u; split; auto.

    rewrite idElementwiseId.
    replace (liftPLabel _ _ _ _) with l; [|destruct l as [[[|]|] ? ?]; simpl; f_equal].
    unfold id.

    clear H.
    apply step_consistent; apply step_consistent in H0.

    pose proof (inlineDmToRule_stepInd H0).
    
    apply stepInd_filterDm; auto.

    - apply inlineDmToRule_ModEquiv.
    - inv H0; pose proof getCallsA_getCalls_In.
      clear -HWellHidden H0.
      destruct (hide l0) as [ann ds cs].
      unfold wellHidden in HWellHidden; dest; simpl in *.
      specialize (H (attrName dm) H0).
      findeq.
    - constructor; simpl.
      + apply Forall_forall; intros.
        destruct (string_dec (attrName r) (attrName x)).
        * apply in_map_iff in H1; dest.
          destruct (string_dec _ _); subst; auto.
          apply inlineDmToRule_noCallDmSigA; auto.
        * apply HnoRuleCalls; auto.
          apply in_map_iff in H1; dest.
          destruct (string_dec _ _); subst; auto.
          elim n; auto.
      + apply Forall_forall; intros.
        apply HnoMethCalls; auto.
  Qed.

End Partial.

