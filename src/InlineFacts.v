Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct Lib.StringBound.
Require Import Lib.ilist Lib.Word Lib.FMap Lib.StringEq.
Require Import Syntax Semantics SemFacts Refinement Equiv Inline.

Require Import FunctionalExtensionality.

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
  - inv H3; destruct_existT.
    constructor 4 with (newRegs := M.union u1 newRegs).
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
  pose proof (inlineDmToMod_wellHidden m l a H) as iwh.
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
  pose proof (inline_correct_Step _ Hequiv Hdms Hit _ _ _ H).
  rewrite <-Heqimb in H0; simpl in H0.
  pose proof (step_dms_hidden _ _ _ _ H).
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

