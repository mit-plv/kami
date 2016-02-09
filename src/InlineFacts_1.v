Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct Lib.StringBound Lib.ilist Lib.Word Lib.FMap.
Require Import Syntax SemanticsExprAction Wf Equiv Inline.

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
      destruct (string_dec _ _); [|discriminate].
      subst; rewrite M.find_add_1 in H0; inv H0.
    + subst.
      unfold getBody in Heqomb.
      destruct (string_dec _ _);
        [subst; rewrite M.find_add_1 in H0; inv H0|].
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
    forall {retK2} a (Ha: WfAction nil nil a)
           u2 cm2 (retV2: type retK2),
      M.Disj u1 u2 -> M.Disj cm1 cm2 ->
      Some (existT _ (projT1 (attrType meth))
                   (argV, retV1)) =
      M.find meth cm2 ->
      SemAction or a u2 cm2 retV2 ->
      SemAction or (inlineDm a meth) (M.union u1 u2)
                (M.union cm1 (M.remove meth cm2))
                retV2.
Proof.
  induction a; intros; simpl.

  - inv H4; destruct_existT.
    remember (getBody meth0 meth s) as ob; destruct ob.
    + unfold getBody in Heqob.
      destruct (string_dec meth0 meth); [subst|inv Heqob].
      destruct (SignatureT_dec _ _); [|inv Heqob].
      generalize dependent HSemAction; inv Heqob; intros.
      rewrite M.find_add_1 in H3.
      inv H3; destruct_existT.
      simpl; constructor.

      eapply appendAction_SemAction; eauto.
      inv Ha; destruct_existT.
      pose proof (wfAction_SemAction_calls
                    (H7 mret) HSemAction
                    meth (or_introl eq_refl)).
      rewrite M.remove_add.
      rewrite M.remove_find_None by assumption.

      destruct meth; apply inlineDm_SemAction_intact; auto.

    + unfold getBody in Heqob.
      destruct (string_dec meth0 meth).

      * subst; destruct (SignatureT_dec _ _); [inv Heqob|].

        econstructor.
        { instantiate (1:= M.union cm1 (M.remove meth calls)).
          instantiate (1:= mret).
          meq.
          elim n. clear -H3.
          inv H3; destruct_existT; auto.
        }
        { apply H0; auto.
          { inv Ha; destruct_existT.
            eapply wfAction_calls_weakening; eauto.
            apply SubList_nil.
          }
          { elim n.
            rewrite M.find_add_1 in H3.
            clear -H3; inv H3; destruct_existT; auto.
          }
        }

      * econstructor.
        { instantiate (1:= M.union cm1 (M.remove meth calls)).
          instantiate (1:= mret).
          meq.
        }
        { apply H0; auto.
          { inv Ha; destruct_existT.
            eapply wfAction_calls_weakening; eauto.
            apply SubList_nil.
          }
          { rewrite M.find_add_2 in H3 by auto; auto. }
        }
        
  - inv H4; inv Ha; destruct_existT.
    constructor; auto.
  - inv H4; inv Ha; destruct_existT.
    econstructor; eauto.
  - inv H3; inv Ha; destruct_existT.
    econstructor; eauto.

    + instantiate (1:= M.union u1 newRegs).
      meq.
    + apply IHa; auto.
      * eapply wfAction_regs_weakening; eauto.
        apply SubList_nil.

  - inv Ha; destruct_existT.
    inv H4; destruct_existT.
    + rewrite M.find_union in H3.
      remember (M.find meth calls1) as omv1; destruct omv1.
      * remember (M.find meth calls2) as omv2; destruct omv2.
        { exfalso.
          pose proof (wfAction_appendAction_calls_disj _ H10 HAction HSemAction).
          specialize (H4 meth); destruct H4; elim H4.
          { apply M.F.P.F.in_find_iff; rewrite <-Heqomv1; discriminate. }
          { apply M.F.P.F.in_find_iff; rewrite <-Heqomv2; discriminate. }
        }
        { inv H3.
          rewrite M.union_assoc, M.remove_union, M.union_assoc.
          eapply SemIfElseTrue; eauto.
          { eapply IHa1; eauto.
            eapply wfAction_appendAction_calls_1; eauto.
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

        assert (M.union cm1 (M.remove meth (M.union calls1 calls2)) =
                M.union (M.remove meth calls1) (M.union cm1 (M.remove meth calls2))).
        { rewrite M.remove_union, M.union_assoc.
          rewrite M.union_comm with (m1:= cm1);
            [|apply M.Disj_remove_2; eapply M.Disj_union_1; eauto].
          rewrite <-M.union_assoc; auto.
        }
        rewrite H4; clear H4.
        eapply SemIfElseTrue; eauto.
        { rewrite M.remove_find_None by auto.
          destruct meth; eapply inlineDm_SemAction_intact; eauto.
        }
        { apply H0; auto.
          eapply wfAction_appendAction_calls_2; eauto.
        }
        
    + rewrite M.find_union in H3.
      remember (M.find meth calls1) as omv1; destruct omv1.
      * remember (M.find meth calls2) as omv2; destruct omv2.
        { exfalso.
          pose proof (wfAction_appendAction_calls_disj _ H14 HAction HSemAction).
          specialize (H4 meth); destruct H4; elim H4.
          { apply M.F.P.F.in_find_iff; rewrite <-Heqomv1; discriminate. }
          { apply M.F.P.F.in_find_iff; rewrite <-Heqomv2; discriminate. }
        }
        { inv H3.
          rewrite M.union_assoc, M.remove_union, M.union_assoc.
          eapply SemIfElseFalse; eauto.
          { eapply IHa2; eauto.
            eapply wfAction_appendAction_calls_1; eauto.
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

        assert (M.union cm1 (M.remove meth (M.union calls1 calls2)) =
                M.union (M.remove meth calls1) (M.union cm1 (M.remove meth calls2))).
        { rewrite M.remove_union, M.union_assoc.
          rewrite M.union_comm with (m1:= cm1);
            [|apply M.Disj_remove_2; eapply M.Disj_union_1; eauto].
          rewrite <-M.union_assoc; auto.
        }
        rewrite H4; clear H4.
        eapply SemIfElseFalse; eauto.
        { rewrite M.remove_find_None by auto.
          destruct meth; eapply inlineDm_SemAction_intact; eauto.
        }
        { apply H0; auto.
          eapply wfAction_appendAction_calls_2; eauto.
        }

  - inv H3; inv Ha; destruct_existT.
    constructor; auto.

  - inv H3; inv Ha; destruct_existT.
    rewrite M.find_empty in H2; inv H2.
Qed.

Lemma isLeaf_SemAction_calls:
  forall {retK} G aU aT,
    ActionEquiv (k:= retK) G aU aT ->
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
      destruct (in_dec _ n lcalls); [inv H1|elim n0; auto].
    + simpl in H1.
      destruct (in_dec _ n lcalls); [inv H1|].
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
    eapply IHActionEquiv; eauto.
  - inv H4.
    apply andb_true_iff in H8; dest.
    apply andb_true_iff in H4; dest.
    inv H5; destruct_existT; rewrite M.find_union.
    + erewrite IHActionEquiv1; eauto.
    + erewrite IHActionEquiv2; eauto.
  - inv H2; destruct_existT.
    simpl in H1.
    eapply IHActionEquiv; eauto.
  - inv H1; destruct_existT.
    rewrite M.find_empty; auto.
Qed.

Lemma noCallDm_SemAction_calls:
  forall mn (mb: sigT MethodT) G or nr calls argV retV
         (Hmb: ActionEquiv G (projT2 mb typeUT tt)
                           (projT2 mb type argV)),
    noCallDm (mn :: mb)%struct (mn :: mb)%struct = true ->
    SemAction or (projT2 mb type argV) nr calls retV ->
    M.find (elt:=sigT SignT) mn calls = None.
Proof.
  intros; unfold noCallDm in H; simpl in H.
  eapply isLeaf_SemAction_calls; eauto.
Qed.

