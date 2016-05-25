Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct Lib.StringBound.
Require Import Lib.ilist Lib.Word Lib.FMap Lib.StringEq.
Require Import Syntax Semantics SemFacts Equiv Inline InlineFacts_1 InlineFacts_2 Tactics.
Require Import Refinement.

Set Implicit Arguments.

Lemma substepsInd_defs_sig:
  forall m dm,
    NoDup (getDefs m) ->
    In dm (getDefsBodies m) ->
    forall o u l,
      SubstepsInd m o u l ->
      forall s,
        Some s = M.find (elt:=sigT SignT) (attrName dm) (defs l) ->
        projT1 s = projT1 (attrType dm).
Proof.
  induction 3; simpl; intros; [mred|].
  subst; destruct sul as [|odm].

  - apply IHSubstepsInd.
    destruct l as [ann ds cs]; simpl in *; findeq.

  - destruct odm as [dm'|].
    + destruct dm as [dmn dmb], dm' as [dmn' dmb'], l as [ann ds cs]; simpl in *.
      destruct (string_dec dmn dmn').
      * subst; mred.
        inv H2; inv Hsig; simpl in *.
        destruct f as [fn fb]; simpl in *.
        f_equal.
        assert ((fn :: fb)%struct = (fn :: dmb)%struct).
        { eapply in_NoDup_attr; eauto. }
        inv H2; auto.
      * apply IHSubstepsInd; findeq.
    + apply IHSubstepsInd.
      destruct l as [ann ds cs]; simpl in *; findeq.
Qed.

Section NoCallDmSig.
  Fixpoint noCallDmSigA {retT} (a: ActionT typeUT retT) (dmn: string) (dsig: SignatureT) :=
    match a with
    | MCall name sig _ cont =>
      ((negb (string_eq name dmn))
       || (if SignatureT_dec sig dsig then false else true))
        && (noCallDmSigA (cont tt) dmn dsig)
    | Let_ _ ar cont => noCallDmSigA (cont (getUT _)) dmn dsig
    | ReadReg reg k cont => noCallDmSigA (cont (getUT _)) dmn dsig
    | WriteReg reg _ e cont => noCallDmSigA cont dmn dsig
    | IfElse ce _ ta fa cont =>
      (noCallDmSigA ta dmn dsig) && (noCallDmSigA fa dmn dsig) && (noCallDmSigA (cont tt) dmn dsig)
    | Assert_ ae cont => noCallDmSigA cont dmn dsig
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
      simpl in H4; clear -H1 H4; subst.
      destruct (SignatureT_dec _ _); auto.
      discriminate.
    + apply string_eq_dec_neq in Heqndeq.
      rewrite M.find_add_2 in H3 by intuition.
      eapply H0; eauto.

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
  forall (dm: DefMethT) (Hdm: noCallDm dm dm = true)
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
    apply noCallDm_noCallDmSigA; auto.
  - simpl; rewrite <-Heqmd; simpl.
    destruct (SignatureT_dec _ _); [elim n; auto|].
    simpl; auto.
Qed.

Lemma inlineDmToRule_noCallDmSigA:
  forall (dm: DefMethT) (Hdm: noCallDm dm dm = true) r,
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

Lemma substep_label_weakening:
  forall regs rules dms dmn o u ul cs,
    Substep (Mod regs rules dms) o u ul cs ->
    None = M.find (elt:=sigT SignT) dmn (defs (getLabel ul cs)) ->
    None = M.find (elt:=sigT SignT) dmn (calls (getLabel ul cs)) ->
    Substep (Mod regs rules (filterDm dms dmn)) o u ul cs.
Proof.
  induction 1; simpl; intros; try (econstructor; eauto; fail).

  econstructor; eauto.
  simpl; apply filter_In; split; auto.
  destruct (string_dec _ _); subst; auto.
  mred.
Qed.

Lemma substepsInd_label_weakening:
  forall regs rules dms dmn o u l,
    SubstepsInd (Mod regs rules dms) o u l ->
    None = M.find (elt:=sigT SignT) dmn (defs l) ->
    None = M.find (elt:=sigT SignT) dmn (calls l) ->
    SubstepsInd (Mod regs rules (filterDm dms dmn)) o u l.
Proof.
  induction 1; simpl; intros; [constructor|subst].

  destruct l as [a d c]; simpl in *.
  econstructor.
  - apply IHSubstepsInd.
    + rewrite M.find_union in H4.
      match goal with
      | [H: None = match M.find dmn ?lm with Some _ => _ | None => _ end |- _] =>
        destruct (M.find dmn lm); [inv H|]
      end.
      auto.
    + rewrite M.find_union in H5.
      destruct (M.find dmn scs); [inv H5|]; auto.
  - apply substep_label_weakening; eauto.
    + rewrite M.find_union in H4; simpl.
      match goal with
      | [H: None = match M.find dmn ?lm with Some _ => _ | None => _ end |- _] =>
        destruct (M.find dmn lm); [inv H|]
      end.
      auto.
    + simpl; findeq.
  - inv H1; dest; simpl in *.
    repeat split; auto.
  - reflexivity.
  - reflexivity.
Qed.

Lemma wellHidden_weakening:
  forall l m1 m2,
    SubList (getCalls m1) (getCalls m2) ->
    SubList (getDefs m1) (getDefs m2) ->
    wellHidden m2 l ->
    wellHidden m1 l.
Proof.
  unfold wellHidden; intros.
  dest; split.
  - eapply M.KeysDisj_SubList; eauto.
  - eapply M.KeysDisj_SubList; eauto.
Qed.

Lemma filterDm_wellHidden:
  forall regs rules dms dmn l,
    wellHidden (Mod regs rules dms) l ->
    wellHidden (Mod regs rules (filterDm dms dmn)) l.
Proof.
  intros; eapply wellHidden_weakening; eauto.
  - apply SubList_app_3.
    + apply SubList_app_1, SubList_refl.
    + apply SubList_app_2; simpl.
      clear; induction dms; simpl; [apply SubList_nil|].
      destruct (string_dec _ _).
      * apply SubList_app_2; auto.
      * simpl; apply SubList_app_3.
        { apply SubList_app_1, SubList_refl. }
        { apply SubList_app_2; auto. }
  - unfold getDefs; simpl.
    apply SubList_map.
    unfold SubList; intros.
    unfold filterDm in H0; apply filter_In in H0; dest; auto.
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
    apply substepsInd_label_weakening; auto.
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
             (HnoCallDm: noCallDm dm dm = true)
             (HnoRuleCalls: forall rule,
                 In rule (getRules m) ->
                 attrName rule <> attrName r ->
                 noCallDmSigA (attrType rule typeUT)
                              (attrName dm) (projT1 (attrType dm)) = true)
                 (* ~ In (attrName dm) (getCallsA (attrType rule typeUT))) *)
             (HnoMethCalls: forall meth,
                 In meth (getDefsBodies m) ->
                 noCallDmSigA (projT2 (attrType meth) typeUT tt)
                              (attrName dm) (projT1 (attrType dm)) = true).
                 (* ~ In (attrName dm) (getCallsA (projT2 (attrType meth) typeUT tt))). *)

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

