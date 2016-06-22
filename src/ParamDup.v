Require Import String List FunctionalExtensionality.
Require Import Lib.CommonTactics Lib.Word Lib.Struct Lib.FMap Lib.Concat Lib.Indexer.
Require Import Syntax Semantics SemFacts Equiv Wf.
Require Import Specialize Duplicate Refinement Renaming ParametricSyntax.

Lemma getMetaRegName_sinRegs:
  forall {A} (strA: A -> string) Hgood1 Hgood2 {ls} (HnoDup: NoDup ls) sregs,
    map getMetaRegName (regsToRep strA Hgood1 Hgood2 HnoDup sregs) =
    map (fun sr => nameVal (regName sr)) sregs.
Proof.
  induction sregs; simpl; intros; auto.
  destruct a; simpl; f_equal; auto.
Qed.

Lemma EquivList_cons:
  forall {A} (a1 a2: A) l1 l2,
    EquivList l1 l2 -> a1 = a2 -> EquivList (a1 :: l1) (a2 :: l2).
Proof.
  intros; inv H; subst; split;
    try (apply SubList_cons; [left; auto|apply SubList_cons_right; auto]).
Qed.

Lemma hasNoIndex_app_inv:
  forall l1 l2,
    hasNoIndex (l1 ++ l2) = true ->
    hasNoIndex l1 = true /\ hasNoIndex l2 = true.
Proof.
  induction l1; simpl; intros; auto.
  destruct (index _ _ _); auto; inv H.
Qed.

Lemma getGenAction_convSinToGen_renameAction:
  forall genK getConst i {ty retK} (a: SinActionT ty retK),
    getGenAction string_of_nat getConst i (convSinToGen true genK a) =
    renameAction (spf i) (getSinAction a).
Proof.
  induction a; simpl; auto;
    try (f_equal; extensionality v; auto).
  - f_equal; auto.
  - f_equal; auto.
    extensionality v; auto.
  - f_equal; auto.
Qed.

Lemma renameAction_specializer_rules:
  forall regs rules dms i {ty} rn (a: Action Void),
    In (rn :: a)%struct rules ->
    Specializable (Mod regs rules dms) ->
    Wf.ValidRegsAction (namesOf regs) (a ty) ->
    ActionEquiv (a ty) (a typeUT) ->
    renameAction (specializer (Mod regs rules dms) i) (a ty) =
    renameAction (spf i) (a ty).
Proof.
  intros; apply renameAction_spDom_weakening with (regs:= namesOf regs) (au:= a typeUT); auto.
  intros; apply specializer_dom; auto.
  apply in_app_or in H3; destruct H3.
  - unfold spDom; apply makeNoDup_SubList_2.
    apply in_or_app; left; auto.
  - unfold spDom; apply makeNoDup_SubList_2.
    do 3 (apply in_or_app; right).
    apply in_or_app; left; simpl.

    clear -H H3; induction rules; [inv H|].
    inv H.
    + simpl; apply in_or_app; left; auto.
    + simpl; apply in_or_app; right; auto.
Qed.

Section SinModuleDup.

  Lemma Specializable_weakening:
    forall m1 m2,
      Specializable m1 ->
      SubList (namesOf (getRegInits m2)) (namesOf (getRegInits m1)) ->
      SubList (namesOf (getRules m2)) (namesOf (getRules m1)) ->
      SubList (getDefs m2) (getDefs m1) ->
      SubList (getCalls m2) (getCalls m1) ->
      Specializable m2.
  Proof.
    unfold Specializable, spDom; intros.
    rewrite <-hasNoIndex_makeNoDup in *.
    eapply hasNoIndex_SubList; eauto.
    repeat (apply SubList_app_6; auto).
  Qed.

  Lemma specializer_weakening_rules:
    forall regs erules1 erules2 dms i rules,
      Specializable (Mod regs erules1 dms) ->
      Specializable (Mod regs erules2 dms) ->
      (forall ty, RulesEquiv ty typeUT rules) ->
      (forall ty, ValidRegsRules ty (namesOf regs) rules) ->
      SubList rules erules1 ->
      SubList rules erules2 ->
      renameRules (specializer (Mod regs erules1 dms) i) rules =
      renameRules (specializer (Mod regs erules2 dms) i) rules.
  Proof.
    induction rules; simpl; intros; auto.
    f_equal.
    - destruct a as [an ar]; simpl; f_equal.
      + rewrite specializer_dom; auto.
        * rewrite specializer_dom; auto.
          unfold spDom; apply makeNoDup_SubList_2.
          apply in_or_app; right.
          apply in_or_app; left; simpl.
          apply SubList_map with (f:= @attrName _) in H4; simpl in H4.
          apply H4; left; auto.
        * unfold spDom; apply makeNoDup_SubList_2.
          apply in_or_app; right.
          apply in_or_app; left; simpl.
          apply SubList_map with (f:= @attrName _) in H3; simpl in H3.
          apply H3; left; auto.
      + extensionality ty.
        repeat (rewrite renameAction_specializer_rules with (rn:= an); auto).
        * apply SubList_cons_inv in H4; dest; auto.
        * specialize (H2 ty); inv H2; auto.
        * specialize (H1 ty); inv H1; auto.
        * apply SubList_cons_inv in H3; dest; auto.
        * specialize (H2 ty); inv H2; auto.
        * specialize (H1 ty); inv H1; auto.
    - apply IHrules; auto.
      + intros; specialize (H1 ty); inv H1; auto.
      + intros; specialize (H2 ty); inv H2; auto.
      + eapply SubList_cons_inv; eauto.
      + eapply SubList_cons_inv; eauto.
  Qed.

  Lemma renameListAttr_specializer_regs:
    forall eregs regs rules dms i,
      Specializable (Mod eregs rules dms) ->
      SubList regs eregs ->
      renameListAttr (specializer (Mod eregs rules dms) i) regs =
      renameListAttr (spf i) regs.
  Proof.
    induction regs; simpl; intros; auto.
    f_equal.
    - unfold renameAttr; f_equal.
      apply specializer_dom; auto.
      unfold spDom; apply makeNoDup_SubList_2.
      apply in_or_app; left; simpl.
      apply in_map; apply H0; left; auto.
    - apply IHregs; auto.
      apply SubList_cons_inv in H0; dest; auto.
  Qed.

  Lemma regsToRep_duplicate_regs_equiv:
    forall rules dms n (l: list (SinReg nat)),
      (forall sr, In sr l -> forall i j, regGen sr i = regGen sr j) ->
      Specializable (Mod (map (fun sr => (nameVal (regName sr) :: regGen sr 0)%struct) l)
                         rules dms) ->
      EquivList
        (concat
           (map getListFromMetaReg
                (regsToRep string_of_nat string_of_nat_into withIndex_index_eq
                           (getNatListToN_NoDup n) l)))
        (getRegInits
           (duplicate
              (Mod (map (fun sr => (nameVal (regName sr) :: regGen sr 0)%struct) l)
                   rules dms) n)).
  Proof.
    intros; induction l; [simpl; induction n; [apply EquivList_nil|auto]|].
    destruct a as [arg arn]; simpl.

    assert (EquivList
              ((getListFromRep string_of_nat arg (nameVal arn) (getNatListToN n))
                 ++ (getRegInits
                       (duplicate
                          (Mod (map (fun sr => (nameVal (regName sr) :: regGen sr 0)%struct) l)
                               rules dms) n)))
              (getRegInits
                 (duplicate
                    (Mod
                       (((nameVal arn :: arg 0)%struct)
                          :: map (fun sr => (nameVal (regName sr) :: regGen sr 0)%struct) l)
                       rules dms) n))).
    { clear -H H0.
      simpl in H0; generalize dependent H0.
      generalize (map (fun sr => (nameVal (regName sr) :: regGen sr 0)%struct) l) as ml.
      intros.
      assert (Specializable (Mod ml rules dms)).
      { eapply Specializable_weakening; eauto;
        try (unfold getDefs, getCalls; simpl; apply SubList_refl).
        simpl; apply SubList_cons_right, SubList_refl.
      }
      generalize dependent n; induction n.
      
      - simpl; apply EquivList_cons.
        + rewrite renameListAttr_specializer_regs; [|auto|apply SubList_refl].
          rewrite renameListAttr_specializer_regs; [|auto|apply SubList_cons_right, SubList_refl].
          apply EquivList_refl.
        + unfold renameAttr; simpl; f_equal.
          rewrite specializer_dom; auto.
          apply makeNoDup_SubList_2; left; auto.
      - generalize dependent IHn.
        unfold duplicate at 3. fold (duplicate (Mod ml rules dms)).
        generalize (duplicate (Mod ml rules dms) n) as nm1.
        unfold duplicate at 2.
        fold (duplicate (Mod ((nameVal arn :: arg 0)%struct :: ml) rules dms)).
        generalize (duplicate (Mod ((nameVal arn :: arg 0)%struct :: ml) rules dms) n) as nm2.
        simpl.
        generalize (getListFromRep string_of_nat arg (nameVal arn) (getNatListToN n)) as rr1.
        rewrite renameListAttr_specializer_regs; [|auto|apply SubList_refl].
        rewrite renameListAttr_specializer_regs; [|auto|apply SubList_cons_right, SubList_refl].
        generalize (renameListAttr (spf (S n)) ml) as rr2.
        intros.

        apply EquivList_cons.
        + inv IHn; split.
          * repeat apply SubList_app_3.
            { eapply SubList_app_2, SubList_app_4; eauto. }
            { apply SubList_app_1, SubList_refl. }
            { eapply SubList_app_2, SubList_app_5; eauto. }
          * repeat apply SubList_app_3.
            { apply SubList_app_2, SubList_app_1, SubList_refl. }
            { apply SubList_app_comm; rewrite <-app_assoc.
              apply SubList_app_2, SubList_app_comm; auto.
            }
        + unfold renameAttr; rewrite specializer_dom; auto.
          * f_equal; simpl. 
            specialize (H {| regGen := arg; regName := arn |}).
            apply H; left; auto.
          * simpl; unfold spDom; apply makeNoDup_SubList_2.
            apply in_or_app; left.
            left; auto.
    }

    eapply EquivList_trans; [|apply H1]; clear H1.
    apply EquivList_app; [apply EquivList_refl|].
    apply IHl.
    - clear -H; intros; apply H; right; auto.
    - clear -H0.
      eapply Specializable_weakening; eauto;
        try (unfold getDefs, getCalls; simpl; apply SubList_refl).
      simpl; apply SubList_cons_right, SubList_refl.
  Qed.

  Lemma rulesToRep_duplicate_rules_equiv:
    forall regs dms {genK} (getConst: nat -> ConstT genK) n (l: list SinRule),
      (forall ty, RulesEquiv ty typeUT
                             (map (fun sr => ((nameVal (ruleName sr))
                                                :: getActionFromSin (ruleGen sr))%struct) l)) ->
      (forall ty, ValidRegsRules ty (namesOf regs)
                                 (map (fun sr => ((nameVal (ruleName sr))
                                                    :: getActionFromSin (ruleGen sr))%struct) l)) ->
      Specializable
        (Mod regs (map (fun sr => (nameVal (ruleName sr)
                                           :: getActionFromSin (ruleGen sr))%struct) l) dms) ->
      EquivList
        (concat
           (map getListFromMetaRule
                (rulesToRep string_of_nat string_of_nat_into getConst withIndex_index_eq 
                            (getNatListToN_NoDup n) 
                            l)))
        (getRules
           (duplicate
              (Mod regs (map (fun sr => (nameVal (ruleName sr)
                                                 :: getActionFromSin (ruleGen sr))%struct) 
                             l) dms) n)).
  Proof.
    intros; induction l; [simpl; induction n; [apply EquivList_nil|auto]|].
    destruct a as [arg arn]; simpl.

    assert (EquivList
              ((repRule string_of_nat getConst (fun ty => convSinToGen true genK (arg ty))
                        (nameVal arn) (getNatListToN n))
                 ++ (getRules
                       (duplicate
                          (Mod regs
                               (map (fun sr => ((nameVal (ruleName sr))
                                                  :: getActionFromSin (ruleGen sr))%struct)
                                    l) dms) n)))
              (getRules
                 (duplicate
                    (Mod regs
                         (((nameVal arn :: getActionFromSin arg)%struct)
                            :: (map
                                  (fun sr : SinRule =>
                                     ((nameVal (ruleName sr))
                                        :: getActionFromSin (ruleGen sr))%struct)
                                  l)) dms) n))).
    { clear -H H0 H1.
      simpl in H; generalize dependent H.
      simpl in H0; generalize dependent H0.
      simpl in H1; generalize dependent H1.
      generalize (map (fun sr => ((nameVal (ruleName sr))
                                    :: getActionFromSin (ruleGen sr))%struct)
                      l) as ml.
      intros.
      assert (Specializable (Mod regs ml dms)).
      { eapply Specializable_weakening; eauto; try (unfold getDefs; simpl; apply SubList_refl).
        { simpl; apply SubList_cons_right, SubList_refl. }
        { unfold getCalls; simpl.
          rewrite <-app_assoc; apply SubList_app_2, SubList_refl.
        }
      }
      generalize dependent n; induction n.
      
      - simpl; apply EquivList_cons.
        + rewrite specializer_weakening_rules with
          (erules1:= (nameVal arn :: getActionFromSin arg)%struct :: ml)
            (erules2:= ml); auto.
          * apply EquivList_refl.
          * intros; specialize (H ty); inv H; auto.
          * intros; specialize (H0 ty); inv H0; auto.
          * apply SubList_cons_right, SubList_refl.
          * apply SubList_refl.
        + f_equal.
          * rewrite specializer_dom; auto.
            apply makeNoDup_SubList_2.
            apply in_or_app; right.
            apply in_or_app; left.
            simpl; auto.
          * unfold getActionFromGen, getActionFromSin.
            extensionality ty.
            change (getSinAction (arg ty)) with ((fun ty0 => getSinAction (arg ty0)) ty).
            rewrite renameAction_specializer_rules with (rn:= nameVal arn); auto.
            { apply getGenAction_convSinToGen_renameAction. }
            { left; auto. }
            { specialize (H0 ty); inv H0; auto. }
            { specialize (H ty); inv H; auto. }
            
      - generalize dependent IHn.
        unfold duplicate at 3. fold (duplicate (Mod regs ml dms)).
        generalize (duplicate (Mod regs ml dms) n) as nm1.
        unfold duplicate at 2.
        fold (duplicate
                (Mod regs ((nameVal arn :: getActionFromSin arg)%struct :: ml) dms)).
        generalize (duplicate
                      (Mod regs ((nameVal arn :: getActionFromSin arg)%struct :: ml) dms)
                      n) as nm2.
        simpl.
        generalize (repRule string_of_nat getConst
                            (fun ty =>
                               convSinToGen true genK (arg ty)) (nameVal arn)
                            (getNatListToN n)) as rr1.
        rewrite specializer_weakening_rules with
        (erules1:= (nameVal arn :: getActionFromSin arg)%struct :: ml)
          (erules2:= ml); auto.
        5:(apply SubList_refl).
        4:(apply SubList_cons_right, SubList_refl).
        3:(intros; specialize (H0 ty); inv H0; auto).
        2:(intros; specialize (H ty); inv H; auto).

        generalize (renameRules (specializer (Mod regs ml dms) (S n)) ml) as rr2.
        intros.

        apply EquivList_cons.
        + inv IHn; split.
          * repeat apply SubList_app_3.
            { eapply SubList_app_2, SubList_app_4; eauto. }
            { apply SubList_app_1, SubList_refl. }
            { eapply SubList_app_2, SubList_app_5; eauto. }
          * repeat apply SubList_app_3.
            { apply SubList_app_2, SubList_app_1, SubList_refl. }
            { apply SubList_app_comm; rewrite <-app_assoc.
              apply SubList_app_2, SubList_app_comm; auto.
            }
        + rewrite specializer_dom; auto.
          * f_equal; simpl.
            unfold getActionFromGen; extensionality ty.
            unfold getActionFromSin.
            change (getSinAction (arg ty)) with ((fun ty0 => getSinAction (arg ty0)) ty).
            rewrite renameAction_specializer_rules with (rn:= nameVal arn); auto.
            { apply getGenAction_convSinToGen_renameAction. }
            { left; auto. }
            { specialize (H0 ty); inv H0; auto. }
            { specialize (H ty); inv H; auto. }
          * simpl; unfold spDom; apply makeNoDup_SubList_2.
            apply in_or_app; right.
            apply in_or_app; left.
            left; auto.
    }

    eapply EquivList_trans; [|apply H2]; clear H2.
    apply EquivList_app; [apply EquivList_refl|].
    apply IHl.
    - intros; specialize (H ty); inv H; auto.
    - intros; specialize (H0 ty); inv H0; auto.
    - clear -H1.
      eapply Specializable_weakening; eauto; try (unfold getDefs; simpl; apply SubList_refl).
      + simpl; apply SubList_cons_right, SubList_refl.
      + unfold getCalls; simpl.
        rewrite <-app_assoc; apply SubList_app_2, SubList_refl.
  Qed.

  Variable sm: SinModule nat.
  Hypotheses
    (* Hsp is provable generally, but fine to prove for each instantiation *)
    (Hsp: Specializable (getModFromSin sm))
    (Hequiv: forall ty, ModEquiv ty typeUT (getModFromSin sm))
    (Hvr: forall ty, ValidRegsModules ty (getModFromSin sm))
    (HnoDupRegs: NoDup (map (fun sr => nameVal (regName sr)) (sinRegs sm)))
    (HregInits: forall sr, In sr (sinRegs sm) -> forall i j, regGen sr i = regGen sr j).

  Lemma sinModule_duplicate_1:
    forall n, (modFromMeta (getMetaFromSinNat n sm) <<==
                           duplicate (getModFromSin sm) (wordToNat (wones n))).
  Proof.
    intros; unfold MethsT; rewrite SemFacts.idElementwiseId.
    apply traceRefines_same_module_structure.
    - apply noDup_metaRegs.
      simpl; rewrite getMetaRegName_sinRegs; auto.
    - apply duplicate_regs_NoDup; auto.
      p_equal HnoDupRegs; unfold getModFromSin; simpl.
      clear; induction (sinRegs sm); simpl; auto.
      f_equal; auto.
    - apply regsToRep_duplicate_regs_equiv; auto.
    - apply rulesToRep_duplicate_rules_equiv; auto.
      + intros; specialize (Hequiv ty); inv Hequiv; auto.
      + intros; specialize (Hvr ty); inv Hvr; auto.
    - admit.
  Qed.

  Lemma sinModule_duplicate_2:
    forall n, (duplicate (getModFromSin sm) (wordToNat (wones n)) <<==
                         modFromMeta (getMetaFromSinNat n sm)).
  Proof.
    intros; unfold MethsT; rewrite SemFacts.idElementwiseId.
    apply traceRefines_same_module_structure.
    - apply duplicate_regs_NoDup; auto.
      p_equal HnoDupRegs; unfold getModFromSin; simpl.
      clear; induction (sinRegs sm); simpl; auto.
      f_equal; auto.
    - apply noDup_metaRegs.
      simpl; rewrite getMetaRegName_sinRegs; auto.
    - apply EquivList_comm, regsToRep_duplicate_regs_equiv; auto.
    - apply EquivList_comm, rulesToRep_duplicate_rules_equiv; auto.
      + intros; specialize (Hequiv ty); inv Hequiv; auto.
      + intros; specialize (Hvr ty); inv Hvr; auto.
    - admit.
  Qed.

End SinModuleDup.

