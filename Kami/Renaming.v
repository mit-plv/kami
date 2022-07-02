Require Import Lib.FMap Lib.Struct Kami.Semantics Kami.Syntax String List Kami.RefinementFacts.
Require Import Program.Equality.

Require Import Lib.CommonTactics.

Set Implicit Arguments.
Set Asymmetric Patterns.

Lemma prepend1To1: forall c s1 s2: string, (c ++ s1)%string = (c ++ s2)%string -> s1 = s2.
Proof.
  induction c; simpl in *; intros.
  - intuition.
  - injection H; intros H'.
    intuition.
Qed.
#[global] Hint Resolve prepend1To1.

Section Rename.
  Variable i: string.
  Variable rename: string -> string.
  Variable rename1To1: forall s1 s2, rename s1 = rename s2 -> s1 = s2.

  Definition renameAttr A a := {| attrName := rename (@attrName A a); attrType := attrType a |}.
  
  Definition renameListAttr A (ls: list (Attribute A)) :=
    map (@renameAttr _) ls.

  Definition renameMap A (m: M.t A) :=
    M.fold (fun k v old => M.add (rename k) v old) m (M.empty _).

  Definition renameUnitLabel l :=
    match l with
      | Rle None => Rle None
      | Meth None => Meth None
      | Rle (Some r) => Rle (Some (rename r))
      | Meth (Some {| attrName := f; attrType := v |}) =>
        Meth (Some {| attrName := rename f; attrType := v |})
    end.

  Definition renameLabel l :=
    match l with
    | Build_LabelT annot defs calls =>
      Build_LabelT (match annot with
                    | Some (Some r) => Some (Some (rename r))
                    | x => x
                    end) (renameMap defs) (renameMap calls)
    end.

  Fixpoint renameAction k t (a: ActionT t k) :=
    match a with
    | MCall meth s e cont => MCall (rename meth) s e (fun v => renameAction (cont v))
    | Let_ lret' e cont => Let_ e (fun v => renameAction (cont v))
    | ReadNondet k cont => ReadNondet k (fun v => renameAction (cont v))
    | ReadReg r k cont => ReadReg (rename r) k (fun v => renameAction (cont v))
    | WriteReg r k e cont => WriteReg (rename r) e (renameAction cont)
    | IfElse e k t f cont => IfElse e (renameAction t) (renameAction f)
                                   (fun v => renameAction (cont v))
    | Assert_ e cont => Assert_ e (renameAction cont)
    | Displ ls cont => Displ ls (renameAction cont)
    | Return e => Return e
    end.

  Definition renameRules (rules: list (Attribute (Action Void))) :=
                              map (fun x => match x with
                                         | {| attrName := r;
                                              attrType := a |} =>
                                           {| attrName := rename r;
                                              attrType := fun ty => renameAction (a ty) |}
                                            end) rules.

  Lemma renameInRules k a rules:
    In (k :: a)%struct rules ->
    In (rename k :: fun ty => renameAction (a ty))%struct (renameRules rules).
  Proof.
    induction rules; simpl; intros.
    - intuition.
    - destruct H; subst; intros.
      + intuition.
      + specialize (IHrules H).
        right; intuition.
  Qed.

  Definition renameMeth (meth: DefMethT): DefMethT.
    refine match meth with
           | {| attrName := m;
                attrType := a |} =>
             {| attrName := rename m;
                attrType := existT _ (projT1 a) (fun ty v => _) |}
           end.
    exact (renameAction (projT2 a ty v)).
  Defined.

  Definition renameMeths (meths: list DefMethT): list DefMethT :=
    map renameMeth meths.

  Lemma renameInMeths f meths:
    In f meths ->
    In (renameMeth f) (renameMeths meths).
  Proof.
    induction meths; simpl; intros.
    - intuition.
    - destruct H; subst; intros.
      + intuition.
      + specialize (IHmeths H).
        right; intuition.
  Qed.

  Fixpoint renameModules (m: Modules) :=
    match m with
    | PrimMod prim =>
      PrimMod {| pm_name := prim.(pm_name);
                 pm_regInits := renameListAttr prim.(pm_regInits);
                 pm_rules := renameRules prim.(pm_rules);
                 pm_methods := renameMeths prim.(pm_methods)
              |}
    | Mod regs rules dms => Mod (renameListAttr regs) (renameRules rules) (renameMeths dms)
    | ConcatMod m1 m2 => ConcatMod (renameModules m1) (renameModules m2)
    end.

  Lemma renameListAttr_namesOf:
    forall {A} (l: list (Attribute A)),
      namesOf (renameListAttr l) = map rename (namesOf l).
  Proof.
    induction l; simpl; intros; auto.
    f_equal; auto.
  Qed.

  Lemma renameGetRegInits m: getRegInits (renameModules m) = renameListAttr (getRegInits m).
  Proof.
    induction m.
    - reflexivity.
    - reflexivity.
    - simpl; rewrite IHm1, IHm2.
      unfold renameListAttr.
      rewrite map_app.
      reflexivity.
  Qed.

  Lemma renameGetRules m: getRules (renameModules m) = renameRules (getRules m).
  Proof.
    induction m.
    - reflexivity.
    - reflexivity.
    - simpl; rewrite IHm1, IHm2.
      unfold renameRules.
      rewrite map_app.
      reflexivity.
  Qed.

  Lemma renameGetMeths m: getDefsBodies (renameModules m) = renameMeths (getDefsBodies m).
  Proof.
    induction m.
    - unfold renameMeths, renameMeth; simpl.
      rewrite ?map_map; simpl.
      reflexivity.
    - reflexivity.
    - simpl; rewrite IHm1, IHm2.
      unfold renameMeths.
      rewrite map_app.
      reflexivity.
  Qed.

  Lemma renameGetDefs m: getDefs (renameModules m) = map rename (getDefs m).
  Proof.
    unfold getDefs.
    rewrite renameGetMeths; simpl.
    remember (getDefsBodies m) as sth.
    clear Heqsth m.
    induction sth; simpl.
    - reflexivity.
    - f_equal; intuition.
      destruct a; reflexivity.
  Qed.
  
  Lemma renameMapEmpty A: renameMap (M.empty A) = M.empty A.
  Proof.
    apply (M.F.P.fold_Empty); intuition.
  Qed.

  Lemma renameAdd_transpose_neqkey A:
    M.F.P.transpose_neqkey
      eq
      (fun (k0 : M.key) (v0 : A) (old : M.t A) => M.add (rename k0) v0 old).
  Proof.
    unfold M.F.P.transpose_neqkey; intros.
    meq; M.cmp (rename k) (rename k'); findeq.
    elim H; eauto.
  Qed.

  #[local] Hint Immediate renameAdd_transpose_neqkey.
  
  Lemma renameMapAdd:
    forall {A} m k (v: A),
      renameMap (M.add k v m) = M.add (rename k) v (renameMap m).
  Proof.
    intros; remember (M.find k m) as okm. destruct okm.
    - apply eq_sym, M.find_add_3 in Heqokm.
      destruct Heqokm as [sm [? ?]]; subst.
      rewrite M.add_idempotent.
      unfold renameMap.
      rewrite M.F.P.fold_add; auto.
      rewrite M.F.P.fold_add; auto.
    - unfold renameMap.
      rewrite M.F.P.fold_add; auto.
      apply M.F.P.F.not_find_in_iff; auto.
  Qed.

  #[local] Hint Extern 1 (_ = renameMap _) => rewrite renameMapAdd.

  Lemma renameMapFind A (m: M.t A):
    forall k, M.find k m = M.find (rename k) (renameMap m).
  Proof.
    intros; remember (M.find k m) as okm; destruct okm.
    - apply eq_sym, M.find_add_3 in Heqokm.
      destruct Heqokm as [sm [? ?]]; subst.
      unfold renameMap.
      rewrite M.F.P.fold_add; auto.
      rewrite M.find_add_1; intuition.
      unfold Morphisms.Proper, Morphisms.respectful; intros.
      rewrite H, H1, H2.
      intuition.
      unfold M.F.P.transpose_neqkey, M.Map.Equal; intros.
      f_equal.
      M.cmp (rename k0) (rename k').
      apply rename1To1 in e0.
      intuition.
      eauto.
    - M.mind m.
      + rewrite renameMapEmpty.
        apply eq_sym, M.find_empty.
      + rewrite renameMapAdd.
        assert (neq: k <> k0) by
            (unfold not; intros;
             subst;
             rewrite M.find_add_1 in Heqokm;
             discriminate).
        rewrite M.find_add_2 in Heqokm.
        specialize (H Heqokm).
        rewrite M.find_add_2.
        assumption.
        unfold not; intros K; apply rename1To1 in K.
        intuition.
        intuition.
  Qed.

  Lemma renameMapUnion A (m1: M.t A): forall m2,
      renameMap (M.union m1 m2) = M.union (renameMap m1) (renameMap m2).
  Proof.
    M.mind m1.
    - repeat (try rewrite renameMapEmpty; try rewrite M.union_empty_L).
      intuition.
    - rewrite renameMapAdd.
      rewrite M.union_add.
      rewrite M.union_add.
      rewrite renameMapAdd.
      f_equal.
      apply (H m2).
  Qed.

  Lemma renameMapDisj A (m1: M.t A):
    forall m2,
      M.Disj m1 m2 -> M.Disj (renameMap m1) (renameMap m2).
  Proof.
    M.mind m1; simpl in *.
    - rewrite renameMapEmpty; apply M.Disj_empty_1.
    - dest_disj.
      specialize (H _ H1).
      rewrite renameMapAdd.
      solve_disj.
      unfold not; intros.
      apply M.F.P.F.not_find_in_iff in H2.
      apply M.F.P.F.in_find_iff in H3.
      rewrite <- renameMapFind in H3.
      intuition.
  Qed.
  
  Lemma renameMapIn A (m: M.t A):
    forall i, M.In i m <-> M.In (rename i) (renameMap m).
  Proof.
    constructor; intros;
    apply M.F.P.F.in_find_iff in H;
      [rewrite renameMapFind in * | rewrite <- renameMapFind in *];
      apply M.F.P.F.in_find_iff in H;
      auto.
  Qed.
  
  Lemma renameMapNotIn A (m: M.t A):
    forall i, ~ M.In i m <-> ~ M.In (rename i) (renameMap m).
  Proof.
    unfold not; constructor; intros H H0; apply renameMapIn in H0; intuition.
  Qed.

  Lemma renameMapDisjInv A (m1: M.t A):
    forall m2,
      M.Disj (renameMap m1) (renameMap m2) -> M.Disj m1 m2.
  Proof.
    M.mind m1; simpl in *.
    - rewrite renameMapEmpty in *; apply M.Disj_empty_1.
    - rewrite renameMapAdd in H1; dest_disj.
      specialize (H _ H1).
      solve_disj.
      apply renameMapNotIn in H2; auto.
  Qed.
  
  Lemma renameSemAction o k a u cs r (sa: @SemAction o k a u cs r):
    SemAction (renameMap o) (renameAction a) (renameMap u) (renameMap cs) r.
  Proof.
    dependent induction sa; simpl in *.
    - rewrite HAcalls; simpl in *.
      rewrite renameMapAdd.
      apply M.F.P.F.not_find_in_iff in HDisjCalls.
      eapply SemMCall; eauto.
      apply M.F.P.F.not_find_in_iff.
      unfold not; intros H; apply renameMapIn in H; auto.
    - eapply SemLet; eauto; intuition.
    - eapply SemReadNondet; eauto.
    - rewrite renameMapFind in HRegVal.
      eapply SemReadReg; eauto.
    - apply M.F.P.F.not_find_in_iff in HDisjRegs.
      eapply SemWriteReg; eauto.
      apply M.F.P.F.not_find_in_iff.
      unfold not; intros H; apply renameMapIn in H; auto.
      rewrite <- renameMapAdd.
      f_equal; intuition.
    - constructor 6 with (newRegs1 := renameMap newRegs1) (newRegs2 := renameMap newRegs2)
                                                          (calls1 := renameMap calls1)
                                                          (calls2 := renameMap calls2)
                                                          (r1 := r1); auto.
      apply renameMapDisj; auto.
      apply renameMapDisj; auto.
      rewrite <- renameMapUnion.
      f_equal; intuition.
      rewrite <- renameMapUnion.
      f_equal; intuition.
    - constructor 7 with (newRegs1 := renameMap newRegs1) (newRegs2 := renameMap newRegs2)
                                                          (calls1 := renameMap calls1)
                                                          (calls2 := renameMap calls2)
                                                          (r1 := r1); auto.
      apply renameMapDisj; auto.
      apply renameMapDisj; auto.
      rewrite <- renameMapUnion.
      f_equal; intuition.
      rewrite <- renameMapUnion.
      f_equal; intuition.
    - eapply SemAssertTrue; eauto.
    - eapply SemDispl; eauto.
    - eapply SemReturn; eauto.
  Qed.

  Lemma renameModulesConcat m1 m2: renameModules (ConcatMod m1 m2) =
                                   ConcatMod (renameModules m1) (renameModules m2).
  Proof.
    reflexivity.
  Qed.

  Lemma renameMapsTo1 A m: forall k (v: A),
      M.MapsTo k v m ->
      M.MapsTo (rename k) v (renameMap m).
  Proof.
    assert (rename1To1': forall s1 s2, rename s1 = rename s2 -> s1 = s2) by
        (intros; specialize (@rename1To1 s1 s2); intuition).
    M.mind m.
    - apply M.F.P.F.empty_mapsto_iff in H; intuition.
    - apply M.F.P.F.add_mapsto_iff in H1.
      destruct H1 as [[keq veq] | [kneq kin]].
      + subst.
        rewrite renameMapAdd; intuition.
        apply M.F.P.F.add_mapsto_iff; intuition.
      + specialize (H _ _ kin).
        rewrite renameMapAdd; intuition.
        apply M.F.P.F.add_mapsto_iff; intuition.
  Qed.

  Lemma renameFind1 A m: forall k (v: A),
      M.find k m = Some v ->
      M.find (rename k) (renameMap m) = Some v.
  Proof.
    intros.
    apply M.F.P.F.find_mapsto_iff in H.
    apply M.F.P.F.find_mapsto_iff.
    apply renameMapsTo1; intuition.
  Qed.

  Lemma renameMapsTo2 A m: forall k (v: A),
      M.MapsTo (rename k) v (renameMap m) ->
      M.MapsTo k v m.
  Proof.
    M.mind m.
    - apply M.F.P.F.empty_mapsto_iff in H; intuition.
    - rewrite renameMapAdd in H1; intuition; apply M.F.P.F.add_mapsto_iff in H1.
      destruct H1 as [[keq veq] | [kneq kin]].
      + specialize (rename1To1 keq).
        subst.
        apply M.F.P.F.add_mapsto_iff; intuition.
      + specialize (H _ _ kin).
        assert (kneq': k <> k0) by (unfold not; intros; subst; intuition).
        apply M.F.P.F.add_mapsto_iff; intuition.
  Qed.

  Lemma renameFind2 A m: forall k (v: A),
      M.find (rename k) (renameMap m) = Some v ->
      M.find k m = Some v.
  Proof.
    intros.
    apply M.F.P.F.find_mapsto_iff in H.
    apply M.F.P.F.find_mapsto_iff.
    apply renameMapsTo2; intuition.
  Qed.

  Lemma renameMapsTo2' A m: forall k (v: A),
      M.MapsTo k v (renameMap m) ->
      exists k', k = rename k' /\ M.MapsTo k' v m.
  Proof.
    M.mind m.
    - apply M.F.P.F.empty_mapsto_iff in H; intuition.
    - rewrite renameMapAdd in H1; intuition; apply M.F.P.F.add_mapsto_iff in H1.
      destruct H1 as [[keq veq] | [kneq kin]]; subst.
      + exists k.
        constructor; intuition.
        apply M.F.P.F.add_mapsto_iff; intuition.
      + specialize (H _ _ kin).
        destruct H as [k' [kEq kMaps]].
        exists k'.
        constructor; intuition.
        assert (kneq': k' <> k) by (unfold not; intros; subst; intuition).
        apply M.F.P.F.add_mapsto_iff; intuition.
  Qed.

  Lemma renameFind2' A m: forall k (v: A),
      M.find k (renameMap m) = Some v ->
      exists k', k = rename k' /\ M.find k' m = Some v.
  Proof.
    intros.
    apply M.F.P.F.find_mapsto_iff in H.
    apply renameMapsTo2' in H.
    dest.
    exists x; constructor; try apply M.F.P.F.find_mapsto_iff; intuition.
  Qed.

  Lemma renameMapsTo A m: forall k (v: A),
      M.MapsTo k v m <-> M.MapsTo (rename k) v (renameMap m).
  Proof.
    intros; constructor.
    - apply renameMapsTo1.
    - apply renameMapsTo2.
  Qed.

  Lemma renameMapIn1 A (m: M.t A): forall k,
      M.In k m -> M.In (rename k) (renameMap m).
  Proof.
    intros. 
    apply M.MapsToIn2 in H.
    destruct H.
    apply renameMapsTo in H.
    apply (M.MapsToIn1 (v := x)); intuition.
  Qed.

  Lemma renameMapIn2 A (m: M.t A): forall k,
      M.In (rename k) (renameMap m) -> M.In k m.
  Proof.
    intros. 
    apply M.MapsToIn2 in H.
    destruct H.
    apply renameMapsTo in H.
    apply (M.MapsToIn1 (v := x)); intuition.
  Qed.

  Lemma renameMapIn2' A (m: M.t A): forall k,
      M.In k (renameMap m) -> exists k', k = rename k' /\ M.In k' m.
  Proof.
    intros.
    apply M.MapsToIn2 in H.
    destruct H.
    apply renameMapsTo2' in H.
    destruct H as [k' [kEq maps]].
    exists k'.
    constructor; auto.
    apply M.MapsToIn1 in maps.
    intuition.
  Qed.

  Lemma renameMapEmptyImpEmpty A o: M.empty _ = renameMap o -> M.empty A = o.
  Proof.
    M.mind o; intros.
    - reflexivity.
    - rewrite renameMapAdd in H1.
      apply eq_sym in H1; apply M.add_empty_neq in H1; intuition.
  Qed.
  
  Lemma renameMapEq A o1: forall (o2: M.t A), renameMap o1 = renameMap o2 -> o1 = o2.
  Proof.
    intros o2 rnEq.
    apply M.leibniz; apply M.F.P.F.Equal_mapsto_iff.
    intros.
    constructor; intros H;
      apply renameMapsTo in H;
      [rewrite rnEq in H | rewrite <- rnEq in H];
      apply renameMapsTo in H;
      assumption.
  Qed.
                            
  Lemma renameSemActionRev o' k a' u cs r:
    SemAction (renameMap o') (renameAction a') u cs r ->
    exists u' cs',
      u = renameMap u' /\
      cs = renameMap cs' /\
      @SemAction o' k a' u' cs' r.
  Proof.
    intros sa; simpl in *.
    dependent induction sa; simpl in *; intros; destruct a'; simpl in *; try discriminate.
    - generalize dependent mret;
        inv x; destruct_existT; intros.
      destruct (IHsa rename1To1 o' (a mret) JMeq_refl eq_refl) as
          [u' [cs' [uEq [csEq sa']]]]; subst.
      apply M.F.P.F.not_find_in_iff in HDisjCalls.
      apply renameMapNotIn in HDisjCalls.
      repeat (econstructor; eauto).
      apply M.F.P.F.not_find_in_iff; eauto.
    - inv x; destruct_existT; intros.
      destruct (IHsa rename1To1 o' (a (evalExpr e0)) JMeq_refl eq_refl) as
          [u' [cs' [uEq [csEq sa']]]]; subst.
      repeat (econstructor; eauto).
    - generalize dependent sa; generalize dependent IHsa; inv x; destruct_existT; intros.
      destruct (IHsa rename1To1 o' (a valueV) JMeq_refl eq_refl) as
          [u' [cs' [uEq [csEq sa']]]]; subst.
      repeat (econstructor; eauto).
    - generalize dependent regV; inv x; destruct_existT; intros.
      destruct (IHsa rename1To1 o' (a regV) JMeq_refl eq_refl) as
          [u' [cs' [uEq [csEq sa']]]]; subst.
      repeat (econstructor; eauto).
      rewrite <- HRegVal; auto.
      rewrite renameMapFind; reflexivity.
    - inv x; destruct_existT; intros.
      destruct (IHsa rename1To1 o' a' JMeq_refl eq_refl) as
          [u' [cs' [uEq [csEq sa']]]]; subst.
      apply M.F.P.F.not_find_in_iff in HDisjRegs.
      apply renameMapNotIn in HDisjRegs.
      repeat (econstructor; eauto).
      apply M.F.P.F.not_find_in_iff; auto.
    - generalize dependent r1.
      inv x; destruct_existT; intros.
      destruct (IHsa1 rename1To1 o' a'1 JMeq_refl eq_refl) as
          [u1' [cs1' [uEq1 [csEq1 sa1']]]]; subst;
        clear IHsa1.
      destruct (IHsa2 rename1To1 o' (a0 r1) JMeq_refl eq_refl) as
          [u2' [cs2' [uEq2 [csEq2 sa2']]]]; subst;
      clear IHsa2.
      apply renameMapDisjInv in HDisjCalls.
      apply renameMapDisjInv in HDisjRegs.
      exists (M.union u1' u2'), (M.union cs1' cs2').
      constructor; rewrite renameMapUnion; auto.
      constructor; auto.
      econstructor; eauto.
    - generalize dependent r1.
      inv x; destruct_existT; intros.
      destruct (IHsa1 rename1To1 o' a'2 JMeq_refl eq_refl) as
          [u1' [cs1' [uEq1 [csEq1 sa1']]]]; subst;
        clear IHsa1.
      destruct (IHsa2 rename1To1 o' (a0 r1) JMeq_refl eq_refl) as
          [u2' [cs2' [uEq2 [csEq2 sa2']]]]; subst;
      clear IHsa2.
      apply renameMapDisjInv in HDisjCalls.
      apply renameMapDisjInv in HDisjRegs.
      exists (M.union u1' u2'), (M.union cs1' cs2').
      constructor; rewrite renameMapUnion; auto.
      constructor; auto.
      econstructor 7; eauto.
    - inv x; destruct_existT; intros.
      destruct (IHsa rename1To1 o' a' JMeq_refl eq_refl) as
          [u1' [cs1' [uEq1 [csEq1 sa1']]]]; subst;
        clear IHsa.
      repeat (econstructor; eauto).
    - inv x; destruct_existT; intros.
      destruct (IHsa rename1To1 o' a' JMeq_refl eq_refl) as
          [u' [cs' [uEq [csEq sa']]]]; subst; clear IHsa.
      exists u', cs'; repeat (split; auto).
      constructor; auto.
    - inv x; destruct_existT; intros.
      repeat (econstructor; eauto; try (rewrite renameMapEmpty; reflexivity)).
  Qed.

  Lemma renameSign f:
    projT1 (attrType (renameMeth f)) = projT1 (attrType f).
  Proof.
    unfold renameMeth; simpl.
    destruct f; simpl.
    reflexivity.
  Qed.

  Lemma renameSubstep m o u l cs
        (sa: Substep m o u l cs):
    Substep (renameModules m) (renameMap o) (renameMap u) (renameUnitLabel l) (renameMap cs).
  Proof.
    dependent induction sa; intros; simpl in *.
    - repeat rewrite renameMapEmpty.
      econstructor; eauto.
    - repeat rewrite renameMapEmpty.
      econstructor; eauto.
    - apply renameSemAction in HAction.
      apply renameInRules in HInRules.
      constructor 3 with (a := fun ty => renameAction (a ty)).
      + rewrite renameGetRules; intuition.
      + intuition.
    - apply renameSemAction in HAction.
      apply renameInMeths in HIn.
      rewrite <- renameGetMeths in *.
      destruct f; simpl in *.
      subst; eapply SingleMeth; eauto.
      simpl; auto.
  Qed.

  Definition renameSubstepRec m o (sr: SubstepRec m o) :=
    {| upd := renameMap (upd sr);
       unitAnnot := renameUnitLabel (unitAnnot sr);
       cms := renameMap (cms sr);
       substep := renameSubstep (substep sr) |}.

  Definition renameSubsteps m o ss := map (@renameSubstepRec m o) ss.

  Lemma renameSubstepsIn m o ss:
    forall s, In s (renameSubsteps ss) ->
              exists s', s = renameSubstepRec (m := m) (o := o) s' /\ In s' ss.
  Proof.
    induction ss; intros; simpl in *.
    - intuition.
    - destruct H.
      + exists a; intuition.
      + specialize (IHss _ H).
        destruct IHss as [s' [eqq inq]].
        exists s'; intuition.
  Qed.

  Lemma renameDisj A m1 m2: M.Disj (A := A) m1 m2 -> M.Disj (renameMap m1) (renameMap m2).
  Proof.
    intros; unfold M.Disj in *; intros.
    pose proof (M.F.P.F.In_dec (renameMap m1) k) as sth1.
    pose proof (M.F.P.F.In_dec (renameMap m2) k) as sth2.
    destruct sth1, sth2.
    apply renameMapIn2' in i0.
    apply renameMapIn2' in i1.
    destruct i0 as [k1 [k1Eq k1In]].
    destruct i1 as [k2 [k2Eq k2In]].
    subst.
    specialize (rename1To1 k2Eq).
    subst.
    specialize (H k2).
    intuition.
    apply renameMapIn2' in i0.
    destruct i0 as [k1 [k1Eq k1In]].
    subst.
    specialize (H k1).
    assert (~ M.In k1 m2) by intuition.
    right; unfold not; intros.
    apply renameMapIn2 in H1.
    intuition.
    apply renameMapIn2' in i0.
    destruct i0 as [k1 [k1Eq k1In]].
    subst.
    specialize (H k1).
    assert (~ M.In k1 m1) by intuition.
    left; unfold not; intros.
    apply renameMapIn2 in H1.
    intuition.
    intuition.
  Qed.

  Lemma renameCanCombine m o s1 s2:
    canCombine (m := m) (o := o) s1 s2 ->
    canCombine (renameSubstepRec s1) (renameSubstepRec s2).
  Proof.
    intros.
    destruct s1, s2.
    unfold canCombine in *.
    simpl in *.
    repeat match goal with
           | H: _ /\ _ |- _ => destruct H
           | H: exists x, _ |- _ => destruct H
           end.
    constructor.
    - apply renameDisj; intuition.
    - constructor; intros.
      + destruct unitAnnot, unitAnnot0; simpl in *.
        destruct o0, o1; discriminate.
        destruct o0; discriminate.
        destruct o1; discriminate.
        destruct o0, o1; try discriminate.
        destruct a, a0.
        inv H3; destruct_existT.
        inv H4; destruct_existT.
        unfold not; intros.
        simpl in *.
        specialize (rename1To1 H3).
        subst.
        specialize (H0 (attrName0 :: attrType)%struct (attrName0 :: attrType0)%struct
                       eq_refl eq_refl).
        simpl in *.
        intuition.
      + constructor.
        * destruct H1.
          destruct unitAnnot; try discriminate.
          injection H1; intros; subst.
          simpl in *.
          destruct x. destruct a; simpl in *.
          eexists; eauto.
          eexists; eauto.
          destruct unitAnnot0; try discriminate.
          injection H1; intros; subst.
          simpl in *.
          destruct x. destruct a; simpl in *.
          eexists; eauto.
          eexists; eauto.
        * apply renameDisj; intuition.
  Qed.
  
  Lemma renameSubstepsComb m o ss: substepsComb (m := m) (o := o) ss ->
                                   substepsComb (renameSubsteps ss).
  Proof.
    intros H.
    dependent induction H; simpl.
    - constructor.
    - constructor; intros.
      + intuition.
      + apply renameSubstepsIn in H1.
        destruct H1 as [s1 [s1Eq inS1]].
        specialize (H0 _ inS1).
        subst.
        apply renameCanCombine; intuition.
  Qed.

  Lemma renameSubtractKV m1 m2:
      renameMap (M.subtractKV signIsEq m1 m2) =
      M.subtractKV signIsEq (renameMap m1) (renameMap m2).
  Proof.
    apply M.leibniz; apply M.F.P.F.Equal_mapsto_iff;
    constructor; intros.
    - apply renameMapsTo2' in H.
      destruct H as [? [? sth]]; subst.
      apply M.subtractKV_mapsto in sth.
      destruct sth as [K1 K2].
      apply M.subtractKV_mapsto.
      constructor.
      + apply renameMapsTo in K1; intuition.
      + unfold not; intros.
        apply renameMapsTo in H; intuition.
    - apply M.subtractKV_mapsto in H.
      destruct H.
      apply renameMapsTo2' in H.
      destruct H as [? [? ?]]; subst.
      apply renameMapsTo with (m := M.subtractKV signIsEq m1 m2).
      apply M.subtractKV_mapsto.
      constructor; intuition.
      apply renameMapsTo in H; intuition.
  Qed.
  
  Lemma renameHide l: renameLabel (hide l) = hide (renameLabel l).
  Proof.
    simpl in *.
    unfold hide, renameLabel; simpl.
    destruct l; simpl.
    repeat rewrite renameSubtractKV in *.
    reflexivity.
  Qed.

  Lemma renameHideFoldSS m o ss:
    hide (foldSSLabel (renameSubsteps (m := m) (o := o) ss)) =
    renameLabel (hide (foldSSLabel ss)).
  Proof.
    rewrite renameHide.
    f_equal.
    induction ss; simpl.
    - rewrite renameMapEmpty; reflexivity.
    - rewrite IHss.
      remember (foldSSLabel ss) as sth; clear Heqsth ss IHss.
      destruct a, sth; simpl in *.
      destruct unitAnnot, annot; simpl in *;
      unfold addLabelLeft; simpl;
      destruct o0; try destruct o1; try destruct a;
      repeat rewrite M.union_empty_L in *;
      repeat rewrite renameMapUnion in *; try reflexivity.
  Qed.

  Lemma renameFoldSSUpdsSubsteps m o ss:
    foldSSUpds (renameSubsteps (m := m) (o := o) ss) = renameMap (foldSSUpds ss).
  Proof.
    induction ss; simpl.
    - rewrite renameMapEmpty; reflexivity.
    - rewrite IHss.
      rewrite renameMapUnion.
      reflexivity.
  Qed.

  Lemma renameListIn k l: In k l <-> In (rename k) (map rename l).
  Proof.
    induction l; simpl.
    - intuition.
    - constructor; intros.
      + destruct H; subst; intuition.
      + destruct H.
        * apply rename1To1 in H; intuition.
        * intuition.
  Qed.

  Lemma renameGetCallsA k a: getCallsA (renameAction (k := k) a) = map rename (getCallsA a).
  Proof.
    induction a; simpl; try f_equal; intuition.
    specialize (H tt).
    repeat rewrite List.map_app.
    rewrite H, IHa1, IHa2.
    reflexivity.
  Qed.

  Lemma renameGetCallsR (rl: list (Attribute (Action (Bit 0)))):
    getCallsR (renameRules rl) = map rename (getCallsR rl).
  Proof.
    induction rl; simpl.
    - reflexivity.
    - repeat rewrite List.map_app.
      rewrite IHrl.
      destruct a; simpl.
      rewrite renameGetCallsA.
      reflexivity.
  Qed.

  Lemma renameGetCallsR' m:
    getCallsR (getRules (renameModules m)) = map rename (getCallsR (getRules m)).
  Proof.
    induction m; simpl.
    - apply renameGetCallsR.
    - apply renameGetCallsR.
    - repeat rewrite getCallsR_app.
      rewrite List.map_app.
      rewrite <- IHm1, <- IHm2.
      reflexivity.
  Qed.

  Lemma renameGetCallsM (ms: list DefMethT):
    getCallsM (renameMeths ms) = map rename (getCallsM ms).
  Proof.
    induction ms; simpl.
    - reflexivity.
    - repeat rewrite List.map_app.
      rewrite IHms.
      destruct a; simpl.
      rewrite renameGetCallsA.
      reflexivity.
  Qed.

  Lemma renameGetCallsM' m:
    getCallsM (getDefsBodies (renameModules m)) = map rename (getCallsM (getDefsBodies m)).
  Proof.
    induction m; simpl.
    - apply renameGetCallsM.
    - apply renameGetCallsM.
    - repeat rewrite getCallsM_app.
      rewrite List.map_app.
      rewrite <- IHm1, <- IHm2.
      reflexivity.
  Qed.

  Lemma renameGetCalls m:
    getCalls (renameModules m) = map rename (getCalls m).
  Proof.
    unfold getCalls in *.
    rewrite List.map_app.
    rewrite renameGetCallsM', renameGetCallsR'.
    reflexivity.
  Qed.

  Lemma renameWellHidden m l: wellHidden m l -> wellHidden (renameModules m) (renameLabel l).
  Proof.
    intros wh.
    unfold wellHidden in *.
    unfold M.KeysDisj in *.
    destruct wh as [wh1 wh2].
    destruct l; simpl in *.
    constructor; unfold not; intros.
    - apply renameMapIn2' in H0.
      destruct H0 as [? [kEq kIn]]; subst.
      rewrite renameGetCalls in H.
      apply renameListIn in H.
      apply (wh1 _ H kIn).
    - apply renameMapIn2' in H0.
      destruct H0 as [? [kEq kIn]]; subst.
      simpl in *.
      rewrite renameGetDefs in H.
      apply renameListIn in H.
      apply (wh2 _ H kIn).
  Qed.

  Lemma renameStep m o u l
        (sa: Step m o u l):
    Step (renameModules m) (renameMap o) (renameMap u) (renameLabel l).
  Proof.
    dependent induction sa.
    pose proof (StepIntro (m := renameModules m) (o := renameMap o) (ss := renameSubsteps ss)
                          (renameSubstepsComb HSubsteps)).
    rewrite renameHideFoldSS, renameFoldSSUpdsSubsteps in *.
    apply H.
    apply renameWellHidden; intuition.
  Qed.
  
  Theorem traceRefinesRename m: traceRefines (renameMap (A := _)) m (renameModules m).
  Proof.
    apply (stepRefinement (@renameMap _) (fun _ s => Some (rename s)) (@renameMap _)).
    - rewrite renameGetRegInits.
      remember (getRegInits m) as sth; clear m Heqsth.
      induction sth.
      + reflexivity.
      + destruct a as [rn [[? ?]|]];
          unfold initRegs in *; simpl in *;
            rewrite <- IHsth;
            rewrite renameMapAdd;
            reflexivity.
    - intros.
      exists (renameMap u).
      constructor.
      + unfold liftPLabel.
        pose proof (renameStep H0).
        destruct l; simpl in *.
        destruct annot;
          try destruct o0; simpl in *; intuition.
      + rewrite renameMapUnion.
        reflexivity.
  Qed.

  Lemma renameInRulesAction m r a: In (r :: a)%struct (getRules (renameModules m)) ->
                                   exists r' (a': Action Void),
                                     r = rename r' /\
                                     a type = renameAction (a' type) /\
                                     In (r' :: a')%struct (getRules m).
  Proof.
    intros ina.
    rewrite renameGetRules in *.
    induction (getRules m); simpl in *.
    - intuition.
    - destruct a0; simpl in *.
      destruct ina.
      + inversion H; subst.
        exists attrName; exists attrType.
        repeat (constructor; try reflexivity).
      + specialize (IHl H).
        clear - IHl.
        firstorder.
  Qed.

  Lemma renameInMethsAction m f: In f (getDefsBodies (renameModules m)) ->
                                 exists f',
                                   f = renameMeth f' /\
                                   In f' (getDefsBodies m).
  Proof.
    rewrite renameGetMeths in *.
    induction (getDefsBodies m); simpl in *; intros.
    - intuition.
    - destruct H.
      + exists a; intuition.
      + specialize (IHl H); firstorder.
  Qed.

  Lemma renameSubstepRev m' o' u l cs:
    Substep (renameModules m') (renameMap o') u l cs ->
    exists u' l' cs',
      u = renameMap u' /\
      l = renameUnitLabel l' /\
      cs = renameMap cs' /\
      Substep m' o' u' l' cs'.
  Proof.
    intros s.
    dependent induction s; subst.
    - repeat (econstructor; eauto);
        try rewrite renameMapEmpty; reflexivity.
    - exists (M.empty _).
      exists (Meth None).
      repeat (econstructor; eauto).
      try rewrite renameMapEmpty; reflexivity.
    - apply renameInRulesAction in HInRules.
      dest; subst.
      rewrite H0 in HAction.
      apply renameSemActionRev in HAction.
      dest; subst.
      repeat (econstructor; eauto).
      reflexivity.
    - apply renameInMethsAction in HIn.
      dest; subst.
      destruct x; simpl in *.
      apply renameSemActionRev in HAction.
      dest; subst.
      exists x.
      exists (Meth (Some (attrName :: existT SignT (projT1 attrType) (argV, retV))%struct)).
      exists x0.
      intuition.
      eapply SingleMeth; eauto.
  Qed.

  Lemma renameSubstepRecRev m' o'
        (ss: SubstepRec (renameModules m') (renameMap o')):
    exists (ss': SubstepRec m' o'),
      upd ss = renameMap (upd ss') /\
      unitAnnot ss = renameUnitLabel (unitAnnot ss') /\
      cms ss = renameMap (cms ss').
  Proof.
    destruct ss.
    simpl.
    apply renameSubstepRev in substep.
    dest.
    exists {| upd := x;
              unitAnnot := x0;
              cms := x1;
              substep := H2 |}; simpl.
    intuition.
  Qed.

  Lemma renameGetLabel l1 l2: getLabel (renameUnitLabel l1) (renameMap l2) =
                              renameLabel (getLabel l1 l2).
  Proof.
    destruct l1;
      unfold getLabel, renameUnitLabel, renameLabel; repeat rewrite renameMapEmpty;
    destruct o; try destruct a;
      intuition.
  Qed.

  Lemma renameMergeLabel l1 l2: mergeLabel (renameLabel l1) (renameLabel l2) =
                                renameLabel (mergeLabel l1 l2).
  Proof.
    unfold mergeLabel, renameLabel.
    destruct l1, l2.
    destruct annot, annot0; try destruct o, o0;
      repeat rewrite renameMapUnion; intuition.
    destruct o; intuition.
  Qed.

  Lemma renameDisjRev A (m1 m2: M.t A): M.Disj (renameMap m1) (renameMap m2) ->
                                        M.Disj m1 m2.
  Proof.
    intros.
    unfold M.Disj in *; intros.
    pose proof (M.F.P.F.In_dec m1 k).
    pose proof (M.F.P.F.In_dec m2 k).
    destruct H0, H1; try intuition.
    pose proof (renameMapIn1 i0) as sth1;
    pose proof (renameMapIn1 i1) as sth2.
    destruct (H (rename k)); intuition.
  Qed.
  
  Lemma renameCanCombineUUL a b c d e:
    CanCombineUUL (renameMap a) (renameLabel b) (renameMap c) (renameMap d) (renameUnitLabel e) ->
    CanCombineUUL a b c d e.
  Proof.
    intros cc.
    unfold CanCombineUUL in *.
    dest.
    constructor.
    apply renameDisjRev in H; intuition.
    constructor.
    unfold renameLabel in H0; destruct b; simpl in *.
    apply renameDisjRev in H0; intuition.
    destruct b; simpl in *.
    destruct annot, e; try destruct o;
      simpl in *; try destruct o0; intuition; try destruct a0;
    apply renameMapIn1 in H2;
    intuition.
  Qed.
  
  Lemma renameSubstepsIndRev m' o' u l
        (ssi: SubstepsInd (renameModules m') (renameMap o') u l):
    exists u' l',
      u = renameMap u' /\
      l = renameLabel l' /\
      SubstepsInd m' o' u' l'.
  Proof.
    dependent induction ssi; simpl.
    - repeat (econstructor; eauto); simpl;
        rewrite renameMapEmpty; reflexivity.
    - dest; subst.
      apply renameSubstepRev in H; dest; subst.
      rewrite <- renameMapUnion.
      rewrite renameGetLabel, renameMergeLabel.
      eexists (M.union x x1).
      exists (mergeLabel (getLabel x2 x3) x0).
      repeat (constructor; intuition).
      apply (SubstepsCons H5 H3); intuition.
      apply renameCanCombineUUL; intuition.
  Qed.

  Lemma renameWellHiddenRev m l:
    wellHidden (renameModules m) (renameLabel l) -> wellHidden m l.
  Proof.
    intros.
    unfold wellHidden in *.
    unfold M.KeysDisj in *.
    dest.
    constructor; unfold not; intros.
    - specialize (H (rename k)).
      specialize (H0 (rename k)).
      apply renameListIn in H1.
      apply renameMapIn1 in H2.
      rewrite <- renameGetCalls in H1.
      destruct l; simpl in *.
      apply (H H1 H2).
    - specialize (H (rename k)).
      specialize (H0 (rename k)).
      apply renameListIn in H1.
      apply renameMapIn1 in H2.
      rewrite <- renameGetDefs in H1.
      destruct l; simpl in *.
      apply (H0 H1 H2).
  Qed.

  Lemma renameStepIndRev m' o' u l:
    StepInd (renameModules m') (renameMap o') u l ->
    exists u' l',
      u = renameMap u' /\
      l = renameLabel l' /\
      StepInd m' o' u' l'.
  Proof.
    intros s.
    dependent induction s.
    apply renameSubstepsIndRev in HSubSteps.
    dest; subst.
    rewrite <- renameHide in *.
    exists x; exists (hide x0).
    intuition.
    constructor.
    intuition.
    apply renameWellHiddenRev in HWellHidden; intuition.
  Qed.

  Lemma renameStepRev m' o' u l:
    Step (renameModules m') (renameMap o') u l ->
    exists u' l',
      u = renameMap u' /\
      l = renameLabel l' /\
      Step m' o' u' l'.
  Proof.
    intros s.
    apply step_consistent in s.
    apply renameStepIndRev in s.
    dest.
    repeat (econstructor; eauto).
    apply step_consistent; intuition.
  Qed.

  Lemma renameInitRegs m:
    initRegs (getRegInits (renameModules m)) = renameMap (initRegs (getRegInits m)).
  Proof.
    rewrite renameGetRegInits.
    remember (getRegInits m) as sth; clear m Heqsth.
    induction sth.
    + reflexivity.
    + destruct a as [rn [[? ?]|]];
        unfold initRegs in *; simpl in *;
          rewrite IHsth;
          rewrite renameMapAdd;
          reflexivity.
  Qed.

  Lemma renameMultistep m' n l:
    Multistep (renameModules m') (renameMap (initRegs (getRegInits m'))) n l ->
    exists n' l',
      n = renameMap n' /\
      l = map renameLabel l' /\
      Multistep m' (initRegs (getRegInits m')) n' l'.
  Proof.
    intros m.
    dependent induction m.
    - repeat (econstructor; eauto).
      reflexivity.
    - specialize (IHm rename1To1 _ eq_refl JMeq_refl).
      dest; subst.
      apply renameStepRev in HStep.
      dest; subst.
      exists (M.union x1 x).
      exists (x2 :: x0).
      constructor.
      rewrite renameMapUnion; intuition.
      constructor.
      reflexivity.
      constructor; intuition.
  Qed.

  Lemma renameListLabel1To1 l1: forall l2,
      map renameLabel l1 = map renameLabel l2 -> l1 = l2.
  Proof.
    induction l1; intros.
    - destruct l2.
      + reflexivity.
      + discriminate.
    - simpl in *.    
      destruct l2.
      + discriminate.
      + inversion H; subst.
        specialize (IHl1 _ H2); subst.
        f_equal.
        clear - H1 rename1To1.
        destruct a, l.
        simpl in *.
        destruct annot, annot0; try destruct o0, o; inversion H1.
        * apply rename1To1 in H0.
          apply renameMapEq in H2.
          apply renameMapEq in H3.
          subst.
          reflexivity.
        * apply renameMapEq in H0.
          apply renameMapEq in H2.
          subst.
          reflexivity.
        * destruct o;
            discriminate.
        * destruct o; discriminate.
        * apply renameMapEq in H0.
          apply renameMapEq in H2.
          subst; reflexivity.
  Qed.
  
  Lemma renameBehavior m n l:
    Behavior m n l ->
    Behavior (renameModules m) (renameMap n) (map renameLabel l).
  Proof.
    intros b.
    dependent induction b.
    constructor.
    dependent induction HMultistepBeh; simpl.
    - rewrite <- renameInitRegs.
      repeat constructor; intuition.
    - rewrite renameMapUnion.
      specialize (IHHMultistepBeh rename1To1).
      apply renameStep in HStep.
      repeat constructor; intuition.
  Qed.
  
  Lemma renameBehaviorRev m' n l:
    Behavior (renameModules m') n l ->
    exists n' l',
      n = renameMap n' /\
      l = map renameLabel l' /\
      Behavior m' n' l'.
  Proof.
    intros b.
    dependent induction b.
    dependent induction HMultistepBeh.
    repeat (econstructor; eauto).
    - apply renameInitRegs.
    - reflexivity.
    - specialize (IHHMultistepBeh rename1To1 _ eq_refl eq_refl).
      dest; subst.
      apply renameStepRev in HStep.
      dest; subst.
      rewrite <- renameMapUnion.
      exists (M.union x1 x).
      exists (x2 :: x0).
      constructor; intuition.
      rewrite renameInitRegs in *.
      apply renameMultistep in HMultistepBeh.
      dest; subst.
      apply renameMapEq in H; subst.
      apply renameListLabel1To1 in H0; subst.
      constructor; intuition.
      constructor; intuition.
  Qed.

  Theorem renameTheorem p a b:
    traceRefines p a b ->
    forall na la1, Behavior (renameModules a) na la1 ->
                   exists nb la2 lb2,
                     la1 = map renameLabel la2 /\
                     Behavior (renameModules b) nb (map renameLabel lb2) /\
                     equivalentLabelSeq p la2 lb2.
  Proof.
    intros.
    unfold traceRefines in *; dest.
    apply renameBehaviorRev in H0.
    dest; subst.
    specialize (H _ _ H2); dest; subst.
    apply renameBehavior in H.
    dest; subst.
    exists (renameMap x1); exists x0; exists x2.
    intuition.
  Qed.
End Rename.

Section RenameInv.
  Variable f: string -> string.
  Variable g: string -> string.
  Variable gInvF: forall x, g (f x) = x.
  Variable fInvG: forall x, f (g x) = x.

  Lemma f1To1 x1 x2: f x1 = f x2 -> x1 = x2.
  Proof.
    intros hyp.
    pose proof (gInvF x1) as y1.
    pose proof (gInvF x2) as y2.
    rewrite <- y1, <- y2.
    f_equal; intuition.
  Qed.

  Lemma g1To1 x1 x2: g x1 = g x2 -> x1 = x2.
  Proof.
    intros hyp.
    pose proof (fInvG x1) as y1.
    pose proof (fInvG x2) as y2.
    rewrite <- y1, <- y2.
    f_equal; intuition.
  Qed.

  Lemma renameMap_bijective_find:
    forall {A} (m: M.t A) k,
      M.find k (renameMap f m) = M.find (g k) m.
  Proof.
    intros; unfold renameMap; M.mind m.
    - reflexivity.
    - rewrite M.F.P.fold_add with (eqA:= eq); auto.
      + destruct (string_dec k (f k0)); [subst|].
        * rewrite gInvF.
          do 2 rewrite M.find_add_1; reflexivity.
        * assert (g k <> k0) by (intro Hx; elim n; subst; auto).
          do 2 (rewrite M.find_add_2 by assumption); assumption.
      + apply renameAdd_transpose_neqkey.
        intros.
        rewrite <-gInvF with (x:= s1).
        rewrite <-gInvF with (x:= s2).
        rewrite H1; auto.
  Qed.

  Lemma renameMapGInvF A (m: M.t A): renameMap g (renameMap f m) = m.
  Proof.
    apply M.leibniz; apply M.F.P.F.Equal_mapsto_iff; constructor; intros.
    apply renameMapsTo2' in H;
    dest; subst.
    apply renameMapsTo2' in H0; dest; subst.
    rewrite gInvF; intuition.
    apply f1To1.
    apply g1To1.
    apply renameMapsTo1 with (rename := f) in H.
    apply renameMapsTo1 with (rename := g) in H.
    rewrite gInvF in H.
    intuition.
    apply g1To1.
    apply f1To1.
  Qed.
    
  Lemma renameMapFInvG A (m: M.t A): renameMap f (renameMap g m) = m.
  Proof.
    apply M.leibniz; apply M.F.P.F.Equal_mapsto_iff; constructor; intros.
    apply renameMapsTo2' in H;
    dest; subst.
    apply renameMapsTo2' in H0; dest; subst.
    rewrite fInvG; intuition.
    apply g1To1.
    apply f1To1.
    apply renameMapsTo1 with (rename := g) in H.
    apply renameMapsTo1 with (rename := f) in H.
    rewrite fInvG in H.
    intuition.
    apply f1To1.
    apply g1To1.
  Qed.

  Lemma renameLabelGInvF l: renameLabel g (renameLabel f l) = l.
  Proof.
    destruct l.
    unfold renameLabel.
    destruct annot; try destruct o;
      repeat rewrite renameMapGInvF; repeat rewrite gInvF; reflexivity.
  Qed.
    
  Lemma renameLabelFInvG l: renameLabel f (renameLabel g l) = l.
  Proof.
    destruct l.
    unfold renameLabel.
    destruct annot; try destruct o;
      repeat rewrite renameMapFInvG; repeat rewrite fInvG; reflexivity.
  Qed.

  Lemma renameLabelsGInvF ls: map (renameLabel g) (map (renameLabel f) ls) = ls.
  Proof.
    induction ls.
    - reflexivity.
    - simpl in *.
      rewrite renameLabelGInvF.
      f_equal; intuition.
  Qed.
    
  Lemma renameLabelsFInvG ls: map (renameLabel f) (map (renameLabel g) ls) = ls.
  Proof.
    induction ls.
    - reflexivity.
    - simpl in *.
      rewrite renameLabelFInvG.
      f_equal; intuition.
  Qed.
End RenameInv.

Section RenameRefinement.
  Variables fa fb: string -> string.
  Variables ga gb: string -> string.
  Hypotheses (Hgfa: forall x, ga (fa x) = x)
             (Hfga: forall x, fa (ga x) = x)
             (Hgfb: forall x, gb (fb x) = x)
             (Hfgb: forall x, fb (gb x) = x).

  Definition liftPRename (p: MethsT -> MethsT) :=
    fun m => renameMap fb (p (renameMap ga m)).

  Theorem renameRefinement:
    forall p ma mb,
      traceRefines p ma mb ->
      forall rp,
        rp = liftPRename p ->
        traceRefines rp (renameModules fa ma) (renameModules fb mb).
  Proof.
    intros; subst; unfold liftPRename.
    change (fun m => renameMap fb (p (renameMap ga m))) with
    (fun m => (fun m => renameMap fb (p m)) (renameMap ga m)).

    apply traceRefines_trans with (mb := ma).
    - clear H.
      unfold traceRefines; intros.
      apply renameBehaviorRev in H;
        [|apply f1To1 with (g:= ga); auto].
      destruct H as [n [l ?]]; dest; subst.
      do 2 eexists; split; eauto.

      clear H1.
      induction l; simpl; [constructor|].
      constructor; auto.
      destruct a as [ann ds cs].
      unfold equivalentLabel; repeat split; simpl.
      + apply renameMapGInvF; auto.
      + apply renameMapGInvF; auto.
      + destruct ann as [[|]|]; auto.
      
    - apply traceRefines_trans with (mb := mb).
      + auto.
      + clear H; unfold traceRefines; intros.
        apply renameBehavior with (rename:= fb) in H;
          [|apply f1To1 with (g:= gb); auto].
        do 2 eexists; split; eauto.

        clear.
        induction sig1; simpl; [constructor|].
        constructor; auto.
        destruct a as [ann ds cs].
        unfold equivalentLabel; repeat split; simpl.
        destruct ann as [[|]|]; auto.
  Qed.

End RenameRefinement.

Fixpoint bijective dom img s :=
  match dom, img with
  | d :: dt, i :: it =>
    if string_dec s d then i
    else if string_dec s i then d
         else bijective dt it s
  | _, _ => s
  end.

Ltac bijective_correct_tac :=
  repeat
    match goal with
    | [ |- context[string_dec ?s1 ?s2] ] =>
      destruct (string_dec s1 s2); [subst|]; intuition
    end.

Lemma bijective_dom_in:
  forall dom img
         (HlengthEq: length dom = length img)
         (HdisjDomImg: forall i, ~ (In i dom /\ In i img))
         s, In s dom -> In (bijective dom img s) img.
Proof.
  induction dom as [|d]; simpl; intros; [elim H|].
  destruct img as [|i]; inv HlengthEq.
  destruct H; subst.
  - bijective_correct_tac.
  - bijective_correct_tac.
    + elim (HdisjDomImg i); intuition.
    + right; apply IHdom; auto.
      intros; apply (HdisjDomImg i0); intuition.
Qed.

Lemma bijective_img_in:
  forall img dom
         (HlengthEq: length dom = length img)
         (HdisjDomImg: forall i, ~ (In i dom /\ In i img))
         s, In s img -> In (bijective dom img s) dom.
Proof.
  induction img as [|i]; simpl; intros; [elim H|].
  destruct dom as [|d]; inv HlengthEq.
  destruct H; subst; simpl.
  - bijective_correct_tac.
  - bijective_correct_tac.
    + elim (HdisjDomImg d); intuition.
    + right; apply IHimg; auto.
      intros; apply (HdisjDomImg i0); intuition.
Qed.

Lemma bijective_id:
  forall dom img
         (HlengthEq: length dom = length img)
         (HdisjDomImg: forall i, ~ (In i dom /\ In i img))
         s, ~ In s dom -> ~ In s img -> bijective dom img s = s.
Proof.
  induction dom as [|d]; simpl; intros; auto.
  destruct img as [|i]; inv HlengthEq; simpl in *.
  bijective_correct_tac.
  apply IHdom; auto.
  intros; apply (HdisjDomImg i0); intuition.
Qed.

Lemma bijectiveCorrect:
  forall (dom img: list string)
         (HlengthEq: length dom = length img)
         (HdisjDomImg: forall i, ~ (In i dom /\ In i img))
         (HnoDupDom: NoDup dom) (HnoDupImg: NoDup img),
  forall s, bijective dom img (bijective dom img s) = s.
Proof.
  induction dom as [|d]; simpl; intros; auto.
  destruct img as [|i]; auto.
  inv HlengthEq; inv HnoDupDom; inv HnoDupImg.

  assert (forall i, ~ (In i dom /\ In i img)).
  { intros; intro Hx; elim (HdisjDomImg i0); intuition. }

  destruct (string_dec s d); subst.
  - bijective_correct_tac.
  - destruct (string_dec s i); subst.
    + bijective_correct_tac.
    + assert (bijective dom img s <> d).
      { intro Hx.
        destruct (in_dec string_dec s dom) as [Hdin|Hdnin].
        { pose proof (bijective_dom_in dom img H0 H _ Hdin).
          rewrite Hx in H1.
          elim (HdisjDomImg d); intuition.
        }
        { destruct (in_dec string_dec s img) as [Hiin|Hinin].
          { pose proof (bijective_img_in img dom H0 H _ Hiin).
            rewrite Hx in H1.
            elim (HdisjDomImg d); intuition.
          }
          { pose proof (bijective_id dom img H0 H s).
            elim n; rewrite <-H1, <-Hx; auto.
          }
        }
      }
      assert (bijective dom img s <> i).
      { intro Hx.
        destruct (in_dec string_dec s dom) as [Hdin|Hdnin].
        { pose proof (bijective_dom_in dom img H0 H _ Hdin).
          rewrite Hx in H6.
          elim H4; auto.
        }
        { destruct (in_dec string_dec s img) as [Hiin|Hinin].
          { pose proof (bijective_img_in img dom H0 H _ Hiin).
            rewrite Hx in H6.
            elim (HdisjDomImg i); intuition.
          }
          { pose proof (bijective_id dom img H0 H s).
            elim n0; rewrite <-H6, <-Hx; auto.
          }
        }
      }
      bijective_correct_tac.
Qed.

