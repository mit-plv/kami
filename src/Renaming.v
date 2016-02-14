Require Import Lib.FMap Lib.Struct Semantics Syntax String List.
Require Import Program.Equality.

Set Implicit Arguments.

Lemma rename1To1: forall c s1 s2: string, (c ++ s1)%string = (c ++ s2)%string -> s1 = s2.
Proof.
  induction c; simpl in *; intros.
  - intuition.
  - injection H; intros H'.
    intuition.
Qed.
Hint Resolve rename1To1.

Section Rename.
  Variable i: string.
  Definition rename s := ((i ++ "--") ++ s)%string.

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
    | ReadReg r k cont => ReadReg (rename r) k (fun v => renameAction (cont v))
    | WriteReg r k e cont => WriteReg (rename r) e (renameAction cont)
    | IfElse e k t f cont => IfElse e (renameAction t) (renameAction f)
                                   (fun v => renameAction (cont v))
    | Assert_ e cont => Assert_ e (renameAction cont)
    | Return e => Return e
    end.

  Definition renameRules (rules: list (Attribute (Action Void))) :=
                              map (fun x => match x with
                                         | {| attrName := r;
                                              attrType := a |} =>
                                           {| attrName := rename r;
                                              attrType := fun ty => renameAction (a ty) |}
                                         end) rules.

  Definition renameMeths (meths: list DefMethT): list DefMethT.
    refine (map (fun x => match x with
                       | {| attrName := m;
                            attrType := a |} =>
                         {| attrName := rename m;
                            attrType := existT _ (projT1 a)
                                               (fun ty v => _) |}
                       end) meths).
    exact (renameAction (projT2 a ty v)).
  Defined.

  Fixpoint renameModules (m: Modules) :=
    match m with
    | Mod regs rules dms => Mod (renameListAttr regs) (renameRules rules) (renameMeths dms)
    | ConcatMod m1 m2 => ConcatMod (renameModules m1) (renameModules m2)
    end.
  
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

  Hint Immediate renameAdd_transpose_neqkey.
  
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
  
  Lemma renameSemAction o k a u cs r (sa: @SemAction o k a u cs r):
    SemAction (renameMap o) (renameAction a) (renameMap u) (renameMap cs) r.
  Proof.
    dependent induction sa; simpl in *.
    - rewrite HAcalls; simpl in *.
      rewrite renameMapAdd.
      eapply SemMCall; eauto; intuition.
    - eapply SemLet; eauto; intuition.
    - rewrite renameMapFind in HRegVal.
      eapply SemReadReg; eauto.
    - eapply SemWriteReg; eauto.
      rewrite <- renameMapAdd.
      f_equal; intuition.
    - eapply SemIfElseTrue; eauto.
      rewrite <- renameMapUnion.
      f_equal; intuition.
      rewrite <- renameMapUnion.
      f_equal; intuition.
    - eapply SemIfElseFalse; eauto.
      rewrite <- renameMapUnion.
      f_equal; intuition.
      rewrite <- renameMapUnion.
      f_equal; intuition.
    - eapply SemAssertTrue; eauto.
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
        (intros; specialize (rename1To1 (i ++ "--") s1 s2); intuition).
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

  Lemma renameMapsTo2 A m: forall k (v: A),
      M.MapsTo (rename k) v (renameMap m) ->
      M.MapsTo k v m.
  Proof.
    assert (rename1To1': forall s1 s2, rename s1 = rename s2 -> s1 = s2) by
        (intros; specialize (rename1To1 (i ++ "--") s1 s2); intuition).
    M.mind m.
    - apply M.F.P.F.empty_mapsto_iff in H; intuition.
    - rewrite renameMapAdd in H1; intuition; apply M.F.P.F.add_mapsto_iff in H1.
      destruct H1 as [[keq veq] | [kneq kin]].
      + specialize (rename1To1' _ _ keq).
        subst.
        apply M.F.P.F.add_mapsto_iff; intuition.
      + specialize (H _ _ kin).
        assert (kneq': k <> k0) by (unfold not; intros; subst; intuition).
        apply M.F.P.F.add_mapsto_iff; intuition.
  Qed.

  Lemma renameMapsTo A m: forall k (v: A),
      M.MapsTo k v m <-> M.MapsTo (rename k) v (renameMap m).
  Proof.
    intros; constructor.
    - apply renameMapsTo1.
    - apply renameMapsTo2.
  Qed.

  Lemma MapsToIn1 A m k (v: A):
    M.MapsTo k v m -> M.In k m.
  Proof.
    unfold M.MapsTo, M.In.
    unfold M.Raw.PX.In.
    intros.
    eexists; eauto.
  Qed.

  Lemma MapsToIn2 A m k:
    M.In k m -> (exists (v: A), M.MapsTo k v m).
  Proof.
    unfold M.MapsTo, M.In.
    unfold M.Raw.PX.In.
    intuition.
  Qed.

  Lemma renameMapIn1 A (m: M.t A): forall k,
      M.In k m -> M.In (rename k) (renameMap m).
  Proof.
    intros. 
    apply MapsToIn2 in H.
    destruct H.
    apply renameMapsTo in H.
    apply (MapsToIn1 (v := x)); intuition.
  Qed.

  Lemma renameMapIn2 A (m: M.t A): forall k,
      M.In (rename k) (renameMap m) -> M.In k m.
  Proof.
    intros. 
    apply MapsToIn2 in H.
    destruct H.
    apply renameMapsTo in H.
    apply (MapsToIn1 (v := x)); intuition.
  Qed.

  (*
  Lemma renameKeysEq A (m: M.t A) l: M.KeysEq m l -> M.KeysEq (renameMap m) (map rename l).
  Proof.
    intros keysEq.
    unfold M.KeysEq in *.
    assert (keysEq1: forall k, M.Map.In k m -> In k l) by
        (intros k0; specialize (keysEq k0); intuition).
    assert (keysEq2: forall k, In k l -> M.Map.In k m) by
        (intros k0; specialize (keysEq k0); intuition).
    clear keysEq.
    constructor; intros.
    split in keysEq.
    specialize (keysEq k).
    destruct keysEq as [fwd bck].
    destruct (renameMapIn m k) as 
    assert (fwd: forall v, M.MapsTo k v m -> In k l) by
        (intros v mmap;
         apply (fwd' (MapsToIn1 mmap))).
    assert (bck: In k l -> (exists v, M.MapsTo k v m)) by intuition.
    clear fwd' bck'.
    constructor; intros H'.
    destruct (MapsToIn2 H') as [v mmap]; clear H'.
    assert (H: 
mmap]
    clear fwd' bck'.
    pose proof (MapsToIn (renameMap m) k) as [lfact rfact].
    constructor; intros.
    - destruct (rfact H) as [v mmap].
    intros ink.
    intuition.
        (intros [v mmap];
         pose proof (MapsToIn m k) as [lfact rfact];
         apply (fwd' (lfact (@ex_intro _ _ v mmap)))).
    firstorder.
    intuition.
    assert (M.In k m) by apply (or_introl (MapsToIn m k)) in mmap.
    eapply MapsToIn in mmap.
    eapply MapsToIn.
      by (apply MapsToIn; intuition).
    rewrite MapsToIn in fwd.
    constructor; intros.
    - apply MapsToIn in H.
      destruct H as [v mrn].
      apply MapsToIn in keysEq.

  Lemma renameSubstep m o u ul cs (sa: @Substep m o u ul cs):
    Substep (renameModules m) (renameMap o) (renameMap u) (renameUnitLabel ul) (renameMap cs).
  Proof.
    dependent induction sa; simpl in *.
    - repeat rewrite renameMapEmpty.
      constructor.
      unfold renameModules.
      simpl in *.
   *)
  
  Lemma renameSemActionRev o k a' u cs r:
    SemAction o (renameAction a') u cs r ->
    exists o' u' cs',
      o = renameMap o' /\
      u = renameMap u' /\
      cs = renameMap cs' /\
      @SemAction o' k a' u' cs' r.
  Proof.
    intros sa; simpl in *.
    dependent induction sa; simpl in *; intros.
    - destruct a'; simpl in *.
      injection x; intros.
      admit.
  Admitted.
  (*     CommonTactics.destruct_existT. *)
  (*     rewrite H2 in H0. *)
  (*     apply Eqdep.EqdepTheory.inj_pair2. subst. *)
  (*   - destruct IHsa as [o' [u' [cs' [oEq [aEq [uEq [csEq sa']]]]]]]; subst. *)
  (*     rewrite aEq in sa. *)
  (*     exists o'. *)
  (*     exists (MCall *)
  (*     constructor. *)
  (*   - destruct IHsa as [[[ ] ] ]. *)
  (*   - specialize (IHsa _ eq_refl eq_refl). *)
  (*   - specialize (IHsa o a u cs). *)
  (*   - rewrite HAcalls; simpl in *. *)
  (*     rewrite renameMapAdd. *)
  (*     eapply SemMCall; eauto; intuition. *)
  (*   - eapply SemLet; eauto; intuition. *)
  (*   - rewrite renameMapFind in HRegVal. *)
  (*     eapply SemReadReg; eauto. *)
  (*   - eapply SemWriteReg; eauto. *)
  (*     rewrite <- renameMapAdd. *)
  (*     f_equal; intuition. *)
  (*   - eapply SemIfElseTrue; eauto. *)
  (*     rewrite <- renameMapUnion. *)
  (*     f_equal; intuition. *)
  (*     rewrite <- renameMapUnion. *)
  (*     f_equal; intuition. *)
  (*   - eapply SemIfElseFalse; eauto. *)
  (*     rewrite <- renameMapUnion. *)
  (*     f_equal; intuition. *)
  (*     rewrite <- renameMapUnion. *)
  (*     f_equal; intuition. *)
  (*   - eapply SemAssertTrue; eauto. *)
  (*   - eapply SemReturn; eauto. *)
  (* Qed. *)


  Theorem traceRefinesRename m: traceRefines (renameMap (A := _)) m (renameModules m).
  Proof.
    admit.
  Qed.
(*
  Lemma renameSubstep m o u ul cs (ss: @Substep m o u ul cs):
    Substep (renameModules m) (renameMap o) (renameMap u) (renameUnitLabel ul) (renameMap cs).
  Proof.
    induction ss; simpl in *.
    - rewrite renameMapEmpty.
      constructor.
      admit.
    - rewrite renameMapEmpty.
      constructor.
      admit.
    - pose proof (renameSemAction HAction) as act1.
      simpk
    
  Lemma renameKeysEq A (m: M.t A) l:
    M.KeysEq m l ->
    M.KeysEq (renameMap m) (map p l).
  Proof.
    admit.
  Qed.

*)
End Rename.