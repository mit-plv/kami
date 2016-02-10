Require Import Lib.FMap Lib.Struct Semantics Syntax String List.
Require Import Program.Equality.

Set Implicit Arguments.
Section FnInv.
  Variable A B: Type.
  Variable f: A -> B.
  Variable f1To1: forall a1 a2, f a1 = f a2 -> a1 = a2.
  Variable fOnto: forall b, exists a, f a = b.
  
  Variable fInv: B -> A.
  Variable fInvFInverse: forall a, fInv (f a) = a.

  Lemma inv1To1: forall b1 b2, fInv b1 = fInv b2 -> b1 = b2.
  Proof.
    intros.
    destruct (fOnto b1) as [a1 fa1].
    destruct (fOnto b2) as [a2 fa2].
    subst.
    pose proof (fInvFInverse a1) as fa1.
    pose proof (fInvFInverse a2) as fa2.
    rewrite fa1, fa2 in H.
    f_equal; intuition.
  Qed.

  Lemma invOnto: forall a, exists b, fInv b = a.
  Proof.
    intros.
    exists (f a).
    intuition.
  Qed.

  Lemma fFInvInverse: forall b, f (fInv b) = b.
  Proof.
    intros.
    destruct (fOnto b) as [a fa].
    subst.
    f_equal.
    intuition.
  Qed.
End FnInv.

Section Rename.
  Variable p: string -> string.
  Variable p1To1: forall x y, p x = p y -> x = y.
  Variable pOnto: forall x, exists y, p y = x.

  Definition renameAttr A a := {| attrName := p (@attrName A a); attrType := attrType a |}.
  
  Fixpoint renameList A (ls: list (Attribute A)) :=
    map (@renameAttr _) ls.

  Definition renameMap A (m: M.t A) :=
    M.fold (fun k v old => M.add (p k) v old) m (M.empty _).

  Definition renameUnitLabel l :=
    match l with
      | Rle None => Rle None
      | Meth None => Meth None
      | Rle (Some r) => Rle (Some (p r))
      | Meth (Some {| attrName := f; attrType := v |}) => Meth (Some {| attrName := p f; attrType := v |})
    end.

  Definition renameLabel l :=
    match l with
    | Build_LabelT annot defs calls =>
      Build_LabelT (match annot with
                    | Some (Some r) => Some (Some (p r))
                    | x => x
                    end) (renameMap defs) (renameMap calls)
    end.
  
  Lemma renameMapEmpty A: renameMap (M.empty A) = M.empty A.
  Proof.
    apply (M.F.P.fold_Empty); intuition.
  Qed.

  Lemma renameAdd_transpose_neqkey A:
    M.F.P.transpose_neqkey
      eq
      (fun (k0 : M.key) (v0 : A) (old : M.t A) => M.add (p k0) v0 old).
  Proof.
    unfold M.F.P.transpose_neqkey; intros.
    meq; M.cmp (p k) (p k'); findeq.
    elim H; auto.
  Qed.
  Hint Immediate renameAdd_transpose_neqkey.
  
  Lemma renameMapAdd:
    forall {A} m k (v: A),
      (* ~ M.In k m -> *)
      renameMap (M.add k v m) = M.add (p k) v (renameMap m).
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
  
  Lemma renameMapsTo1 A m: forall k (v: A),
      M.MapsTo k v m ->
      M.MapsTo (p k) v (renameMap m).
  Proof.
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
      M.MapsTo (p k) v (renameMap m) ->
      M.MapsTo k v m.
  Proof.
    M.mind m.
    - apply M.F.P.F.empty_mapsto_iff in H; intuition.
    - rewrite renameMapAdd in H1; intuition; apply M.F.P.F.add_mapsto_iff in H1.
      destruct H1 as [[keq veq] | [kneq kin]].
      + specialize (p1To1 keq).
        subst.
        apply M.F.P.F.add_mapsto_iff; intuition.
      + specialize (H _ _ kin).
        assert (kneq': k <> k0) by (unfold not; intros; subst; intuition).
        apply M.F.P.F.add_mapsto_iff; intuition.
  Qed.

  Fixpoint renameAction k t (a: ActionT t k) :=
    match a with
    | MCall meth s e cont => MCall (p meth) s e (fun v => renameAction (cont v))
    | Let_ lret' e cont => Let_ e (fun v => renameAction (cont v))
    | ReadReg r k cont => ReadReg r k (fun v => renameAction (cont v))
    | WriteReg r k e cont => WriteReg r e (renameAction cont)
    | IfElse e k t f cont => IfElse e (renameAction t) (renameAction f)
                                   (fun v => renameAction (cont v))
    | Assert_ e cont => Assert_ e (renameAction cont)
    | Return e => Return e
    end.

  Definition renameRules (rules: list (Attribute (Action Void))) :=
                              map (fun x => match x with
                                         | {| attrName := r;
                                              attrType := a |} =>
                                           {| attrName := p r;
                                              attrType := fun ty => renameAction (a ty) |}
                                         end) rules.

  Definition renameMeths (meths: list DefMethT): list DefMethT.
    refine (map (fun x => match x with
                       | {| attrName := m;
                            attrType := a |} =>
                         {| attrName := p m;
                            attrType := existT _ (projT1 a)
                                               (fun ty v => _) |}
                       end) meths).
    exact (renameAction (projT2 a ty v)).
  Defined.

  Fixpoint renameModules (m: Modules) :=
    match m with
    | Mod regs rules dms => Mod (renameList regs) (renameRules rules) (renameMeths dms)
    | ConcatMod m1 m2 => ConcatMod (renameModules m1) (renameModules m2)
    end.

  Theorem traceRefinesRename m: traceRefines (renameMap (A := _)) m (renameModules m).
  Proof.
    admit.
  Qed.

  Lemma actionMapName o k a u cs r (sa: @SemAction o k a u cs r):
    SemAction (renameMap o) (renameAction a) (renameMap u) (renameMap cs) r.
  Proof.
    admit.
  Qed.

  Lemma renameKeysEq A (m: M.t A) l:
    M.KeysEq m l ->
    M.KeysEq (renameMap m) (map p l).
  Proof.
    admit.
  Qed.

End Rename.