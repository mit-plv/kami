Require Import Lib.FMap Lib.Struct Semantics Syntax String List.

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

Section AlphaRename.
  Variable nameMap: string -> string.
  Variable nameMap1To1: forall x y, nameMap x = nameMap y -> x = y.
  Variable nameMapOnto: forall x, exists y, nameMap y = x.

  Definition mapName A a := {| attrName := nameMap (@attrName A a); attrType := attrType a |}.
  
  Fixpoint mapNames A (ls: list (Attribute A)) :=
    map (@mapName _) ls.

  Definition mapNamesMap A (m: M.t A) :=
    M.fold (fun k v old => M.add (nameMap k) v old) m (M.empty _).

  Lemma mapNamesMapEmpty A: mapNamesMap (M.empty A) = M.empty A.
  Proof.
    apply (M.F.P.fold_Empty); intuition.
  Qed.

  Definition mapNameUnitLabel l :=
    match l with
      | Rle None => Rle None
      | Meth None => Meth None
      | Rle (Some r) => Rle (Some (nameMap r))
      | Meth (Some {| attrName := f; attrType := v |}) => Meth (Some {| attrName := nameMap f; attrType := v |})
    end.

  Lemma mapNamesKeysEq A (m: M.t A) l:
    M.KeysEq m l ->
    M.KeysEq (mapNamesMap m) (map nameMap l).
  Proof.
    admit.
  Qed.

End AlphaRename.