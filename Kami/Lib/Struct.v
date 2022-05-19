Require Import String Lib.Word List Arith.
Require Import Equality Eqdep_dec FunctionalExtensionality.
Require Import Lib.CommonTactics Lib.StringEq.

Set Implicit Arguments.

Record Attribute (A : Type) := { attrName: string; attrType: A }.

Section Attribute.
  Variable A: Type.

  Implicit Types k : A.
  Implicit Types a : Attribute A.

  Lemma attribute_inv:
    forall n1 n2 k1 k2, {| attrName := n1; attrType := k1 |} = {| attrName := n2; attrType := k2 |} ->
      n1 = n2 /\ k1 = k2.
  Proof.
    intros; inv H; auto.
  Qed.

  Definition Attribute_dec (kdec: forall (k1 k2: A), {k1 = k2} + {k1 <> k2})
  : forall (a1 a2: Attribute A), {a1 = a2} + {a1 <> a2}.
  Proof.
    intros;
    repeat decide equality.
  Qed.

  Fixpoint getAttribute (n: string) (attrs: list (Attribute A)) :=
    match attrs with
      | nil => None
      | attr :: attrs' =>
        if string_eq n (attrName attr) then Some attr
        else getAttribute n attrs'
    end.
  
  
  Lemma in_NoDup_attr:
    forall a1 a2 attrs,
      NoDup (map (@attrName _) attrs) ->
      attrName a1 = attrName a2 -> In a1 attrs -> In a2 attrs -> a1 = a2.
  Proof.
    induction attrs; intros; simpl in *; [destruct H1|].
    destruct a1 as [an1 ab1], a2 as [an2 ab2]; simpl in *.
    destruct H1; [subst|].
    - destruct H2; [auto|].
      inv H; elim H3.
      replace an2 with (attrName {| attrName := an2; attrType := ab2 |}) by reflexivity.
      apply in_map; auto.
    - destruct H2.
      + subst; inv H.
        elim H3.
        replace an2 with (attrName {| attrName := an2; attrType := ab1 |}) by reflexivity.
        apply in_map; auto.
      + inv H; apply IHattrs; auto.
  Qed.
  
  Fixpoint getAttrType (n: string) (attrs: list (Attribute A)) :=
    match attrs with
      | nil => None
      | attr :: attrs' =>
        if string_eq n (attrName attr)
        then Some (attrType attr)
        else getAttrType n attrs'
    end.

  Lemma getAttrType_attrType_getAttribute n attrs:
    getAttrType n attrs = match getAttribute n attrs with
                            | None => None
                            | Some a => Some (attrType a)
                          end.
  Proof.
    induction attrs; simpl; auto.
    destruct (string_eq n (attrName a)); auto.
  Qed.
  
  Definition namesOf (attrs: list (Attribute A)) := map (@attrName _) attrs.

  Lemma namesOf_app:
    forall (l1 l2: list (Attribute A)),
      namesOf (l1 ++ l2) = namesOf l1 ++ namesOf l2.
  Proof.
    unfold namesOf; simpl; intros.
    rewrite map_app; reflexivity.
  Qed.

  Lemma getAttribute_app:
    forall n (attrs1 attrs2: list (Attribute A)) dm
           (Hdm: dm = getAttribute n (attrs1 ++ attrs2)),
      dm = getAttribute n attrs1 \/ dm = getAttribute n attrs2.
  Proof.
    induction attrs1; intros; simpl; [right; assumption|].
    simpl in Hdm; destruct (string_eq n (attrName a)); subst; intuition.
  Qed.

  Lemma getAttribute_Some_name:
    forall n (attrs: list (Attribute A)) dm
           (Hdm: Some dm = getAttribute n attrs),
      attrName dm = n.
  Proof.
    induction attrs; intros; simpl; [inv Hdm|].
    simpl in Hdm.
    remember (string_eq _ _) as seq; destruct seq; [|auto].
    apply string_eq_dec_eq in Heqseq.
    inv Hdm; reflexivity.
  Qed.

  Lemma getAttribute_Some_body:
    forall n (attrs: list (Attribute A)) dm
           (Hdm: Some dm = getAttribute n attrs),
      In dm attrs.
  Proof.
    induction attrs; intros; simpl; [inv Hdm|].
    simpl in Hdm.
    destruct (string_eq _ _); [|auto].
    left; inv Hdm; reflexivity.
  Qed.

  Lemma getAttribute_Some:
    forall n (attrs: list (Attribute A)) dm
           (Hdm: Some dm = getAttribute n attrs),
      In n (map (@attrName _) attrs).
  Proof.
    induction attrs; intros; simpl; [inv Hdm|].
    simpl in Hdm.
    remember (string_eq _ _) as seq; destruct seq.
    - left; apply string_eq_dec_eq in Heqseq; auto.
    - right; eauto.
  Qed.

  Lemma getAttribute_None:
    forall n (attrs: list (Attribute A))
           (Hdm: None = getAttribute n attrs),
      ~ In n (map (@attrName _) attrs).
  Proof.
    induction attrs; intros; intuition; inv H.
    - simpl in Hdm.
      remember (string_eq _ _) as seq; destruct seq; [inv Hdm|].
      apply string_eq_dec_neq in Heqseq; elim Heqseq; reflexivity.
    - inv Hdm.
      remember (string_eq _ _) as seq; destruct seq; [inv H1|].
      apply IHattrs; auto.
  Qed.
End Attribute.

Section MapAttr.
  Variable A B: Type.
  Variable f: A -> B.
  Definition changeAttr (a: Attribute A) := (attrName a, f (attrType a)).

  Definition mapAttr (ls: list (Attribute A)) := map changeAttr ls.
End MapAttr.

#[global] Hint Unfold attrName attrType namesOf changeAttr mapAttr.
