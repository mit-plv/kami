Require FSets.FMapList FSets.FMapFacts.
Require Import Structures.OrderedType.
Require Import Lib.String_as_OT.

Require Import Eqdep_dec.

Require Import String.

Scheme Sorted_ind' := Induction for Sorted Sort Prop.

Theorem eq_rect_eq_list :
  forall (A : Type), (forall (x y : A), {x = y} + {x <> y}) ->
  forall (p:list A) (Q:list A->Type) (x:Q p) (h:p=p), 
  x = eq_rect p Q x p h.
Proof.
intros.
apply K_dec_type with (p := h).
apply list_eq_dec.
assumption.
reflexivity.
Qed.

Scheme HdRel_ind' := Induction for HdRel Sort Prop.


Fixpoint HdRel_irrel {A : Type} {le : A -> A -> Prop}
  (eq_dec_A : forall x y : A, {x = y} + {x <> y})
  (le_irrel : forall {x y} (a b : le x y), a = b)
  (x : A) (xs : list A) p {struct p}
  : forall (q : HdRel le x xs), p = q.
Proof.
induction p using HdRel_ind'; intros.
- replace (HdRel_nil le x) with
  (eq_rect _ (fun xs => HdRel le x xs) (HdRel_nil le x) _ eq_refl)
  by reflexivity.
  generalize (@eq_refl (list A) nil).
  pattern (@nil A) at 1 3 4 6, q. destruct q; intro Heq.
  + rewrite <- eq_rect_eq_list by assumption. reflexivity.
  + inversion Heq.
- replace (HdRel_cons le x b l r) with
  (eq_rect _ (HdRel le x) (HdRel_cons le x b l r) _ eq_refl)
  by reflexivity.
  generalize (eq_refl (b :: l)).
  pattern (b :: l) at 1 3 4 6, q. destruct q; intro Heq.
  + inversion Heq.
  + inversion Heq. subst.
    rewrite <- eq_rect_eq_list by assumption.
    replace r with l1 by (apply le_irrel).
    reflexivity.
Qed.

Fixpoint Sorted_irrel {A : Type} {le : A -> A -> Prop}
  (eq_dec_A : forall x y : A, {x = y} + {x <> y})
  (le_irrel : forall {x y} (a b : le x y), a = b)
  (xs : list A) p {struct p}
  : forall (q : Sorted le xs), p = q.
Proof.
induction p using Sorted_ind'; intros.
- replace (Sorted_nil le) with
    (eq_rect _ (fun l => Sorted le l) (Sorted_nil le) _ eq_refl)
    by reflexivity.
  generalize (@eq_refl (list A) nil).
    pattern (@nil A) at 1 3 4 6, q. destruct q; intro Heq.
    + rewrite <- eq_rect_eq_list by assumption. reflexivity.
    + inversion Heq.
- replace (Sorted_cons p h) with
    (eq_rect _ (fun l => Sorted le l) (Sorted_cons p h) _ eq_refl)
    by reflexivity.
  generalize (eq_refl (a :: l)).
    pattern (a :: l) at 1 3 4 6, q. destruct q; intro Heq.
    + inversion Heq.
    + inversion Heq. subst. 
      rewrite <- (eq_rect_eq_list) by assumption.
      replace q with p by apply IHp.
      replace h0 with h. reflexivity.
      apply HdRel_irrel; assumption.
Qed.

Module FMap := FMapList.Make String_as_OT. 
Module FMapF := FMapFacts.OrdProperties FMap.

Theorem FMap_equal {A : Type}
   (eq_dec_A : forall x y : A, {x = y} + {x <> y})
  {m1 m2 : FMap.t A}
  : FMap.Equal m1 m2 -> m1 = m2.
Proof.
induction m1. induction m2. intros. 
assert (this = this0).
Focus 2.
induction H0.
replace sorted0 with sorted.
trivial. 
apply Sorted_irrel.
intros. decide equality. apply string_dec.
unfold FMap.Raw.PX.ltk. intros.
apply UIP_dec.
decide equality.

apply (FMapF.P.F.Equal_Equivb_eqdec eq_dec_A) in H.
apply FMap.Raw.equal_1 in H;
  try assumption.
simpl in H.

generalize dependent this0.
induction this; induction this0; intros. simpl in H.
reflexivity. inversion H. destruct a in H. inversion H.
simpl in H. destruct a, a0.
destruct (String_as_OT.compare s s0). inversion H.
destruct (eq_dec_A a a0); simpl in H.
unfold String_as_OT.eq in e. subst. 
f_equal. apply IHthis.
inversion sorted; clear sorted; subst. assumption.
inversion sorted0; clear sorted0; subst. assumption.
assumption.
inversion H. inversion H.
Qed.

Theorem FMap_dec {A : Type}
  (eq_dec_A : forall x y : A, {x = y} + {x <> y })
  (m1 m2 : FMap.t A)
  : {m1 = m2} + {m1 <> m2}.
Proof.
pose (cmp := fun x y => if eq_dec_A x y then true else false).
pose proof (FMapF.P.F.Equal_Equivb_eqdec eq_dec_A).
destruct (FMap.equal cmp m1 m2) eqn:eqtest; [left | right].
- apply FMap.equal_2 in eqtest.
  apply FMap_equal. assumption. apply H. assumption.
- unfold not. intros contra. induction contra.
  assert (FMap.equal cmp m1 m1 = true).
  apply FMap.equal_1.
  apply H. apply FMapF.P.F.Equal_refl. rewrite H0 in eqtest.
  inversion eqtest.
Qed.

Section Map.

  Definition Map := FMap.t.

  Definition empty := FMap.empty.
  Definition unionL {A : Type} (m1 m2 : Map A) := FMap.fold 
    (@FMap.add A) m2 m1.

  Definition unionR {A : Type} (m1 m2 : Map A) := unionL m2 m1.

  Definition add {A : Type} := @FMap.add A.
  Definition union {A : Type} := @unionL A.
  Definition find {A : Type} := @FMap.find A.
  Definition remove {A : Type} := @FMap.remove A.

  Definition update {A : Type} := @unionR A.

  Definition MapsTo {A : Type} := @FMap.MapsTo A.
  Definition Equal {A : Type} := @FMap.Equal A.

  Lemma Equal_val: forall {A : Type} (m1 m2: Map A) k, m1 = m2 -> find k m1 = find k m2.
  Proof. intros; subst; reflexivity. Qed.

End Map.

Hint Unfold empty unionL unionR add union
     find remove update : MapDefs.

Hint Unfold MapsTo Equal : MapDefs.

Require Import Lib.Struct Lib.CommonTactics.

Section StringEq.
  Definition string_eq s1 s2 :=
    match string_dec s1 s2 with
      | left _ => true
      | right _ => false
    end.

  Lemma string_dec_eq: forall s, string_eq s s = true.
  Proof.
    intros; unfold string_eq; destruct (string_dec s s).
    - reflexivity.
    - elim n; reflexivity.
  Qed.

  Lemma string_dec_neq: forall s t, s <> t <-> string_eq s t = false.
  Proof.
    intros; unfold string_eq; destruct (string_dec s t); intuition.
  Qed.

  Lemma string_eq_append:
    forall p s t, string_eq s t = false -> string_eq (p -n- s) (p -n- t) = false.
  Proof.
    unfold string_eq; intros.
    destruct (string_dec s t); [inversion H|].
    destruct (string_dec (p -n- s) (p -n- t)); [|reflexivity].
    elim n; clear -e.
    induction p.
    - unfold appendName in e; simpl in e; inversion e; auto.
    - inversion e; apply IHp; auto.
  Qed.

End StringEq.

Section Facts.

  Lemma find_empty : forall {A} k, (find k (@empty A)) = None.
  Proof. intros. repeat autounfold with MapDefs.
  apply FMapF.P.F.not_find_in_iff.
  unfold not.
  apply FMapF.P.F.empty_in_iff.
  Qed.

  Lemma find_add_1 : forall {A} k v (m: Map A), find k (add k v m) = Some v.
  Proof. intros. repeat autounfold with MapDefs.
  apply FMap.find_1. apply FMap.add_1. reflexivity.
  Qed.

  Lemma find_add_2: forall {A} k k' v (m: Map A),
                      string_eq k' k = false -> find k (add k' v m) = find k m.
  Proof.
    intros; repeat autounfold with MapDefs.
    apply FMapF.P.F.add_neq_o.
    apply string_dec_neq. assumption.
  Qed.

 Lemma add_empty_neq: forall {A} (m: Map A) k v, add k v m = @empty A -> False.
  Proof.
    intros; apply @Equal_val with (k:= k) in H.
    repeat autounfold with MapDefs in H.
    rewrite find_empty in H. rewrite find_add_1 in H.
    inversion H.
  Qed.
  
  Lemma union_empty_1: forall {A} (m: Map A), union (@empty A) m = m.
  Proof.
    intros; repeat autounfold with MapDefs. admit.
  Qed.

  Lemma union_empty_2: forall {A} (dec_eq_A : forall x y : A, {x = y} + {x <> y})
 (m: Map A), union m (@empty A) = m.
  Proof.
    intros; repeat autounfold with MapDefs.
    apply FMap_equal. assumption.
    apply FMapF.P.F.Equal_refl.
  Qed.

  Lemma union_idempotent: forall {A} (m: Map A), union m m = m.
  Proof. Admitted.

  Lemma update_empty_1: forall {A} (m: Map A), update (@empty A) m = m.
  Proof. Admitted.

  Lemma update_empty_2: forall {A} (m: Map A), update m (@empty A) = m.
  Proof. Admitted.

End Facts.