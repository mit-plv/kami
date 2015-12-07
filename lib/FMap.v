Require FSets.FMapList FSets.FMapFacts.
Require Import Lists.SetoidList.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
  
Require Import Eqdep_dec.

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

Require Import FMapInterface.

Module FMapListEq (UOT : UsualOrderedType).
  Module OT := UOT_to_OT UOT.
  Module Export M := FMapList.Make(OT).
  Module Facts := FMapFacts.OrdProperties M.

    Lemma eq_leibniz_list: forall (A:Type) (xs ys: list A),
      eqlistA eq xs ys -> xs = ys.
    Proof. intros ? ? ? H; induction H; simpl; congruence. Qed.

    Lemma eqke_sub_eq A: subrelation (@M.Raw.PX.eqke A) eq.
    Proof. intros [] [] [??]; simpl in *; subst; auto. Qed.

    Lemma eq_sub_eqke A: subrelation eq (@M.Raw.PX.eqke A).
    Proof. intro H; split; subst; auto. Qed.

    Add Parametric Morphism A: (@InA A)
      with signature subrelation ==> eq ==> eq ==> impl
      as InA_rel_d.
    Proof.
      unfold impl; firstorder.
      apply InA_alt in H0.
      destruct H0 as [?[??]].
      apply InA_alt.
      exists x0; split; auto.
      apply H; auto.
    Qed.

    Add Parametric Morphism A: (@eqlistA A)
      with signature subrelation ==> eq ==> eq ==> impl
      as eqlistA_rel_d.
    Proof.
      unfold impl; firstorder.
      induction H0; auto.
      constructor; auto.
      apply H; auto.
    Qed.

    Lemma Equal_this: forall elt L1 L2,
      Equal (elt:=elt) L1 L2 -> this L1 = this L2.
    Proof.
      unfold Equal; destruct L1, L2; simpl. intros.
      lapply (SortA_equivlistA_eqlistA _ _ _ sorted0 sorted1); intros.
      clear H.
      rewrite eqke_sub_eq in H0.
      apply eq_leibniz_list in H0.
      assumption.
      * red.
      apply Facts.P.F.Equal_Equiv in H. destruct H.
      intros [a e].
      specialize (H a).
      repeat rewrite Facts.P.F.elements_in_iff in H. simpl in H.
      specialize (H0 a).
      setoid_rewrite Facts.P.F.elements_mapsto_iff in H0. simpl in H0.
      firstorder.
      edestruct H as [??]; eauto.
      specialize (H0 e x H2 H3); subst; auto.
      edestruct H1 as [??]; eauto.
      specialize (H0 x e H3 H2); subst; auto.
  Qed.

  Theorem proof_irrel_leibniz {A : Type}
    (proof_irrel : forall (P : Prop) (x y : P), x = y) (m m' : t A)
    : Equal m m' -> m = m'.
  Proof. intros H. 
  apply Equal_this in H.
  induction m. induction m'. simpl in H. induction H.
  replace sorted1 with sorted0 by (apply proof_irrel).
  reflexivity.
  Qed.

End FMapListEq.


Require Import Lib.String_as_OT.

Require Import String.

Module FMapEq := FMapListEq String_as_OT.
Module FMap := FMapEq.M. 
Module FMapF := FMapFacts.OrdProperties FMap.

Theorem FMap_dec_leibniz {A : Type}
   (eq_dec_A : forall x y : A, {x = y} + {x <> y})
  {m1 m2 : FMap.t A}
  : FMap.Equal m1 m2 -> m1 = m2.
Proof.
intros.
apply FMapEq.Equal_this in H.
induction m1. induction m2. 
simpl in *. induction H.
replace sorted0 with sorted. reflexivity. 
apply Sorted_irrel.
intros. decide equality. apply string_dec.
unfold FMap.Raw.PX.ltk. intros.
apply UIP_dec.
decide equality.
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
  apply FMap_dec_leibniz. assumption. apply H. assumption.
- unfold not. intros contra. induction contra.
  assert (FMap.equal cmp m1 m1 = true).
  apply FMap.equal_1.
  apply H. apply FMapF.P.F.Equal_refl. rewrite H0 in eqtest.
  inversion eqtest.
Qed.

Axiom proof_irrel : forall (P : Prop) (x y : P), x = y.

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

Hint Unfold FMap.empty FMap.add FMap.find FMap.remove : FMapDefs.

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
  Proof. intros. repeat autounfold with MapDefs FMapDefs. reflexivity.
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

  Lemma union_empty_2: forall {A}
 (m: Map A), union m (@empty A) = m.
  Proof.
    intros; repeat autounfold with MapDefs. simpl.
    apply FMapEq.proof_irrel_leibniz. apply proof_irrel.
    apply FMapF.P.F.Equal_refl.
  Qed.

  Lemma union_idempotent: forall {A} (m: Map A), union m m = m.
  Proof. Admitted.

  Lemma update_empty_1: forall {A} (m: Map A), update (@empty A) m = m.
  Proof. Admitted.

  Lemma update_empty_2: forall {A} (m: Map A), update m (@empty A) = m.
  Proof. Admitted.

End Facts.