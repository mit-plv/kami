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

Definition HdRel_irrel {A : Type} {le : A -> A -> Prop}
  (le_irrel : forall {x y} (a b : le x y), a = b)
  (x : A) (xs : list A) (p q : HdRel le x xs)
  : p = q.
Proof. 
induction p using HdRel_ind'.
- refine (
  match q as q' in HdRel _ _ xs return 
    (match xs with 
       | nil => fun (q : HdRel le x nil) => HdRel_nil le x = q
       | _ :: _ => fun _ => True
       end q'
    )
      with
      | HdRel_nil => eq_refl
      | HdRel_cons _ _ _ => I
  end
  ).
- generalize dependent r.
  assert (forall r : le x (hd b (b :: l)), HdRel_cons le x b l r = q).
  2:assumption.
refine (
  match q as q' in HdRel _ _ xs return
    forall r' : le x (hd b xs), (match xs as xs'
      return HdRel le x xs' -> le x (hd b xs') -> Prop with
      | nil => fun _ _ => True
      | b' :: l' => fun (q'' : HdRel le x _) r''
         => HdRel_cons le x b' l' r'' = q''
     end q' r')
  with
    | HdRel_nil => fun _ => I
    | HdRel_cons _ _ _ => fun _ => _
  end
  ).
  replace r' with l1 by apply le_irrel.
  reflexivity.
Qed.

Theorem Sorted_irrel {A : Type} {le : A -> A -> Prop}
  (le_irrel : forall {x y} (a b : le x y), a = b)
  (xs : list A) p
  : forall (q : Sorted le xs), p = q.
Proof.
induction p using Sorted_ind'; intros.
- refine (
  match q as q' in Sorted _ xs return 
    (match xs with 
       | nil => fun (q : Sorted le nil) => Sorted_nil le = q
       | _ :: _ => fun _ => True
       end q'
    )
      with
      | Sorted_nil => eq_refl
      | Sorted_cons _ _ _ _ => I
  end
  ).
- generalize dependent h.
  generalize dependent p.
  assert (forall p : Sorted le (tl (a :: l)),
    (forall q' : Sorted le (tl (a :: l)), p = q') -> 
    forall h : HdRel le (hd a (a :: l)) (tl (a :: l)), Sorted_cons p h = q).
  2:assumption.
refine (
  match q as q' in Sorted _ xs return
    (forall p : Sorted le (tl xs),
    (forall q' : Sorted le (tl xs), p = q') -> 
    forall h : HdRel le (hd a xs) (tl xs),
    (match xs as xs'
      return Sorted le (tl xs') -> HdRel le (hd a xs') (tl xs') ->
             Sorted le xs' -> Prop with
      | nil => fun _ _ _ => True
      | a' :: l' => fun p' h' q''
         => Sorted_cons p' h' = q''
     end p h q'))
  with
    | Sorted_nil => fun _ _ _ => I
    | Sorted_cons _ _ _ _ => fun _ _ _ => _
  end
  ).
  replace h0 with h. replace p with s. reflexivity. 
  symmetry. apply _H. apply HdRel_irrel; assumption.
Qed.

Require Import FMapInterface.

Module FMapListEq (UOT : UsualOrderedType) <: FMapInterface.S
  with Module E := UOT.
  Module OT := UOT_to_OT UOT.
  Module Export M := FMapList.Make(OT).
  Include M.
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

  Theorem lt_irrel_leibniz {A : Type}
  (lt_irrel : forall (a b : UOT.t) (x y : UOT.lt a b), x = y) (m m' : t A)
    : Equal m m' -> m = m'.
  Proof. intros H. 
  apply Equal_this in H.
  induction m. induction m'. simpl in H. induction H.
  replace sorted1 with sorted0.
  reflexivity. apply Sorted_irrel.
  intros. destruct x, y. apply lt_irrel.
  Qed.

End FMapListEq.

Require Import Equalities.

Module Type LT_IRREL (Import T : OrderedType).
  Parameter Inline lt_irrel : forall (x y : t) (p q : lt x y), p = q.
End LT_IRREL.

Module Type UsualOrderedTypeUIP := UsualOrderedType <+ LT_IRREL.

Module Type MapLeibniz.
  Declare Module E : UsualOrderedType.
  Include Sfun E.

  Parameter leibniz : forall {A : Type} (m m' : t A), Equal m m' -> m = m'.
End MapLeibniz.

Module LeibnizFacts (M : MapLeibniz).
  Export M.
  Module Export F := FMapFacts.OrdProperties M.
  Include F.

  Theorem empty_canon {A : Type} : forall (m : t A), Empty m -> m = empty A.
  Proof.
  intros. apply leibniz. unfold Equal. unfold Empty in H.
  intros k. rewrite F.P.F.empty_o. apply F.P.F.not_find_in_iff.
  unfold In. firstorder.
  Qed.

  Theorem add_canon {A : Type} {x} {e : A} {m m' : t A} :
    F.P.Add x e m m' -> m' = add x e m.
  Proof. intros. apply leibniz. assumption. Qed.

  Theorem map_induction {A : Type} {P : t A -> Type} :
    P (empty A)
    -> (forall m, P m -> forall k v, ~ In k m -> P (add k v m))
    -> forall m, P m.
  Proof. intros. apply F.P.map_induction.
  intros. replace m0 with (empty A). assumption. symmetry. apply empty_canon.
  assumption. intros. replace m' with (add x e m0).
  apply X0; assumption. symmetry. apply add_canon. assumption.
  Qed.
  
  Lemma add_idempotent : forall {A} k (e : A) m, MapsTo k e m
  -> add k e m = m. 
  Proof. intros. apply leibniz. unfold Equal. intros.
  rewrite F.P.F.add_o. destruct (E.eq_dec k y).
  rewrite <- e0. symmetry. apply F.P.F.find_mapsto_iff. assumption.
  reflexivity.
  Qed.

  Definition unionL {A} (m m' : t A) := fold (@add A) m' m.

  Definition union {A} := @unionL A.

  Lemma union_empty_L {A : Type} : forall m, union (empty A) m = m.
  Proof. intros. unfold union, unionL. 
  apply leibniz. apply F.P.fold_identity.
  Qed.

  Lemma union_empty_R {A : Type} : forall m, union m (empty A) = m.
  Proof. intros. unfold union, unionL. pattern m.
  apply map_induction.
  - apply leibniz. apply F.P.fold_identity.
  - intros. apply F.P.fold_Empty. auto. apply empty_1.
  Qed.

  Lemma transpose_neqkey_add {A : Type} 
    : F.P.transpose_neqkey Equal (add (elt:=A)).
  Proof. unfold F.P.transpose_neqkey. intros. 
  unfold Equal. intros y. do 4 rewrite F.P.F.add_o.
  destruct (E.eq_dec k y); destruct (E.eq_dec k' y);
  unfold E.eq in *; subst; congruence || reflexivity.
  Qed.

  Lemma union_smothered {A : Type} : forall (m m' : t A),
    (forall k, In k m -> In k m')
    -> (forall k v, MapsTo k v m -> MapsTo k v m')
    -> union m' m = m'.
  Proof. intros m. pattern m. apply map_induction; intros.
  - apply union_empty_R.
  - unfold union, unionL in *. apply leibniz. unfold Equal.
    intros y. rewrite F.P.fold_add. rewrite H. 
    rewrite F.P.F.add_o. destruct (E.eq_dec k y); unfold E.eq in *.
    symmetry. apply F.P.F.find_mapsto_iff. apply H2.
    apply add_1. assumption. reflexivity. 
    intros. apply H1.
    destruct (E.eq_dec k k0); unfold E.eq in *.
    unfold In. exists v. apply add_1. assumption. apply F.P.F.add_neq_in_iff. 
    assumption. assumption.
    intros. apply H2. destruct (E.eq_dec k k0); unfold E.eq in *.
    subst. apply False_rect. apply H0. exists v0. assumption.
    apply add_2; assumption.
    auto. apply F.P.F.add_m_Proper. apply transpose_neqkey_add.
    assumption.
  Qed.

  Lemma union_idempotent {A : Type} : forall (m : t A), union m m = m.
  Proof. intros. apply union_smothered; auto.
  Qed.

  Lemma add_empty_neq: forall {A} (m: t A) k v, add k v m <> @empty A.
  Proof.
    intros; unfold not; intros H. pose proof (@empty_1 A).
    rewrite <- H in H0. unfold Empty in H0.
    eapply H0. apply add_1. reflexivity.
  Qed.

  Theorem eq_dec {A : Type}
  (eq_dec_A : forall x y : A, {x = y} + {x <> y })
  (m1 m2 : t A)
  : {m1 = m2} + {m1 <> m2}.
  Proof.
    pose (cmp := fun x y => if eq_dec_A x y then true else false).
    pose proof (F.P.F.Equal_Equivb_eqdec eq_dec_A).
    destruct (equal cmp m1 m2) eqn:eqtest; [left | right].
    - apply equal_2 in eqtest.
      apply leibniz. apply H. assumption.
    - unfold not. intros contra. induction contra.
      assert (equal cmp m1 m1 = true).
      apply equal_1.
      apply H. apply F.P.F.Equal_refl. rewrite H0 in eqtest.
      inversion eqtest.
  Qed.

End LeibnizFacts.
  

Module FMapListEqUIP (UOT : UsualOrderedTypeUIP) <: MapLeibniz.
  Module Export M := FMapListEq UOT.
  Include M.
  
  Theorem leibniz {A : Type} (m m' : t A) : Equal m m' -> m = m'.
  Proof. apply lt_irrel_leibniz. apply UOT.lt_irrel. Qed.
End FMapListEqUIP.

Require Import Lib.String_as_OT.

Require Import String.

Module String_as_OT' <: UsualOrderedTypeUIP.
  Include String_as_OT.
  Lemma lt_irrel : forall (x y : t) (p q : lt x y), p = q.
  Proof. intros. apply UIP_dec. decide equality. 
  Qed.
End String_as_OT'.

Module FMap := FMapListEqUIP String_as_OT'. 
Module FMapF := LeibnizFacts FMap.

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

End Facts.