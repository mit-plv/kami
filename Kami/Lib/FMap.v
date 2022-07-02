Require Import String.
Require FSets.FMapList FSets.FMapFacts.
Require Import Lists.SetoidList.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import Equalities Eqdep_dec FMapInterface.

Require Import Lib.CommonTactics Lib.StringAsOT Lib.StringEq Lib.Struct.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section Lists. (* For dealing with domains *)
  Context {A: Type}.
  
  Definition DisjList (l1 l2: list A) := forall e, ~ In e l1 \/ ~ In e l2.
  Definition SubList (l1 l2: list A) := forall e, In e l1 -> In e l2.
  Definition EquivList (l1 l2: list A) := SubList l1 l2 /\ SubList l2 l1.

  Lemma SubList_nil: forall l, SubList nil l.
  Proof. unfold SubList; intros; inv H. Qed.

  Lemma SubList_nil_inv: forall l, SubList l nil -> l = nil.
  Proof.
    unfold SubList; intros; destruct l; auto.
    specialize (H a (or_introl eq_refl)); inv H.
  Qed.
  
  Lemma SubList_cons: forall a l1 l2, In a l2 -> SubList l1 l2 -> SubList (a :: l1) l2.
  Proof. unfold SubList; intros; inv H1; auto. Qed.

  Lemma SubList_cons_inv: forall a l1 l2, SubList (a :: l1) l2 -> In a l2 /\ SubList l1 l2.
  Proof. unfold SubList; intros; split; intuition. Qed.

  Lemma SubList_cons_right: forall a l1 l2, SubList l1 l2 -> SubList l1 (a :: l2).
  Proof. unfold SubList; intros; right; auto. Qed.
  
  Lemma SubList_refl: forall l, SubList l l.
  Proof. unfold SubList; intros; auto. Qed.

  Lemma SubList_refl': forall l1 l2, l1 = l2 -> SubList l1 l2.
  Proof. intros; subst; apply SubList_refl. Qed.
  
  Lemma SubList_trans:
    forall l1 l2 l3, SubList l1 l2 -> SubList l2 l3 -> SubList l1 l3.
  Proof. unfold SubList; intros; auto. Qed.

  Lemma SubList_app_1: forall l1 l2 l3, SubList l1 l2 -> SubList l1 (l2 ++ l3).
  Proof.
    unfold SubList; intros; apply in_or_app; left; auto.
  Qed.

  Lemma SubList_app_2: forall l1 l2 l3, SubList l1 l3 -> SubList l1 (l2 ++ l3).
  Proof.
    unfold SubList; intros; apply in_or_app; right; auto.
  Qed.

  Lemma SubList_app_3: forall l1 l2 l3, SubList l1 l3 -> SubList l2 l3 -> SubList (l1 ++ l2) l3.
  Proof.
    unfold SubList; intros.
    apply in_app_or in H1; destruct H1; intuition.
  Qed.

  Lemma SubList_app_4: forall l1 l2 l3, SubList (l1 ++ l2) l3 -> SubList l1 l3.
  Proof.
    unfold SubList; intros; apply H; apply in_or_app; left; auto.
  Qed.

  Lemma SubList_app_5: forall l1 l2 l3, SubList (l1 ++ l2) l3 -> SubList l2 l3.
  Proof.
    unfold SubList; intros; apply H; apply in_or_app; right; auto.
  Qed.

  Lemma SubList_app_6:
    forall l1 l2 l3 l4, SubList l1 l2 -> SubList l3 l4 -> SubList (l1 ++ l3) (l2 ++ l4).
  Proof.
    intros; apply SubList_app_3.
    - apply SubList_app_1; auto.
    - apply SubList_app_2; auto.
  Qed.

  Lemma SubList_app_7:
    forall l1 l2 l3, SubList (l1 ++ l2) l3 -> SubList l1 l3 /\ SubList l2 l3.
  Proof.
    intros; split.
    - eapply SubList_app_4; eauto.
    - eapply SubList_app_5; eauto.
  Qed.

  Lemma SubList_app_comm:
    forall l1 l2 l3, SubList l1 (l2 ++ l3) -> SubList l1 (l3 ++ l2).
  Proof.
    unfold SubList; intros.
    apply in_or_app.
    specialize (H e H0); apply in_app_or in H; intuition.
  Qed.

  Lemma SubList_app_idempotent:
    forall l1 l2, SubList l1 (l2 ++ l2) -> SubList l1 l2.
  Proof.
    unfold SubList; intros.
    specialize (H e H0).
    apply in_app_or in H; intuition.
  Qed.

  Lemma EquivList_nil: EquivList nil nil.
  Proof. split; unfold SubList; intros; inv H. Qed.

  Lemma EquivList_nil_inv_1: forall l, EquivList l nil -> l = nil.
  Proof. intros; inv H; apply SubList_nil_inv; auto. Qed.

  Lemma EquivList_nil_inv_2: forall l, EquivList nil l -> l = nil.
  Proof. intros; inv H; apply SubList_nil_inv; auto. Qed.

  Lemma EquivList_cons:
    forall a1 a2 l1 l2,
      EquivList l1 l2 -> a1 = a2 -> EquivList (a1 :: l1) (a2 :: l2).
  Proof.
    intros; inv H; subst; split;
      try (apply SubList_cons; [left; auto|apply SubList_cons_right; auto]).
  Qed.

  Lemma EquivList_refl: forall l, EquivList l l.
  Proof. intros; split; apply SubList_refl. Qed.
  
  Lemma EquivList_comm: forall l1 l2, EquivList l1 l2 -> EquivList l2 l1.
  Proof. unfold EquivList; intros; dest; split; auto. Qed.

  Lemma EquivList_trans:
    forall l1 l2 l3, EquivList l1 l2 -> EquivList l2 l3 -> EquivList l1 l3.
  Proof. intros; inv H; inv H0; split; eapply SubList_trans; eauto. Qed.

  Lemma EquivList_app:
    forall l1 l2 l3 l4,
      EquivList l1 l2 -> EquivList l3 l4 ->
      EquivList (l1 ++ l3) (l2 ++ l4).
  Proof.
    unfold EquivList; intros; dest; split.
    - apply SubList_app_3.
      + apply SubList_app_1; auto.
      + apply SubList_app_2; auto.
    - apply SubList_app_3.
      + apply SubList_app_1; auto.
      + apply SubList_app_2; auto.
  Qed.

  Lemma EquivList_app_comm: forall l1 l2, EquivList (l1 ++ l2) (l2 ++ l1).
  Proof.
    unfold EquivList; intros; split.
    - apply SubList_app_3.
      + apply SubList_app_2, SubList_refl; auto.
      + apply SubList_app_1, SubList_refl; auto.
    - apply SubList_app_3.
      + apply SubList_app_2, SubList_refl; auto.
      + apply SubList_app_1, SubList_refl; auto.
  Qed.

  Lemma EquivList_app_idempotent:
    forall l1 l2, EquivList l1 (l2 ++ l2) -> EquivList l1 l2.
  Proof.
    unfold EquivList; intros; dest; split.
    - apply SubList_app_idempotent; auto.
    - eapply SubList_app_4; eauto.
  Qed.

  Lemma DisjList_nil_1: forall l, DisjList nil l.
  Proof. unfold DisjList; auto. Qed.

  Lemma DisjList_nil_2: forall l, DisjList l nil.
  Proof. unfold DisjList; auto. Qed.

  Lemma DisjList_cons:
    forall a l1 l2, DisjList (a :: l1) l2 -> DisjList l1 l2.
  Proof.
    unfold DisjList; intros.
    specialize (H e); intuition.
  Qed.

  Lemma DisjList_comm: forall l1 l2, DisjList l1 l2 -> DisjList l2 l1.
  Proof. 
    intros. unfold DisjList in *. intros e. specialize (H e). intuition.
  Qed.

  Lemma DisjList_SubList: forall sl1 l1 l2, SubList sl1 l1 -> DisjList l1 l2 -> DisjList sl1 l2.
  Proof. 
    intros. unfold SubList, DisjList in *. intros e. 
    specialize (H e). specialize (H0 e). intuition.
  Qed.

  Lemma NoDup_DisjList:
    forall l1 l2,
      NoDup l1 -> NoDup l2 -> DisjList l1 l2 ->
      NoDup (l1 ++ l2).
  Proof.
    induction l1; simpl; intros; auto.
    inv H; constructor.
    - intro Hx; apply in_app_or in Hx; destruct Hx; [auto|].
      specialize (H1 a); destruct H1; auto.
      elim H1; simpl; tauto.
    - apply IHl1; auto.
      eapply DisjList_cons; eauto.
  Qed.

  Lemma DisjList_app_1: forall l1 l2 l3, DisjList l1 (l2 ++ l3) -> DisjList l1 l2.
  Proof. 
    intros. unfold DisjList in *. intros e.
    destruct (H e); [left | right].
    - assumption.
    - intuition.
  Qed.

  Lemma DisjList_app_2: forall l1 l2 l3, DisjList l1 (l2 ++ l3) -> DisjList l1 l3.
  Proof. 
    intros. unfold DisjList in *. intros e.
    destruct (H e); [left | right].
    - assumption.
    - intuition.
  Qed.

  Lemma DisjList_app_3:
    forall l1 l2 l3, DisjList (l1 ++ l2) l3 -> DisjList l1 l3 /\ DisjList l2 l3.
  Proof.
    intros; unfold DisjList in *; split.
    - intros; destruct (H e).
      + left; intuition.
      + right; intuition.
    - intros; destruct (H e).
      + left; intuition.
      + right; intuition.
  Qed.

  Lemma DisjList_app_4:
    forall l1 l2 l3,
      DisjList l1 l3 -> DisjList l2 l3 -> DisjList (l1 ++ l2) l3.
  Proof.
    intros; unfold DisjList in *; intros.
    specialize (H e); specialize (H0 e).
    destruct H; auto.
    destruct H0; auto.
    left; intro Hx.
    apply in_app_or in Hx; destruct Hx; auto.
  Qed.

End Lists.

Ltac subList_app_tac :=
  auto;
  repeat
    match goal with
    | [H: SubList _ _ |- _] => apply SubList_app_7 in H; destruct H
    end;
  repeat apply SubList_app_3;
  match goal with
  | _ => apply SubList_refl
  | _ => apply SubList_app_1; subList_app_tac
  | _ => apply SubList_app_2; subList_app_tac
  end.
Ltac equivList_app_tac := split; subList_app_tac.

Lemma SubList_map: forall {A B} (l1 l2: list A) (f: A -> B),
                     SubList l1 l2 -> SubList (map f l1) (map f l2).
Proof.
  induction l1; intros; simpl; unfold SubList in *; intros; inv H0.
  - apply in_map; apply H; left; reflexivity.
  - apply IHl1; auto.
    intros; specialize (H e0); apply H; right; assumption.
Qed.

Lemma DisjList_logic:
  forall (l1 l2: list string),
    (forall e, In e l1 -> In e l2 -> False) ->
    DisjList l1 l2.
Proof.
  unfold DisjList; intros.
  specialize (H e).
  destruct (in_dec string_dec e l1); intuition.
Qed.

Lemma DisjList_logic_inv:
  forall (l1 l2: list string),
    DisjList l1 l2 ->
    (forall e, In e l1 -> In e l2 -> False).
Proof.
  unfold DisjList; intros.
  specialize (H e); destruct H; auto.
Qed.

Scheme Sorted_ind' := Induction for Sorted Sort Prop.
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
              forall r' : le x (hd b xs),
                (match xs as xs'
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
    replace l2 with l1 by apply le_irrel.
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
    replace h0 with h by (apply HdRel_irrel; assumption).
    specialize (e s); subst; reflexivity.
Qed.

Module FMapListEq (UOT : UsualOrderedType) <: FMapInterface.S with Module E := UOT.

  Module OT := UOT_to_OT UOT.
  Module M := FMapList.Make(OT).
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
  Qed.

  Add Parametric Morphism A: (@eqlistA A)
      with signature subrelation ==> eq ==> eq ==> impl
        as eqlistA_rel_d.
  Proof.
    unfold impl; firstorder.
    induction H0; auto.
  Qed.

  Lemma Equal_this: forall elt L1 L2,
                      Equal (elt:=elt) L1 L2 -> this L1 = this L2.
  Proof.
    unfold Equal; destruct L1, L2; simpl; intros.
    lapply (SortA_equivlistA_eqlistA _ _ _ sorted0 sorted1); intros.
    - clear H.
      rewrite eqke_sub_eq in H0.
      apply eq_leibniz_list in H0.
      assumption.
    - red.
      apply Facts.P.F.Equal_Equiv in H; destruct H.
      intros [a e].
      specialize (H a).
      repeat rewrite Facts.P.F.elements_in_iff in H; simpl in H.
      specialize (H0 a).
      setoid_rewrite Facts.P.F.elements_mapsto_iff in H0; simpl in H0.
      destruct H; split; intros.
      + assert (exists e, InA (M.eq_key_elt (elt:=elt)) (a, e) this0)
          by (eexists; eauto).
        specialize (H H3); dest.
        specialize (H0 e x0 H2 H); subst; auto.
      + assert (exists e, InA (M.eq_key_elt (elt:=elt)) (a, e) this1)
          by (eexists; eauto).
        specialize (H1 H3); dest.
        specialize (H0 x0 e H1 H2); subst; auto.
  Qed.

  Theorem lt_irrel_leibniz {A : Type}
          (lt_irrel : forall (a b : UOT.t) (x y : UOT.lt a b), x = y) (m m' : t A)
  : Equal m m' -> m = m'.
  Proof.
    intros H. 
    apply Equal_this in H.
    induction m. induction m'. simpl in H. induction H.
    replace sorted1 with sorted0.
    reflexivity. apply Sorted_irrel.
    intros. destruct x, y. apply lt_irrel.
  Qed.

End FMapListEq.

Module Type LT_IRREL (Import T : OrderedType).
  Parameter Inline lt_irrel : forall (x y : t) (p q : lt x y), p = q.
End LT_IRREL.

Module Type UsualOrderedTypeLTI := UsualOrderedType <+ LT_IRREL.

Module Type MapLeibniz.
  Declare Module E : UsualOrderedType.
  Include Sfun E.

  Parameter leibniz : forall {A : Type} (m m' : t A), Equal m m' -> m = m'.
End MapLeibniz.

Module LeibnizFacts (M : MapLeibniz).
  Import M.
  Module F := FMapFacts.OrdProperties M.
  Import F.

  Ltac ext k := apply leibniz; unfold Equal; intros k.

  Lemma Equal_val: forall {A : Type} (m1 m2: t A) k, m1 = m2 -> find k m1 = find k m2.
  Proof. intros; subst; reflexivity. Qed.

  Lemma elements_eq_leibniz:
    forall {A : Type} (m1 m2: t A),
      elements m1 = elements m2 -> m1 = m2.
  Proof.
    intros; ext y.
    do 2 rewrite P.F.elements_o.
    rewrite H; auto.
  Qed.

  Theorem empty_canon {A : Type} : forall (m : t A), Empty m -> m = empty A.
  Proof.
    intros; ext k.
    rewrite P.F.empty_o.
    apply P.F.not_find_in_iff.
    unfold In. firstorder.
  Qed.

  Theorem add_canon {A : Type} {x} {e : A} {m m' : t A} :
    P.Add x e m m' -> m' = add x e m.
  Proof. intros; apply leibniz; assumption. Qed.

  Theorem map_induction {A : Type} {P : t A -> Type} :
    P (empty A)
    -> (forall m, P m -> forall k v, ~ In k m -> P (add k v m))
    -> forall m, P m.
  Proof.
    intros. apply P.map_induction.
    intros. replace m0 with (empty A). assumption. symmetry. apply empty_canon.
    assumption. intros. replace m' with (add x e m0).
    apply X0; assumption. symmetry. apply add_canon. assumption.
  Qed.

  Ltac mind v :=
    generalize dependent v; intro; pattern v;
    apply map_induction; clear v; intros.

  Ltac cmp k1 k2 :=
    let e := fresh "e" in
    destruct (E.eq_dec k1 k2) as [e|]; [unfold E.eq in e; subst|].
  
  Definition unionL {A} (m m' : t A) := fold (@add A) m m'.
  Definition union {A} := @unionL A.
  Definition update {A : Type} (m1 m2: t A) := unionL m2 m1.

  Definition Sub {A : Type} (m m' : t A) :=
    forall k v, find k m = Some v -> find k m' = Some v.

  Definition subtract {A : Type} (m m' : t A) :=
    fold (fun k _ => remove k) m' m.

  Definition subtractKV {A}
             (deceqA : forall x y : A, sumbool (x = y) (x <> y))
             (m1 m2 : t A) : t A :=
    fold (fun k v2 m1' =>
            match find k m1' with
            | Some v1 =>
              match deceqA v1 v2 with
              | left _ => remove k m1'
              | _ => m1'
              end
            | _ => m1'
            end) m2 m1.

  Definition subtractKVD {A}
           (deceqA : forall x y : A, sumbool (x = y) (x <> y))
           (m1 m2 : t A) (dom: list E.t): t A :=
    fold (fun k v2 m1' =>
            if in_dec E.eq_dec k dom then
              match find k m1' with
              | Some v1 =>
                match deceqA v1 v2 with
                | left _ => remove k m1'
                | _ => m1'
                end
              | _ => m1'
              end
            else m1') m2 m1.

  Definition restrict {A} (m: t A) (d: list E.t) :=
    fold (fun k v m' =>
            if in_dec E.eq_dec k d then add k v m' else m') m (empty _).

  Definition complement {A} (m: t A) (d: list E.t) :=
    fold (fun k v m' =>
            if in_dec E.eq_dec k d then m' else add k v m') m (empty _).

  (* NOTE: do not add [subtractKV], [restrict], and [complement] to below *)
  #[global] Hint Unfold update Sub subtract : MapDefs.
  #[global] Hint Unfold E.eq.

  Ltac mintros := repeat autounfold with MapDefs; intros.

  #[global] Hint Extern 1 (Empty (empty _)) => apply empty_1.

  Lemma find_empty : forall {A} k, (find k (@empty A)) = None.
  Proof. intros; apply P.F.empty_o. Qed.

  Lemma find_add_1 : forall {A} k v (m: t A), find k (add k v m) = Some v.
  Proof. intros; apply find_1, add_1; reflexivity. Qed.

  Lemma find_add_2:
    forall {A} k k' v (m: t A), k <> k' -> find k (add k' v m) = find k m.
  Proof. intros; apply P.F.add_neq_o; firstorder. Qed.

  Lemma find_add_3:
    forall {A} k v (m: t A),
      find k m = Some v -> exists m', m = add k v m' /\ ~ In k m'.
  Proof.
    intros; exists (remove k m); split.
    - ext y; cmp y k.
      + rewrite find_add_1; assumption.
      + rewrite find_add_2 by assumption.
        rewrite P.F.remove_neq_o by intuition; auto.
    - apply remove_1; auto.
  Qed.

  Ltac find_add_tac :=
    repeat ((rewrite find_add_1 ||rewrite find_add_2 by auto); try reflexivity).

  Ltac proper_tac := unfold Morphisms.Proper, Morphisms.respectful; intros; subst; auto.
  #[global] Hint Extern 1 (Proper _ _) => proper_tac.

  Lemma add_idempotent:
    forall {A} k (e1 e2 : A) m, add k e1 (add k e2 m) = add k e1 m.
  Proof.
    mintros; ext y; cmp y k; find_add_tac.
  Qed.

  Lemma add_comm:
    forall {A} k1 k2 v1 v2 (m: t A),
      k1 <> k2 -> add k1 v1 (add k2 v2 m) = add k2 v2 (add k1 v1 m).
  Proof.
    intros; ext k.
    cmp k k1; try cmp k k2; find_add_tac.
  Qed.

  Lemma transpose_neqkey_Equal_add {A : Type} :
    P.transpose_neqkey Equal (add (elt:=A)).
  Proof.
    unfold P.transpose_neqkey. intros. 
    unfold Equal. intros y. do 4 rewrite P.F.add_o.
    cmp k y; cmp k' y; unfold E.eq in *; subst; congruence || reflexivity.
  Qed.
  #[global] Hint Immediate transpose_neqkey_Equal_add.

  Lemma transpose_neqkey_eq_add {A : Type} :
    P.transpose_neqkey eq (add (elt:=A)).
  Proof.
    unfold P.transpose_neqkey; intros.
    apply add_comm; auto.
  Qed.
  #[global] Hint Immediate transpose_neqkey_eq_add.

  Lemma union_add {A}:
    forall {m m' : t A} k v,
      union (add k v m) m' = add k v (union m m').
  Proof.
    mintros; unfold union, unionL; mind m.
    - rewrite P.fold_add; auto.
      intro Hx; eapply P.F.empty_in_iff; eauto.
    - cmp k k0.
      + rewrite add_idempotent, H.
        rewrite P.fold_add with (eqA:= eq); auto.
        * rewrite add_idempotent; auto.
      + rewrite add_comm by assumption.
        rewrite P.fold_add; auto.
        * rewrite H.
          rewrite P.fold_add with (eqA:= eq); auto.
          apply add_comm; auto.
        * intro Hx; elim H0.
          apply P.F.add_in_iff in Hx; destruct Hx; auto; elim n; auto.
  Qed.

  Lemma union_empty_L {A : Type} : forall m, union (empty A) m = m.
  Proof.
    mintros; mind m.
    - apply leibniz, P.fold_identity.
    - apply P.fold_Empty; auto.
  Qed.

  Lemma union_empty_R {A : Type} : forall m, union m (empty A) = m.
  Proof. mintros; apply leibniz, P.fold_identity. Qed.

  Lemma find_union {A}:
    forall {m m' : t A} k,
      find k (union m m') = match find k m with
                            | Some v => Some v
                            | None => find k m'
                            end.
  Proof.
    intros m m'. pattern m.
    apply map_induction; simpl; intros.
    - rewrite union_empty_L. rewrite P.F.empty_o. reflexivity. 
    - rewrite union_add by assumption. 
      do 2 rewrite P.F.add_o.
      cmp k k0; auto.
  Qed.

  Lemma union_empty:
    forall {A} (m1 m2: t A),
      union m1 m2 = empty _ -> m1 = empty _ /\ m2 = empty _.
  Proof.
    intros; split.
    - ext y.
      rewrite find_empty.
      assert (find y (union m1 m2) = find y (empty A)) by (rewrite H; reflexivity).
      rewrite find_union in H0.
      destruct (find y m1); auto.
      rewrite find_empty in H0; auto.
    - ext y.
      rewrite find_empty.
      assert (find y (union m1 m2) = find y (empty A)) by (rewrite H; reflexivity).
      rewrite find_union in H0.
      destruct (find y m2); auto.
      rewrite find_empty in H0.
      destruct (find y m1); inv H0.
  Qed.

  Lemma union_smothered {A : Type}:
    forall (m m' : t A), Sub m m' -> union m m' = m'.
  Proof. 
    intros m. unfold Sub. pattern m. apply map_induction; intros.
    - apply union_empty_L.
    - unfold union, unionL in *. ext y.
      rewrite P.fold_add; auto.
      + rewrite H. 
        * rewrite P.F.add_o; destruct (E.eq_dec k y); unfold E.eq in *; auto.
          symmetry. apply P.F.find_mapsto_iff.
          apply find_2, H1.
          subst; apply find_add_1.
        * intros. apply H1. destruct (E.eq_dec k k0); unfold E.eq in *.
          { subst. apply False_rect. apply H0. exists v0.
            apply find_2; assumption.
          }
          { rewrite find_add_2; auto. }
      + apply P.F.add_m_Proper.
  Qed.

  Lemma MapsToIn1 A m k (v: A):
    MapsTo k v m -> In k m.
  Proof.
    unfold In.
    eexists; eauto.
  Qed.

  Lemma MapsToIn2 A m k:
    In k m -> (exists (v: A), MapsTo k v m).
  Proof.
    unfold In.
    intuition.
  Qed.

  Lemma mapsto_union A:
    forall (m m': t A) k v,
      MapsTo k v (union m m') <-> MapsTo k v m \/ ~ In k m /\ MapsTo k v m'.
  Proof.
    intros.
    constructor; intros.
    - apply P.F.find_mapsto_iff in H.
      rewrite find_union in H.
      case_eq (find k m); intros; subst.
      + rewrite H0 in *.
        inversion H; subst.
        apply P.F.find_mapsto_iff in H0; intuition.
      + rewrite H0 in *.
        inversion H; subst.
        apply P.F.find_mapsto_iff in H.
        apply P.F.not_find_in_iff in H0.
        intuition.
    - apply P.F.find_mapsto_iff.
      destruct H.
      + apply P.F.find_mapsto_iff in H.
        rewrite find_union.
        rewrite H; reflexivity.
      + rewrite find_union.
        dest.
        apply P.F.find_mapsto_iff in H0.
        apply P.F.not_find_in_iff in H.
        rewrite H, H0.
        reflexivity.
  Qed.

  Lemma update_empty_1: forall {A} (m: t A), update (empty A) m = m.
  Proof.
    mintros; unfold unionL; mind m.
    - apply P.fold_Empty; auto.
    - apply leibniz. rewrite P.fold_add; auto.
      + rewrite H; apply P.F.Equal_refl.
      + apply P.F.add_m_Proper.
  Qed.

  Lemma update_empty_2: forall {A} (m: t A), update m (empty A) = m.
  Proof. mintros; apply P.fold_Empty; auto. Qed.

  Lemma Sub_empty_1:
    forall {A} (m: t A), Sub (empty _) m.
  Proof. mintros; rewrite find_empty in H; inv H. Qed.

  Lemma Sub_empty_2:
    forall {A} (m: t A), Sub m (empty _) -> m = empty _.
  Proof.
    mintros; mind m; auto.
    specialize (H1 k v).
    rewrite find_add_1, find_empty in H1.
    specialize (H1 eq_refl); inv H1.
  Qed.
    
  Lemma Sub_union_1:
    forall {A} (m1 m2: t A), Sub m1 (union m1 m2).
  Proof.
    mintros; mind m1; [rewrite find_empty in H; inv H|].
    rewrite union_add.
    cmp k k0.
    - rewrite find_add_1; rewrite find_add_1 in H1; auto.
    - rewrite find_add_2 by auto; rewrite find_add_2 in H1 by auto; auto.
  Qed.

  Lemma remove_empty:
    forall {A} k, remove k (empty A) = empty A.
  Proof.
    mintros; ext y; cmp y k.
    - rewrite P.F.remove_eq_o by reflexivity.
      rewrite find_empty; reflexivity.
    - rewrite P.F.remove_neq_o by auto; reflexivity.
  Qed.

  Lemma remove_comm:
    forall {A} k1 k2 (m: t A), remove k1 (remove k2 m) = remove k2 (remove k1 m).
  Proof.
    intros; ext y.
    cmp y k1.
    - rewrite P.F.remove_eq_o; auto.
      cmp k1 k2.
      + rewrite P.F.remove_eq_o; auto.
      + rewrite P.F.remove_neq_o; auto.
        rewrite P.F.remove_eq_o; auto.
    - rewrite P.F.remove_neq_o; auto.
      cmp y k2.
      + do 2 (rewrite P.F.remove_eq_o; auto).
      + do 3 (rewrite P.F.remove_neq_o; auto).
  Qed.
      
  Lemma remove_find_None:
    forall {A} (m: t A) k,
      find k m = None -> remove k m = m.
  Proof.
    mintros; ext y; cmp y k.
    - rewrite P.F.remove_eq_o; auto.
    - rewrite P.F.remove_neq_o; auto.
  Qed.

  Lemma remove_add:
    forall {A} (m: t A) k v,
      remove k (add k v m) = remove k m.
  Proof.
    mintros; ext y; cmp y k.
    - do 2 (rewrite P.F.remove_eq_o; auto).
    - do 2 (rewrite P.F.remove_neq_o; auto).
      find_add_tac.
  Qed.

  Lemma remove_union:
    forall {A} (m1 m2: t A) k,
      remove k (union m1 m2) = union (remove k m1) (remove k m2).
  Proof.
    mintros; ext y; cmp y k; rewrite find_union.
    - do 3 (rewrite P.F.remove_eq_o; auto).
    - do 3 (rewrite P.F.remove_neq_o; auto).
      rewrite find_union; reflexivity.
  Qed.

  Lemma transpose_neqkey_subtractKV:
    forall {A} (deceqA : forall x y : A, sumbool (x = y) (x <> y)),
      P.transpose_neqkey
        eq
        (fun (k0 : key) (v2 : A) (m1' : t A) =>
           match find k0 m1' with
           | Some v1 => if deceqA v1 v2 then remove k0 m1' else m1'
           | None => m1'
           end).
  Proof.
    unfold P.transpose_neqkey; intros.
    repeat
      (match goal with
       (* basic destruction *)
       | [ |- context [deceqA ?a1 ?a2] ] =>
         destruct (deceqA a1 a2); [subst|]
       | [H: _ = find ?k ?m |- context [find ?k ?m] ] =>
         rewrite <-H
       | [ |- context [find ?y ?m] ] =>
         (is_var m;
          let v := fresh "v" in
          remember (find y m) as v; destruct v)
       (* goal reduction *)
       | [H: ?y <> ?k |- context [find ?y (remove ?k ?m)] ] =>
         rewrite F.P.F.remove_neq_o by intuition auto
       | [H: ?k <> ?y |- context [find ?y (remove ?k ?m)] ] =>
         rewrite F.P.F.remove_neq_o by intuition auto
       end; try discriminate; try reflexivity; try (intuition idtac; fail)).
    apply remove_comm.
  Qed.
  #[global] Hint Immediate transpose_neqkey_subtractKV.

  Lemma transpose_neqkey_subtractKVD:
    forall {A} (deceqA : forall x y, sumbool (x = y) (x <> y)) d,
      P.transpose_neqkey
        eq
        (fun (k1 : key) (v2 : A) (m1' : t A) =>
           if in_dec P.F.eq_dec k1 d
           then
             match find k1 m1' with
             | Some v1 => if deceqA v1 v2 then remove k1 m1' else m1'
             | None => m1'
             end
           else m1').
  Proof.
    unfold P.transpose_neqkey; intros.
    repeat
      (match goal with
       (* basic destruction *)
       | [ |- context [deceqA ?a1 ?a2] ] =>
         destruct (deceqA a1 a2); [subst|]
       | [ |- context [in_dec ?dc ?k ?d] ] =>
         destruct (in_dec dc k d)
       | [H: _ = find ?k ?m |- context [find ?k ?m] ] =>
         rewrite <-H
       | [ |- context [find ?y ?m] ] =>
         (is_var m;
          let v := fresh "v" in
          remember (find y m) as v; destruct v)
       (* goal reduction *)
       | [H: ?y <> ?k |- context [find ?y (remove ?k ?m)] ] =>
         rewrite F.P.F.remove_neq_o by intuition auto
       | [H: ?k <> ?y |- context [find ?y (remove ?k ?m)] ] =>
         rewrite F.P.F.remove_neq_o by intuition auto
       end; try discriminate; try reflexivity; try (intuition idtac; fail)).
    apply remove_comm.
  Qed.
  #[global] Hint Immediate transpose_neqkey_subtractKVD.
        
  Lemma subtractKV_find:
    forall {A} deceqA (m1 m2: t A) k,
      find k (subtractKV deceqA m1 m2) =
      match find k m1 with
      | None => None
      | Some v1 =>
        match find k m2 with
        | None => Some v1
        | Some v2 => if deceqA v1 v2 then None else Some v1
        end
      end.
  Proof.
    mintros; unfold subtractKV; mind m2.
    - rewrite P.fold_Empty, find_empty; auto.
      destruct (find k m1); auto.

    - rewrite P.fold_add with (eqA:= eq); auto.
      remember (fold
                  (fun (k0 : key) (v2 : A) (m1' : t A) =>
                     match find k0 m1' with
                     | Some v1 => if deceqA v1 v2 then remove k0 m1' else m1'
                     | None => m1'
                     end) m m1) as mprev; clear Heqmprev.
      remember (find k0 mprev) as ov0; destruct ov0.

      + destruct (deceqA a v); [subst|].
        * cmp k k0.
          { rewrite P.F.remove_eq_o, find_add_1 by auto.
            remember (find k0 m1) as ov1; destruct ov1; auto.
            destruct (deceqA a v); auto.
            exfalso.
            rewrite <-Heqov0 in H.
            destruct (find k0 m).
            { destruct (deceqA a a0); inv H.
              elim n; auto.
            }
            { inv H; elim n; auto. }
          }
          { rewrite P.F.remove_neq_o, find_add_2 by auto.
            rewrite H; auto.
          }

        * remember (find k m1) as ov1; destruct ov1; auto.
          cmp k k0.
          { rewrite find_add_1.
            destruct (deceqA a0 v); [subst|].
            { exfalso.
              rewrite <-Heqov0 in H.
              destruct (find k0 m).
              { destruct (deceqA v a0); [inv H|].
                elim n; inv H; auto.
              }
              { elim n; inv H; auto. }
            }
            { rewrite <-Heqov0 in *.
              destruct (find k0 m); auto.
              destruct (deceqA a0 a1); [inv H|].
              auto.
            }
          }
          { rewrite find_add_2; auto. }

      + cmp k k0.
        * rewrite <-Heqov0 in *.
          rewrite find_add_1.
          remember (find k0 m1) as ov1; destruct ov1; auto.
          destruct (deceqA a v); auto.
          exfalso.
          remember (find k0 m) as ov; destruct ov; [|inv H].
          elim H0.
          apply P.F.in_find_iff; rewrite <-Heqov; discriminate.
        * rewrite find_add_2 by auto; auto.
  Qed.

  Lemma subtractKVD_find:
    forall {A} deceqA (m1 m2: t A) d k,
      find k (subtractKVD deceqA m1 m2 d) =
      match find k m1 with
      | None => None
      | Some v1 =>
        if in_dec E.eq_dec k d then
          match find k m2 with
          | None => Some v1
          | Some v2 => if deceqA v1 v2 then None else Some v1
          end
        else Some v1
      end.
  Proof.
    mintros; unfold subtractKVD; mind m2.
    - rewrite P.fold_Empty, find_empty; auto.
      destruct (find k m1); auto.
      destruct (in_dec _ _ _); auto.

    - rewrite P.fold_add with (eqA:= eq); auto.
      remember (fold
                  (fun (k0 : key) (v2 : A) (m1' : t A) =>
                     if in_dec P.F.eq_dec k0 d
                     then
                       match find k0 m1' with
                       | Some v1 =>
                         if deceqA v1 v2 then remove k0 m1' else m1'
                       | None => m1'
                       end
                     else m1') m m1) as mprev; clear Heqmprev.
      remember (find k0 mprev) as ov0; destruct ov0.

      + destruct (in_dec P.F.eq_dec k0 d).
        * destruct (deceqA a v); [subst|].
          { cmp k k0.
            { rewrite P.F.remove_eq_o by reflexivity.
              destruct (find k0 m1); auto.
              destruct (in_dec P.F.eq_dec k0 d); [|elim n; auto].
              rewrite find_add_1.
              destruct (deceqA a v); [subst|]; auto.
              exfalso; rewrite <-Heqov0 in H.
              destruct (find k0 m).
              { destruct (deceqA a a0); inv H.
                elim n; auto.
              }
              { elim n; inv H; auto. }
            }
            { rewrite P.F.remove_neq_o by auto.
              destruct (find k m1); auto.
              destruct (in_dec P.F.eq_dec k d); auto.
              rewrite find_add_2 by auto.
              destruct (find k m); auto.
            }
          }
          { destruct (find k m1); auto.
            destruct (in_dec P.F.eq_dec k d); auto.
            cmp k k0.
            { rewrite find_add_1.
              apply P.F.not_find_in_iff in H0.
              rewrite H0 in *.
              destruct (deceqA a0 v); [subst|]; intuition.
              rewrite <-Heqov0 in H; elim n; inv H; auto.
            }
            { rewrite find_add_2; auto. }
          }
        * destruct (find k m1); auto.
          destruct (in_dec P.F.eq_dec k d); auto.
          cmp k k0; intuition.
          rewrite find_add_2; auto.

      + destruct (in_dec P.F.eq_dec k0 d).
        * cmp k k0.
          { apply P.F.not_find_in_iff in H0.
            rewrite H0 in *.
            rewrite find_add_1.
            destruct (find k0 m1); auto.
            destruct (in_dec P.F.eq_dec k0 d); auto.
            destruct (deceqA a v); auto.
          }
          { rewrite find_add_2; auto. }
        * cmp k k0.
          { apply P.F.not_find_in_iff in H0.
            rewrite H0 in *.
            rewrite find_add_1.
            destruct (find k0 m1); auto.
            destruct (in_dec P.F.eq_dec k0 d); auto.
            destruct (deceqA a v); auto.
          }
          { rewrite find_add_2; auto. }
  Qed.

  Ltac subtractKVD_solve deceqA :=
    repeat
      (match goal with
       | [ |- context [find _ (subtractKVD _ _ _ _)] ] =>
         rewrite subtractKVD_find
       | [ |- context [M.find ?y ?m] ] =>
         (is_var m;
          let v := fresh "v" in
          remember (M.find y m) as v; destruct v)
       | [ |- context [in_dec E.eq_dec ?k ?d] ] =>
         destruct (in_dec E.eq_dec k d)
       | [ |- context [E.eq_dec ?k1 ?k2] ] =>
         is_var k1; is_var k2; cmp k1 k2
       | [ |- context [deceqA ?v1 ?v2] ] =>
         destruct (deceqA v1 v2); [subst|]
       | [ |- context [deceqA ?v1 ?v2] ] =>
         destruct (deceqA v1 v2); [subst|]
       | [ |- context [M.find ?y (M.remove ?k ?m)] ] =>
         cmp y k;
         [rewrite F.P.F.remove_eq_o|
          rewrite F.P.F.remove_neq_o by intuition auto]
       | [ |- context [M.find ?y (M.remove ?y ?m)] ] =>
         rewrite F.P.F.remove_eq_o
       | [H: ~ E.eq ?y ?k |- context [M.find ?y (M.remove ?k ?m)] ] =>
         rewrite F.P.F.remove_neq_o by intuition auto
       | [H: ~ E.eq ?k ?y |- context [M.find ?y (M.remove ?k ?m)] ] =>
         rewrite F.P.F.remove_neq_o by intuition auto
       | [H: ?y <> ?k |- context [M.find ?y (M.remove ?k ?m)] ] =>
         rewrite F.P.F.remove_neq_o by intuition auto
       | [H: ?k <> ?y |- context [M.find ?y (M.remove ?k ?m)] ] =>
         rewrite F.P.F.remove_neq_o by intuition auto
       end;
       repeat
         match goal with
         | [H: ~ E.eq ?a ?a |- _] => elim H; auto
         | [H1: ~ ?p, H2: ?p |- _] => elim H1; auto
         | [H: Some _ = Some _ |- _] => inv H
         | [H: ?a <> ?a |- _] => elim H; auto
         | [H1: Some _ = ?v, H2: None = ?v |- _] =>
           rewrite <-H1 in H2; inv H2
         | [H1: Some _ = ?v, H2: Some _ = ?v |- _] =>
           rewrite <-H1 in H2; inv H2
         end; simpl; auto).

  Lemma subtractKVD_nil:
    forall {A} deceqA (m1 m2: t A),
      subtractKVD deceqA m1 m2 nil = m1.
  Proof.
    mintros; ext y.
    subtractKVD_solve deceqA.
  Qed.
    
  Lemma subtractKVD_cons:
    forall {A} deceqA (m1 m2: t A) a d,
      subtractKVD deceqA m1 m2 (a :: d) =
      match find a m1 with
      | Some v1 =>
        match find a m2 with
        | Some v2 =>
          if deceqA v1 v2
          then subtractKVD deceqA (remove a m1) (remove a m2) d
          else subtractKVD deceqA m1 m2 d
        | _ => subtractKVD deceqA m1 m2 d
        end
      | _ => subtractKVD deceqA m1 m2 d
      end.
  Proof.
    mintros; ext y.
    subtractKVD_solve deceqA.
  Qed.

  Lemma subtractKVD_remove:
    forall {A} (deceqA : forall x y : A, sumbool (x = y) (x <> y))
           dom m1 m2 a,
      subtractKVD deceqA (remove a m1) (remove a m2) dom =
      subtractKVD deceqA (remove a m1) m2 dom.
  Proof.
    mintros; ext y.
    subtractKVD_solve deceqA.
  Qed.

  Lemma subtractKV_mapsto A (decA: forall x y: A, {x = y} + {x <> y}):
    forall m1 m2 k e, MapsTo k e (subtractKV decA m1 m2) <-> MapsTo k e m1 /\ ~ MapsTo k e m2.
  Proof.
    intros; constructor; intros.
    - apply P.F.find_mapsto_iff in H.
      rewrite subtractKV_find in H.
      constructor.
      + apply P.F.find_mapsto_iff.
        repeat match goal with
        | H: context [match ?P with
                      | _ => _
                      end] |- _ => case_eq P; intros;
                                     match goal with
                                     | H : _ = _ |- _ => try rewrite H in *
                                     end
               end; intuition; try discriminate.
      + unfold not; intros Heq; apply P.F.find_mapsto_iff in Heq.
        repeat match goal with
        | H: context [match ?P with
                      | _ => _
                      end] |- _ => case_eq P; intros;
                                     match goal with
                                     | H : _ = _ |- _ => try rewrite H in *
                                     end
               end; intuition; try discriminate.
        injection H; injection Heq; intros; subst; intuition.
    - destruct H as [c1 c2].
      apply P.F.find_mapsto_iff.
      apply P.F.find_mapsto_iff in c1.
      rewrite subtractKV_find.
      assert (find k m2 <> Some e) by (unfold not; intros Y; apply P.F.find_mapsto_iff in Y;
                                      intuition).
        repeat match goal with
               | |- context [match ?P with
                             | _ => _
                             end] => case_eq P; intros;
                   match goal with
                   | H : _ = _ |- _ => try rewrite H in *
                   end
               end; intuition; try discriminate.
        rewrite e0 in *; intuition.
  Qed.

  Lemma subtractKV_empty_1:
    forall {A : Type} deceqA (m: t A),
      subtractKV deceqA (empty A) m = empty A.
  Proof.
    mintros; ext y.
    rewrite subtractKV_find, find_empty; reflexivity.
  Qed.

  Lemma subtractKV_empty_2:
    forall {A : Type} deceqA (m: t A),
      subtractKV deceqA m (empty A) = m.
  Proof.
    mintros; unfold subtractKV; apply P.fold_Empty; auto.
  Qed.

  Lemma subtractKV_empty_3:
    forall {A} deceqA (m: t A),
      subtractKV deceqA m m = empty A.
  Proof.
    mintros; ext y.
    rewrite subtractKV_find, find_empty.
    destruct (find y m); auto.
    destruct (deceqA a a); auto.
    elim n; auto.
  Qed.

  Lemma subtractKV_sub:
    forall {A} deceqA (m1 m2: t A),
      Sub (subtractKV deceqA m1 m2) m1.
  Proof.
    mintros.
    rewrite subtractKV_find in H.
    destruct (find k m1); auto.
    destruct (find k m2); auto.
    destruct (deceqA a a0); auto.
    inv H.
  Qed.

  Lemma subtractKV_sub_empty:
    forall {A} deceqA (m1 m2: t A),
      Sub m1 m2 -> subtractKV deceqA m1 m2 = empty _.
  Proof.
    intros; ext y.
    rewrite subtractKV_find, find_empty.
    remember (find y m1) as ov1; destruct ov1; auto.
    remember (find y m2) as ov2; destruct ov2.
    - destruct (deceqA a a0); auto.
      exfalso; specialize (H _ _ (eq_sym Heqov1)).
      rewrite H in Heqov2; inv Heqov2; elim n; auto.
    - exfalso; specialize (H _ _ (eq_sym Heqov1)).
      rewrite H in Heqov2; inv Heqov2; elim n; auto.
  Qed.
  
  Lemma subtractKV_not_In_find:
    forall {A} deceqA (m1 m2: t A) k v,
      ~ In k (subtractKV deceqA m1 m2) ->
      find k m1 = Some v ->
      find k m2 = Some v.
  Proof.
    mintros.
    apply P.F.not_find_in_iff in H; rewrite subtractKV_find in H.
    destruct (find k m1); inv H0.
    destruct (find k m2); auto.
    destruct (deceqA v a); [|inv H].
    subst; auto.
  Qed.

  Lemma subtractKV_in_find:
    forall {A} deceqA k (m1 m2: t A) v1 v2,
      find k m1 = Some v1 -> find k m2 = Some v2 -> v1 <> v2 ->
      In k (subtractKV deceqA m1 m2).
  Proof.
    intros.
    apply F.P.F.in_find_iff.
    rewrite subtractKV_find.
    rewrite H, H0.
    destruct (deceqA v1 v2); auto.
    discriminate.
  Qed.

  Lemma subtractKV_remove:
    forall {A : Type} deceqA (m2 m1: t A) k,
      find k m1 = find k m2 ->
      subtractKV deceqA (remove k m1) (remove k m2) =
      subtractKV deceqA m1 m2.
  Proof.
    mintros; ext y.
    do 2 rewrite subtractKV_find.
    cmp y k.
    - rewrite P.F.remove_eq_o by auto.
      destruct (find k m1), (find k m2); auto.
      destruct (deceqA a a0); auto.
      inv H; elim n; auto.
    - do 2 rewrite P.F.remove_neq_o by auto.
      destruct (find y m1); auto.
  Qed.

  Lemma subtractKV_idempotent:
    forall {A} deceqA (m1 m2: t A),
       subtractKV deceqA m1 m2 =
       subtractKV deceqA (subtractKV deceqA m1 m2)
                  (subtractKV deceqA m2 m1).
  Proof.
    mintros; ext y.
    repeat rewrite subtractKV_find.
    destruct (find y m1); auto.
    destruct (find y m2); auto.
    destruct (deceqA a a0); auto.
    destruct (deceqA a0 a); auto.
    destruct (deceqA a a0); auto.
    elim n; auto.
  Qed.

  Lemma transpose_neqkey_restrict:
    forall {A} d,
      P.transpose_neqkey
        eq
        (fun (k : key) (v0 : A) (m' : t A) =>
           if in_dec P.F.eq_dec k d then add k v0 m' else m').
  Proof.
    unfold P.transpose_neqkey; intros.
    destruct (in_dec E.eq_dec k d), (in_dec E.eq_dec k' d); auto.
    apply add_comm; auto.
  Qed.
  #[global] Hint Immediate transpose_neqkey_restrict.

  Lemma restrict_find:
    forall {A} d (m: t A) k,
      find k (restrict m d) =
      if in_dec E.eq_dec k d then find k m else None.
  Proof.
    mintros; unfold restrict; mind m.
    - rewrite P.fold_Empty; auto.
      rewrite find_empty.
      destruct (in_dec _ _ _); auto.
    - cmp k k0.
      + rewrite P.fold_add with (eqA:= eq); auto.
        destruct (in_dec E.eq_dec k0 d); auto.
        do 2 rewrite find_add_1; auto.
      + rewrite P.fold_add with (eqA:= eq); auto.
        destruct (in_dec E.eq_dec k0 d).
        * do 2 rewrite find_add_2 by auto; auto.
        * rewrite find_add_2 by auto; auto.
  Qed.

  Lemma restrict_empty:
    forall A d,
      restrict (empty A) d = empty A.
  Proof.
    intros.
    ext y.
    rewrite restrict_find.
    rewrite find_empty.
    destruct (in_dec P.F.eq_dec y d); intuition.
  Qed.

  Lemma restrict_add_in A (m: t A) d:
    forall k v,
      List.In k d ->
      add k v (restrict m d) = restrict (add k v m) d.
  Proof.
    intros.
    ext y.
    rewrite restrict_find.
    destruct (in_dec P.F.eq_dec y d).
    rewrite P.F.add_o.
    rewrite P.F.add_o.
    destruct (P.F.eq_dec k y); intuition.
    rewrite restrict_find.
    destruct (in_dec P.F.eq_dec y d); intuition.
    assert (sth: k <> y) by (unfold not; intros; subst; intuition).
    pose proof (P.F.add_neq_o (restrict m d) v sth).
    rewrite H0.
    rewrite restrict_find.
    destruct (in_dec P.F.eq_dec y d);
      intuition.
  Qed.

  Lemma restrict_add_not_in A (m: t A) d:
    forall k v,
      ~ List.In k d ->
      restrict (add k v m) d = restrict m d.
  Proof.
    intros.
    ext y.
    repeat rewrite restrict_find.
    destruct (in_dec P.F.eq_dec y d).
    assert (sth: k <> y) by (unfold not; intros; subst; intuition).
    apply (P.F.add_neq_o m v sth).
    intuition.
  Qed.
    
  Lemma restrict_in_find:
    forall {A} (m: t A) d e,
      List.In e d -> find e (restrict m d) = find e m.
  Proof.
    mintros; rewrite restrict_find.
    destruct (in_dec E.eq_dec e d); auto.
    elim n; auto.
  Qed.

  Lemma restrict_union:
    forall {A} (m1 m2: t A) d,
      restrict (union m1 m2) d = union (restrict m1 d) (restrict m2 d).
  Proof.
    mintros; ext y.
    repeat (rewrite restrict_find || rewrite find_union).
    destruct (in_dec E.eq_dec y d); auto.
  Qed.

  Lemma restrict_idempotent:
    forall {A} (m: t A) d,
      restrict (restrict m d) d = restrict m d.
  Proof.
    mintros; ext y.
    repeat rewrite restrict_find.
    destruct (in_dec E.eq_dec y d); auto.
  Qed.

  Lemma restrict_EquivList:
    forall {A} (m: t A) d1 d2,
      EquivList d1 d2 ->
      restrict m d1 = restrict m d2.
  Proof.
    mintros; ext y.
    repeat rewrite restrict_find.
    destruct (in_dec E.eq_dec y d1), (in_dec E.eq_dec y d2); auto;
      try (elim n; apply H; auto).
  Qed.

  Lemma restrict_subtractKV:
    forall {A} deceqA (m1 m2: t A) d,
      restrict (subtractKV deceqA m1 m2) d =
      subtractKV deceqA (restrict m1 d) (restrict m2 d).
  Proof.
    mintros; ext y.
    rewrite restrict_find; destruct (in_dec P.F.eq_dec y d).
    - rewrite 2! subtractKV_find.
      rewrite 2! restrict_find.
      destruct (in_dec P.F.eq_dec y d); [|elim n; auto].
      reflexivity.
    - rewrite subtractKV_find.
      rewrite 2! restrict_find.
      destruct (in_dec P.F.eq_dec y d); [elim n; auto|].
      reflexivity.
  Qed.

  Lemma restrict_subtractKV_empty:
    forall {A} deceqA (m: t A) d,
      subtractKV deceqA (restrict m d) m = M.empty _.
  Proof.
    mintros; ext y.
    rewrite subtractKV_find.
    rewrite restrict_find.
    destruct (in_dec F.P.F.eq_dec y d); [|rewrite find_empty; reflexivity].
    destruct (M.find y m); [|rewrite find_empty; reflexivity].
    destruct (deceqA a a); [|elim n; auto].
    rewrite find_empty; reflexivity.
  Qed.

  Lemma transpose_neqkey_complement:
    forall {A} d,
      P.transpose_neqkey
        eq
        (fun (k : key) (v0 : A) (m' : t A) =>
           if in_dec P.F.eq_dec k d then m' else add k v0 m').
  Proof.
    unfold P.transpose_neqkey; intros.
    destruct (in_dec E.eq_dec k d), (in_dec E.eq_dec k' d); auto.
    apply add_comm; auto.
  Qed.
  #[global] Hint Immediate transpose_neqkey_complement.

  Lemma complement_find:
    forall {A} d (m: t A) k,
      find k (complement m d) =
      if in_dec E.eq_dec k d then None else find k m.
  Proof.
    mintros; unfold complement; mind m.
    - rewrite P.fold_Empty; auto.
      rewrite find_empty.
      destruct (in_dec _ _ _); auto.
    - cmp k k0.
      + rewrite P.fold_add with (eqA:= eq); auto.
        destruct (in_dec E.eq_dec k0 d); auto.
        do 2 rewrite find_add_1; auto.
      + rewrite P.fold_add with (eqA:= eq); auto.
        destruct (in_dec E.eq_dec k0 d).
        * rewrite find_add_2 by auto; auto.
        * do 2 rewrite find_add_2 by auto; auto.
  Qed.

  Lemma complement_nil:
    forall {A} (m: t A),
      complement m nil = m.
  Proof.
    mintros; ext y.
    rewrite complement_find.
    destruct (in_dec P.F.eq_dec y nil); auto.
    inv i.
  Qed.

  Lemma complement_empty:
    forall A d,
      complement (empty A) d = empty A.
  Proof.
    intros.
    ext y.
    rewrite complement_find.
    rewrite find_empty.
    destruct (in_dec P.F.eq_dec y d); intuition.
  Qed.

  Lemma complement_EquivList:
    forall {A} (m: t A) d1 d2,
      EquivList d1 d2 ->
      complement m d1 = complement m d2.
  Proof.
    mintros; ext y.
    repeat rewrite complement_find.
    destruct (in_dec E.eq_dec y d1), (in_dec E.eq_dec y d2); auto;
      try (elim n; apply H; auto).
  Qed.

  Lemma complement_add_not_in A (m: t A) d:
    forall k v,
      ~ List.In k d ->
      add k v (complement m d) = complement (add k v m) d.
  Proof.
    intros; ext y.
    rewrite complement_find.
    destruct (in_dec P.F.eq_dec y d).
    - cmp k y; intuition.
      rewrite find_add_2 by auto.
      rewrite complement_find.
      destruct (in_dec P.F.eq_dec y d); intuition.
    - cmp k y.
      + rewrite 2! find_add_1; auto.
      + rewrite 2! find_add_2 by auto.
        rewrite complement_find.
        destruct (in_dec P.F.eq_dec y d); intuition.
  Qed.

  Lemma complement_add_in A (m: t A) d:
    forall k v,
      List.In k d ->
      complement (add k v m) d = complement m d.
  Proof.
    intros; ext y.
    rewrite 2! complement_find.
    destruct (in_dec P.F.eq_dec y d); auto.
    cmp k y; intuition.
    rewrite find_add_2 by auto; auto.
  Qed.

  Lemma complement_union:
    forall {A} (m1 m2: t A) d,
      complement (union m1 m2) d = union (complement m1 d) (complement m2 d).
  Proof.
    mintros; ext y.
    repeat (rewrite complement_find || rewrite find_union).
    destruct (in_dec E.eq_dec y d); auto.
  Qed.

  Lemma complement_idempotent:
    forall {A} (m: t A) d,
      complement (complement m d) d = complement m d.
  Proof.
    mintros; ext y.
    repeat rewrite complement_find.
    destruct (in_dec E.eq_dec y d); auto.
  Qed.

  Lemma complement_subtractKV:
    forall {A} deceqA (m1 m2: t A) d,
      complement (subtractKV deceqA m1 m2) d =
      subtractKV deceqA (complement m1 d) (complement m2 d).
  Proof.
    mintros; ext y.
    rewrite complement_find; destruct (in_dec P.F.eq_dec y d).
    - rewrite subtractKV_find.
      rewrite 2! complement_find.
      destruct (in_dec P.F.eq_dec y d); [|elim n; auto].
      reflexivity.
    - rewrite 2! subtractKV_find.
      rewrite 2! complement_find.
      destruct (in_dec P.F.eq_dec y d); [elim n; auto|].
      reflexivity.
  Qed.

  Lemma restrict_complement_union:
    forall {A} (m: t A) d,
      m = union (restrict m d) (complement m d).
  Proof.
    mintros; ext y.
    rewrite find_union, restrict_find, complement_find.
    destruct (in_dec P.F.eq_dec y d); auto.
    destruct (find y m); auto.
  Qed.

  Lemma complement_restrict_subtractKV:
    forall {A} deceqA (m: t A) d,
      subtractKV deceqA m (restrict m d) = complement m d.
  Proof.
    mintros; ext y.
    rewrite subtractKV_find, complement_find, restrict_find.
    destruct (in_dec P.F.eq_dec y d).
    { destruct (M.find y m); auto.
      destruct (deceqA a a); auto.
      elim n; auto.
    }
    { destruct (M.find y m); auto. }
  Qed.

  Lemma union_idempotent {A : Type} : forall (m : t A), union m m = m.
  Proof. 
    intros. apply union_smothered. unfold Sub. auto.
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
    pose proof (P.F.Equal_Equivb_eqdec eq_dec_A).
    destruct (equal cmp m1 m2) eqn:eqtest; [left | right].
    - apply equal_2 in eqtest.
      apply leibniz. apply H. assumption.
    - unfold not. intros contra. induction contra.
      assert (equal cmp m1 m1 = true).
      apply equal_1.
      apply H. apply P.F.Equal_refl. rewrite H0 in eqtest.
      inversion eqtest.
  Qed.

  Lemma in_union_L A: forall (m: t A) k, M.In k m -> forall m', In k (union m m').
  Proof.
    intros m.
    mind m.
    - apply P.F.empty_in_iff in H; intuition.
    - rewrite union_add.
      apply P.F.add_in_iff.
      apply P.F.add_in_iff in H1.
      destruct H1; intuition.
  Qed.

  Lemma in_union_R A: forall (m' m: t A) k, M.In k m -> In k (union m' m).
  Proof.
    intros m'.
    mind m'.
    - rewrite union_empty_L; intuition.
    - rewrite union_add.
      apply P.F.add_in_iff.
      intuition.
  Qed.

  Lemma union_In {A} : forall {m m' : t A} k, In k (union m m') -> In k m \/ In k m'.
  Proof. 
    intros m. pattern m.
    apply map_induction; simpl; intros.
    - rewrite union_empty_L in H. right. assumption.
    - rewrite union_add in H1 by assumption.
      rewrite P.F.add_in_iff in H1. destruct H1.
      subst. left. rewrite P.F.add_in_iff. left. reflexivity.
      specialize (H m' k0 H1). destruct H; [left | right].
      rewrite P.F.add_in_iff. right. assumption. assumption.
  Qed.

  Definition Disj {A} (m m' : t A) := forall k, ~ In k m \/ ~ In k m'.
  Definition DomainSubset {A B} (s1: t A) (s2: t B) := forall k, In k s1 -> In k s2.

  Definition KeysSubset {A} (m: t A) (d: list E.t) := forall k, In k m -> List.In k d.
  Definition KeysSupset {A} (m: t A) (d: list E.t) := forall k, List.In k d -> In k m.
  Definition KeysDisj {A} (m: t A) (d: list E.t) := forall k, List.In k d -> ~ In k m.
  Definition KeysEq {A} (m: t A) (d: list E.t) := forall k, In k m <-> List.In k d.

  #[global] Hint Unfold Equal Disj Sub DomainSubset KeysSubset KeysSupset KeysDisj KeysEq : MapDefs.

  Lemma Sub_union_2:
    forall {A} (m1 m2: t A), Disj m1 m2 -> Sub m2 (union m1 m2).
  Proof.
    mintros; rewrite find_union.
    remember (find k m1) as okv; destruct okv; auto.
    destruct (H k).
    - elim H1; apply P.F.in_find_iff; rewrite <-Heqokv; discriminate.
    - elim H1; apply P.F.in_find_iff; rewrite H0; discriminate.
  Qed.

  Lemma DomainSubset_Disj:
    forall {A} (m1 m2 m3: t A),
      Disj m2 m3 -> DomainSubset m1 m2 -> Disj m1 m3.
  Proof.
    mintros.
    specialize (H k); specialize (H0 k).
    destruct H; auto.
  Qed.

  Lemma restrict_DomainSubset:
    forall {A} (m: t A) d,
      DomainSubset (restrict m d) m.
  Proof.
    mintros.
    apply P.F.in_find_iff; apply P.F.in_find_iff in H.
    rewrite restrict_find in H.
    destruct (in_dec P.F.eq_dec k d); auto.
  Qed.

  Lemma complement_DomainSubset:
    forall {A} (m: t A) d,
      DomainSubset (complement m d) m.
  Proof.
    mintros.
    apply P.F.in_find_iff; apply P.F.in_find_iff in H.
    rewrite complement_find in H.
    destruct (in_dec P.F.eq_dec k d); auto.
  Qed.

  Lemma find_KeysSubset {A} :
    forall {m : t A} k d, KeysSubset m d -> ~ List.In k d -> find k m = None.
  Proof.
    mintros; specialize (H k).
    remember (find k m) as v; destruct v; [|reflexivity].
    elim H0; apply H; apply P.F.in_find_iff; rewrite <-Heqv; discriminate.
  Qed.
    
  Lemma KeysSubset_empty:
    forall {A} d, KeysSubset (empty A) d.
  Proof.
    mintros; inv H; exfalso; eapply P.F.empty_mapsto_iff; eauto.
  Qed.

  Lemma KeysSubset_nil:
    forall {A} m, KeysSubset m nil -> m = M.empty A.
  Proof.
    mintros; ext y.
    rewrite find_empty.
    apply P.F.not_find_in_iff; intro Hx.
    specialize (H y Hx); inv H.
  Qed.

  Lemma KeysSubset_cons:
    forall {A} (m: t A) a d, KeysSubset m d -> KeysSubset m (a :: d).
  Proof. mintros; specialize (H k); right; auto. Qed.

  Lemma KeysSubset_find_None:
    forall {A} (m: t A) k d,
      KeysSubset m (k :: d) -> find k m = None -> KeysSubset m d.
  Proof.
    mintros; specialize (H k0).
    cmp k k0.
    - apply P.F.in_find_iff in H1; intuition auto.
    - specialize (H H1); inv H; auto.
      elim n; reflexivity.
  Qed.
  
  Lemma KeysSubset_add:
    forall {A} (m: t A) k v d,
      KeysSubset m d -> List.In k d -> KeysSubset (add k v m) d.
  Proof.
    mintros.
    apply P.F.add_in_iff in H1. destruct H1.
    subst. assumption. auto.
  Qed.

  Lemma KeysSubset_add_1:
    forall {A} (m: t A) k v d,
      KeysSubset (add k v m) d -> KeysSubset m d.
  Proof.
    mintros; apply H; apply P.F.add_in_iff; auto.
  Qed.

  Lemma KeysSubset_add_2:
    forall {A} (m: t A) k v d,
      KeysSubset (add k v m) d -> List.In k d.
  Proof.
    mintros; apply H; apply P.F.add_in_iff; auto.
  Qed.

  Lemma KeysSubset_remove:
    forall {A} (m: t A) k d,
      KeysSubset m (k :: d) -> KeysSubset (remove k m) d.
  Proof.
    mintros; specialize (H k0).
    cmp k k0.
    - elim (@remove_1 _ m k0 k0 eq_refl); auto.
    - apply P.F.remove_neq_in_iff in H0; auto.
      specialize (H H0); inv H; auto.
      elim n; reflexivity.
  Qed.

  Lemma KeysSubset_union:
    forall {A} (m1 m2: t A) (d: list E.t),
      KeysSubset m1 d -> KeysSubset m2 d -> KeysSubset (union m1 m2) d.
  Proof.
    mintros; specialize (H k); specialize (H0 k); case_eq (find k m2); intros.
    - apply H0. exists a. apply find_2. assumption.
    - destruct H1. apply find_1 in H1. rewrite find_union in H1.
      case_eq (find k m1); intros.
      apply H. exists a. apply find_2. assumption.
      apply H0. rewrite H3 in H1. exists x. apply find_2. assumption.
  Qed.

  Lemma KeysSubset_union_app:
    forall {A} (m1 m2: t A) (d1 d2: list E.t),
      KeysSubset m1 d1 -> KeysSubset m2 d2 -> KeysSubset (union m1 m2) (d1 ++ d2).
  Proof.
    mintros; specialize (H k); specialize (H0 k); apply in_or_app.
    apply union_In in H1; destruct H1; intuition.
  Qed.

  Lemma KeysSubset_SubList:
    forall {A} (m: t A) (d1 d2: list E.t),
      KeysSubset m d1 -> SubList d1 d2 -> KeysSubset m d2.
  Proof. mintros; apply H0, H; auto. Qed.

  Lemma KeysSubset_elements:
    forall {A} (m: t A) (d: list E.t),
      KeysSubset m d -> SubList (List.map (fun e => fst e) (elements m)) d.
  Proof.
    unfold SubList; mintros.
    apply H; rewrite P.F.elements_in_iff.
    apply in_map_iff in H0; dest.
    destruct x; simpl in *; subst.
    exists a.
    apply In_InA; auto.
    apply P.eqke_equiv.
  Qed.

  Lemma KeysDisj_empty:
    forall {A} d, KeysDisj (empty A) d.
  Proof.
    mintros; auto; intro.
    eapply P.F.empty_in_iff; eauto.
  Qed.
  
  Lemma KeysDisj_nil A (x: t A):
    KeysDisj x nil.
  Proof.
    unfold KeysDisj.
    unfold not; intros.
    intuition.
  Qed.

  Lemma KeysDisj_app A (x: t A):
    forall d1 d2, KeysDisj x d1 -> KeysDisj x d2 -> KeysDisj x (d1 ++ d2).
  Proof.
    mintros; apply in_app_or in H1; destruct H1; firstorder.
  Qed.

  Lemma KeysDisj_add:
    forall {A} k v (m: t A) d,
      KeysDisj m d -> ~ List.In k d -> KeysDisj (add k v m) d.
  Proof.
    mintros; auto; intro.
    apply P.F.add_in_iff in H2; destruct H2; subst.
    - elim H0; auto.
    - elim (H k0 H1); auto.
  Qed.

  Lemma KeysDisj_union:
    forall {A} (m1 m2: t A) d,
      KeysDisj m1 d -> KeysDisj m2 d -> KeysDisj (union m1 m2) d.
  Proof.
    mintros.
    specialize (H _ H1); specialize (H0 _ H1).
    apply P.F.not_find_in_iff.
    apply P.F.not_find_in_iff in H.
    apply P.F.not_find_in_iff in H0.
    rewrite find_union.
    destruct (find k m1); auto.
  Qed.

  Lemma KeysDisj_union_1:
    forall {A} (m1 m2: t A) d, KeysDisj (union m1 m2) d -> KeysDisj m1 d.
  Proof.
    mintros; specialize (H _ H0).
    apply P.F.not_find_in_iff; apply P.F.not_find_in_iff in H.
    rewrite find_union in H; destruct (find k m1); auto.
  Qed.

  Lemma KeysDisj_union_2:
    forall {A} (m1 m2: t A) d, KeysDisj (union m1 m2) d -> KeysDisj m2 d.
  Proof.
    mintros; specialize (H _ H0).
    apply P.F.not_find_in_iff; apply P.F.not_find_in_iff in H.
    rewrite find_union in H; destruct (find k m1); auto; inv H.
  Qed.

  Lemma KeysDisj_SubList:
    forall {A} (m: t A) (d1 d2: list E.t),
      KeysDisj m d1 -> SubList d2 d1 -> KeysDisj m d2.
  Proof. mintros; auto. Qed.

  Lemma KeysSubset_Sub:
    forall {A} (m1 m2: t A) (d: list E.t),
      KeysSubset m2 d -> Sub m1 m2 -> KeysSubset m1 d.
  Proof.
    mintros.
    apply H.
    apply P.F.in_find_iff in H1; apply P.F.in_find_iff.
    specialize (H0 k); destruct (find k m1); [|elim H1; auto].
    specialize (H0 a eq_refl); rewrite H0; discriminate.
  Qed.

  Lemma DisjList_KeysSubset_Disj:
    forall {A} (m1 m2: t A) (d1 d2: list E.t),
      DisjList d1 d2 -> KeysSubset m1 d1 -> KeysSubset m2 d2 -> Disj m1 m2.
  Proof.
    mintros; unfold DisjList in H.
    specialize (H k).
    remember (M.find k m1) as ov; destruct ov.
    - right.
      assert (In k m1) by (apply P.F.in_find_iff; rewrite <-Heqov; discriminate).
      specialize (H0 _ H2).
      inv H; intuition.
    - left.
      inv H; intuition.
      specialize (H0 _ H).
      apply eq_sym, P.F.not_find_in_iff in Heqov; intuition.
  Qed.

  Lemma subtractKV_KeysDisj_1:
    forall {A} deceqA (m1 m2: t A) d,
      KeysDisj m1 d -> KeysDisj (subtractKV deceqA m1 m2) d.
  Proof.
    mintros.
    specialize (H k H0).
    rewrite P.F.not_find_in_iff in *.
    rewrite subtractKV_find; rewrite H; auto.
  Qed.

  Lemma subtractKV_KeysDisj_2:
    forall {A} deceqA (m1 m2: t A) d,
      (forall k, List.In k d -> find k m1 <> None -> find k m1 = find k m2) ->
      KeysDisj (subtractKV deceqA m1 m2) d.
  Proof.
    mintros.
    specialize (H k H0).
    rewrite P.F.not_find_in_iff.
    rewrite subtractKV_find.
    destruct (find k m1); auto.
    rewrite <-H by discriminate.
    destruct (deceqA _ _); intuition.
  Qed.

  Lemma subtractKV_KeysDisj_cases:
    forall {A} deceqA (m1 m2: t A) d,
      KeysDisj (subtractKV deceqA m1 m2) d ->
      forall k v, List.In k d -> find k m1 = Some v -> find k m2 = Some v.
  Proof.
    unfold KeysDisj; intros.
    specialize (H _ H0).
    apply F.P.F.not_find_in_iff in H.
    rewrite subtractKV_find in H.
    rewrite H1 in H.
    destruct (M.find k m2).
    - destruct (deceqA v a); subst; auto.
      inv H.
    - inv H.
  Qed.

  Lemma subtractKV_disj_1:
    forall {A} deceqA (m1 m2 m3: t A),
      Disj m1 m2 -> Disj (subtractKV deceqA m1 m3) m2.
  Proof.
    mintros.
    specialize (H k); destruct H; auto.
    left; rewrite P.F.not_find_in_iff in *.
    rewrite subtractKV_find; rewrite H; auto.
  Qed.

  Lemma subtractKV_disj_2:
    forall {A} deceqA (m1 m2 m3: t A),
      Disj m1 m2 -> Disj m1 (subtractKV deceqA m2 m3).
  Proof.
    mintros.
    specialize (H k); destruct H; auto.
    right; rewrite P.F.not_find_in_iff in *.
    rewrite subtractKV_find; rewrite H; auto.
  Qed.

  Lemma subtractKV_disj_invalid:
    forall {A} deceqA (m1 m2: t A),
      Disj m1 m2 -> subtractKV deceqA m1 m2 = m1.
  Proof.
    mintros; ext y.
    specialize (H y).
    do 2 rewrite P.F.not_find_in_iff in H.
    rewrite subtractKV_find.
    destruct (find y m1); auto.
    destruct (find y m2); auto.
    inv H; discriminate.
  Qed.

  Lemma subtractKV_disj_union_1:
    forall {A} deceqA (m1 m2 m: t A),
      Disj m1 m2 ->
      subtractKV deceqA (union m1 m2) m =
      union (subtractKV deceqA m1 m) (subtractKV deceqA m2 m).
  Proof.
    mintros; ext y.
    specialize (H y).
    do 2 rewrite P.F.not_find_in_iff in H.
    repeat (rewrite subtractKV_find || rewrite find_union).
    destruct (find y m1); auto.
    destruct (find y m); auto.
    destruct (deceqA a a0); auto.
    destruct (find y m2); auto.
    inv H; inv H0.
  Qed.

  Lemma subtractKV_disj_union_2:
    forall {A} deceqA (m m1 m2: t A),
      Disj m1 m2 ->
      subtractKV deceqA m (union m1 m2) =
      subtractKV deceqA (subtractKV deceqA m m1) m2.
  Proof.
    mintros; ext y.
    specialize (H y).
    do 2 rewrite P.F.not_find_in_iff in H.
    repeat (rewrite subtractKV_find || rewrite find_union).
    destruct (find y m); auto.
    destruct (find y m1); auto.
    destruct (deceqA a a0); auto.
    destruct (find y m2); auto.
    inv H; inv H0.
  Qed.

  Lemma subtractKV_disj_union_3:
    forall {A} (deceqA : forall x y : A, {x = y} + {x <> y})
           (m1 m2 m : t A),
      Disj m1 m ->
      subtractKV deceqA (union m1 m2) m = union m1 (subtractKV deceqA m2 m).
  Proof.
    mintros; ext y.
    specialize (H y).
    rewrite 2! P.F.in_find_iff in H.
    repeat (rewrite subtractKV_find || rewrite find_union).
    destruct (find y m1), (find y m); intuition;
      try (elim H0; intros; inv H).
  Qed.

  Lemma subtractKV_disj_union_4:
    forall {A} (deceqA : forall x y : A, {x = y} + {x <> y})
           (m1 m2 m : t A),
      Disj m2 m ->
      subtractKV deceqA (union m1 m2) m = union (subtractKV deceqA m1 m) m2.
  Proof.
    mintros; ext y.
    specialize (H y).
    rewrite 2! P.F.in_find_iff in H.
    repeat (rewrite subtractKV_find || rewrite find_union).
    destruct (find y m1), (find y m), (find y m2); auto.
    - destruct H; elim H; discriminate.
    - destruct (deceqA a a0); auto.
    - destruct H; elim H; discriminate.
  Qed.

  Lemma subtractKV_disj_union_5:
    forall {A} deceqA (m m1 m2: t A),
      Disj m m1 ->
      subtractKV deceqA m (union m1 m2) =
      subtractKV deceqA m m2.
  Proof.
    mintros; ext y.
    specialize (H y).
    rewrite 2! P.F.in_find_iff in H.
    repeat (rewrite subtractKV_find || rewrite find_union).
    destruct (find y m), (find y m1); auto.
    destruct H; elim H; discriminate.
  Qed.

  Lemma subtractKV_disj_union_6:
    forall {A} deceqA (m m1 m2: t A),
      Disj m m2 ->
      subtractKV deceqA m (union m1 m2) =
      subtractKV deceqA m m1.
  Proof.
    mintros; ext y.
    specialize (H y).
    rewrite 2! P.F.in_find_iff in H.
    repeat (rewrite subtractKV_find || rewrite find_union).
    destruct (find y m), (find y m1), (find y m2); auto.
    destruct H; elim H; discriminate.
  Qed.

  Lemma subtractKV_disj_union_7:
    forall {A} deceqA (m m1 m2: t A),
      Disj m1 m2 ->
      subtractKV deceqA m (union m1 m2) =
      subtractKV deceqA m (union m2 m1).
  Proof.
    mintros; ext y.
    specialize (H y).
    rewrite 2! P.F.in_find_iff in H.
    repeat (rewrite subtractKV_find || rewrite find_union).
    destruct (find y m), (find y m1), (find y m2); auto.
    destruct H; elim H; discriminate.
  Qed.
    
  Lemma subtractKV_subtractKVD_1:
    forall {A} (deceqA : forall x y : A, sumbool (x = y) (x <> y))
           (m1 m2: t A) dom,
      KeysSubset m1 dom ->
      subtractKV deceqA m1 m2 = subtractKVD deceqA m1 m2 dom.
  Proof.
    mintros; ext y.
    specialize (H y).
    rewrite P.F.in_find_iff in H.
    rewrite subtractKV_find, subtractKVD_find.
    destruct (find y m1); auto.
    destruct (in_dec E.eq_dec y dom); auto.
    elim n; apply H; discriminate.
  Qed.

  Lemma subtractKV_subtractKVD_2:
    forall {A} (deceqA : forall x y : A, sumbool (x = y) (x <> y))
           (m1 m2: t A) dom,
      KeysSubset m2 dom ->
      subtractKV deceqA m1 m2 = subtractKVD deceqA m1 m2 dom.
  Proof.
    mintros; ext y.
    specialize (H y).
    rewrite P.F.in_find_iff in H.
    rewrite subtractKV_find, subtractKVD_find.
    destruct (find y m1); auto.
    destruct (find y m2).
    - destruct (in_dec E.eq_dec y dom); auto.
      elim n; apply H; discriminate.
    - destruct (in_dec E.eq_dec y dom); auto.
  Qed.

  Lemma Disj_empty_1: forall {A} (m: t A), Disj (empty A) m.
  Proof.
    mintros; left; intro.
    apply (proj1 (P.F.empty_in_iff A k)); auto.
  Qed.

  Lemma Disj_empty_2: forall {A} (m: t A), Disj m (empty A).
  Proof.
    mintros; right; intro.
    apply (proj1 (P.F.empty_in_iff A k)); auto.
  Qed.

  Lemma Disj_find_union_1:
    forall {A} (m1 m2: t A) k v,
      Disj m1 m2 -> find k m1 = Some v ->
      find k (union m1 m2) = Some v.
  Proof. mintros; rewrite find_union; rewrite H0; reflexivity. Qed.

  Lemma Disj_find_union_2:
    forall {A} (m1 m2: t A) k v,
      Disj m1 m2 -> find k m2 = Some v ->
      find k (union m1 m2) = Some v.
  Proof.
    mintros; rewrite find_union; rewrite H0.
    remember (find k m1) as v1; destruct v1; [|reflexivity].
    exfalso; specialize (H k); inv H.
    - elim H1; apply P.F.in_find_iff.
      rewrite <-Heqv1; discriminate.
    - elim H1; apply P.F.in_find_iff.
      rewrite H0; discriminate.
  Qed.

  Lemma Disj_find_union_3:
    forall {A} (m1 m2: t A) k v1 v2,
      Disj m1 m2 -> Some v1 = find k m1 -> Some v2 = find k m2 -> False.
  Proof.
    mintros; specialize (H k); destruct H.
    - elim H; apply P.F.in_find_iff; rewrite <-H0; discriminate.
    - elim H; apply P.F.in_find_iff; rewrite <-H1; discriminate.
  Qed.

  Lemma Disj_Sub:
    forall {A} (m1 m2 m3: t A),
      Disj m2 m3 -> Sub m1 m2 -> Disj m1 m3.
  Proof.
    mintros.
    specialize (H k); specialize (H0 k).
    destruct H; auto.
    left; rewrite P.F.not_find_in_iff in *.
    destruct (find k m1); auto.
    elim H0; auto.
  Qed.

  Lemma Disj_add_1 {A}:
    forall {m m' : t A} k v,
      Disj m m' -> ~ In k m' -> Disj (add k v m) m'.
  Proof. 
    intros. unfold Disj in *.
    intros. destruct (H k0).
    - cmp k k0.
      + right; assumption.
      + left; rewrite P.F.add_in_iff; intuition.
    - right; assumption.
  Qed.

  Lemma Disj_add_2 {A}:
    forall {m m' : t A} k v,
      Disj (add k v m) m' -> Disj m m' /\ ~ In k m'.
  Proof. 
    intros. unfold Disj in *.
    split.
    - intros. destruct (H k0).
      rewrite P.F.add_in_iff in H0. intuition.
      right.  assumption.
    - specialize (H k). destruct H.
      rewrite P.F.add_in_iff in H. intuition. assumption.
  Qed.

  Lemma Disj_comm {A} : forall {m m' : t A}, Disj m m' -> Disj m' m.
  Proof. 
    intros. unfold Disj in *. intros k.
    specialize (H k). intuition.
  Qed.

  Lemma Disj_remove_1 {A}:
    forall (m1 m2: t A) k,
      Disj m1 m2 -> Disj (remove k m1) m2.
  Proof.
    mintros; specialize (H k0); destruct H; [left|right]; intro Hx; auto.
    elim H; apply (proj1 (P.F.remove_in_iff _ k _)); auto.
  Qed.

  Lemma Disj_remove_2 {A}:
    forall (m1 m2: t A) k,
      Disj m1 m2 -> Disj m1 (remove k m2).
  Proof. intros; apply Disj_comm, Disj_remove_1, Disj_comm; auto. Qed.

  Lemma Disj_union_1 {A}:
    forall {m m1 m2 : t A},
      Disj m (union m1 m2) -> Disj m m1.
  Proof.
    intros m m1 m2. pattern m1. apply map_induction; simpl; intros.
    - unfold Disj. intros. right. rewrite P.F.empty_in_iff.
      intuition.
    - rewrite union_add in H1 by assumption. apply Disj_comm in H1. 
      apply Disj_add_2 in H1. destruct H1. apply Disj_comm in H1.
      specialize (H H1). apply Disj_comm. apply Disj_add_1.
      apply Disj_comm. assumption.
      assumption.
  Qed.

  Lemma Disj_union_2 {A}:
    forall {m m1 m2 : t A}
    , Disj m (union m1 m2) -> Disj m m2.
  Proof.
    intros m m1 m2. pattern m1. apply map_induction; simpl; intros.
    - rewrite union_empty_L in H. assumption. 
    - apply H. rewrite union_add in H1 by assumption.
      apply Disj_comm in H1.
      apply Disj_add_2 in H1. destruct H1. apply Disj_comm. assumption.
  Qed.

  Lemma Disj_union {A}:
    forall {m m1 m2 : t A}
    , Disj m m1 -> Disj m m2 -> Disj m (union m1 m2).
  Proof.
    intros. unfold Disj in *.
    intros k. specialize (H k). specialize (H0 k).
    intuition. right. intros contra.
    apply union_In in contra. intuition.
  Qed.

  Lemma Disj_find_None {A}:
    forall {m1 m2: t A} k,
      Disj m1 m2 -> find k m1 = None \/ find k m2 = None.
  Proof.
    intros; autounfold with MapDefs in *.
    destruct (H k).
    - left; apply P.F.not_find_in_iff; auto.
    - right; apply P.F.not_find_in_iff; auto.
  Qed.

  Lemma union_Disj_reorder {A}:
    forall (m m1 m2 : M.t A),
      Disj m1 m2 -> union m2 (union m1 m) = union m1 (union m2 m).
  Proof.
    intros; ext k.
    repeat rewrite find_union.
    destruct (H k) as [H0 | H0];
      apply P.F.not_find_in_iff in H0;
      repeat rewrite H0; reflexivity.
  Qed.

  Lemma union_assoc {A}:
    forall (m1 m2 m3: t A)
    , union m1 (union m2 m3) = union (union m1 m2) m3.
  Proof.
    intros; ext y.
    repeat rewrite find_union. simpl.
    destruct (find y m1); destruct (find y m2); reflexivity.
  Qed.

  Lemma union_comm:
    forall {A} (m1 m2: t A), Disj m1 m2 -> union m1 m2 = union m2 m1.
  Proof.
    mintros; mind m1.
    - rewrite union_empty_L, union_empty_R; reflexivity.
    - rewrite union_add.
      assert (forall k, ~ In k m \/ ~ In k m2).
      { intros; specialize (H1 k0).
        cmp k k0.
        { left; auto. }
        { destruct H1; [left|right]; auto.
          intro Hx; elim H1.
          eapply P.F.add_neq_in_iff in n.
          eapply n; eauto.
        }
      }
      specialize (H H2); clear H2.
      specialize (H1 k).
      destruct H1.
      + elim H1; apply P.F.add_in_iff; left; auto.
      + rewrite H; apply leibniz.
        unfold Equal; intros.
        apply P.F.not_find_in_iff in H1.
        cmp y k.
        * rewrite find_union, H1.
          find_add_tac.
        * find_add_tac.
          do 2 rewrite find_union.
          destruct (find y m2); find_add_tac; reflexivity.
  Qed.

  Lemma restrict_KeysSubset:
    forall {A} (m: t A) d,
      KeysSubset m d -> restrict m d = m.
  Proof.
    mintros; ext y.
    specialize (H y); rewrite P.F.in_find_iff in H.
    rewrite restrict_find.
    destruct (in_dec E.eq_dec y d); auto.
    destruct (find y m); auto.
    elim n; apply H; discriminate.
  Qed.

  Lemma KeysSubset_restrict:
    forall {A} (m: t A) d, KeysSubset (restrict m d) d.
  Proof.
    mintros.
    apply P.F.in_find_iff in H.
    rewrite restrict_find in H.
    destruct (in_dec P.F.eq_dec k d); auto.
    elim H; auto.
  Qed.

  Lemma restrict_DisjList:
    forall {A} (m: t A) d1 d2,
      KeysSubset m d1 -> DisjList d1 d2 -> restrict m d2 = empty _.
  Proof.
    mintros; ext y.
    specialize (H y); rewrite P.F.in_find_iff in H.
    rewrite restrict_find, find_empty.
    destruct (in_dec E.eq_dec y d2); auto.
    destruct (find y m); auto.
    specialize (H0 y); destruct H0.
    - elim H0; apply H; discriminate.
    - elim H0; auto.
  Qed.

  Lemma restrict_Disj:
    forall {A} (m1 m2: t A) d,
      Disj m1 m2 -> Disj (restrict m1 d) (restrict m2 d).
  Proof.
    mintros.
    rewrite 2! P.F.not_find_in_iff.
    specialize (H k).
    rewrite 2! P.F.not_find_in_iff in H.
    destruct H; [left|right]; rewrite restrict_find; find_if_inside; auto.
  Qed.

  Lemma complement_KeysSubset:
    forall {A} (m: t A) d,
      KeysSubset m d -> complement m d = empty _.
  Proof.
    mintros; ext y.
    specialize (H y); rewrite P.F.in_find_iff in H.
    rewrite complement_find, find_empty.
    destruct (in_dec E.eq_dec y d); auto.
    destruct (find y m); auto.
    elim n; apply H; discriminate.
  Qed.

  Lemma complement_DisjList:
    forall {A} (m: t A) d1 d2,
      KeysSubset m d1 -> DisjList d1 d2 -> complement m d2 = m.
  Proof.
    mintros; ext y.
    specialize (H y); rewrite P.F.in_find_iff in H.
    rewrite complement_find.
    destruct (in_dec E.eq_dec y d2); auto.
    destruct (find y m); auto.
    specialize (H0 y); destruct H0.
    - elim H0; apply H; discriminate.
    - elim H0; auto.
  Qed.

  Lemma complement_KeysDisj:
    forall {A} (m: t A) d, KeysDisj (complement m d) d.
  Proof.
    mintros.
    apply P.F.not_find_in_iff.
    rewrite complement_find.
    destruct (in_dec _ k d); auto.
    elim n; auto.
  Qed.

  Lemma complement_Disj:
    forall {A} (m1 m2: t A) d,
      Disj m1 m2 -> Disj (complement m1 d) (complement m2 d).
  Proof.
    mintros.
    rewrite 2! P.F.not_find_in_iff.
    specialize (H k).
    rewrite 2! P.F.not_find_in_iff in H.
    destruct H; [left|right]; rewrite complement_find; find_if_inside; auto.
  Qed.

  Lemma restrict_complement_disj:
    forall {A} (m1 m2: t A) d,
      Disj (restrict m1 d) (complement m2 d).
  Proof.
    mintros.
    rewrite 2! P.F.not_find_in_iff.
    rewrite restrict_find, complement_find.
    destruct (in_dec P.F.eq_dec k d); auto.
  Qed.

  Lemma KeysSubset_subtractKV:
    forall {A} (m1 m2: t A) deceqA d,
      KeysSubset m1 d -> KeysSubset (subtractKV deceqA m1 m2) d.
  Proof.
    unfold KeysSubset; intros.
    apply H; rewrite F.P.F.in_find_iff in *.
    intro Hx; elim H0; clear H0.
    rewrite subtractKV_find; rewrite Hx; auto.
  Qed.

  Lemma DomainSubset_KeysSubset:
    forall {A} (m1 m2: t A) d,
      KeysSubset m1 d -> DomainSubset m2 m1 -> KeysSubset m2 d.
  Proof.
    unfold KeysSubset, DomainSubset; auto.
  Qed.

End LeibnizFacts.

Module FMapListLeib (UOT : UsualOrderedTypeLTI) <: MapLeibniz.
  Include (FMapListEq UOT).
  
  Theorem leibniz {A : Type} (m m' : t A) : Equal m m' -> m = m'.
  Proof. apply lt_irrel_leibniz, UOT.lt_irrel. Qed.
End FMapListLeib.

Module String_as_OT' <: UsualOrderedTypeLTI.
  Include String_as_OT.
  Lemma lt_irrel : forall (x y : t) (p q : lt x y), p = q.
  Proof. intros. apply UIP_dec. decide equality. 
  Qed.
End String_as_OT'.

Module M.
  Module Map := FMapListLeib String_as_OT'.
  Include Map.
  Include (LeibnizFacts Map).
End M.

(** FMap Notations *)

Declare Scope fmap_scope.
Notation "'[]'" := (M.empty _) : fmap_scope.
Notation " [ k <- v ] " := (M.add k%string v (M.empty _)) : fmap_scope.
Notation " m +[ k <- v ] " := (M.add k%string v m) (at level 10) : fmap_scope.
Notation " m @[ k ] " := (M.find k%string m) (at level 10) : fmap_scope.

Delimit Scope fmap_scope with fmap.

Ltac dest_disj :=
  repeat
    match goal with
    | [H: M.Disj (M.add _ _ _) _ |- _] =>
      apply M.Disj_add_2 in H; destruct H
    | [H: M.Disj _ (M.add _ _ _) |- _] =>
      apply M.Disj_comm, M.Disj_add_2 in H; destruct H
    | [H: M.Disj _ (M.union _ _) |- _] =>
      pose proof (M.Disj_union_1 H); pose proof (M.Disj_union_2 H); clear H
    | [H: M.Disj (M.union _ _) _ |- _] =>
      apply M.Disj_comm in H
    | [H: M.Disj _ (M.empty _) |- _] => clear H
    | [H: M.Disj (M.empty _) _ |- _] => clear H
    end.

Ltac solve_disj :=
  repeat
    (try assumption;
     match goal with
     | [ |- M.Disj (M.empty _) _ ] =>
       apply M.Disj_empty_1
     | [ |- M.Disj _ (M.empty _) ] =>
       apply M.Disj_empty_2
     | [H: M.Disj ?m1 ?m2 |- M.Disj ?m2 ?m1] =>
       apply M.Disj_comm; auto
     | [ |- M.Disj (M.add _ _ _) _ ] =>
       apply M.Disj_add_1; auto
     | [ |- M.Disj _ (M.add _ _ _) ] =>
       apply M.Disj_comm, M.Disj_add_1; auto
     | [ |- M.Disj _ (M.union _ _) ] =>
       apply M.Disj_union
     | [ |- M.Disj (M.union _ _) _ ] =>
       apply M.Disj_comm, M.Disj_union
     | [ |- M.Disj (M.remove _ _) _ ] =>
       try (apply M.Disj_remove_1; solve_disj; fail)
     | [ |- M.Disj _ (M.remove _ _) ] =>
       try (apply M.Disj_remove_2; solve_disj; fail)
     end).

Ltac dest_in :=
  repeat
    match goal with
    | [H: ~ M.In _ _ |- _] =>
      apply M.F.P.F.not_find_in_iff in H
    | [H: M.In _ _ -> False |- _] =>
      apply M.F.P.F.not_find_in_iff in H
    | [ |- ~ M.In _ _] =>
      apply M.F.P.F.not_find_in_iff
    | [ |- M.In _ _ -> False] =>
      apply M.F.P.F.not_find_in_iff
    | [ |- M.In _ _] =>
      apply M.F.P.F.in_find_iff; intro
    end.

Ltac mred_unit :=
  match goal with
  (* basic destruction *)
  | [H: Some _ = Some _ |- _] => inv H
  | [H: _ = M.find ?k ?m |- context [M.find ?k ?m] ] =>
    rewrite <-H
  | [H1: None = M.find ?k ?m, H2: context [M.find ?k ?m] |- _] =>
    rewrite <-H1 in H2
  | [H1: Some _ = M.find ?k ?m, H2: context [M.find ?k ?m] |- _] =>
    rewrite <-H1 in H2
  | [ |- context [M.find ?y ?m] ] =>
    (is_var m;
     let v := fresh "v" in
     remember (M.find y m) as v; destruct v)
  (* hypothesis reduction *)
  | [H: context [M.find _ (M.empty _)] |- _] =>
    rewrite M.find_empty in H
  | [H: context [M.union (M.empty _) _] |- _] =>
    rewrite M.union_empty_L in H
  | [H: context [M.union _ (M.empty _)] |- _] =>
    rewrite M.union_empty_R in H
  | [H: context [M.find _ (M.union _ _)] |- _] =>
    rewrite M.find_union in H
  | [H: context [M.find ?k (M.add ?k _ _)] |- _] =>
    rewrite M.find_add_1 in H
  | [H: context [M.find ?k1 (M.add ?k2 _ _)] |- _] =>
    rewrite M.find_add_2 in H by discriminate
  | [Hk: ?k1 <> ?k2, H: context [M.find ?k1 (M.add ?k2 _ _)] |- _] =>
    rewrite M.find_add_2 in H by auto
  | [Hk: ?k1 = ?k2 -> False, H: context [M.find ?k1 (M.add ?k2 _ _)] |- _] =>
    rewrite M.find_add_2 in H by auto
  | [H1: In ?y ?d, H2: context [M.find ?y (M.restrict _ ?d)] |- _] =>
    rewrite M.restrict_in_find in H2 by auto
  | [H: context [M.find ?y (M.subtractKV _ ?m1 ?m2)] |- _] =>
    rewrite M.subtractKV_find in H
  | [H: context [if ?c then _ else _] |- _] =>
    match type of c with
    | {_ = _} + {_ <> _} => destruct c; [subst|]
    end
  (* goal reduction *)
  | [ |- context [M.find ?y (M.remove ?k ?m)] ] =>
    destruct (string_dec y k);
    [subst; rewrite M.F.P.F.remove_eq_o|
     rewrite M.F.P.F.remove_neq_o by intuition auto]
  | [ |- context [M.find _ (M.empty _)] ] =>
    rewrite M.find_empty
  | [ |- context [M.union (M.empty _) _] ] =>
    rewrite M.union_empty_L
  | [ |- context [M.union _ (M.empty _)] ] =>
    rewrite M.union_empty_R
  | [ |- context [M.find ?y (M.union _ _)] ] =>
    rewrite M.find_union
  | [ |- context [M.find ?y (M.remove ?y ?m)] ] =>
    rewrite M.F.P.F.remove_eq_o
  | [H: ?y <> ?k |- context [M.find ?y (M.remove ?k ?m)] ] =>
    rewrite M.F.P.F.remove_neq_o by intuition auto
  | [H: ?k <> ?y |- context [M.find ?y (M.remove ?k ?m)] ] =>
    rewrite M.F.P.F.remove_neq_o by intuition auto
  | [H: ?y = ?k -> False |- context [M.find ?y (M.remove ?k ?m)] ] =>
    rewrite M.F.P.F.remove_neq_o by intuition auto
  | [H: ?k = ?y -> False |- context [M.find ?y (M.remove ?k ?m)] ] =>
    rewrite M.F.P.F.remove_neq_o by intuition auto
  | [ |- context [M.find ?y (M.add ?y _ _)] ] => rewrite M.find_add_1
  | [ |- context [M.find ?y (M.add ?k _ _)] ] => rewrite M.find_add_2 by discriminate
  | [H: ?y <> ?k |- context [M.find ?y (M.add ?k _ _)] ] =>
    rewrite M.find_add_2 by intuition idtac
  | [H: ?k <> ?y |- context [M.find ?y (M.add ?k _ _)] ] =>
    rewrite M.find_add_2 by intuition idtac
  | [H: ?y = ?k -> False |- context [M.find ?y (M.add ?k _ _)] ] =>
    rewrite M.find_add_2 by intuition idtac
  | [H: ?k = ?y -> False |- context [M.find ?y (M.add ?k _ _)] ] =>
    rewrite M.find_add_2 by intuition idtac
  | [ |- context [M.find ?y (M.add ?k _ _)] ] =>
    M.cmp y k; [rewrite M.find_add_1|
                rewrite M.find_add_2 by intuition idtac]
  | [H: In ?y ?d |- context [M.find ?y (M.restrict _ ?d)] ] =>
    rewrite M.restrict_in_find by auto
  | [ |- context [M.find ?y (M.subtractKV _ ?m1 ?m2)] ] =>
    rewrite M.subtractKV_find
  | [ |- context [if ?c then _ else _] ] =>
    match type of c with
    | {_ = _} + {_ <> _} => destruct c; [subst|]
    end
  end;
  try discriminate; try reflexivity; try (intuition idtac; fail).

Ltac mred := repeat mred_unit.

Ltac mcontra :=
  repeat
    match goal with
    | [H: M.Disj ?m1' ?m2', Hl: Some _ = M.find ?k ?m1', Hr: Some _ = M.find ?k ?m2' |- _] =>
      try (exfalso; eapply @M.Disj_find_union_3 with (m1:= m1') (m2:= m2'); eauto; fail)
    | [H: Some _ = None |- _] => inv H
    | [H: None = Some _ |- _] => inv H
    | [H1: None = ?f, H2: Some _ = ?f |- _] => rewrite <-H1 in H2; discriminate
    | [H1: None = ?f, H2: ?f = Some _ |- _] => rewrite <-H1 in H2; discriminate
    | [H1: ?f = None, H2: Some _ = ?f |- _] => rewrite H1 in H2; discriminate
    | [H1: ?f = None, H2: Some _ = ?f |- _] => rewrite <-H1 in H2; discriminate
    | [H: match ?c with | Some _ => Some _ | None => Some _ end = None |- _] =>
      destruct c; discriminate
    | [H: match ?c with | Some _ => None | None => None end = Some _ |- _] =>
      destruct c; discriminate
    | [H1: ~ M.In ?k ?m, H2: Some _ = M.find ?k ?m |- _] =>
      elim H1; apply M.F.P.F.in_find_iff; rewrite <-H2; discriminate
    end.

Ltac findeq := dest_disj; dest_in; mred; mcontra; intuition idtac.

Ltac is_new_find y m :=
  match goal with
  | [ _: Some _ = M.find y m |- _] => fail 1
  | [ _: None = M.find y m |- _] => fail 1
  | [ _: M.find y m = Some _ |- _] => fail 1
  | [ _: M.find y m = None |- _] => fail 1
  | _ => idtac
  end.

Ltac dest_find_more :=
  repeat
    match goal with
    | [H: context [M.find ?y ?m] |- _] =>
      (is_var m; is_new_find y m;
       let v := fresh "v" in
       remember (M.find y m) as v; destruct v)
    end.

Ltac findeq_custom tac := tac; dest_find_more; mred; mcontra; intuition idtac.
Ltac findeq_more := findeq_custom idtac.

Ltac meq := let y := fresh "y" in M.ext y; findeq.
Ltac mdisj := mred; dest_disj; solve_disj; try findeq.

#[global] Hint Extern 1 (_ = _) => try (meq; fail).
#[global] Hint Extern 1 (M.Disj _ _) => try (mdisj; fail).

Lemma elements_cons:
  forall {A} m (k: string) (v: A) l,
    (k, v) :: l = M.elements m ->
    exists pm,
      m = M.add k v pm /\ M.find k pm = None /\
      l = M.elements pm.
Proof.
  intros.
  exists (M.remove k m); repeat split.
  - case_eq (M.find k m); intros.
    + pose proof H0.
      rewrite M.F.P.F.elements_o in H0.
      rewrite <-H in H0.
      simpl in H0.
      unfold M.F.P.F.eqb in H0.
      destruct (M.F.P.F.eq_dec k k); [|elim n; auto].
      inv H0.
      meq.
    + rewrite M.F.P.F.elements_o in H0.
      rewrite <-H in H0.
      simpl in H0.
      unfold M.F.P.F.eqb in H0.
      destruct (M.F.P.F.eq_dec k k); try discriminate.
      elim n; auto.
  - findeq.
  - unfold M.elements, M.Raw.elements in *.
    unfold M.remove; simpl.
    rewrite <-H; simpl.
    pose proof (@M.F.ME.elim_compare_eq k k eq_refl); dest.
    rewrite H0; auto.
Qed.

Lemma eqlistA_eqke_eq_compat:
  forall {A} l1 l2,
    SetoidList.eqlistA (M.F.O.eqke (elt:=A)) l1 l2 ->
    SetoidList.eqlistA eq l1 l2.
Proof.
  induction 1; simpl; intros; [constructor|].
  constructor; auto.
  destruct x, x'; inv H; simpl in *; subst; auto.
Qed.

Section MakeMap.
  Variable A: Type.
  Variable f1 f2: A -> Type.
  Variable f: forall x, f1 x -> f2 x.

  Fixpoint makeMap (l: list (Attribute (sigT f1))) : M.t (sigT f2) :=
    match l with
    | nil => M.empty _
    | {| attrName := n; attrType := existT _ rv |} :: xs =>
      M.add n (existT _ _ (f rv)) (makeMap xs)
    end.

  Lemma makeMap_find:
    forall l (Hl: NoDup (namesOf l)) k,
      M.find k (makeMap l) =
      match getAttribute k l with
      | None => None
      | Some {| attrType := existT _ rv |} => Some (existT _ _ (f rv))
      end.
  Proof.
    induction l; simpl; intros; [reflexivity|].
    destruct a as [an [asig av]]; simpl in *.
    inv Hl; specialize (IHl H2).
    remember (string_eq k an) as ka; destruct ka.
    - apply string_eq_dec_eq in Heqka; subst.
      rewrite M.find_add_1; auto.
    - apply string_eq_dec_neq in Heqka.
      rewrite M.find_add_2; auto.
  Qed.
  
  Lemma makeMap_KeysSubset:
    forall m, M.KeysSubset (makeMap m) (namesOf m).
  Proof.
    induction m; simpl; intros; [apply M.KeysSubset_empty|].
    destruct a as [an [atype av]]; simpl.
    apply M.KeysSubset_add; intuition.
  Qed.

  Lemma makeMap_union:
    forall m1 m2,
      DisjList (namesOf m1) (namesOf m2) ->
      makeMap (m1 ++ m2) = M.union (makeMap m1) (makeMap m2).
  Proof.
    induction m1; simpl; intros;
      [rewrite M.union_empty_L; reflexivity|].

    destruct a as [rn [rk r]].
    rewrite M.union_add.
    f_equal.
    apply IHm1.
    eapply DisjList_cons; eauto.
  Qed.
End MakeMap.

Inductive MapR {A} : M.t A -> Type :=
| MRUnknown: forall (m: M.t A), MapR m
| MREmpty: MapR (M.empty _)
| MRAdd:
    forall k v {m},
      MapR m -> MapR (M.add k v m)
| MRUnion:
    forall {m1 m2},
      MapR m1 -> MapR m2 ->
      MapR (M.union m1 m2).

Fixpoint findMR {A} (k : string) {m} (mr : MapR (A:= A) m): option A :=
  match mr with
  | MRUnknown m' => M.find k m'
  | MREmpty => None
  | MRAdd k' v _ mr' => if string_eq k k' then Some v else findMR k mr'
  | MRUnion _ _ mr1 mr2 =>
    match findMR k mr1 with
    | Some v => Some v
    | _ => findMR k mr2
    end
  end.

Lemma findMR_find:
  forall {A} k (m: M.t A) (mr: MapR m),
    findMR k mr = M.find k m.
Proof.
  induction mr; simpl; intros.
  - reflexivity.
  - rewrite M.find_empty; reflexivity.
  - remember (string_eq k k0) as kb; destruct kb.
    + apply string_eq_dec_eq in Heqkb; subst.
      rewrite M.find_add_1; auto.
    + apply string_eq_dec_neq in Heqkb.
      rewrite M.find_add_2 by assumption; auto.
  - rewrite M.find_union.
    destruct (findMR k mr1).
    + rewrite <-IHmr1; reflexivity.
    + rewrite <-IHmr1; auto.
Qed.

Ltac mapReify m :=
  match m with
  | M.empty ?A => constr:(@MREmpty A)
  | M.add ?k ?v ?m' =>
    let mr' := mapReify m' in
    constr:(MRAdd k v mr')
  | M.union ?m1 ?m2 =>
    let mr1 := mapReify m1 in
    let mr2 := mapReify m2 in
    constr:(MRUnion mr1 mr2)
  | _ => constr:(MRUnknown m)
  end.

Ltac findReify :=
  match goal with
  | [ |- context[M.find ?k ?m] ] =>
    tryif is_evar m then idtac
    else (let rfd := mapReify m in
          rewrite <-findMR_find with (mr:= rfd))
  end; unfold findMR;
  repeat
    match goal with
    | [ |- context[string_eq ?s ?s] ] =>
      rewrite string_eq_true
    end; cbv [string_eq ascii_eq Bool.eqb andb].

(* NOTE: using f_equal instead of below destructs values also, which may generate
 * subgoals that cannot be proven. In that case, use this reflection. 
 *)
Section FMapRawReflection.
  Variable A: Type.

  Fixpoint meqReifyRaw (mr1 mr2: list (string * A)) :=
    match mr1, mr2 with
    | nil, nil => True
    | (s1, v1) :: mr1', (s2, v2) :: mr2' =>
      s1 = s2 /\ v1 = v2 /\ meqReifyRaw mr1' mr2'
    | _, _ => False
    end.

  Lemma meqReifyRaw_ok: forall mr1 mr2, meqReifyRaw mr1 mr2 -> mr1 = mr2.
  Proof.
    induction mr1; simpl; intros.
    - destruct mr2; intuition idtac.
    - destruct mr2.
      + destruct a; intuition idtac.
      + destruct a, p; dest; subst.
        f_equal; auto.
  Qed.

End FMapRawReflection.

Ltac meqReify_eq_tac := idtac.

Ltac meqReify :=
  simpl; try reflexivity;
  apply M.elements_eq_leibniz;
  try reflexivity;
  simpl; meqReify_eq_tac.

Ltac meqReify_eq_tac ::= repeat (unfold M.Raw.key, M.OT.t; f_equal).
Ltac meqReify_eq_tac ::=
     unfold M.Raw.key, M.OT.t;
apply meqReifyRaw_ok; repeat split; try assumption; try reflexivity.

