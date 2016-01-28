Require FSets.FMapList FSets.FMapFacts.
Require Import Lists.SetoidList.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.

Require Import Eqdep_dec.

Require Import Lib.CommonTactics.

Section Lists. (* For dealing with domains *)
  Context {A: Type}.
  
  Definition DisjList (l1 l2: list A) := forall e, ~ In e l1 \/ ~ In e l2.
  Definition SubList (l1 l2: list A) := forall e, In e l1 -> In e l2.

  Lemma SubList_nil: forall l, SubList nil l.
  Proof. unfold SubList; intros; inv H. Qed.

  Lemma SubList_cons: forall a l1 l2, In a l2 -> SubList l1 l2 -> SubList (a :: l1) l2.
  Proof. unfold SubList; intros; inv H1; auto. Qed.

  Lemma SubList_cons_inv: forall a l1 l2, SubList (a :: l1) l2 -> In a l2 /\ SubList l1 l2.
  Proof. unfold SubList; intros; split; intuition. Qed.
  
  Lemma SubList_refl: forall l, SubList l l.
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

  Lemma DisjList_comm: forall l1 l2, DisjList l1 l2 -> DisjList l2 l1.
  Proof. 
    intros. unfold DisjList in *. intros e. specialize (H e). intuition.
  Qed.

  Lemma DisjList_SubList: forall sl1 l1 l2, SubList sl1 l1 -> DisjList l1 l2 -> DisjList sl1 l2.
  Proof. 
    intros. unfold SubList, DisjList in *. intros e. 
    specialize (H e). specialize (H0 e). intuition.
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

End Lists.

Lemma SubList_map: forall {A B} (l1 l2: list A) (f: A -> B),
                     SubList l1 l2 -> SubList (map f l1) (map f l2).
Proof.
  induction l1; intros; simpl; unfold SubList in *; intros; inv H0.
  - apply in_map; apply H; left; reflexivity.
  - apply IHl1; auto.
    intros; specialize (H e0); apply H; right; assumption.
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

Module FMapListEq (UOT : UsualOrderedType) <: FMapInterface.S with Module E := UOT.

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
  Proof.
    intros H. 
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
    forall k v, MapsTo k v m -> MapsTo k v m'.

  Definition subtract {A : Type} (m m' : t A) :=
    fold (fun k _ => remove k) m' m.
  Definition subtractKV {A : Type}
             (deceqA : forall x y : A, sumbool (x = y) (x <> y))
             (m1 m2 : t A) : t A :=
    fold (fun k2 v2 m1' =>
            match M.find k2 m1' with
              | None => m1'
              | Some v1 => if deceqA v1 v2 then 
                             remove k2 m1' else m1' 
            end) m2 m1.

  Hint Unfold update Sub subtract subtractKV : MapDefs.

  Ltac mintros := repeat autounfold with MapDefs; intros.

  Hint Extern 1 (Empty (empty _)) => apply empty_1.

  Lemma find_empty : forall {A} k, (find k (@empty A)) = None.
  Proof. intros; apply P.F.empty_o. Qed.

  Lemma find_add_1 : forall {A} k v (m: t A), find k (add k v m) = Some v.
  Proof. intros; apply find_1, add_1; reflexivity. Qed.

  Lemma find_add_2:
    forall {A} k k' v (m: t A), k <> k' -> find k (add k' v m) = find k m.
  Proof. intros; apply P.F.add_neq_o; firstorder. Qed.

  Ltac find_add_tac :=
    repeat ((rewrite find_add_1 ||rewrite find_add_2 by auto); try reflexivity).

  Ltac proper_tac := compute; intros; subst; auto.
  Hint Extern 1 (Proper _ _) => proper_tac.

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
  Hint Immediate transpose_neqkey_Equal_add.

  Lemma transpose_neqkey_eq_add {A : Type} :
    P.transpose_neqkey eq (add (elt:=A)).
  Proof.
    unfold P.transpose_neqkey; intros.
    apply add_comm; auto.
  Qed.
  Hint Immediate transpose_neqkey_eq_add.

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

  Lemma union_smothered {A : Type}:
    forall (m m' : t A), Sub m m' -> union m m' = m'.
  Proof. 
    intros m. unfold Sub. pattern m. apply map_induction; intros.
    - apply union_empty_L.
    - unfold union, unionL in *. ext y.
      rewrite P.fold_add; auto.
      + rewrite H. 
        * rewrite P.F.add_o; destruct (E.eq_dec k y); unfold E.eq in *; auto.
          symmetry. apply P.F.find_mapsto_iff. apply H1.
          apply add_1. assumption.
        * intros. apply H1. destruct (E.eq_dec k k0); unfold E.eq in *.
          { subst. apply False_rect. apply H0. exists v0. assumption. }
          { apply add_2; assumption. }
      + apply P.F.add_m_Proper.
  Qed.

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

  Lemma transpose_neqkey_Equal_subtractKV:
    forall {A} (deceqA : forall x y : A, sumbool (x = y) (x <> y)),
      P.transpose_neqkey
        eq
        (fun k2 v2 m1' =>
           match find k2 m1' with
             | Some v1 => if deceqA v1 v2 then remove k2 m1' else m1'
             | None => m1'
           end).
  Proof.
    compute; intros; simpl.

    repeat
      match goal with
        | [ |- context [find ?k ?m] ] =>
          let okv := fresh "okv" in
          remember (find k m) as okv; destruct okv
        | [H: _ = find _ _ |- _] => rewrite <-H
        | [ |- context [deceqA ?a1 ?a2] ] =>
          destruct (deceqA a1 a2); [subst|]
        | [ |- context [remove ?k ?m] ] =>
          try rewrite remove_find_None by auto
      end;
      repeat
        match goal with
          | [H1: ?v1 = find ?k ?m, H2: ?v2 = find ?k ?m |- _] =>
            rewrite <-H1 in H2
          | [H: Some ?v1 = Some ?v2 |- _] => inv H
          | [H: Some _ = None |- _] => discriminate
          | [H: ?a = ?a -> False |- _] => elim H; auto
          | [H: context [find ?k (remove ?k _)] |- _] =>
            rewrite P.F.remove_eq_o in H; auto
          | [H: context [find ?k1 (remove ?k2 _)] |- _] =>
            try (rewrite P.F.remove_neq_o in H; auto)
        end; try reflexivity; try discriminate.
    
    apply remove_comm.
  Qed.
  Hint Immediate transpose_neqkey_Equal_subtractKV.

  Lemma subtractKV_empty_1:
    forall {A : Type} deceqA (m: t A),
      subtractKV deceqA (empty A) m = empty A.
  Proof.
    mintros; mind m.
    - apply P.fold_Empty; auto.
    - apply leibniz; rewrite P.fold_add with (eqA:= eq); auto.
      rewrite H; rewrite P.F.empty_o.
      apply P.F.Equal_refl.
  Qed.

  Lemma subtractKV_empty_2:
    forall {A : Type} deceqA (m: t A),
      subtractKV deceqA m (empty A) = m.
  Proof. mintros; apply P.fold_Empty; auto. Qed.

  Lemma subtractKV_remove:
    forall {A : Type} deceqA (m2 m1: t A) k,
      find k m1 = find k m2 ->
      subtractKV deceqA (remove k m1) (remove k m2) =
      subtractKV deceqA m1 m2.
  Proof.
    admit.
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
  Definition InDomain {A} (m: t A) (d: list E.t) := forall k, In k m -> List.In k d.
  Definition OnDomain {A} (m: t A) (d: list E.t) := forall k, List.In k d -> In k m.
  Definition NotOnDomain {A} (m: t A) (d: list E.t) := forall k, List.In k d -> ~ In k m.
  Definition DomainOf {A} (m: t A) (d: list E.t) := forall k, In k m <-> List.In k d.

  Hint Unfold Equal Disj Sub InDomain OnDomain NotOnDomain DomainOf : MapDefs.

  Lemma find_InDomain {A} :
    forall {m : t A} k d, InDomain m d -> ~ List.In k d -> find k m = None.
  Proof.
    mintros; specialize (H k).
    remember (find k m) as v; destruct v; [|reflexivity].
    elim H0; apply H; apply P.F.in_find_iff; rewrite <-Heqv; discriminate.
  Qed.
    
  Lemma InDomain_empty:
    forall {A} d, InDomain (empty A) d.
  Proof.
    mintros; inv H; exfalso; eapply P.F.empty_mapsto_iff; eauto.
  Qed.

  Lemma InDomain_nil:
    forall {A} m, InDomain m nil -> m = M.empty A.
  Proof.
    mintros; ext y.
    rewrite find_empty.
    apply P.F.not_find_in_iff; intro Hx.
    specialize (H y Hx); inv H.
  Qed.

  Lemma InDomain_find_None:
    forall {A} (m: t A) k d,
      InDomain m (k :: d) -> find k m = None -> InDomain m d.
  Proof.
    mintros; specialize (H k0).
    cmp k k0.
    - apply P.F.in_find_iff in H1; intuition auto.
    - specialize (H H1); inv H; auto.
      elim n; reflexivity.
  Qed.
  
  Lemma InDomain_add:
    forall {A} (m: t A) k v d,
      InDomain m d -> List.In k d -> InDomain (add k v m) d.
  Proof.
    mintros.
    apply P.F.add_in_iff in H1. destruct H1.
    subst. assumption. auto.
  Qed.

  Lemma InDomain_remove:
    forall {A} (m: t A) k d,
      InDomain m (k :: d) -> InDomain (remove k m) d.
  Proof.
    mintros; specialize (H k0).
    cmp k k0.
    - elim (@remove_1 _ m k0 k0 eq_refl); auto.
    - apply P.F.remove_neq_in_iff in H0; auto.
      specialize (H H0); inv H; auto.
      elim n; reflexivity.
  Qed.

  Lemma InDomain_union:
    forall {A} (m1 m2: t A) (d: list E.t),
      InDomain m1 d -> InDomain m2 d -> InDomain (union m1 m2) d.
  Proof.
    mintros; specialize (H k); specialize (H0 k); case_eq (find k m2); intros.
    - apply H0. exists a. apply find_2. assumption.
    - destruct H1. apply find_1 in H1. rewrite find_union in H1.
      case_eq (find k m1); intros.
      apply H. exists a. apply find_2. assumption.
      apply H0. rewrite H3 in H1. exists x. apply find_2. assumption.
  Qed.

  Lemma InDomain_union_app:
    forall {A} (m1 m2: t A) (d1 d2: list E.t),
      InDomain m1 d1 -> InDomain m2 d2 -> InDomain (union m1 m2) (d1 ++ d2).
  Proof.
    mintros; specialize (H k); specialize (H0 k); apply in_or_app.
    apply union_In in H1; destruct H1; intuition.
  Qed.

  Lemma InDomain_SubList:
    forall {A} (m: t A) (d1 d2: list E.t),
      InDomain m d1 -> SubList d1 d2 -> InDomain m d2.
  Proof. mintros; apply H0, H; auto. Qed.

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
      Disj m1 m2 -> find k m1 = Some v1 -> find k m2 = Some v2 -> False.
  Proof.
    mintros; specialize (H k); destruct H.
    - elim H; apply P.F.in_find_iff; rewrite H0; discriminate.
    - elim H; apply P.F.in_find_iff; rewrite H1; discriminate.
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

End LeibnizFacts.

Module FMapListLeib (UOT : UsualOrderedTypeLTI) <: MapLeibniz.
  Include (FMapListEq UOT).
  
  Theorem leibniz {A : Type} (m m' : t A) : Equal m m' -> m = m'.
  Proof. apply lt_irrel_leibniz, UOT.lt_irrel. Qed.
End FMapListLeib.

Require Import Lib.String_as_OT String.

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

