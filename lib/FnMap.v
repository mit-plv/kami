Require Import Omega String Ascii List Struct.
Require Import Lib.CommonTactics.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

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

  Lemma string_dec_neq: forall s t, s <> t -> string_eq s t = false.
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

Section Lists. (* About domains *)
  Context {A: Type}.
  
  Definition DisjList (l1 l2: list A) := forall e, ~ In e l1 \/ ~ In e l2.
  Definition SubList (l1 l2: list A) := forall e, In e l1 -> In e l2.

  Lemma DisjList_comm: forall l1 l2, DisjList l1 l2 -> DisjList l2 l1.
  Proof. admit. Qed.

  Lemma DisjList_SubList: forall sl1 l1 l2, SubList sl1 l1 -> DisjList l1 l2 -> DisjList sl1 l2.
  Proof. admit. Qed.

  Lemma DisjList_app_1: forall l1 l2 l3, DisjList l1 (l2 ++ l3) -> DisjList l1 l2.
  Proof. admit. Qed.

  Lemma DisjList_app_2: forall l1 l2 l3, DisjList l1 (l2 ++ l3) -> DisjList l1 l3.
  Proof. admit. Qed.

End Lists.

Lemma SubList_map: forall {A B} (l1 l2: list A) (f: A -> B),
                     SubList l1 l2 -> SubList (map f l1) (map f l2).
Proof.
  induction l1; intros; simpl; unfold SubList in *; intros; [inv H0|].
  inv H0.
  - apply in_map; apply H; left; reflexivity.
  - apply IHl1; auto.
    intros; specialize (H e0); apply H; right; assumption.
Qed.

Section Domains.
  Definition listSub (l1 l2: list string) :=
    filter (fun s => if in_dec string_dec s l2 then false else true) l1.

  Lemma listSub_In_1:
    forall s l1 l2, In s (listSub l1 l2) <-> In s l1 /\ ~ In s l2.
  Proof.
    intros; split; intros.
    - unfold listSub in H; apply filter_In in H; dest; split; auto.
      destruct (in_dec _ s l2); intuition.
    - dest; unfold listSub; apply filter_In; split; auto.
      destruct (in_dec _ s l2); intuition.
  Qed.

  Lemma listSub_In_2:
    forall s l1 l2, ~ In s (listSub l1 l2) <-> (~ In s l1 \/ In s l2).
  Proof.
    intros; split; intros.
    - destruct (in_dec string_dec s l1).
      + right; destruct (in_dec string_dec s l2); [assumption|].
        elim H; apply filter_In; split; [assumption|].
        destruct (in_dec string_dec s l2); intuition.
      + left; assumption.
    - intro Hx; apply listSub_In_1 in Hx; dest; destruct H.
      + elim H; assumption.
      + elim H1; assumption.
  Qed.

End Domains.

Ltac in_tac_ex :=
  repeat
    match goal with
      | [ |- In _ (_ ++ _) ] =>
        (apply in_or_app; (left; in_tac_ex; fail || right; in_tac_ex; fail))
      | [ |- In _ (listSub _ _) ] => (apply listSub_In_1; split)
      | [ |- ~ In _ (listSub _ _) ] =>
        (apply listSub_In_2; (left; in_tac_ex; fail || right; in_tac_ex; fail))
      | [ |- In _ _ ] => in_tac
      | [ |- ~ In _ _ ] => (let Hx := fresh "Hx" in intro Hx)
      | [H: In _ (_ ++ _) |- _] => (apply in_app_or in H; destruct H)
      | [H: In _ (listSub _ _) |- _] => (apply listSub_In_1 in H; dest)
      | [H: ~ In _ (listSub _ _) |- _] => (apply listSub_In_2 in H; destruct H)
      | [H: In _ _ |- _] => (try (in_tac_H; vdiscriminate; fail); clear H)
      | [H: ~ In _ _ |- _] => (try (elim H; clear H; in_tac_ex; fail); clear H)
    end.

Ltac ssimpl H :=
  repeat rewrite string_dec_eq in H;
  repeat rewrite string_dec_neq in H by discriminate;
  repeat rewrite string_eq_append in H by reflexivity;
  repeat
    (match type of H with
       | context [in_dec string_dec ?s ?l] =>
         let Hin := fresh "Hin" in
         destruct (in_dec string_dec s l) as [Hin|Hin] in H;
       try (clear -Hin; exfalso; in_tac_ex; fail)
     end).

Ltac ssimpl_G :=
  repeat rewrite string_dec_eq;
  repeat rewrite string_dec_neq by discriminate;
  repeat rewrite string_eq_append by reflexivity;
  repeat
    (match goal with
       | [ |- context [in_dec string_dec ?s ?l] ] =>
         let Hin := fresh "Hin" in
         destruct (in_dec string_dec s l) as [Hin|Hin];
       try (clear -Hin; exfalso; in_tac_ex; fail)
     end).

(* a value of type `Map A` is a map from strings to values of `A` *)
Section Map.
  Context {A: Type}.

  Definition Map := string -> option A.
  
  Definition empty: Map := fun _ => None.

  Definition unionL (m1 m2: Map) k :=
    match m1 k with
      | Some _ => m1 k
      | None => m2 k
    end.

  Definition unionR m1 m2 := unionL m2 m1.

  Definition add (k: string) (v: A) (m: Map) :=
    unionL (fun k' => if string_eq k k' then Some v else None) m.

  Definition union := unionL.

  Definition disjUnion (m1 m2: Map) (d: list string) k :=
    if in_dec string_dec k d then m1 k else m2 k.

  Definition find k (m: Map) := m k.

  Definition remove k (m: Map) k' :=
    if string_eq k k' then None else m k'.

  Definition subtract (m1 m2: Map) k :=
    match m2 k with
      | Some _ => None
      | None => m1 k
    end.

  Definition update (m1 m2: Map) := unionL m2 m1.

  Definition restrict (m: Map) (l: list string) k :=
    match in_dec string_dec k l with
      | left _ => m k
      | right _ => None
    end.

  Definition complement (m: Map) (l: list string) k :=
    match in_dec string_dec k l with
      | left _ => None
      | right _ => m k
    end.

  Definition MapsTo k v (m: Map) := m k = Some v.

  Definition InMap k (m: Map) := find k m <> None.

  Definition Equal (m1 m2: Map) := forall k, find k m1 = find k m2.

  Definition Disj (m1 m2: Map) := forall k, find k m1 = None \/ find k m2 = None.
  Definition Sub (m1 m2: Map) := forall k, InMap k m1 -> m1 k = m2 k.

  Definition InDomain (m: Map) (d: list string) := forall k, InMap k m -> In k d.
  Definition OnDomain (m: Map) (d: list string) := forall k, In k d -> InMap k m.
  Definition NotOnDomain (m: Map) (d: list string) := forall k, In k d -> ~ InMap k m.
  Definition DomainOf (m: Map) (d: list string) := forall k, InMap k m <-> In k d.

  Lemma Equal_eq: forall m1 m2, Equal m1 m2 -> m1 = m2.
  Proof. intros; apply functional_extensionality; assumption. Qed.

  Lemma Equal_val: forall (m1 m2: Map) k, m1 = m2 -> m1 k = m2 k.
  Proof. intros; subst; reflexivity. Qed.

End Map.

Arguments Map : clear implicits.

Hint Unfold empty unionL unionR add union disjUnion
     find remove subtract update restrict complement : MapDefs.

Hint Unfold MapsTo InMap Equal Disj Sub
     InDomain OnDomain NotOnDomain DomainOf : MapDefs.
    
Section MakeMap.
  Variable A: Type.
  Variable f1 f2: A -> Type.
  Variable f: forall x, f1 x -> f2 x.

  Fixpoint makeMap (l: list (Attribute (Typed f1))) : Map (Typed f2) :=
    match l with
      | nil => empty
      | {| attrName := n; attrType := {| objVal := rv |} |} :: xs =>
        add n {| objVal := f rv |} (makeMap xs)
    end.

  Lemma disjUnionProp: forall (l1 l2: list (Attribute (Typed f1))),
                         disjUnion (makeMap l1) (makeMap l2) (map (@attrName _) l1) =
                         makeMap (l1 ++ l2).
  Proof.
    induction l1; simpl.
    - simpl; intros;
      apply functional_extensionality_dep; intros; simpl.
      unfold disjUnion, unionL; intros; reflexivity.
    - intros.
      destruct a.
      destruct attrType.
      apply functional_extensionality_dep; intros; simpl.
      unfold add, disjUnion, unionL.
      destruct (in_dec string_dec x (attrName :: map (Struct.attrName (Kind:=Typed f1)) l1)).
      + inv i.
        * rewrite string_dec_eq; reflexivity.
        * destruct (string_eq attrName x).
          { reflexivity. }
          { specialize (IHl1 l2).
            apply Equal_val with (k:=x) in IHl1.
            rewrite <-IHl1.
            unfold disjUnion.
            destruct (in_dec string_dec _ _); intuition.
          }
      + unfold string_eq.
        destruct (string_dec attrName x).
        * exfalso; subst; elim n; intuition.
        * specialize (IHl1 l2).
          apply Equal_val with (k:=x) in IHl1.
          rewrite <-IHl1.
          unfold disjUnion.
          destruct (in_dec string_dec _ _); intuition.
  Qed.
End MakeMap.

Section Facts.

  Lemma find_empty: forall {A} k, find k (@empty A) = None.
  Proof. intros; repeat autounfold with MapDefs; reflexivity. Qed.

  Lemma find_add_1: forall {A} k v (m: Map A), find k (add k v m) = Some v.
  Proof.
    intros; repeat autounfold with MapDefs; rewrite string_dec_eq; reflexivity.
  Qed.

  Lemma find_add_2: forall {A} k k' v (m: Map A),
                      string_eq k' k = false -> find k (add k' v m) = find k m.
  Proof.
    intros; repeat autounfold with MapDefs.
    rewrite H; reflexivity.
  Qed.

  Lemma add_empty_neq: forall {A} (m: Map A) k v, add k v m = empty -> False.
  Proof.
    intros; apply @Equal_val with (k:= k) in H.
    repeat autounfold with MapDefs in H.
    rewrite string_dec_eq in H; inv H.
  Qed.
  
  Lemma union_empty_1: forall {A} (m: Map A), union empty m = m.
  Proof.
    intros; repeat autounfold with MapDefs; reflexivity.
  Qed.

  Lemma union_empty_2: forall {A} (m: Map A), union m empty = m.
  Proof.
    intros; repeat autounfold with MapDefs.
    apply Equal_eq; repeat autounfold with MapDefs.
    intro k; destruct (m k); reflexivity.
  Qed.

  Lemma union_idempotent: forall {A} (m: Map A), union m m = m.
  Proof.
    intros; apply Equal_eq; repeat autounfold with MapDefs; intros.
    destruct (m k); auto.
  Qed.

  Lemma disjUnion_empty_1: forall {A} (m: Map A), disjUnion empty m nil = m.
  Proof.
    intros; repeat autounfold with MapDefs; reflexivity.
  Qed.

  Lemma disjUnion_empty_2: forall {A} (m: Map A) d, disjUnion m empty d = restrict m d.
  Proof.
    intros; repeat autounfold with MapDefs; apply Equal_eq; repeat autounfold with MapDefs.
    intro k; destruct (m k); reflexivity.
  Qed.

  Lemma disjUnion_In_1: forall {A} k (m1 m2: Map A) d,
                          In k d -> find k (disjUnion m1 m2 d) = find k m1.
  Proof.
    repeat autounfold with MapDefs; intros.
    destruct (in_dec string_dec k d); intuition.
  Qed.

  Lemma disjUnion_In_2: forall {A} k (m1 m2: Map A) d,
                          ~ In k d -> find k (disjUnion m1 m2 d) = find k m2.
  Proof.
    repeat autounfold with MapDefs; intros.
    destruct (in_dec string_dec k d); intuition.
  Qed.

  Lemma update_empty_1: forall {A} (m: Map A), update empty m = m.
  Proof.
    repeat autounfold with MapDefs; intros.
    apply Equal_eq; repeat autounfold with MapDefs.
    intro k; destruct (m k); reflexivity.
  Qed.

  Lemma update_empty_2: forall {A} (m: Map A), update m empty = m.
  Proof.
    repeat autounfold with MapDefs; intros.
    apply Equal_eq; repeat autounfold with MapDefs.
    intro k; reflexivity.
  Qed.

  Lemma restrict_nil: forall {A} (m: Map A), restrict m nil = empty.
  Proof.
    intros; apply Equal_eq; intro k; repeat autounfold with MapDefs.
    destruct (in_dec string_dec k nil); [|reflexivity].
    inversion i.
  Qed.

  Lemma restrict_empty: forall {A} (l: list string), restrict (@empty A) l = @empty A.
  Proof.
    intros; apply Equal_eq; intro k; repeat autounfold with MapDefs.
    destruct (in_dec string_dec k l); reflexivity.
  Qed.

  Lemma restrict_add: forall {A} (m: Map A) (l: list string) a v,
                        In a l -> restrict (add a v m) l = add a v (restrict m l).
  Proof.
    intros; apply Equal_eq; intro k; repeat autounfold with MapDefs.
    destruct (in_dec string_dec k l); intuition.
    unfold string_eq; destruct (string_dec _ _); intuition.
    subst; elim n; assumption.
  Qed.

  Lemma restrict_add_not: forall {A} (m: Map A) (l: list string) a v,
                            ~ In a l -> restrict (add a v m) l = restrict m l.
  Proof.
    intros; apply Equal_eq; intro k; repeat autounfold with MapDefs.
    destruct (in_dec _ k l); intuition.
    unfold string_eq; destruct (string_dec _ _); intuition.
    subst; elim H; assumption.
  Qed.
    
  Lemma restrict_union:
    forall {A} (m1 m2: Map A) l,
      restrict (union m1 m2) l = union (restrict m1 l) (restrict m2 l).
  Proof.
    intros; apply Equal_eq; intro k; repeat autounfold with MapDefs.
    destruct (in_dec _ k l); intuition.
  Qed.

  Lemma restrict_in: forall {A} k (m: Map A) (l: list string),
                       In k l -> find k (restrict m l) = find k m.
  Proof.
    intros; repeat autounfold with MapDefs.
    destruct (in_dec string_dec k l); intuition.
  Qed.

  Lemma restrict_not_in: forall {A} k (m: Map A) (l: list string),
                           ~ In k l -> find k (restrict m l) = None.
  Proof.
    intros; repeat autounfold with MapDefs.
    destruct (in_dec string_dec k l); intuition.
  Qed.    

  Lemma restrict_InDomain: forall {A} (m: Map A) (l: list string),
                             InDomain (restrict m l) l.
  Proof.
    repeat autounfold with MapDefs; intros.
    destruct (in_dec string_dec k l); intuition.
  Qed.

  Lemma restrict_InDomain_itself: forall {A} (m: Map A) (l: list string),
                                    InDomain m l -> restrict m l = m.
  Proof.
    intros; apply Equal_eq; repeat autounfold with MapDefs in *; intros.
    specialize (H k).
    destruct (in_dec _ _ _); intuition.
    destruct (m k); intuition.
    specialize (H (opt_discr _)); elim n; assumption.
  Qed.

  Lemma restrict_comm: forall {A} (m: Map A) (l1 l2: list string),
                           restrict (restrict m l1) l2 = restrict (restrict m l2) l1.
  Proof.
    intros; apply Equal_eq; repeat autounfold with MapDefs; intros.
    destruct (in_dec _ k l1); destruct (in_dec _ k l2); intuition.
  Qed.

  Lemma restrict_app: forall {A} (m: Map A) (l1 l2: list string),
                        restrict m (l1 ++ l2) = union (restrict m l1) (restrict m l2).
  Proof.
    intros; apply Equal_eq; repeat autounfold with MapDefs; intros.
    destruct (in_dec _ k (l1 ++ l2)).
    - apply in_app_or in i; destruct i.
      + destruct (in_dec _ k l1), (in_dec _ k l2), (m k); intuition.
      + destruct (in_dec _ k l1), (in_dec _ k l2), (m k); intuition.
    - destruct (in_dec _ k l1), (in_dec _ k l2); intuition.
  Qed.

  Lemma restrict_SubList:
    forall {A} (m: Map A) (l1 l2: list string),
      SubList l1 l2 -> restrict (restrict m l2) l1 = restrict m l1.
  Proof.
    intros; apply Equal_eq; intro k; repeat autounfold with MapDefs.
    specialize (H k).
    destruct (in_dec _ k l1); destruct (in_dec string_dec k l2); intuition.
  Qed.
  
  Lemma complement_nil: forall {A} (m: Map A), complement m nil = m.
  Proof.
    intros; apply Equal_eq; intro k; repeat autounfold with MapDefs.
    destruct (in_dec string_dec k nil); [|reflexivity].
    inversion i.
  Qed.

  Lemma complement_empty: forall {A} (l: list string), complement (@empty A) l = @empty A.
  Proof.
    intros; apply Equal_eq; intro k; repeat autounfold with MapDefs.
    destruct (in_dec string_dec k l); reflexivity.
  Qed.

  Lemma complement_in: forall {A} k (m: Map A) (l: list string),
                         ~ In k l -> find k (complement m l) = find k m.
  Proof.
    intros; repeat autounfold with MapDefs.
    destruct (in_dec string_dec k l); intuition.
  Qed.

  Lemma complement_add_1: forall {A} k v (m: Map A) (l: list string),
                            In k l -> complement (add k v m) l = complement m l.
  Proof.
    intros; repeat autounfold with MapDefs.
    apply Equal_eq; intro k'; repeat autounfold with MapDefs; simpl.
    destruct (in_dec string_dec k' l); [reflexivity|].
    unfold string_eq; destruct (string_dec k k'); [|reflexivity].
    subst; intuition.
  Qed.

  Lemma complement_add_2: forall {A} k v (m: Map A) (l: list string),
                            ~ In k l -> complement (add k v m) l = add k v (complement m l).
  Proof.
    intros; repeat autounfold with MapDefs.
    apply Equal_eq; intro k'; repeat autounfold with MapDefs; simpl.
    destruct (in_dec string_dec k' l); unfold string_eq;
    destruct (string_dec k k'); try reflexivity.
    subst; intuition.
  Qed.

  Lemma complement_union:
    forall {A} (m1 m2: Map A) l,
      complement (union m1 m2) l = union (complement m1 l) (complement m2 l).
  Proof.
    repeat autounfold with MapDefs; intros.
    apply Equal_eq; repeat autounfold with MapDefs; intros.
    destruct (in_dec _ k l); [reflexivity|].
    destruct (m1 k); intuition.
  Qed.

  Lemma complement_app: forall {A} (m: Map A) (l1 l2: list string),
                          complement m (l1 ++ l2) = complement (complement m l2) l1.
  Proof.
    intros; apply Equal_eq; repeat autounfold with MapDefs; intros.
    destruct (in_dec _ k (l1 ++ l2)).
    - apply in_app_or in i; destruct i.
      + destruct (in_dec _ k l1); intuition.
      + destruct (in_dec _ k l1); destruct (in_dec string_dec k l2); intuition.
    - destruct (in_dec _ k l1); destruct (in_dec string_dec k l2); intuition.
  Qed.

  Lemma complement_comm: forall {A} (m: Map A) (l1 l2: list string),
                           complement (complement m l1) l2 = complement (complement m l2) l1.
  Proof.
    intros; apply Equal_eq; repeat autounfold with MapDefs; intros.
    destruct (in_dec _ k l1); destruct (in_dec _ k l2); intuition.
  Qed.

  Lemma restrict_complement: forall {A} (m: Map A) (l: list string),
                               disjUnion (restrict m l) (complement m l) l = m.
  Proof.
    intros; repeat autounfold with MapDefs.
    apply Equal_eq; repeat autounfold with MapDefs; intros.
    destruct (in_dec string_dec k l); intuition.
  Qed.

  Lemma restrict_complement_DisjList:
    forall {A} (m: Map A) (l1 l2: list string),
      DisjList l1 l2 -> restrict (complement m l1) l2 = restrict m l2.
  Proof.
    intros; apply Equal_eq; intro k; repeat autounfold with MapDefs in *.
    specialize (H k).
    destruct (in_dec _ k l1); destruct (in_dec _ k l2); intuition.
  Qed.
    
  Lemma complement_restrict_DisjList:
    forall {A} (m: Map A) (l1 l2: list string),
      DisjList l1 l2 -> complement (restrict m l1) l2 = restrict m l1.
  Proof.
    intros; apply Equal_eq; intro k; repeat autounfold with MapDefs in *.
    specialize (H k).
    destruct (in_dec _ k l1); destruct (in_dec _ k l2); intuition.
  Qed.

  Lemma complement_DisjList:
    forall {A} (m: Map A) (l1 l2: list string),
      DisjList l1 l2 -> complement (complement m l1) l2 = complement (complement m l2) l1.
  Proof.
    intros; apply Equal_eq; intro k; repeat autounfold with MapDefs in *.
    specialize (H k).
    destruct (in_dec _ k l1); destruct (in_dec _ k l2); intuition.
  Qed.
    
  Lemma restrict_complement_nil:
    forall {A} (m: Map A) (l: list string),
      restrict m l = m -> complement m l = empty.
  Proof.
    intros; apply Equal_eq; intro k; repeat autounfold with MapDefs in *.
    apply @Equal_val with (k := k) in H.
    destruct (in_dec _ k l); intuition.
  Qed.

  Lemma restrict_complement_itself:
    forall {A} (m: Map A) (l: list string),
      restrict m l = empty -> complement m l = m.
  Proof.
    intros; apply Equal_eq; intro k; repeat autounfold with MapDefs in *.
    apply @Equal_val with (k := k) in H.
    destruct (in_dec _ k l); intuition.
  Qed.

  Lemma complement_restrict_nil:
    forall {A} (m: Map A) (l: list string),
      complement m l = m -> restrict m l = empty.
  Proof.
    intros; apply Equal_eq; intro k; repeat autounfold with MapDefs in *.
    apply @Equal_val with (k := k) in H.
    destruct (in_dec _ k l); intuition.
  Qed.

  Lemma complement_restrict_itself:
    forall {A} (m: Map A) (l: list string),
      complement m l = empty -> restrict m l = m.
  Proof.
    intros; apply Equal_eq; intro k; repeat autounfold with MapDefs in *.
    apply @Equal_val with (k := k) in H.
    destruct (in_dec _ k l); intuition.
  Qed.

  Lemma complement_InDomain:
    forall {A} (m: Map A) (cd rd: list string),
      InDomain m (cd ++ rd) -> InDomain (complement m cd) rd.
  Proof.
    repeat autounfold with MapDefs; intros.
    destruct (in_dec string_dec k cd); [intuition|].
    specialize (H _ H0); apply in_app_or in H.
    inversion H; intuition.
  Qed.

  Lemma find_InDomain: forall {A} k (m: Map A) (d: list string),
                         InDomain m d -> ~ In k d -> find k m = None.
  Proof.
    repeat autounfold with MapDefs; intros; specialize (H k).
    destruct (m k); [|reflexivity].
    elim H0; apply H; intro X; inversion X.
  Qed.

  Lemma union_InDomain:
    forall {A} (m1 m2: Map A) (d1 d2: list string),
      InDomain m1 d1 -> InDomain m2 d2 -> InDomain (union m1 m2) (d1 ++ d2).
  Proof.
    repeat autounfold with MapDefs; intros.
    specialize (H k); specialize (H0 k).
    destruct (m1 k); destruct (m2 k); intuition.
  Qed.

  Lemma disjUnion_InDomain:
    forall {A} (m1 m2: Map A) (d1 d2: list string),
      InDomain m1 d1 -> InDomain m2 d2 -> InDomain (disjUnion m1 m2 d1) (d1 ++ d2).
  Proof.
    repeat autounfold with MapDefs; intros.
    specialize (H k); specialize (H0 k).
    destruct (in_dec string_dec k d1); intuition.
  Qed.

  Lemma Disj_comm: forall {A} (m1 m2: Map A), Disj m1 m2 -> Disj m2 m1.
  Proof.
    repeat autounfold with MapDefs; intros.
    specialize (H k); destruct H; intuition idtac.
  Qed.

  Lemma Disj_empty_1: forall {A} (m: Map A), Disj empty m.
  Proof.
    repeat autounfold with MapDefs; intros; left; reflexivity.
  Qed.

  Lemma Disj_empty_2: forall {A} (m: Map A), Disj m empty.
  Proof. intros; apply Disj_comm; apply Disj_empty_1. Qed.

  Lemma Disj_find_union:
    forall {A} (m1 m2: Map A) k v,
      Disj m1 m2 -> find k m2 = Some v -> find k (union m1 m2) = Some v.
  Proof.
    repeat autounfold with MapDefs; intros; rewrite H0.
    specialize (H k); destruct H; [rewrite H; reflexivity|].
    rewrite H in H0; discriminate.
  Qed.

  Lemma Disj_unionL_unionR: forall {A} (m1 m2: Map A), Disj m1 m2 -> unionL m1 m2 = unionR m1 m2.
  Proof.
    repeat autounfold with MapDefs; intros.
    apply Equal_eq; repeat autounfold with MapDefs; intros.
    specialize (H k).
    destruct (m1 k); destruct (m2 k); intuition; inv H0.
  Qed.

  Lemma Disj_union_unionR: forall {A} (m1 m2: Map A), Disj m1 m2 -> union m1 m2 = unionR m1 m2.
  Proof. intros; apply Disj_unionL_unionR; auto. Qed.

  Lemma Disj_add_1: forall {A} (m1 m2: Map A) k v, Disj (add k v m1) m2 -> Disj m1 m2.
  Proof.
    repeat autounfold with MapDefs; intros.
    specialize (H k0); destruct H; [|auto].
    unfold string_eq in H; destruct (string_dec _ _); auto.
    inv H.
  Qed.

  Lemma Disj_add_2: forall {A} (m1 m2: Map A) k v, Disj m1 (add k v m2) -> Disj m1 m2.
  Proof.
    repeat autounfold with MapDefs; intros.
    specialize (H k0); destruct H; [auto|].
    unfold string_eq in H; destruct (string_dec _ _); auto.
    inv H.
  Qed.

  Lemma Disj_union: forall {A} (m1 m2 m3: Map A),
                      Disj m1 m2 -> Disj m1 m3 -> Disj m1 (union m2 m3).
  Proof.
    repeat autounfold with MapDefs; intros.
    specialize (H k); specialize (H0 k).
    destruct H; [left; assumption|].
    destruct H0; [left; assumption|].
    right; rewrite H; assumption.
  Qed.

  Lemma Disj_union_1: forall {A} (m1 m2 m3: Map A), Disj m1 (union m2 m3) -> Disj m1 m2.
  Proof.
    repeat autounfold with MapDefs; intros.
    specialize (H k); destruct H; [left; assumption|].
    destruct (m2 k); [inv H|right; reflexivity].
  Qed.

  Lemma Disj_union_2: forall {A} (m1 m2 m3: Map A), Disj m1 (union m2 m3) -> Disj m1 m3.
  Proof.
    repeat autounfold with MapDefs; intros.
    specialize (H k); destruct H; [left; assumption|].
    destruct (m2 k); [inv H|right; assumption].
  Qed.

  Lemma Disj_restrict:
    forall {A} (m1 m2: Map A) l, Disj m1 m2 -> Disj (restrict m1 l) m2.
  Proof.
    repeat autounfold with MapDefs; intros.
    specialize (H k); destruct H; [left; destruct (in_dec _ _ _); auto|right; assumption].
  Qed.
    
  Lemma Disj_DisjList_restrict:
    forall {A} (m: Map A) l1 l2, DisjList l1 l2 -> Disj (restrict m l1) (restrict m l2).
  Proof.
    repeat autounfold with MapDefs; intros.
    specialize (H k); destruct H;
    [left; destruct (in_dec _ _ _); intuition|right; destruct (in_dec _ _ _); intuition].
  Qed.

  Lemma Disj_complement: forall {A} (m1 m2: Map A) l, Disj m1 m2 -> Disj m1 (complement m2 l).
  Proof.
    repeat autounfold with MapDefs; intros.
    specialize (H k); destruct H; [left; assumption|].
    right; destruct (in_dec _ _ _); intuition.
  Qed.

  Lemma Disj_OnDomain: forall {A} (m1 m2: Map A) l,
                         Disj m1 m2 -> OnDomain m1 l -> NotOnDomain m2 l.
  Proof.
    repeat autounfold with MapDefs; intros.
    specialize (H k); specialize (H0 k).
    destruct H; intuition.
  Qed.

  Lemma Disj_union1 : forall A (m1 m2 m : Map A),
      Disj (union m1 m2) m
      -> Disj m1 m.
  Proof.
    intros; intro k.
    specialize (H k).
    unfold find, union, unionL in *; intuition idtac.
    destruct (m1 k); auto.
  Qed.

  Lemma Disj_union2 : forall A (m1 m2 m : Map A),
      Disj (union m1 m2) m
      -> Disj m2 m.
  Proof.
    intros; intro k.
    specialize (H k).
    unfold find, union, unionL in *; intuition idtac.
    destruct (m1 k); auto; discriminate.
  Qed.


  Lemma Sub_refl: forall {A} (m: Map A), Sub m m.
  Proof.
    repeat autounfold with MapDefs; reflexivity.
  Qed.

  Lemma Sub_unionL: forall {A} (m1 m2: Map A), Sub m1 (unionL m1 m2).
  Proof.
    repeat autounfold with MapDefs; intros.
    destruct (m1 k); intuition.
  Qed.

  Lemma Sub_unionR: forall {A} (m1 m2: Map A), Sub m2 (unionR m1 m2).
  Proof.
    repeat autounfold with MapDefs; intros.
    destruct (m2 k); intuition.
  Qed.

  Lemma Sub_union: forall {A} (m1 m2: Map A), Sub m1 (union m1 m2).
  Proof. intros; apply Sub_unionL. Qed.

  Lemma Sub_disjUnion: forall {A} (m1 m2: Map A) d1, Sub (restrict m1 d1) (disjUnion m1 m2 d1).
  Proof.
    repeat autounfold with MapDefs; intros.
    destruct (in_dec _ k d1); intuition.
  Qed.

  Lemma Sub_merge: forall {A} (m1 m2: Map A), Sub m1 m2 -> union m1 m2 = m2.
  Proof.
    repeat autounfold with MapDefs; intros.
    apply Equal_eq; repeat autounfold with MapDefs; intros.
    specialize (H k); destruct (m1 k); intuition.
    apply H; discriminate.
  Qed.

  Lemma InDomain_add:
    forall {A} (m: Map A) k v d,
      InDomain m d -> In k d -> InDomain (add k v m) d.
  Proof.
    repeat autounfold with MapDefs; intros.
    unfold string_eq in *.
    destruct (string_dec k k0); subst; intuition.
  Qed.

  Lemma InDomain_update:
    forall {A} (m1 m2: Map A) (d: list string),
      InDomain m1 d -> InDomain m2 d -> InDomain (update m1 m2) d.
  Proof.
    repeat autounfold with MapDefs; intros.
    specialize (H k); specialize (H0 k); case_eq (m2 k); intros.
    + rewrite H2 in H1.
      rewrite <- H2 in H1.
      intuition.
    + rewrite H2 in H1.
      intuition.
  Qed.

  Lemma InDomain_DisjList_restrict:
    forall {A} (m: Map A) (d1 d2: list string),
      InDomain m d1 -> DisjList d1 d2 -> restrict m d2 = empty.
  Proof.
    intros; apply Equal_eq; repeat autounfold with MapDefs in *; intros.
    destruct (in_dec _ k d2); intuition.
    specialize (H k); specialize (H0 k); destruct (m k); auto.
    specialize (H (opt_discr _)); destruct H0; intuition.
  Qed.

  Lemma OnDomain_add:
    forall {A} (m: Map A) (d: list string) k v,
      OnDomain m d -> OnDomain (add k v m) (k :: d).
  Proof.
    repeat autounfold with MapDefs; intros.
    specialize (H k0); unfold string_eq; destruct (string_dec k k0); intuition; [inv H1|].
    inv H0; intuition.
  Qed.

  Lemma NotOnDomain_complement: forall {A} (m: Map A) (d: list string),
                                  NotOnDomain m d -> complement m d = m.
  Proof.
    intros; apply Equal_eq; repeat autounfold with MapDefs in *; intros.
    specialize (H k).
    destruct (in_dec _ _ _); intuition.
    destruct (m k); intuition.
    specialize (H0 (opt_discr _)); elim H0.
  Qed.

  Lemma DomainOf_DisjList_Disj:
    forall {A} (m: Map A) (d1 d2: list string),
      DomainOf m (d1 ++ d2) -> DisjList d1 d2 ->
      exists m1 m2, (* m1 = restrict m d1 /\ m2 = restrict m d2 *)
        Disj m1 m2 /\ m = union m1 m2 /\ DomainOf m1 d1 /\ DomainOf m2 d2.
  Proof.
    admit.
  Qed.

  Lemma disjUnion_div':
    forall {A} (m1 m2 n1 n2: Map A) (d1 d2: list string),
      (forall k, ~ (In k d1 /\ In k d2)) ->
      InDomain m1 d1 -> InDomain m2 d2 -> InDomain n1 d1 -> InDomain n2 d2 ->
      disjUnion m1 m2 d1 = disjUnion n1 n2 d1 ->
      forall x, m1 x = n1 x /\ m2 x = n2 x.
  Proof.
    repeat autounfold with MapDefs; intros.
    specialize (H x); specialize (H0 x); specialize (H1 x); specialize (H2 x); specialize (H3 x).
    apply Equal_val with (k:=x) in H4.
    destruct (in_dec string_dec x d1).
    - split; auto.
      destruct (m2 x); destruct (n2 x).
      + specialize (H1 (opt_discr _)); elim H; intuition.
      + specialize (H1 (opt_discr _)); elim H; intuition.
      + specialize (H3 (opt_discr _)); elim H; intuition.
      + reflexivity.
    - split; auto.
      destruct (m1 x); destruct (n1 x).
      + specialize (H2 (opt_discr _)); elim H; intuition.
      + specialize (H0 (opt_discr _)); elim H; intuition.
      + specialize (H2 (opt_discr _)); elim H; intuition.
      + reflexivity.
  Qed.

  Lemma disjUnion_div:
    forall {A} (m1 m2 n1 n2: Map A) (d1 d2: list string),
      (forall k, ~ (In k d1 /\ In k d2)) ->
      InDomain m1 d1 -> InDomain m2 d2 -> InDomain n1 d1 -> InDomain n2 d2 ->
      disjUnion m1 m2 d1 = disjUnion n1 n2 d1 ->
      m1 = n1 /\ m2 = n2.
  Proof.
    intros.
    pose proof (disjUnion_div' H H0 H1 H2 H3 H4).
    constructor; apply functional_extensionality_dep; intros; specialize (H5 x); intuition.
  Qed.

  Lemma unionL_assoc:
    forall {A} (m1 m2 m3: Map A), unionL m1 (unionL m2 m3) = unionL (unionL m1 m2) m3.
  Proof.
    repeat autounfold with MapDefs; intros.
    apply Equal_eq; repeat autounfold with MapDefs; intro.
    destruct (m1 k), (m2 k); intuition.
  Qed.

  Lemma union_assoc:
    forall {A} (m1 m2 m3: Map A), union m1 (union m2 m3) = union (union m1 m2) m3.
  Proof. intros; apply unionL_assoc. Qed.

  Lemma union_comm:
    forall {A} (m1 m2: Map A), Disj m1 m2 -> union m1 m2 = union m2 m1.
  Proof.
    intros; apply Equal_eq; repeat autounfold with MapDefs; intros.
    specialize (H k); unfold find in H.
    destruct (m1 k), (m2 k); intuition; inv H0.
  Qed.

  Lemma disjUnion_update_comm:
    forall {A} (o1 n1 o2 n2: Map A) d,
      disjUnion (update o1 n1) (update o2 n2) d = update (disjUnion o1 o2 d) (disjUnion n1 n2 d).
  Proof.
    intros.
    apply Equal_eq; intro k.
    unfold find, disjUnion, update, unionL.
    destruct (in_dec string_dec k d); intuition.
  Qed.

  Lemma InMap_empty : forall A k, InMap k (empty (A := A))
                                  -> False.
  Proof.
    clear; unfold InMap, find, empty; intuition idtac.
  Qed.

  Lemma InMap_add : forall A k k' v m, InMap k (add (A := A) k' v m)
                                       -> k = k'
                                          \/ InMap k m.
  Proof.
    clear; unfold InMap, find, add, unionL; intuition idtac.
    destruct (string_dec k' k); subst.
    auto.
    rewrite string_dec_neq in * by assumption; auto.
  Qed.

  Lemma InMap_union : forall A k m1 m2, InMap k (union (A := A) m1 m2)
                                        -> InMap k m1
                                           \/ InMap k m2.
  Proof.
    clear; unfold InMap, find, union, unionL; intuition idtac.
    destruct (m1 k); intuition congruence.
  Qed.

  Lemma InMap_disjUnion: forall A k m1 m2 d1, InMap k (disjUnion (A := A) m1 m2 d1)
                                              -> InMap k m1
                                                 \/ InMap k m2.
  Proof.
    clear; repeat autounfold with MapDefs; intros.
    destruct (in_dec string_dec k d1); intuition idtac.
  Qed.

  Lemma InMap_restrict : forall A k m ls, InMap k (restrict (A := A) m ls)
                                          -> InMap k m
                                             /\ In k ls.
  Proof.
    clear; unfold InMap, find, restrict; intuition idtac;
    destruct (in_dec string_dec k ls); intuition.
  Qed.

  Lemma InMap_complement : forall A k m ls, InMap k (complement (A := A) m ls)
                                            -> InMap k m
                                               /\ ~In k ls.
  Proof.
    clear; unfold InMap, find, complement; intuition idtac;
    destruct (in_dec string_dec k ls); intuition.
  Qed.

End Facts.

Ltac map_simpl H :=
  repeat ((rewrite complement_empty in H)
            || (rewrite complement_nil in H)
            || (rewrite complement_in in H;
                [|clear; intro; in_tac_H; discriminate])
            || (rewrite complement_add_1 in H by in_tac)
            || (rewrite complement_add_2 in H by (intro; in_tac_H; discriminate))
            || (rewrite restrict_complement in H)
            || (rewrite restrict_nil in H)
            || (rewrite restrict_empty in H)
            || (rewrite restrict_in in H by in_tac)
            || (rewrite union_empty_1 in H)
            || (rewrite union_empty_2 in H)
            || (rewrite disjUnion_empty_1 in H)
            || (rewrite disjUnion_empty_2 in H)
            || (rewrite disjUnion_In_1 in H by in_tac)
            || (rewrite disjUnion_In_2 in H by (intro; in_tac_H; discriminate))
            || (rewrite update_empty_1 in H)
            || (rewrite update_empty_2 in H)
            || (rewrite find_add_1 in H)
            || (rewrite find_add_2 in H by reflexivity)
            || (rewrite find_empty in H)).

Ltac map_simpl_G :=
  repeat ((rewrite complement_empty)
            || (rewrite complement_nil)
            || (rewrite complement_in;
                [|clear; intro; in_tac_H; discriminate])
            || (rewrite complement_add_1 by in_tac)
            || (rewrite complement_add_2 by (intro; in_tac_H; discriminate))
            || (rewrite restrict_complement)
            || (rewrite restrict_nil)
            || (rewrite restrict_empty)
            || (rewrite restrict_in by in_tac)
            || (rewrite union_empty_1)
            || (rewrite union_empty_2)
            || (rewrite disjUnion_empty_1)
            || (rewrite disjUnion_empty_2)
            || (rewrite disjUnion_In_1 by in_tac)
            || (rewrite disjUnion_In_2 by (intro; in_tac_H; discriminate))
            || (rewrite update_empty_1)
            || (rewrite update_empty_2)
            || (rewrite find_add_1)
            || (rewrite find_add_2 by reflexivity)
            || (rewrite find_empty)).

Ltac map_compute H :=
  (* map_simpl H; *)
  repeat autounfold with MapDefs in H;
  repeat autounfold with ModulesDefs in H;
  repeat autounfold in H; ssimpl H.
Ltac map_compute_G :=
  (* map_simpl_G; *)
  repeat autounfold with MapDefs;
  repeat autounfold with ModuleDefs;
  repeat autounfold; ssimpl_G.

Ltac find_eq :=
  try reflexivity; (* already structurally equal? *)
  map_compute_G;
  try reflexivity. (* final check *)

Ltac map_eq :=
  try reflexivity; (* already equal? *)
  map_simpl_G;
  try reflexivity;
  let k := fresh "k" in
  apply Equal_eq; intro k; (* If not, let's use functional extensionality *)
  repeat autounfold;
  repeat
    match goal with
      | [ |- context [k] ] =>
        match goal with
          | [ |- context [add ?k' _ _] ] => (* Find all "add"s in two maps and do case analyses *)
            isNew (k' <> k); destruct (string_dec k' k); [subst; find_eq|]
        end
    end; (* Possible to have some unproven equalities between two values *)
  map_simpl_G;
  try reflexivity;
  try
    match goal with
      | [ |- context [k] ] => (* If key is not equal to any added keys, then should be None *)
        repeat autounfold with MapDefs;
          repeat (* Resolve all string_eq branches *)
            match goal with
              | [H: _ <> k |- _] =>
                let Hneq := fresh "Hneq" in
                pose proof (string_dec_neq H) as Hneq; rewrite Hneq; clear Hneq
            end;
          repeat (* Resolve all in_dec string_dec branches, by restrict and complement *)
            match goal with
              | [ |- context [in_dec string_dec ?k' ?l] ] =>
                destruct (in_dec string_dec k' l)
            end;
          try reflexivity (* None = None ? *)
    end.

Ltac inDomain_tac_old :=
  (* provable by existing utility lemmas? *)
  try (apply restrict_InDomain || apply complement_InDomain; auto);
  (* well if not... *)
  let k := fresh "k" in
  let H := fresh "H" in
  unfold InDomain; intros k H; unfold InMap in H; map_simpl H; simpl in H;
  let n := fresh "n" in
  match goal with
    | [ |- In ?k ?l ] =>
      destruct (in_dec string_dec k l) as [|n]; [assumption|]
  end;
    elim H;
    try reflexivity;
    repeat
      match goal with
        | [ |- context [k] ] =>
          match goal with
            | [ |- context [add ?k' _ _] ] =>
              isNew (k' <> k);
                let e := fresh "e" in
                destruct (string_dec k' k) as [e|];
                  [subst; elim n; in_tac|]
          end
      end;
    try
      match goal with
        | [ |- context [k] ] => (* If key is not equal to any added keys, then should be None *)
          repeat autounfold with MapDefs;
            repeat (* Resolve all string_eq branches *)
              match goal with
                | [H: _ <> k |- _] =>
                  let Hneq := fresh "Hneq" in
                  pose proof (string_dec_neq H) as Hneq; rewrite Hneq; clear Hneq
              end;
            repeat (* Resolve all in_dec string_dec branches, by restrict and complement *)
              match goal with
                | [ |- context [in_dec string_dec ?k' ?l] ] =>
                  destruct (in_dec string_dec k' l)
              end;
            try reflexivity (* None = None ? *)
      end.

Ltac inDomain_tac := hnf; simpl; intros;
                     repeat match goal with
                            | [ H : InMap _ (union _ _) |- _ ] =>
                              apply InMap_union in H; destruct H
                            | [ H : InMap _ (add _ _ _) |- _ ] =>
                              apply InMap_add in H; destruct H; subst
                            | [ H : InMap _ empty |- _ ] =>
                              apply InMap_empty in H; destruct H
                            | [ H : InMap _ (restrict _ _) |- _ ] =>
                              apply InMap_restrict in H; destruct H
                            | [ H : InMap _ (complement _ _) |- _ ] =>
                              apply InMap_complement in H; destruct H
                            end; simpl in *; intuition idtac.

Hint Extern 1 (find _ _ = _) => find_eq.
Hint Extern 1 (_ = find _ _) => find_eq.
Hint Extern 1 (_ = _: (Map _)) => map_eq.
Hint Extern 1 (InDomain _ _) => inDomain_tac_old.
Hint Extern 1 (Disj _ empty) => apply Disj_empty_2.
Hint Extern 1 (Disj empty _) => apply Disj_empty_1.

Lemma union_add : forall A k (v : A) m1 m2,
  m1 k = None
  -> union m1 (add k v m2) = union (add k v m1) m2.
Proof.
  unfold union, add, unionL; intros.
  extensionality k0.
  destruct (string_dec k k0); subst.
  rewrite string_dec_eq.
  rewrite H; auto.
  rewrite string_dec_neq by assumption.
  auto.
Qed.

Lemma Disj_add : forall A (m1 m2 : Map A) k v,
  Disj (add k v m1) m2
  -> Disj m1 m2.
Proof.
  intros; intro k0.
  specialize (H k0).
  unfold find, add, unionL in *; intuition idtac.
  destruct (string_dec k k0); subst.
  rewrite string_dec_eq in *; discriminate.
  rewrite string_dec_neq in * by tauto; tauto.
Qed.
