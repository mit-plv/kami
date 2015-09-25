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

  Lemma Equal_eq: forall m1 m2, Equal m1 m2 -> m1 = m2.
  Proof. intros; apply functional_extensionality; assumption. Qed.

  Lemma Equal_val: forall (m1 m2: Map) k, m1 = m2 -> m1 k = m2 k.
  Proof. intros; subst; reflexivity. Qed.

  Lemma InDomainUpd (m1 m2: Map) (d: list string):
    InDomain m1 d -> InDomain m2 d -> InDomain (update m1 m2) d.
  Proof.
    unfold InDomain, InMap, update, unionL, find in *; simpl in *; intros.
    specialize (H k); specialize (H0 k); case_eq (m2 k); intros.
    + rewrite H2 in H1.
      rewrite <- H2 in H1.
      intuition.
    + rewrite H2 in H1.
      intuition.
  Qed.

  Lemma DisjUnionEq' (m1 m2 n1 n2: Map):
    forall d1 d2: list string,
      (forall k, ~ (In k d1 /\ In k d2)) ->
      InDomain m1 d1 -> InDomain m2 d2 -> InDomain n1 d1 -> InDomain n2 d2 ->
      disjUnion m1 m2 d1 = disjUnion n1 n2 d1 ->
      forall x, m1 x = n1 x /\ m2 x = n2 x.
  Proof.
    unfold InDomain, InMap, find, disjUnion; intros.
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

  Lemma DisjUnionEq (m1 m2 n1 n2: Map):
    forall d1 d2: list string,
      (forall k, ~ (In k d1 /\ In k d2)) ->
      InDomain m1 d1 -> InDomain m2 d2 -> InDomain n1 d1 -> InDomain n2 d2 ->
      disjUnion m1 m2 d1 = disjUnion n1 n2 d1 ->
      m1 = n1 /\ m2 = n2.
  Proof.
    intros.
    pose proof (DisjUnionEq' H H0 H1 H2 H3 H4).
    constructor; apply functional_extensionality_dep; intros; specialize (H5 x); intuition.
  Qed.

  Lemma UnionAssoc: forall m1 m2 m3, unionL m1 (unionL m2 m3) = unionL (unionL m1 m2) m3.
  Proof.
    intros.
    apply functional_extensionality_dep; intros.
    unfold union, unionL.
    destruct (m1 x), (m2 x); intuition.
  Qed.

  Lemma UnionComm m1 m2 d1 d2:
    (forall k, ~ (In k d1 /\ In k d2)) ->
    InDomain m1 d1 -> InDomain m2 d2 ->
    unionL m1 m2 = unionL m2 m1.
  Proof.
    intros.
    apply functional_extensionality_dep; intros.
    unfold unionL, InDomain, InMap in *.
    specialize (H x).
    case_eq (m1 x); case_eq (m2 x); intros.
    - assert (K1: m1 x <> None) by (unfold not; intros H'; rewrite H' in *; discriminate).
      assert (K2: m2 x <> None) by (unfold not; intros H'; rewrite H' in *; discriminate).
      specialize (H0 _ K1).
      specialize (H1 _ K2).
      intuition.
    - intuition.
    - intuition.
    - intuition.
  Qed.

  Lemma UpdRewrite o1 n1 o2 n2 d:
    disjUnion (update o1 n1) (update o2 n2) d = update (disjUnion o1 o2 d) (disjUnion n1 n2 d).
  Proof.
    intros.
    apply Equal_eq; intro k.
    unfold find, disjUnion, update, unionL.
    destruct (in_dec string_dec k d); intuition.
  Qed.
End Map.

Hint Unfold empty unionL unionR add union disjUnion
     find remove subtract update restrict complement : MapDefs.

Hint Unfold MapsTo InMap Equal Disj Sub InDomain : MapDefs.
    
Section MakeMap.
  Variable A: Type.
  Variable f1 f2: A -> Type.
  Variable f: forall x, f1 x -> f2 x.

  Fixpoint makeMap (l: list (Attribute (Typed f1))) : @Map (Typed f2) :=
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

  Lemma find_add_1: forall {A} k v (m: @Map A), find k (add k v m) = Some v.
  Proof.
    intros; repeat autounfold with MapDefs; rewrite string_dec_eq; reflexivity.
  Qed.

  Lemma find_add_2: forall {A} k k' v (m: @Map A),
                      string_eq k' k = false -> find k (add k' v m) = find k m.
  Proof.
    intros; repeat autounfold with MapDefs.
    rewrite H; reflexivity.
  Qed.

  Lemma union_empty_1: forall {A} (m: @Map A), union empty m = m.
  Proof.
    intros; repeat autounfold with MapDefs; reflexivity.
  Qed.

  Lemma union_empty_2: forall {A} (m: @Map A), union m empty = m.
  Proof.
    intros; repeat autounfold with MapDefs.
    apply Equal_eq; repeat autounfold with MapDefs.
    intro k; destruct (m k); reflexivity.
  Qed.

  Lemma disjUnion_empty_1: forall {A} (m: @Map A), disjUnion empty m nil = m.
  Proof.
    intros; repeat autounfold with MapDefs; reflexivity.
  Qed.

  Lemma disjUnion_empty_2: forall {A} (m: @Map A) d, disjUnion m empty d = restrict m d.
  Proof.
    intros; repeat autounfold with MapDefs; apply Equal_eq; repeat autounfold with MapDefs.
    intro k; destruct (m k); reflexivity.
  Qed.

  Lemma disjUnion_In_1: forall {A} k (m1 m2: @Map A) d,
                          In k d -> find k (disjUnion m1 m2 d) = find k m1.
  Proof.
    repeat autounfold with MapDefs; intros.
    destruct (in_dec string_dec k d); intuition.
  Qed.

  Lemma disjUnion_In_2: forall {A} k (m1 m2: @Map A) d,
                          ~ In k d -> find k (disjUnion m1 m2 d) = find k m2.
  Proof.
    repeat autounfold with MapDefs; intros.
    destruct (in_dec string_dec k d); intuition.
  Qed.

  Lemma update_empty_1: forall {A} (m: @Map A), update empty m = m.
  Proof.
    repeat autounfold with MapDefs; intros.
    apply Equal_eq; repeat autounfold with MapDefs.
    intro k; destruct (m k); reflexivity.
  Qed.

  Lemma update_empty_2: forall {A} (m: @Map A), update m empty = m.
  Proof.
    repeat autounfold with MapDefs; intros.
    apply Equal_eq; repeat autounfold with MapDefs.
    intro k; reflexivity.
  Qed.

  Lemma restrict_nil: forall {A} (m: @Map A), restrict m nil = empty.
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

  Lemma restrict_in: forall {A} k (m: @Map A) (l: list string),
                       In k l -> find k (restrict m l) = find k m.
  Proof.
    intros; repeat autounfold with MapDefs.
    destruct (in_dec string_dec k l); intuition.
  Qed.

  Lemma restrict_InDomain: forall {A} (m: @Map A) (l: list string),
                             InDomain (restrict m l) l.
  Proof.
    repeat autounfold with MapDefs; intros.
    destruct (in_dec string_dec k l); intuition.
  Qed.
  
  Lemma complement_nil: forall {A} (m: @Map A), complement m nil = m.
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

  Lemma complement_in: forall {A} k (m: @Map A) (l: list string),
                         ~ In k l -> find k (complement m l) = find k m.
  Proof.
    intros; repeat autounfold with MapDefs.
    destruct (in_dec string_dec k l); intuition.
  Qed.

  Lemma complement_add_1: forall {A} k v (m: @Map A) (l: list string),
                            In k l -> complement (add k v m) l = complement m l.
  Proof.
    intros; repeat autounfold with MapDefs.
    apply Equal_eq; intro k'; repeat autounfold with MapDefs; simpl.
    destruct (in_dec string_dec k' l); [reflexivity|].
    unfold string_eq; destruct (string_dec k k'); [|reflexivity].
    subst; intuition.
  Qed.

  Lemma complement_add_2: forall {A} k v (m: @Map A) (l: list string),
                            ~ In k l -> complement (add k v m) l = add k v (complement m l).
  Proof.
    intros; repeat autounfold with MapDefs.
    apply Equal_eq; intro k'; repeat autounfold with MapDefs; simpl.
    destruct (in_dec string_dec k' l); unfold string_eq;
    destruct (string_dec k k'); try reflexivity.
    subst; intuition.
  Qed.

  Lemma restrict_complement: forall {A} (m: @Map A) (l: list string),
                               disjUnion (restrict m l) (complement m l) l = m.
  Proof.
    intros; repeat autounfold with MapDefs.
    apply Equal_eq; repeat autounfold with MapDefs; intros.
    destruct (in_dec string_dec k l); intuition.
  Qed.

  Lemma complement_InDomain:
    forall {A} (m: @Map A) (cd rd: list string),
      InDomain m (cd ++ rd) -> InDomain (complement m cd) rd.
  Proof.
    repeat autounfold with MapDefs; intros.
    destruct (in_dec string_dec k cd); [intuition|].
    specialize (H _ H0); apply in_app_or in H.
    inversion H; intuition.
  Qed.

  Lemma find_InDomain: forall {A} k (m: @Map A) (d: list string),
                         InDomain m d -> ~ In k d -> find k m = None.
  Proof.
    repeat autounfold with MapDefs; intros; specialize (H k).
    destruct (m k); [|reflexivity].
    elim H0; apply H; intro X; inversion X.
  Qed.

  Lemma disjUnion_InDomain:
    forall {A} (m1 m2: @Map A) (d1 d2: list string),
      InDomain m1 d1 -> InDomain m2 d2 -> InDomain (disjUnion m1 m2 d1) (d1 ++ d2).
  Proof.
    repeat autounfold with MapDefs; intros.
    specialize (H k); specialize (H0 k).
    destruct (in_dec string_dec k d1); intuition.
  Qed.

  Lemma Disj_empty_1: forall {A} (m: @Map A), Disj empty m.
  Proof.
    repeat autounfold with MapDefs; intros; left; reflexivity.
  Qed.

  Lemma Disj_empty_2: forall {A} (m: @Map A), Disj m empty.
  Proof.
    repeat autounfold with MapDefs; intros; right; reflexivity.
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
  map_simpl H;
  repeat autounfold with MapDefs in H;
  repeat autounfold with ModulesDefs in H;
  repeat autounfold in H; ssimpl H.
Ltac map_compute_G :=
  map_simpl_G;
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
Hint Extern 1 (_ = _: (@Map _)) => map_eq.
Hint Extern 1 (InDomain _ _) => inDomain_tac_old.
Hint Extern 1 (Disj _ empty) => apply Disj_empty_2.
Hint Extern 1 (Disj empty _) => apply Disj_empty_1.

