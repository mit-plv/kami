Require Import String Word List Arith.
Require Import Lib.CommonTactics Lib.ilist Lib.StringBound.
Require Import Equality Eqdep_dec FunctionalExtensionality.

Set Implicit Arguments.

Section GenAttribute.
  Variable Key: Type.
  Variable ValueT: Key -> Type.

  Record GenAttr :=
    { genAttrKey : Key;
      genAttrVal : ValueT genAttrKey }.

  Variable Key_dec: forall k1 k2: Key, {k1 = k2} + {k1 <> k2}.

  Definition MapGenAttrT := forall key, ValueT key.

  Definition addKeyVal (m: MapGenAttrT) k (v: ValueT k) :=
    fun k' =>
      match Key_dec k k' with
        | left Heq => match Heq with
                        | eq_refl => v
                      end
        | right _ => m k'
      end.

  Definition disjUnionMap (domain1: list Key) (map1: MapGenAttrT) (domain2: list Key) (map2: MapGenAttrT) :=
    fun k =>
      match in_dec Key_dec k domain1 with
        | left _ => map1 k
        | right _ => map2 k
      end.

  Definition filtMap (m: MapGenAttrT) hide def :=
    fun k =>
      match in_dec Key_dec k hide with
        | left _ => def k
        | right _ => m k
      end.

End GenAttribute.

Record Typed A (B: A -> Type) :=
  { objType : A;
    objVal : B objType }.

Hint Unfold objType objVal.

Definition unionMap Key (ValueT: Key -> Type)
                    (map1 map2: MapGenAttrT (fun k => option (ValueT k))) :=
  fun k =>
    match map1 k, map2 k with
      | Some v, _ => Some v
      | _, Some v => Some v
      | _, _ => None
    end.

Section BoundedIndexFull.
  Variable Kind: Type.

  Record Attribute :=
    { attrName : string;
      attrType : Kind }.

  Definition Attribute_dec (kdec: forall (k1 k2: Kind), {k1 = k2} + {k1 <> k2})
  : forall (a1 a2: Attribute), {a1 = a2} + {a1 <> a2}.
  Proof. intros; repeat decide equality. Qed.

  Definition BoundedIndexFull attrs := BoundedIndex (map attrName attrs).

  Definition GetAttr
               {attrs: list Attribute}
               (idx : BoundedIndexFull attrs) :=
    nth_Bounded _ attrs idx.

  Definition GetAttrType
               {attrs: list Attribute}
               (idx : BoundedIndexFull attrs) :=
    attrType (GetAttr idx).

  Lemma BoundedIndexFull_one_attr (a: Attribute):
    forall i: BoundedIndexFull (a :: nil), GetAttrType i = attrType a.
  Proof.
    intros.
    destruct i as [bind [ib bi]].
    destruct ib.
    - simpl in bi; inversion bi; subst; auto.
    - simpl in bi; destruct ib; inversion bi.
  Qed.

End BoundedIndexFull.

Hint Unfold attrName attrType.

Definition appendName nm s := (nm ++ "." ++ s)%string.
Definition appendAttr nm t (a: Attribute t) :=
  {| attrName := appendName nm (attrName a); attrType := attrType a |}.
Definition mapAppendAttr nm t (ls: list (Attribute t)) :=
  map (fun a => appendAttr nm a) ls.

Infix "-n-" := appendName (at level 20, left associativity).
Infix "-a-" := appendAttr (at level 21, right associativity).
Infix "-m-" := mapAppendAttr (at level 22, right associativity).

Section BoundedProp.
  Definition boundedPropIdx (A: Type) (l: list A) (P: BoundedIndex l -> Prop)
             (i: nat): Prop.
  Proof.
    remember (nth_error l i) as v.
    destruct v.
    exact (P {| indexb := Build_IndexBound _ _ (eq_sym Heqv) |}).
    exact True.
  Defined.

  Inductive boundedPropStep
            (A: Type) (l: list A) (P: BoundedIndex l -> Prop) : nat -> Prop :=
  | boundedPropO: boundedPropIdx P O -> boundedPropStep P O
  | boundedPropS n: boundedPropStep P n -> boundedPropIdx P (S n) ->
                    boundedPropStep P (S n).

  Definition boundedProp (A: Type) (l: list A) (P: BoundedIndex l -> Prop)
    := boundedPropStep P (Datatypes.length l - 1).

  Lemma boundedProp_forall (A: Type) (l: list A) (P: BoundedIndex l -> Prop):
    boundedProp P <-> (forall (i: BoundedIndex l), P i).
  Proof.
    split; intros.

    - unfold boundedProp in H.
      destruct i as [bind [ib bi]].
      pose proof (lt_nth _ _ bi).
      induction (Datatypes.length l); [omega|].
      simpl in *.
      destruct (Compare_dec.lt_dec ib n) as [Hlt|Hnlt].
      + destruct n; [omega|].
        simpl in H; inversion H; subst; clear H.
        simpl in IHn.
        apply IHn; auto.
        replace (n - 0) with n by omega; assumption.
      + assert (ib = n) by omega; subst; clear H0 Hnlt IHn.
        replace (n - 0) with n in H by omega.
        destruct n.
        * destruct l; inversion bi; subst.
          simpl in H; inversion H; clear H.
          unfold boundedPropIdx in H0; simpl in H0.
          match goal with
            | [H: P {| indexb := {| boundi := ?pf1 |} |} |-
               P {| indexb := {| boundi := ?pf2 |} |} ] =>
              replace pf2 with pf1 by apply UIP
          end.
          exact H0.
        * inversion H; subst; clear H H1.
          remember (S n) as n'; clear Heqn' n; rename n' into n.
          unfold boundedPropIdx in H2.

          generalize dependent n; generalize dependent l; induction l; intros;
          [destruct n; simpl in bi; inversion bi|].
          destruct n.

          simpl in H2, bi; inversion bi; subst.
          match goal with
            | [H: P {| indexb := {| boundi := ?pf1 |} |} |-
               P {| indexb := {| boundi := ?pf2 |} |} ] =>
              replace pf2 with pf1 by apply UIP
          end.
          exact H2.

          simpl in H2, bi.
          pose (fun i: BoundedIndex l =>
                  P {| indexb := {| boundi := (boundi i): nth_error (a :: l)
                                                                    (S (ibound i))
                                                          = Some (bindex i)
                                 |} |}) as P'.
          apply (IHl P'); auto.
          
    - unfold boundedProp.
      induction (Datatypes.length l);
        [simpl; constructor; unfold boundedPropIdx; destruct l; simpl; auto|].
      simpl in *.
      destruct n;
        [simpl; constructor; unfold boundedPropIdx; destruct l; simpl; auto|].
      simpl in *.
      constructor; replace (n - 0) with n in IHn by omega; [assumption|].
      unfold boundedPropIdx.

      clear -H.
      generalize dependent l.
      induction n; intros.

      + destruct l; simpl; auto.
        destruct l; simpl; auto.

      + destruct l; [simpl; auto|].
        pose (fun i: BoundedIndex l =>
                P {| indexb := {| boundi := (boundi i): nth_error (a::l) (S (ibound i))
                                                        = Some (bindex i) |} |}) as P'.
        assert (forall i, P' i) as H' by (intros; apply H).
        apply (IHn l P' H').
  Qed.

End BoundedProp.

Hint Unfold boundedPropIdx boundedProp.

Section BoundedMap.
  
  Lemma boundedMap_equal:
    forall A (l: list A) (V: BoundedIndex l -> Type)
           (f g: forall (i: BoundedIndex l), V i),
      f = g <-> (forall i, f i = g i).
  Proof.
    split; intros.
    - subst; reflexivity.
    - apply functional_extensionality_dep; auto.
  Qed.

  Lemma boundedMap_equal_separate:
    forall A (l: list A) (V: BoundedIndex l -> Type)
           (f g: forall (i: BoundedIndex l), V i),
      f = g <-> boundedProp (fun i => f i = g i).
  Proof.
    split; intros.
    - apply boundedProp_forall.
      apply boundedMap_equal.
      assumption.
    - apply boundedMap_equal.
      apply boundedProp_forall.
      assumption.
  Qed.    

End BoundedMap.

Section AddUnion.

  Definition disjUnionBounded
             (l: list string) {A: BoundedIndex l -> Type}
             (f1: forall i: BoundedIndex l, option (A i))
             (f2: forall i: BoundedIndex l, option (A i)) :=
    fun i => match f1 i, f2 i with
               | Some x, _ => Some x
               | _, Some x => Some x
               | _, _ => None
             end.

  Section DisjUnionBoundedProp.
    Variable l: list string.
    Context {A: BoundedIndex l -> Type}.

    Theorem noneImpDisjUnionNone
            (f1: forall i: BoundedIndex l, option (A i))
            (f2: forall i: BoundedIndex l, option (A i))
            (f1None: f1 = fun _ => None)
            (f2None: f2 = fun _ => None):
      disjUnionBounded f1 f2 = fun _ => None.
    Proof.
      unfold disjUnionBounded.
      apply functional_extensionality_dep; intros.
      assert (H: f1 x = None) by (rewrite f1None; intuition).
      assert (H2: f2 x = None) by (rewrite f2None; intuition).
      subst; intuition.
    Qed.

    Theorem noneUnionImpDisjUnionSame1
            (f1: forall i: BoundedIndex l, option (A i))
            (f2: forall i: BoundedIndex l, option (A i))
            (f1None: f1 = fun _ => None):
      disjUnionBounded f1 f2 = f2.
    Proof.
      unfold disjUnionBounded.
      apply functional_extensionality_dep; intros.
      assert (H: f1 x = None) by (rewrite f1None; intuition).
      subst; destruct (f2 x); intuition.
    Qed.

    Theorem noneUnionImpDisjUnionSame2
            (f1: forall i: BoundedIndex l, option (A i))
            (f2: forall i: BoundedIndex l, option (A i))
            (f2None: f2 = fun _ => None):
      disjUnionBounded f1 f2 = f1.
    Proof.
      unfold disjUnionBounded.
      apply functional_extensionality_dep; intros.
      assert (H: f2 x = None) by (rewrite f2None; intuition).
      subst; destruct (f1 x); intuition.
    Qed.

    Theorem disjUnionNoneImpNone
            (f1: forall i: BoundedIndex l, option (A i))
            (f2: forall i: BoundedIndex l, option (A i)):
      forall x, disjUnionBounded f1 f2 x = None ->
                f1 x = None /\ f2 x = None.
    Proof.
      intros.
      unfold disjUnionBounded in *.
      destruct (f1 x), (f2 x).
      discriminate.
      discriminate.
      discriminate.
      intuition.
    Qed.

    Theorem disjUnionImpNone
            (f1: forall i: BoundedIndex l, option (A i))
            (f2: forall i: BoundedIndex l, option (A i)):
      disjUnionBounded f1 f2 = (fun _ => None) ->
      f1 = (fun _ => None) /\ f2 = fun _ => None.
    Proof.
      intros.
      unfold disjUnionBounded in *.
      match goal with
        | H: ?x=?y |- _ => remember x as m1; remember y as m2; rewrite Heqm2
      end.
      assert (base: forall x, m1 x = m2 x) by (intros; rewrite H; reflexivity).
      rewrite Heqm1, Heqm2 in base.
      assert (H1: f1 = fun _ => None) by
          (apply functional_extensionality_dep;
           intros;
           specialize (base x);
           destruct (f1 x); intuition).
      assert (H2: f2 = fun _ => None).
      (apply functional_extensionality_dep;
       intros;
       specialize (base x);
       rewrite H1 in base;
       destruct (f2 x); intuition).
      intuition.
    Qed.

    Lemma disjUnionBounded_prop:
      forall l (A: BoundedIndex l -> Type) lm rm i,
        @disjUnionBounded l A lm rm i =
        match lm i with
          | Some v => Some v
          | None => rm i
        end.
    Proof.
      intros.
      unfold disjUnionBounded.
      subst.
      destruct (lm i), (rm i); auto.
    Qed.
  
  End DisjUnionBoundedProp.

  Definition addBounded
             (l: list string) {A: BoundedIndex l -> Type}
             (i: BoundedIndex l)
             (v: A i)
             (f: forall i: BoundedIndex l, A i) :=
    fun i' => match BoundedString_eq_dec i i' with
                | left Heq =>
                  match Heq with
                    | eq_refl => v
                  end
                | right _ => f i'
              end.

  Section AddBoundedProp.
    Variable l: list string.
    Variable A: BoundedIndex l -> Type.

    Theorem addBoundedNotNone
            (i: BoundedIndex l)
            (v: A i)
            (f: forall i: BoundedIndex l, option (A i))
            (contra: addBounded _ (Some v) f = fun _ => None):
      False.
    Proof.
      unfold addBounded in contra.
      match goal with
        | H: ?x=?y |- _ => remember x as m1; remember y as m2
      end.
      assert (base: forall x, m1 x = m2 x) by (intros; rewrite contra; reflexivity).
      rewrite Heqm1, Heqm2 in base.
      specialize (base i).
      destruct (BoundedString_eq_dec i i).
      destruct e.
      discriminate.
      intuition.
    Qed.

    Lemma addBounded_prop1:
      forall l (A: BoundedIndex l -> Type) m i i' (Hii: i = i') v,
        @addBounded l A i v m i' = match Hii with eq_refl => v end.
    Proof.
      intros; subst.
      unfold addBounded.
      destruct (BoundedString_eq_dec i' i').
      - rewrite (UIP_refl _ _ e); auto.
      - elim n; auto.
    Qed.
    
    Lemma addBounded_prop2:
      forall l (A: BoundedIndex l -> Type) m i i' v' (Hii: i <> i'),
        @addBounded l A i' v' m i = m i.
    Proof.
      intros.
      unfold addBounded.
      destruct (BoundedString_eq_dec i' i); auto.
      elim Hii; auto.
    Qed.

  End AddBoundedProp.

End AddUnion.
  
Ltac boundedApplyTac1 :=
  unfold IndexBound_head, IndexBound_tail;
  match goal with
    | [ |- context [addBounded
                      {| bindex := _; indexb := {| ibound := _;
                                                   boundi := ?pf1 |} |}
                      _ _
                      {| bindex := _; indexb := {| ibound := _;
                                                   boundi := ?pf2 |} |}] ] =>
      first [rewrite (addBounded_prop1 _ _ eq_refl) |
             replace pf2 with pf1 by apply UIP; rewrite (addBounded_prop1 _ _ eq_refl)]
  end.

Ltac boundedApplyTac2 :=
  rewrite addBounded_prop2 by (let x := fresh "x" in intro x; inversion x).

Ltac boundedApplyTac :=
  repeat rewrite disjUnionBounded_prop;
  repeat (first [boundedApplyTac1 | boundedApplyTac2 |
                 progress destruct_eq | auto]).

Ltac boundedApplyTac1_H H pf1 pf2 :=
  first [rewrite (addBounded_prop1 _ _ eq_refl) in H |
         replace pf2 with pf1 in H by apply UIP;
           rewrite (addBounded_prop1 _ _ eq_refl) in H].

Ltac boundedApplyTac2_H H :=
  let x := fresh "x" in
  rewrite addBounded_prop2 in H by (intro x; inversion x).

Ltac boundedApplyTac_H :=
  unfold IndexBound_head, IndexBound_tail in *;
  repeat
    match goal with
      | [H: context [addBounded
                       {| bindex := _; indexb := {| ibound := _;
                                                    boundi := ?pf1 |} |}
                       _ _
                       {| bindex := _; indexb := {| ibound := _;
                                                    boundi := ?pf2 |} |}]
         |- _ ] => 
        (repeat rewrite disjUnionBounded_prop in H;
         repeat (first [boundedApplyTac1_H H pf1 pf2 | boundedApplyTac2_H H]))
      | [H: Some _ = None |- _] => inversion H
      | [H: Some _ = Some _ |- _] => inversion H; clear H; subst
    end.

Ltac boundedMapTac :=
  apply boundedMap_equal_separate;
  repeat autounfold with *; repeat constructor; repeat autounfold with *;
  repeat split; simpl; try boundedApplyTac.

Section ConcatStr.
  Fixpoint extendToRightStr (ll rl: list string) (idx: BoundedIndex ll): BoundedIndex (ll ++ rl).
  Proof.
    destruct ll; intros.
    apply (BoundedIndex_nil _ idx).
    destruct idx as [s1 [i pf]].
    destruct i.
    apply ({| indexb :=
                {| boundi :=
                     pf: nth_error ((s :: ll) ++ rl) 0 = Some s1 |} |}).
    pose (extendToRightStr ll rl {| indexb := {| boundi :=
                                                   pf: nth_error ll i = Some s1 |} |}).
    apply {| indexb :=
               {| boundi :=
                    (boundi b): nth_error ((s :: ll) ++ rl)
                                          (S (ibound b)) = Some (bindex b) |} |}.
  Defined.

  Fixpoint extendToLeftStr (ll rl: list string) (idx: BoundedIndex rl): BoundedIndex (ll ++ rl).
  Proof.
    destruct ll; intros.
    apply idx.
    pose (extendToLeftStr ll rl idx).
    apply {| indexb :=
               {| boundi :=
                    (boundi b): nth_error ((s :: ll) ++ rl)
                                          (S (ibound b)) = Some (bindex b) |} |}.
  Defined.

End ConcatStr.

Section ConcatIdx.
  Variable t: Type.
  Variable t2: t -> Type.

  Fixpoint extendToRight (ll rl: list (Attribute t)) (idx: BoundedIndexFull ll):
    BoundedIndexFull (ll ++ rl).
  Proof.
    destruct ll; intros.
    apply (BoundedIndex_nil _ idx).
    destruct idx as [s [i pf]].
    destruct i.
    apply ({| indexb :=
                {| boundi :=
                     pf: nth_error (map (@attrName _) ((a :: ll) ++ rl)) 0 = Some s |} |}).
    pose (extendToRight ll rl {| indexb :=
                                   {| boundi :=
                                        pf: nth_error (map (@attrName _) ll) i = Some s |} |}).
    apply {| indexb :=
               {| boundi :=
                    (boundi b): nth_error (map (@attrName _) ((a :: ll) ++ rl))
                                          (S (ibound b)) = Some (bindex b) |} |}.
  Defined.

  Lemma extendToRight_GetAttrType:
    forall (ll rl: list (Attribute t)) (idx: BoundedIndexFull ll),
      GetAttrType idx = GetAttrType (extendToRight rl idx).
  Proof.
    admit.
  Qed.

  Fixpoint extendToLeft (ll rl: list (Attribute t)) (idx: BoundedIndexFull rl):
    BoundedIndexFull (ll ++ rl).
  Proof.
    destruct ll; intros.
    apply idx.
    pose (extendToLeft ll rl idx).
    apply {| indexb :=
               {| boundi :=
                    (boundi b): nth_error (map (@attrName _) ((a :: ll) ++ rl))
                                          (S (ibound b)) = Some (bindex b) |} |}.
  Defined.

  Lemma extendToLeft_GetAttrType:
    forall (ll rl: list (Attribute t)) (idx: BoundedIndexFull rl),
      GetAttrType idx = GetAttrType (extendToLeft ll idx).
  Proof.
    admit.
  Qed.

  Fixpoint concatIdx (ll rl: list (Attribute t))
           (lMap: forall b: BoundedIndexFull ll, t2 (GetAttrType b))
           (rMap: forall b: BoundedIndexFull rl, t2 (GetAttrType b))
           (idx: BoundedIndexFull (ll ++ rl)):
             t2 (GetAttrType idx).
  Proof.
    destruct ll; intros.
    apply (rMap idx).
    destruct (lt_dec (ibound (indexb idx)) (length (a :: ll)));
      destruct idx as [s [i pf]]; destruct i.
    apply (lMap {| indexb :=
                     {| boundi := pf: nth_error (map (@attrName _) (a :: ll)) 0 =
                                      Some s|} |}).
    apply (concatIdx
             _ _ (fun (b: BoundedIndexFull ll) =>
            lMap {|
                indexb :=
                  {| boundi :=
                       boundi b: nth_error (map (@attrName _) (a :: ll))
                                           (S (ibound b)) = Some (bindex b) |} |})
                          rMap
             {| indexb := {| boundi := pf: nth_error (map (@attrName _) (ll ++ rl)) i =
                                           Some s|} |}).
    simpl in n; exfalso; clear -n ; abstract omega.
    apply (concatIdx
             _ _ (fun (b: BoundedIndexFull ll) =>
            lMap {|
                indexb :=
                  {| boundi :=
                       boundi b: nth_error (map (@attrName _) (a :: ll))
                                           (S (ibound b)) = Some (bindex b) |} |})
                          rMap
             {| indexb := {| boundi := pf: nth_error (map (@attrName _) (ll ++ rl)) i =
                                           Some s|} |}).
  Defined.

End ConcatIdx.

Section ConcatIdxProp.

  Lemma extendToRight_length:
    forall (t: Type) (ll rl: list (Attribute t)) i,
      (ibound (extendToRight (ll:=ll) rl i) < Datatypes.length ll)%nat.
  Proof.
    induction ll; intros; [exfalso; apply (BoundedIndex_nil False i)|].
    simpl; destruct i as [bind [ib bi]].
    destruct ib; [simpl; omega|].
    simpl.
    apply Lt.lt_n_S.
    apply IHll.
  Qed.

  Lemma extendToRight_value:
    forall (t: Type) (t2: t -> Type)
           (ll rl: list (Attribute t))
           (lm: forall b: BoundedIndexFull ll, t2 (GetAttrType b))
           (rm: forall b: BoundedIndexFull rl, t2 (GetAttrType b))
           i,
      concatIdx t2 lm rm (extendToRight rl i) =
      match (extendToRight_GetAttrType rl i) with
        | eq_refl => lm i
      end.
  Proof.
    admit.
  Qed.

  Lemma extendToLeft_length:
    forall (t: Type) (ll rl: list (Attribute t)) i,
      ~ (ibound (extendToLeft (rl:=rl) ll i) < Datatypes.length ll)%nat.
  Proof.
    induction ll; intros; [simpl; omega|].
    simpl; pose (IHll rl i).
    omega.
  Qed.

  Lemma extendToLeft_value:
    forall (t: Type) (t2: t -> Type)
           (ll rl: list (Attribute t))
           (lm: forall b: BoundedIndexFull ll, t2 (GetAttrType b))
           (rm: forall b: BoundedIndexFull rl, t2 (GetAttrType b))
           i,
      concatIdx t2 lm rm (extendToLeft ll i) =
      match (extendToLeft_GetAttrType ll i) with
        | eq_refl => rm i
      end.
  Proof.
    admit.
  Qed.
  
End ConcatIdxProp.

Section FiltIdx.
  Variable t: Type.
  Variable t2: t -> Type.
  Variable filt: Attribute t -> bool.

  Fixpoint getFiltIdx (ls : list (Attribute t)) (idx : BoundedIndexFull ls)
           (Hfilt: filt (nth_Bounded _ ls idx) = true) {struct ls}:
    BoundedIndexFull (filter filt ls).
  Proof.
    destruct ls; [apply (BoundedIndex_nil _ idx)|].
    simpl in *.
    remember (filt a) as fa; destruct fa.
    - destruct idx as [s [i pf]].
      destruct i.
      + unfold nth_Bounded in Hfilt. simpl in Hfilt.
        apply {| indexb :=
                   {| boundi := pf: nth_error (map (@attrName _)
                                                   (a :: filter filt ls)) 0
                                    = Some s |} |}.
      + match goal with
          | [H: filt ?b = true |- _] =>
            assert (b = nth_Bounded
                          _ ls
                          {| bindex := s;
                             indexb := {| ibound := i;
                                          boundi := pf: nth_error (map (@attrName _) ls)
                                                                  i
                                                        = Some s |} |})
              by reflexivity
        end.
        rewrite H in Hfilt; clear H.
        pose (getFiltIdx ls
                         {| indexb :=
                              {| boundi := pf: nth_error (map (@attrName _) ls) i
                                               = Some s |} |} Hfilt).
        apply {| indexb :=
                   {| boundi := (boundi b): nth_error (map (@attrName _)
                                                           (a :: filter filt ls))
                                                      (S (ibound b))
                                            = Some (bindex b) |} |}.
    - destruct idx as [s [i pf]].
      destruct i.
      + unfold nth_Bounded in Hfilt; simpl in Hfilt;
        rewrite <-Heqfa in Hfilt; inversion Hfilt.
      + match goal with
          | [H: filt ?b = true |- _] =>
            assert (b = nth_Bounded
                          _ ls
                          {| bindex := s;
                             indexb := {| ibound := i;
                                          boundi := pf: nth_error (map (@attrName _) ls)
                                                                  i
                                                        = Some s |} |})
              by reflexivity
        end.
        rewrite H in Hfilt; clear H.
        apply (getFiltIdx ls
                          {| indexb :=
                               {| boundi := pf: nth_error (map (@attrName _) ls) i
                                                = Some s |} |} Hfilt).
  Defined.

  Lemma getFiltIdx_GetAttrType:
    forall (ls : list (Attribute t)) (idx : BoundedIndexFull ls)
           (Hfilt: filt (nth_Bounded _ ls idx) = true),
      GetAttrType idx = GetAttrType (getFiltIdx idx Hfilt).
  Proof.
    admit.
  Qed.

  Fixpoint getUnFiltIdx (ls : list (Attribute t)) (idx : BoundedIndexFull (filter filt ls)):
    BoundedIndexFull ls.
  Proof.
    destruct ls.
    apply (BoundedIndex_nil _ idx).
    simpl in *.
    destruct (filt a).
    destruct idx as [s [i pf]].
    destruct i.
    apply {| indexb :=
               {| boundi := pf: nth_error (map (@attrName _) (a :: ls)) 0 = Some s |} |}.
    pose (getUnFiltIdx ls
                    {| indexb :=
                         {| boundi := pf: nth_error (map (@attrName _) (filter filt ls)) i =
                                          Some s |} |}).
    apply {| indexb :=
               {| boundi := (boundi b): nth_error (map (@attrName _) (a :: ls))
                                                  (S (ibound b)) = Some (bindex b) |} |}.
    pose (getUnFiltIdx ls idx).
    apply {| indexb :=
               {| boundi := (boundi b): nth_error (map (@attrName _) (a :: ls))
                                                  (S (ibound b)) = Some (bindex b) |} |}.
  Defined.

  Lemma getUnFiltIdx_GetAttrType:
    forall (ls : list (Attribute t)) (idx : BoundedIndexFull (filter filt ls)),
      GetAttrType idx = GetAttrType (getUnFiltIdx ls idx).
  Proof.
    admit.
  Qed.

  Fixpoint filtIdx (ls: list (Attribute t))
           (fn: forall b: BoundedIndexFull ls, t2 (GetAttrType b))
           (idx: BoundedIndexFull (filter filt ls)): t2 (GetAttrType idx).
  Proof.
    destruct ls; intros.
    apply (BoundedIndex_nil _ idx).
    simpl in *.
    destruct (filt a).
    destruct idx as [s [i pf]].
    destruct i.
    apply (fn {| indexb :=
                   {| boundi :=
                        pf: nth_error (map (@attrName _) (a :: ls)) 0 = Some s |} |}).
    apply (filtIdx ls
                   (fun b: BoundedIndexFull ls =>
                      fn {| indexb :=
                            {|
                              boundi :=
                              (boundi b):
                              nth_error (map (@attrName _) (a :: ls))
                                        (S (ibound b)) = Some (bindex b)|} |})
                   {| indexb := {| boundi := pf:
                                               nth_error (map (@attrName _) (filter filt ls))
                                                         i = Some s |} |}).
    apply (filtIdx ls
                   (fun b: BoundedIndexFull ls =>
                      fn {| indexb :=
                            {|
                              boundi :=
                              (boundi b):
                              nth_error (map (@attrName _) (a :: ls))
                                        (S (ibound b)) = Some (bindex b)|} |})
                   {| indexb := {| boundi :=
                                     (boundi idx):
                                       nth_error (map (@attrName _)
                                                      (filter filt ls)) (ibound idx)
                                       = Some (bindex idx) |} |}).
  Defined.

End FiltIdx.

Section FiltIdxProp.
  Variable t: Type.
  Variable t2: t -> Type.
  Variable filt: Attribute t -> bool.

  Lemma filtIdx_value:
    forall (ls: list (Attribute t))
           (m: forall b: BoundedIndexFull ls, t2 (GetAttrType b))
           (idx: BoundedIndexFull ls)
           (Hfilt: filt (nth_Bounded _ ls idx) = true),
      filtIdx _ _ m (getFiltIdx _ _ Hfilt) =
      match (getFiltIdx_GetAttrType _ _ Hfilt) with
        | eq_refl => m idx
      end.
  Proof.
    admit.
  Qed.

End FiltIdxProp.

Section MapAttr.
  Variable Kind: Type.
  Variable type: Kind -> Type.

  Definition mapAttr a := {| attrName := attrName a;
                             attrType := type (attrType a) |}.

  Definition addFirstBoundedIndex A attrs (a: Attribute A) (idx: BoundedIndexFull attrs):
    BoundedIndexFull (a :: attrs).
  Proof.
    apply {| indexb :=
               {| boundi := (boundi idx): nth_error (map (@attrName _) (a :: attrs))
                                                    (S (ibound idx)) = Some (bindex idx) |} |}.
  Defined.
  
  Fixpoint getNewIdx1 attrs (idx: BoundedIndexFull (map mapAttr attrs)):
    BoundedIndexFull attrs.
  Proof.
    destruct attrs.
    apply (BoundedIndex_nil _ idx).
    destruct idx as [s [i pf]].
    destruct i.
    apply ({| indexb := {|
                         boundi := pf: nth_error (map (@attrName _) (a :: attrs)) 0 =
                                       Some s |} |}).
    apply (addFirstBoundedIndex a
             (getNewIdx1 attrs {| indexb :=
                                    {| boundi := pf: nth_error (map (@attrName _)
                                                                    (map mapAttr attrs)) i =
                                                     Some s |} |})).
  Defined.

  Fixpoint getNewIdx2 attrs (idx: BoundedIndexFull attrs):
    BoundedIndexFull (map mapAttr attrs).
  Proof.
    destruct attrs.
    apply (BoundedIndex_nil _ idx).
    destruct idx as [s [i pf]].
    destruct i.
    apply ({| indexb :=
                {| boundi := pf: nth_error (map (@attrName _) (map mapAttr (a :: attrs))) 0 =
                                 Some s |} |}).
    apply (addFirstBoundedIndex
             (mapAttr a)
             (getNewIdx2 attrs {| indexb :=
                                    {| boundi := pf: nth_error (map (@attrName _) attrs) i =
                                                     Some s |} |})).
  Defined.

  Fixpoint mapAttrEq1 attrs:
    forall (idx: BoundedIndexFull (map mapAttr attrs))
           (val: type (GetAttrType (getNewIdx1 attrs idx))),
      GetAttrType idx.
  Proof.
    destruct attrs; intros.
    apply (BoundedIndex_nil _ idx).
    destruct idx as [s [i pf]].
    destruct i.
    assumption.
    apply (mapAttrEq1 attrs {| indexb :=
                                 {| boundi := pf: nth_error (map (@attrName _)
                                                                 (map mapAttr attrs)) i = Some s
                                 |} |} val).
  Defined.

  Fixpoint mapAttrEq2 attrs:
    forall (idx: BoundedIndexFull attrs) (val: GetAttrType (getNewIdx2 idx)),
      type (GetAttrType idx).
  Proof.
    destruct attrs; intros.
    apply (BoundedIndex_nil _ idx).
    destruct idx as [s [i pf]].
    destruct i.
    assumption.
    apply (mapAttrEq2 attrs {| indexb :=
                                 {| boundi := pf: nth_error (map (@attrName _) attrs) i = Some s
                                 |} |} val).
  Defined.

End MapAttr.

Section Laster.
  Variable Kind: Type.
  Variable type: Kind -> Type.
  Variable decEq: forall k (e1 e2: type k), {e1 = e2} + {e1 <> e2}.

  Definition withoutFirst attrs
             (a: Attribute Kind)
             (t: forall i: BoundedIndexFull (a :: attrs), type (GetAttrType i))
             (i: BoundedIndexFull attrs): type (GetAttrType i) :=
    t {| indexb :=
           {| boundi := (boundi i):
                          nth_error (map (@attrName _) (a :: attrs))
                                    (S (ibound i)) = Some (bindex i) |} |}.

  Fixpoint structEq' attrs:
    forall (t1 t2: forall i, type (@GetAttrType _ attrs i)),
      {forall x, t1 x = t2 x} + {exists x, t1 x <> t2 x}.
  Proof.
    destruct attrs; intros.
    left; intros x; apply (BoundedIndex_nil _ x).

    specialize (structEq' _ (withoutFirst t1) (withoutFirst t2)).

    pose {| indexb := {|
                       boundi := eq_refl:
                                   nth_error (map (@attrName _) (a :: attrs))
                                             0 = Some (attrName a) |} |} as zero.

    specialize (decEq (t1 zero) (t2 zero)).
    destruct decEq, structEq'.
    left.
    intros x.
    destruct x as [s [i pf]].
    destruct i.
    rewrite (idx_ibound_eq string_dec zero {|  indexb := {| boundi := pf |} |} eq_refl) in *.
    intuition.
    specialize (e0 {| indexb := {| boundi :=
                                     pf: nth_error (map (@attrName _) attrs) i = Some s |} |}).
    assumption.
    right.
    dest.
    exists {| indexb :=
                {| boundi :=
                     (boundi x):
                       nth_error
                         (map (@attrName _) (a :: attrs)) (S (ibound x)) = Some (bindex x) |} |}.
    assumption.
    right.
    exists zero.
    assumption.
    right.
    exists zero.
    assumption.
  Qed.

  Definition structEq attrs:
    forall (t1 t2: forall i, type (@GetAttrType _ attrs i)),
      {t1 = t2} + {t1 <> t2}.
  Proof.
    intros.
    pose proof (structEq' t1 t2) as [lt | rt].
    left; apply functional_extensionality_dep; intuition.
    right; destruct rt as [x cond]; unfold not; intros eq; rewrite eq in *; intuition.
  Qed.
End Laster.

Notation "`` A" := ({| bindex := A%string |}) (at level 0, format "`` A").

Notation "[]" := (fun _ => None) (at level 0, format "[]").
Notation "M '(+)' [ K <- V ]" :=
  (addBounded K V M)
    (left associativity, at level 1, format "M '/' '(+)' '/' [ K <- V ]").
Notation "M1 '(+)' M2" :=
  (disjUnionBounded M1 M2)
    (left associativity, at level 2, format "M1 '/' '(+)' '/' M2").
Notation "M1 '{+}' M2" :=
  (concatIdx _ M1 M2)
    (left associativity, at level 3, format "M1 '/' '{+}' '/' M2").

Notation "I ':' [ K '<:-' V ] '(:)' M" :=
  (match BoundedString_eq_dec K I with
     | left Heq => match Heq with eq_refl => V end
     | right Hneq => M
   end) (right associativity, at level 5).

