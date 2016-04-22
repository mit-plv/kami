Set Implicit Arguments.

Require Import List String Arith CommonTactics.

Section ilist.

  (* Lists of elements whose types depend on an indexing set (CPDT's hlists).
     These lists are a convenient way to implement finite maps
     whose elements depend on their keys. The data structures used
     by our ADT notations uses these to implement notation-friendly
     method lookups.  *)

  Variable A : Type. (* The indexing type. *)
  Variable B : A -> Type. (* The type of indexed elements. *)

  Inductive ilist : list A -> Type :=
  | icons : forall a As, B a -> ilist As -> ilist (a :: As)
  | inil : ilist nil.

  (* Get the car of an ilist. *)

  Definition ilist_hd (As : list A) (il : ilist As) :
    match As return ilist As -> Type with
      | a :: As' => fun il => B a
      | nil => fun _ => unit
    end il :=
    match il with
      | icons a As b As' => b
      | inil => tt
    end.

  (* Get the cdr of an ilist. *)

  Definition ilist_tl (As : list A) (il : ilist As) :
    match As return ilist As -> Type with
      | a :: As' => fun il => ilist As'
      | nil => fun _ => unit
    end il :=
    match il with
      | icons a As b As' => As'
      | inil => tt
    end.

  (* Membership in an indexed list. *)

  Inductive ilist_In {a : A} (b : B a)
  : forall (As : list A) (il : ilist As), Prop :=
  | In_hd : forall As' (il : ilist As'),
              ilist_In b (icons b il)
  | In_tl : forall a' (b' : B a') As' (il : ilist As'),
              ilist_In b il ->
              ilist_In b (icons b' il).

  (* ilists can be built from standard lists of sigma types *)

  Fixpoint siglist2ilist (sigList : list (sigT B))
  : ilist (map (@projT1 _ B) sigList) :=
    match sigList
          return ilist (map (@projT1 _ B) sigList) with
      | nil => inil
      | (existT a b) :: sigList' => icons b (siglist2ilist sigList')
    end.

  (* and vice versa. *)

  Fixpoint ilist2siglist {As : list A} (il : ilist As) : list (sigT B) :=
    match il with
      | inil => nil
      | icons a As b il' => (existT B a b) :: (ilist2siglist il')
    end.

  (* ilist2siglist is the inverse of siglist2ilist *)
  Lemma siglist2ilist_id
  : forall (sigList : list (sigT B)),
      ilist2siglist (siglist2ilist sigList) = sigList.
  Proof.
    induction sigList; simpl; auto.
    destruct a; simpl; congruence.
  Qed.

  (* and vice-versa. *)

  Fixpoint ilist2siglist_map
          As (il : ilist As)
  : map (@projT1 _ B) (ilist2siglist il) = As :=
    match il as il' in ilist As' return
          map (@projT1 _ B) (ilist2siglist il') = As' with
      | inil => eq_refl
      | icons a As' b il' => f_equal (fun b' => cons a b') (ilist2siglist_map il')
    end.

  Lemma ilist2sislist_map_cons
  : forall a b As (il il' : ilist As),
      match ilist2siglist_map il in (_ = y) return (ilist y -> Prop) with
        | eq_refl =>
          fun il' => siglist2ilist (ilist2siglist il) = il'
      end il'
      ->
      match
        f_equal (fun b' : list A => a :: b') (ilist2siglist_map il) in (_ = y)
        return (ilist y -> Prop)
      with
        | eq_refl =>
          fun il' : ilist (a :: map (projT1 (P:=B)) (ilist2siglist il)) =>
            icons b (siglist2ilist (ilist2siglist il)) = il'
      end (icons b il').
  Proof.
    intros until il; destruct (ilist2siglist_map il); congruence.
  Qed.

  Lemma ilist2siglist_id
  : forall As (il : ilist As),
      match (ilist2siglist_map il) in (_ = y) return
            forall (il' : ilist y), Prop
      with
        | eq_refl => fun il' => siglist2ilist (ilist2siglist il) = il'
      end il.
  Proof.
    induction il; simpl; auto.
    apply ilist2sislist_map_cons; auto.
  Qed.

  (* Looking up the ith value, returning None for indices not in the list *)

  (* A dependent option. *)
  Inductive Dep_Option : option A -> Type :=
    | Dep_Some : forall a, B a -> Dep_Option (Some a)
    | Dep_None : Dep_Option None.

  (* [Dep_Option_elim] projects out the [B a] value from
     a dependent option indexed with [Some a], and returns
     a unit value otherwise. *)
  Definition Dep_Option_elimT (a_opt : option A) : Type :=
    match a_opt with
      | Some a => B a
      | None => unit
    end.
  Definition Dep_Option_elim (a_opt : option A)
            (b_opt : Dep_Option a_opt) :=
    match b_opt in Dep_Option a_opt' return
          Dep_Option_elimT a_opt' with
      | Dep_Some a b => b
      | Dep_None => tt
    end.

  Fixpoint ith_error
          (As : list A)
          (il : ilist As)
          (n : nat)
          {struct n}
  : Dep_Option (nth_error As n) :=
    match n as n' return
          ilist As
          -> Dep_Option (nth_error As n')
    with
      | 0 => match As as As' return
                   ilist As'
                   -> Dep_Option (nth_error As' 0) with
               | nil => fun il => Dep_None
               | cons a As' => fun il => Dep_Some (ilist_hd il)
             end
      | S n => match As as As' return
                     ilist As'
                     -> Dep_Option (nth_error As' (S n)) with
                 | nil => fun il => Dep_None
                 | cons a As' =>
                   fun il =>
                     ith_error (ilist_tl il) n
             end
    end il.

  (* Looking up the ith value, returning a default value
     for indices not in the list. *)
  Fixpoint ith_default
          (default_A : A)
          (default_B : B default_A)
          (As : list A)
          (il : ilist As)
          (n : nat)
  {struct As} : B (nth n As default_A) :=
    match As as As', n as n' return ilist As' -> B (nth n' As' default_A) with
        | a :: As', 0    => @ilist_hd _
        | a :: As', S n' => fun il => ith_default default_B (ilist_tl il) n'
        | nil     , 0    => fun il => default_B
        | nil     , S n' => fun il => default_B
    end il.

  Lemma ilist_invert (As : list A) (il : ilist As) :
    match As as As' return ilist As' -> Prop with
      | a :: As' => fun il => exists b il', il = icons b il'
      | nil => fun il => il = inil
    end il.
  Proof.
    destruct il; eauto.
  Qed.

  (* The [ith_induction] tactic is for working with lookups of bounded indices.
     It first inducts on n, then destructs the index list [As] and eliminates
     the contradictory cases, then finally destructs any indexed list in the
     context with Bounds of [As]. *)

  Ltac icons_invert :=
    repeat match goal with
             | [il : ilist (_ :: _) |- _]
               => let il' := fresh "il" in
                  let b' := fresh "b" in
                  let il'_eq := fresh "il_eq" in
                  generalize (ilist_invert il);
                    intros il'; destruct il' as [b' [il' il'_eq]]; subst
           end.

  Ltac ith_induction n As :=
    induction n; simpl; intros;
    (destruct As; simpl in *;
                  [intros; elimtype False; eapply lt_n_0; eassumption
                  | icons_invert ]).

  Lemma ith_default_In :
    forall (n : nat)
           (As : list A)
           (il : ilist As)
           (default_A : A)
           (default_B : B default_A),
      n < List.length As ->
      ilist_In (ith_default default_B il n) il.
  Proof.
    ith_induction n As; simpl; constructor; eauto with arith.
  Qed.

  Lemma ith_default_indep :
    forall (n : nat)
           (As : list A)
           (il : ilist As)
           (default_A : A)
           (default_B default_B' : B default_A),
      n < List.length As ->
      ith_default default_B il n = ith_default default_B' il n.
  Proof.
    ith_induction n As; simpl; eauto with arith.
  Qed.

End ilist.

(** ** Mapping a function over a(n i)[list], in two non-dependent ways *)
Section ilist_map.
  Context {A} (B : A -> Type).

  Fixpoint imap_list (f : forall a : A, B a) (As : list A) : ilist B As
    := match As with
         | nil => inil _
         | x::xs => @icons _ B x _ (f x) (imap_list f xs)
       end.

  Fixpoint map_ilist {C} (f : forall (a : A), B a -> C) {As} (Bs : ilist B As) : list C
    := match Bs with
         | inil => nil
         | icons _ _ x xs => (f _ x)::map_ilist f xs
       end.
End ilist_map.

Section of_list.
  Context {T : Type}.

  Definition ilist_of_list : forall ls : list T, ilist (fun _ => T) ls := imap_list (fun _ => T) (fun x => x).
  Definition list_of_ilist {T'} {is} (ls : ilist (fun _ : T' => T) is) : list T
    := map_ilist (B := fun _ => T) (fun _ x => x) ls.

  Lemma list_of_ilist_of_list ls : list_of_ilist (ilist_of_list ls) = ls.
  Proof.
    unfold list_of_ilist, ilist_of_list.
    induction ls; simpl in *; f_equal; assumption.
  Qed.
End of_list.


Ltac icons_invert :=
  repeat match goal with
           | [il : ilist _ (_ :: _) |- _]
             => let il' := fresh "il" in
                let b' := fresh "b" in
                let il'_eq := fresh "il_eq" in
                generalize (ilist_invert il);
                  intros il'; destruct il' as [b' [il' il'_eq]]; subst
         end.

Ltac ith_induction n As :=
  induction n; simpl; intros;
  (destruct As; simpl in *;
                [intros; elimtype False; eapply lt_n_0; eassumption
                | icons_invert ]).

Section ilist_imap.

  (* Mapping a function over an indexed list. *)

  Variable A : Type. (* The indexing type. *)
  Variable B B' : A -> Type. (* The two types of indexed elements. *)
  Variable f : forall a, B a -> B' a. (* The function to map over the list. *)

  Fixpoint imap (As : list A)
           (il : ilist B As)
  : ilist B' As :=
    match il in ilist _ As return ilist _ As with
      | icons a As b il' => icons a (f b) (imap il')
      | inil => inil B'
    end.

  (* [imap] behaves as expected with the [ith_default] lookup
     function. *)
  Lemma ith_default_imap :
    forall (n : nat)
           (As : list A)
           (il : ilist _ As)
           (default_A : A)
           (default_B : B default_A),
      f (ith_default default_A default_B il n) =
      ith_default default_A (f default_B) (imap il) n.
  Proof.
    induction n; destruct As; simpl; eauto;
    intros; icons_invert; simpl; auto.
  Qed.

  (* Mapping [f] over a dependent option. *)
  Definition Dep_Option_Map
             (a_opt : option A)
             (b_opt : Dep_Option B a_opt) :
    Dep_Option B' a_opt :=
    match b_opt with
      | Dep_Some a b' => Dep_Some B' a (f b')
      | Dep_None => Dep_None B'
    end.

  (* Applying [f] to the value projected from a dependent option [b_opt]
     is the same as mapping [f] over the [b_opt] and projecting.
   *)
  Lemma Dep_Option_Map_elim
  : forall (a_opt : option A)
           (b_opt : Dep_Option B a_opt),
      Dep_Option_elim (Dep_Option_Map b_opt) =
      match a_opt return
            Dep_Option B a_opt -> Dep_Option_elimT B' a_opt with
        | Some a => fun b => f (Dep_Option_elim b)
        | None => fun _ => tt
      end b_opt.
  Proof.
    unfold Dep_Option_elim, Dep_Option_Map; destruct b_opt; reflexivity.
  Qed.

  (* Concrete values for [a_opt] produce corrolaries of
     [Dep_Option_Map_elim] with nicer statements. *)
  Corollary Dep_Option_Map_elim_Some
  : forall (a : A)
           (b_opt : Dep_Option B (Some a)),
      Dep_Option_elim (Dep_Option_Map b_opt) = f (Dep_Option_elim b_opt).
  Proof.
    intros; eapply Dep_Option_Map_elim; eauto.
  Qed.

  Corollary Dep_Option_Map_elim_None
  : forall (b_opt : Dep_Option B None),
      Dep_Option_elim (Dep_Option_Map b_opt) = tt.
  Proof.
    intros; eapply Dep_Option_Map_elim; eauto.
  Qed.

  (* [imap] behaves as expected with the [ith_error] lookup
     function as well, albeit with a more dependently-typed statement. *)
  Lemma ith_error_imap :
    forall (n : nat)
           (As : list A)
           (il : ilist _ As),
      Dep_Option_Map (ith_error il n) =
      ith_error (imap il) n.
  Proof.
    induction n; destruct As; simpl; eauto;
    intros; icons_invert; simpl; auto.
  Qed.

End ilist_imap.

Section ilist_izip.

  (* Merging two indexed lists together. *)

  Variable A : Type. (* The indexing type. *)
  Variable B B' D : A -> Type. (* The three types of indexed elements. *)
  Variable f : forall a, B a -> B' a -> D a.

  (* The function which merges the two sets of elements. *)
  Fixpoint izip (As : list A)
           (il : ilist B As) (il' : ilist B' As)
  : ilist D As :=
    match As return ilist B As -> ilist B' As -> ilist D As with
      | a :: As' =>
        fun il il' =>
          icons a (f (ilist_hd il) (ilist_hd il'))
                (izip (ilist_tl il) (ilist_tl il'))
      | nil => fun il il' => inil D
    end il il'.

  (* [izip] behaves as expected with the [ith_default] lookup
     function. *)
  Lemma ith_default_izip :
    forall (n : nat)
           (As : list A)
           (il : ilist B As)
           (il' : ilist B' As)
           (default_A : A)
           (default_B : B default_A)
           (default_B' : B' default_A),
      ith_default _ (f default_B default_B') (izip il il') n =
      f (ith_default _ default_B il n) (ith_default _ default_B' il' n).
  Proof.
    induction n; destruct As; simpl; eauto;
    intros; icons_invert; simpl; auto.
  Qed.

  (* Merging two dependent options together. *)
  Definition Dep_Option_Zip
             (a_opt : option A)
             (b_opt : Dep_Option B a_opt)
             (b'_opt : Dep_Option B' a_opt):
    Dep_Option D a_opt :=
    match a_opt return
          Dep_Option B a_opt -> Dep_Option B' a_opt ->
          Dep_Option D a_opt with
      | Some a =>
        fun b b' =>
          Dep_Some D a (f (Dep_Option_elim b) (Dep_Option_elim b'))
      | None => fun _ _ => Dep_None D
    end b_opt b'_opt.

  (* Projecting the combination of two dependent sums [b_opt] and [b'_opt]
     is the same as combining the projections of [b_opt] and [b'_opt]. *)
  Lemma Dep_Option_Zip_elim
  : forall (a_opt : option A)
           (b_opt : Dep_Option B a_opt)
           (b'_opt : Dep_Option B' a_opt),
      Dep_Option_elim (Dep_Option_Zip b_opt b'_opt) =
      match a_opt return
            Dep_Option B a_opt
            -> Dep_Option B' a_opt
            -> Dep_Option_elimT D a_opt with
        | Some a => fun b b' => f (Dep_Option_elim b) (Dep_Option_elim b')
        | None => fun _ _ => tt
      end b_opt b'_opt.
  Proof.
    unfold Dep_Option_elim, Dep_Option_Zip; destruct b_opt; reflexivity.
  Qed.

  (* Concrete values for [a_opt] produce corrolaries of
     [Dep_Option_Zip_elim] with nicer statements. *)
  Corollary Dep_Option_Zip_elim_Some
  : forall (a : A)
           (b_opt : Dep_Option B (Some a))
           (b'_opt : Dep_Option B' (Some a)),
      Dep_Option_elim (Dep_Option_Zip b_opt b'_opt) =
      f (Dep_Option_elim b_opt) (Dep_Option_elim b'_opt).
  Proof.
    intros; eapply Dep_Option_Zip_elim; eauto.
  Qed.

  Corollary Dep_Option_Zip_elim_None
  : forall (b_opt : Dep_Option B None)
           (b'_opt : Dep_Option B' None),
      Dep_Option_elim (Dep_Option_Zip b_opt b'_opt) = tt.
  Proof.
    intros; eapply Dep_Option_Zip_elim; eauto.
  Qed.

  (* [izip] behaves as expected with the [ith_error] lookup
     function as well, albeit with a more dependently-typed statement. *)

  Lemma ith_error_izip :
    forall (n : nat)
           (As : list A)
           (il : ilist B As)
           (il' : ilist B' As),
      ith_error (izip il il') n =
      Dep_Option_Zip (ith_error il n) (ith_error il' n).
  Proof.
    induction n; destruct As; simpl; eauto;
    intros; icons_invert; simpl; auto.
  Qed.

End ilist_izip.

Section ilist_replace.

  (* Replacing an element of an indexed list. *)
  Variable A : Type. (* The indexing type. *)
  Variable B : A -> Type. (* The two types of indexed elements. *)

  Program Fixpoint replace_Index
           {B : A -> Type}
           (n : nat)
           (As : list A)
           (il : ilist B As)
           (new_b : Dep_Option_elimT B (nth_error As n))
           {struct As} : ilist B As :=
    match n return
            ilist B As
            -> Dep_Option_elimT B (nth_error As n)
            -> ilist B As with
      | 0 => match As return
                   ilist B As
                   -> Dep_Option_elimT B (nth_error As 0)
                   -> ilist B As with
               | nil =>
                 fun il _ => inil _
               | cons a Bound' =>
                 fun il new_b =>
                   icons _ new_b (ilist_tl il)
             end
      | S n => match As return
                     ilist B As
                     -> Dep_Option_elimT B (nth_error As (S n))
                     -> ilist B As with
                 | nil => fun il _ => inil _
                 | cons a Bound' =>
                   fun il new_b =>
                     icons _ (ilist_hd il)
                           (@replace_Index B n Bound'
                                           (ilist_tl il) new_b)
               end
    end il new_b.

  Lemma replace_Index_overflow
  : forall
      (n : nat)
      (As : list A)
      (il : ilist _ As)
      (new_b : Dep_Option_elimT B (nth_error As n)),
      List.length As <= n
      -> replace_Index n il new_b = il.
  Proof.
    induction n; simpl;
    (destruct As; intros;
     [generalize (ilist_invert il); intros; subst; reflexivity |
      icons_invert; simpl in *]).
    - destruct (le_Sn_0 _ H).
    - f_equal; auto with arith.
  Qed.

  Definition Dep_Option_elim_P2
             {B B' : A -> Type}
             (P : forall a, B a -> B' a -> Prop)
             (a_opt : option A)
             (b_opt : Dep_Option B a_opt)
             (b'_opt : Dep_Option B' a_opt)
      := match a_opt return
               Dep_Option_elimT B a_opt -> Dep_Option_elimT B' a_opt -> Prop with
           | Some a => P a
           | None => fun _ _ => True
         end (Dep_Option_elim b_opt) (Dep_Option_elim b'_opt).

  Lemma Dep_Option_P2_refl
  : forall n As b,
      @Dep_Option_elim_P2 B _ (fun a b b' => b = b')
                     (nth_error As n) b b.
  Proof.
    intros n As; destruct (nth_error As n); simpl; auto.
  Qed.

  Lemma ith_replace_Index_neq
  : forall
      (n : nat)
      (As : list A)
      (il : ilist _ As)
      (n' : nat)
      (new_b : Dep_Option_elimT B (nth_error As n')),
      n <> n'
      -> Dep_Option_elim_P2
           (fun a b b' => b = b')
           (ith_error (replace_Index n' il new_b) n)
           (ith_error il n).
  Proof.
    unfold Dep_Option_elim_P2.
    induction n; simpl; destruct As; intros; icons_invert;
    simpl in *; auto;
    destruct n'; simpl; try congruence.
    eapply Dep_Option_P2_refl.
    eapply IHn; congruence.
  Qed.

  Lemma ith_replace_Index_eq
  : forall
      (n : nat)
      (As : list A)
      (il : ilist _ As)
      (new_b : Dep_Option B (nth_error As n)),
      Dep_Option_elim_P2
        (fun a b b' => b = b')
        (ith_error (replace_Index n il (Dep_Option_elim new_b)) n)
        new_b.
  Proof.
    unfold Dep_Option_elim_P2.
    induction n; destruct As; simpl; auto; intros; icons_invert.
    apply IHn.
  Qed.

End ilist_replace.

Section findIndex.

  (* Find the index of an element in a list matching a comparator.
     Originally used to look up the element of an ilist using ith_default. *)

  Variable A : Type. (* The indexing type. *)
  Variable C : Type. (* The type of comparators. *)

  Variable AC_eq : A -> C -> bool. (* Comparision between index and comparator types. *)

  Fixpoint findIndex (As : list A) (c : C)
  : nat :=
    match As with
      | a :: As' => if AC_eq a c then 0 else S (findIndex As' c)
      | _ => 0
    end.

  Lemma findIndex_In
  : forall (As : list A) (c : C) (a : A),
      In a As -> AC_eq a c = true ->
      findIndex As c < List.length As.
  Proof.
    induction As; intros; simpl in *; intuition; subst.
    - rewrite H0; auto with arith.
    - find_if_inside; auto with arith.
      generalize (@IHAs c _ H1 H0); auto with arith.
  Qed.

  Local Hint Resolve findIndex_In.

  Lemma findIndex_NIn
  : forall (As : list A) (c : C),
      (forall a, In a As -> AC_eq a c = false) ->
      findIndex As c = List.length As.
  Proof.
    induction As; intros; simpl in *; intuition; subst.
    rewrite H; auto.
  Qed.

  Local Hint Resolve findIndex_NIn.

  Lemma findIndex_In_dec
  : forall (c : C) (As : list A),
      (forall a, In a As -> AC_eq a c = false)
      \/ (exists a, In a As /\ AC_eq a c = true).
  Proof.
    induction As; intros; simpl in *; intuition.
    case_eq (AC_eq a c); intros; eauto.
    left; intros; intuition; subst; eauto.
    destruct_ex; intuition.
    eauto.
  Qed.

  Lemma nth_findIndex_In
  : forall (As : list A) (c : C) (a : A),
      In a As -> AC_eq a c = true ->
      forall a a',
        nth (findIndex As c) As a = nth (findIndex As c) As a'.
  Proof.
    intros; apply nth_indep; eauto.
  Qed.

  Lemma AC_eq_nth_In
  : forall (As : list A) (c : C) (a default_A : A),
      In a As -> AC_eq a c = true ->
      AC_eq (nth (findIndex As c) As default_A) c = true.
  Proof.
    induction As; simpl; intros; intuition;
    case_eq (AC_eq a c); intros; eauto; subst; congruence.
  Qed.

  Lemma AC_eq_nth_NIn
  : forall (As : list A) (c c' : C) (a default_A : A),
      c <> c' ->
      In a As -> AC_eq a c = true ->
      (forall a, AC_eq a c = true -> AC_eq a c' = false) ->
      AC_eq (nth (findIndex As c) As default_A) c' = false.
  Proof.
    induction As; simpl; intros; intuition;
    case_eq (AC_eq a c); intros; eauto; subst; try congruence.
  Qed.

  Lemma nth_findIndex_NIn
  : forall (As : list A) (c : C),
      (forall a, In a As -> AC_eq a c = false) ->
      forall a, nth (findIndex As c) As a = a.
  Proof.
    intros; apply nth_overflow; rewrite findIndex_NIn;
    auto with arith.
  Qed.

  Lemma In_As
        (As : list A)
        (default_A : A)
  : forall (a : A) (c : C),
      List.In a As -> AC_eq a c = true ->
      List.In (nth (findIndex As c) As default_A) As.
  Proof.
    induction As; simpl; intros; destruct H; subst.
    - rewrite H0; auto.
    - case_eq (AC_eq a c); intros; eauto.
  Qed.

  Lemma In_AC_eq
        (AC_eq_c_c' :
           forall a c c',
             AC_eq a c = true
             -> AC_eq a c' = true
             -> c = c')
        (As : list A)
        (default_A : A)
  : forall (a : A) (c c' : C),
      List.In a As
      -> AC_eq a c' = true
      -> AC_eq (nth (findIndex As c') As default_A) c = true
      -> c = c'.
  Proof.
    induction As; simpl; intros; destruct H; subst.
    - case_eq (AC_eq a0 c'); intros; rewrite H in H1; eauto.
      congruence.
    - case_eq (AC_eq a c'); intros; rewrite H2 in H1; eauto.
  Qed.

End findIndex.
