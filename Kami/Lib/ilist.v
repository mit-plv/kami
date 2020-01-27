Generalizable All Variables.
Set Implicit Arguments.

Set Asymmetric Patterns.

Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Arith.Arith Program.Equality.
Require Export Lib.VectorFacts.
Require Coq.Vectors.Vector.

Set Universe Polymorphism.
Section ilist.

  (* Lists of elements whose types depend on an indexing set (CPDT's hlists).
     These lists are a convenient way to implement finite maps
     whose elements depend on their keys. The data structures used
     by our ADT notations uses these to implement notation-friendly
     method lookups.  *)

  Import Vector.VectorNotations.

  Variable A : Type. (* The indexing type. *)
  Variable B : A -> Type. (* The type of indexed elements. *)

  Inductive ilist: forall n, Vector.t A n -> Type :=
  | inil: ilist (Vector.nil A)
  | icons t n (vs: Vector.t A n) (v: B t) (ils: ilist vs): ilist (t :: vs).

  Definition ilist_hd {n} {As : Vector.t A n} (il : ilist As) :
    match As return ilist As -> Type with
      | a :: As' => fun il => B a
      | [] => fun _ => unit
    end il :=
    match As return
          forall (il : ilist As),
            match As return ilist As -> Type with
              | a :: As' => fun il => B a
              | [] => fun _ => unit
            end il with
      | a :: As => fun il => match il in ilist (a :: As) return B a with
                                          | icons t n' vs v ils => v
                                          | inil => idProp
                                        end
      | [] => fun il => tt
    end il.

  Definition ilist_hd' {n} {As : Vector.t A (S n)} (il : ilist As) :
    B (Vector.hd As)
    := Vector.caseS (fun n As => ilist As -> B (Vector.hd As))
                           (fun a As m => ilist_hd) As il.

  (* Get the cdr of an ilist. *)
  Definition ilist_tl {n} {As : Vector.t A n} (il : ilist As) :
    match As return ilist As -> Type with
      | a :: As' => fun il => ilist As'
      | [] => fun _ => unit
    end il :=
    match As return
          forall (il : ilist As),
            match As return ilist As -> Type with
              | Vector.cons a _ As' => fun il => ilist As'
              | Vector.nil => fun _ => unit
            end il with
      | a :: As => fun il => match il in ilist (a :: As) return ilist As with
                               | icons t n' vs v ils => ils
                               | inil => idProp
                             end
      | [] => fun il => tt
    end il.

  Definition ilist_tl'
             {n} {As : Vector.t A (S n)} (il : ilist As)
    : ilist (Vector.tl As) :=
    Vector.caseS (fun n As => ilist As -> ilist (Vector.tl As))
                 (fun a As m => ilist_tl) As il.


    
  Fixpoint ith
             {m : nat}
             {As : Vector.t A m}
             (il : ilist As)
             (n : Fin.t m)
  : B (Vector.nth As n) :=
    match n in Fin.t m return
          forall (As : Vector.t A m),
            ilist As
            -> B (Vector.nth As n) with
      | Fin.F1 k =>
        fun As =>
          Vector.caseS (fun n As => ilist As
                                    -> B (Vector.nth As (@Fin.F1 n)))
                       (fun h n t => ilist_hd) As
      | Fin.FS k n' =>
        fun As =>
          Vector_caseS' Fin.t
                        (fun n As n' => ilist As
                                        -> B (Vector.nth As (@Fin.FS n n')))
                        (fun h n t m il => ith (ilist_tl il) m)
                        As n'
    end As il.


  Lemma ilist_invert {n} (As : Vector.t A n) (il : ilist As) :
    match As as As' return ilist As' -> Prop with
      | a :: As' => fun il => exists b il', il = icons b il'
      | [] => fun il => il = inil
    end il.
  Proof.
    destruct As; dependent destruction il; simpl; eauto.
  Qed.

  Lemma ilist_invert' {n} (As : Vector.t A n) (il : ilist As) :
    match As as As' return ilist As' -> Type with
      | a :: As' => fun il => sigT (fun b => sigT (fun il' => il = icons b il'))
      | [] => fun il => il = inil
    end il.
  Proof.
    destruct As; dependent destruction il; eauto.
  Qed.

  (* The [ith_induction] tactic is for working with lookups of bounded indices.
     It first inducts on n, then destructs the index Vector.t [As] and eliminates
     the contradictory cases, then finally destructs any indexed Vector.t in the
     context with Bounds of [As]. *)

End ilist.

(** ** Mapping a function over a(n i)[list], in two non-dependent ways *)
Section ilist_map.
  Context {A} (B : A -> Type).

  Import Vector.VectorNotations.

  Fixpoint imap_list (f : forall a : A, B a) {n} (As : Vector.t A n) : ilist _ As
    := match As with
         | [] => inil _
         | x :: xs => @icons _ B x _ _ (f x) (imap_list f xs)
       end.

End ilist_map.

Ltac icons_invert :=
  repeat match goal with
           | [il : ilist _ (_ :: _) |- _]
             => let il' := fresh "il" in
                let b' := fresh "b" in
                let il'_eq := fresh "il_eq" in
                generalize (ilist_invert il);
                  intros il'; destruct il' as [b' [il' il'_eq]]; subst
         end.

Section ilist_imap.

  (* Mapping a function over an indexed Vector.t. *)

  Import Vector.VectorNotations.

  Variable A : Type. (* The indexing type. *)
  Variable B B' : A -> Type. (* The two types of indexed elements. *)
  Variable f : forall a, B a -> B' a. (* The function to map over the Vector.t. *)

  Fixpoint imap {n} (As : Vector.t A n)
    : ilist _ As -> ilist _ As :=
    match As return ilist _ As -> ilist _ As with
    | [] => fun il => inil _
    | a :: As' => fun il => icons _ (@f a (ilist_hd il)) (@imap _ As' (ilist_tl il))
    end.

  (* [imap] behaves as expected with the [ith_default] lookup
     function. *)
  Lemma ith_imap :
    forall {n}
           (m : Fin.t n)
           (As : Vector.t A n)
           (il : ilist _ As),
      f (ith il m) = ith (imap il) m.
  Proof.
    induction m; intro.
    - eapply Vector.caseS with (v := As); intros; simpl in *; dependent destruction il; reflexivity.
    - revert m IHm.
      pattern n, As.
      match goal with
        |- ?P n As =>
        simpl; eapply (@Vector.rectS _ P); intros
      end.
      inversion m.
      eapply IHm.
  Qed.

End ilist_imap.

Section ilist_replace.

  Import Vector.VectorNotations.

  (* Replacing an element of an indexed Vector.t. *)
  Context {A : Type}. (* The indexing type. *)
  Context {B : A -> Type}. (* The two types of indexed elements. *)

  Fixpoint replace_Index
             {m}
             (As : Vector.t A m)
             (il : ilist B As)
             (n : Fin.t m)
             (new_b : B (Vector.nth As n))
             {struct n}
    : ilist _ As :=
    match n in Fin.t m return
          forall (As : Vector.t A m),
            ilist _ As
            -> B (Vector.nth As n)
            -> ilist _ As with
    | Fin.F1 k =>
      fun As =>
        Vector.caseS (fun n As => ilist _ As
                                  -> B (Vector.nth As (@Fin.F1 n))
                                  -> ilist _ As)
                     (fun h n t il new_b => icons _ new_b (ilist_tl il) ) As
    | Fin.FS k n' =>
      fun As =>
        Vector_caseS' Fin.t
                     (fun n As n' =>
                          ilist _ As
                          -> B (Vector.nth As (@Fin.FS n n'))
                          -> ilist _ As)
                     (fun h n t m il new_b => icons _ (ilist_hd il)
                                                    (@replace_Index _ _ (ilist_tl il) _ new_b))
                     As n'
    end As il new_b.

  Lemma ith_replace_Index_neq {m}
    : forall
      (n n' : Fin.t m)
      (As : Vector.t A m)
      (il : ilist _ As)
      (new_b : B (Vector.nth As n')),
      n <> n'
      -> ith (replace_Index il n' new_b) n = ith il n.
  Proof.
    intros n n'; pattern m, n, n'.
    match goal with
      |- ?P m n n' => simpl; eapply (Fin.rect2 P); intros
    end.
    - congruence.
    - generalize il f new_b; clear f new_b il H.
      pattern n0, As.
      match goal with
        |- ?P n0 As =>
        simpl; apply (@Vector.rectS _ P); intros; reflexivity
      end.
    - generalize il f new_b; clear f new_b il H.
      pattern n0, As.
      match goal with
        |- ?P n0 As =>
        simpl; apply (@Vector.rectS _ P); intros; reflexivity
      end.
    - assert (f <> g) by congruence.
      generalize il f g new_b H H1; clear f g new_b il H H1 H0.
      pattern n0, As.
      match goal with
        |- ?P n0 As =>
        simpl; apply (@Vector.caseS _ P); intros;
        dependent destruction il;
        eapply (H _ il new_b); eauto
      end.
  Qed.

  Lemma ith_replace_Index_eq {m}
    : forall
      (n : Fin.t m)
      (As : Vector.t A m)
      (il : ilist _ As)
      (new_b : B (Vector.nth As n)),
      ith (replace_Index il n new_b) n = new_b.
  Proof.
    induction n; simpl.
    - intro As; pattern n, As.
      match goal with
        |- ?P n As =>
        simpl; apply (@Vector.caseS _ P); intros; reflexivity
      end.
    - intro As; revert n0 IHn; pattern n, As.
      match goal with
        |- ?P n As =>
        simpl; apply (@Vector.caseS _ P); simpl; eauto
      end.
  Qed.

End ilist_replace.

Section ListToFunction.
  Variable A: Type.
  Variable B: A -> Type.

  Definition ilist_to_fun :=
    fix ilist_to_fun n (vs : Vector.t A n) (ils : ilist (fun a : A => B a) vs)
        {struct ils} :
      forall i : Fin.t n, Vector.nth (Vector.map (fun p : A => B p) vs) i :=
    match
      vs in Vector.t _ k return (ilist (fun a : A => B a) vs ->
                                 forall i : Fin.t k, Vector.nth (Vector.map (fun p : A => B p) vs) i)
    with
      | Vector.nil => fun _ i0 => Fin.case0 (Vector.nth (Vector.map (fun p : A => B p) (Vector.nil A))) i0
      | Vector.cons a1 n1 vs1 =>
        fun ils1 i1 =>
          match ils1 in ilist _ (Vector.cons a n2 vs2) return
                forall i2, Vector.nth (Vector.map (fun p: A => B p) (Vector.cons A a n2 vs2)) i2 with
            | icons t3 n3 vs3 b ils3 =>
              fun k =>
                match k in Fin.t (S n4)
                      return forall vs4 : Vector.t A n4,
                               (forall i : Fin.t n4, Vector.nth (Vector.map (fun p : A => B p) vs4) i) ->
                               Vector.nth (Vector.map (fun p : A => B p) (Vector.cons A t3 n4 vs4)) k with
                  | Fin.F1 s5 => fun _ _ => b
                  | Fin.FS s5 f5 => fun vs5 f => f f5
                end vs3 (ilist_to_fun n3 vs3 ils3)
          end i1
    end ils.
End ListToFunction.

Section ListToFunctionFun.
  Variable A B: Type.
  Variable f g: A -> Type.
  Variable b_a: B -> A.

  Definition ilist_to_fun_m (m: forall (k: A), f k -> g k) :=
    (fix help n (vs : Vector.t (B) n) (ils : ilist (fun a => f (b_a a)) vs)
         {struct ils} :
       forall i : Fin.t n, Vector.nth (Vector.map (fun p => g (b_a p)) vs) i :=
       match
         vs in Vector.t _ k return (ilist (fun a => f (b_a a)) vs ->
                                    forall i : Fin.t k, Vector.nth (Vector.map (fun p => g (b_a p)) vs) i)
       with
         | Vector.nil => fun _ i0 => Fin.case0 (Vector.nth (Vector.map (fun p => g (b_a p)) (Vector.nil _))) i0
         | Vector.cons a1 n1 vs1 =>
           fun ils1 i1 =>
             match ils1 in ilist _ (Vector.cons a n2 vs2) return
                   forall i2, Vector.nth (Vector.map (fun p => g (b_a p)) (Vector.cons _ a n2 vs2)) i2 with
               | icons t3 n3 vs3 b ils3 =>
                 fun k =>
                   match k in Fin.t (S n4)
                         return forall vs4 : Vector.t _ n4,
                                  (forall i : Fin.t n4, Vector.nth (Vector.map (fun p => g (b_a p)) vs4) i) ->
                                  Vector.nth (Vector.map (fun p => g (b_a p)) (Vector.cons _ t3 n4 vs4)) k with
                     | Fin.F1 s5 => fun _ _ => (@m _ b)
                     | Fin.FS s5 f5 => fun vs5 f => f f5
                   end vs3 (help n3 vs3 ils3)
             end i1
       end ils).
End ListToFunctionFun.
Unset Universe Polymorphism.

