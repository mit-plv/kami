Require Import Bool Ascii String List Eqdep.
Require Import Logic.FunctionalExtensionality.

Ltac isNew P :=
  match goal with
    | [ _: ?P' |- _] => assert (P = P') by reflexivity; fail 1
    | _ => idtac
  end.

Ltac sassumption :=
  match goal with
    | [H: ?P' |- ?P] =>
      progress replace P with P' by reflexivity; assumption
  end.

Ltac ind H := induction H; simpl; intros; subst.
Ltac inv H := inversion H; subst; clear H.

Ltac p_equal H := apply (eq_ind _ (@id _) H); f_equal.

Lemma opt_discr: forall {A} v, Some v <> (@None A).
Proof. discriminate. Qed.

Lemma discr_var: forall s s1 s2: string, s1 <> s2 -> (append s s1) <> (append s s2).
Proof.
  intros; intro X; elim H; clear H; induction s; [assumption|].
  apply IHs; inv X; reflexivity.
Qed.

Ltac vdiscriminate :=
  repeat
    match goal with
      | [H: _ = _ |- _] =>
        try (simpl in H;
             (discriminate || apply discr_var in H; auto))
    end.

Ltac exact_refl :=
  match goal with
    | [ |- ?t = ?t ] => reflexivity
  end.

Ltac find_if_inside :=
  match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
    | [ H : context[if ?X then _ else _] |- _ ]=> destruct X
  end.

Ltac solve_eq :=
  repeat
    match goal with
      | [ |- Some _ = Some _ ] => f_equal; try (simpl; reflexivity)
      | [ |- (_, _) = (_, _) ] => f_equal; auto
      | [ |- (fun _ => _) = (fun _ => _) ] =>
        (first [apply functional_extensionality |
                apply functional_extensionality_dep]; intros)
      | [ |- (if ?eqd then _ else _) = (if ?eqd then _ else _) ] =>
        find_if_inside; auto
      | [ |- (if ?eqd ?ll ?lr then _ else _) =
             (if ?eqd ?rl ?rr then _ else _) ] =>
        (replace ll with rl by auto; replace lr with rr by auto)
    end.

Ltac destruct_ex :=
  repeat match goal with
           | [ H : ex _ |- _ ] => destruct H
         end.

Ltac dest :=
  repeat (match goal with
            | H: _ /\ _ |- _ => destruct H
            | H: exists _, _ |- _ => destruct H
          end).

Ltac dest_in :=
  repeat
    match goal with
    | [H: In _ _ |- _] => inv H
    end.

Ltac destruct_option :=
  repeat
    match goal with
      | [H: Some _ = Some _ |- _] => inversion H; subst; clear H
      | [H: Some _ = None |- _] => inversion H
      | [H: None = Some _ |- _] => inversion H
      | [H: None = None |- _] => clear H
    end.

Ltac destruct_eq :=
  repeat
    match goal with
      | [H: context[eq_rect_r _ _ _] |- _] =>
        unfold eq_rect_r, eq_rect in H
      | [ |- context [eq_rect_r _ _ _] ] =>
        unfold eq_rect_r, eq_rect
      | [H: context [match ?c with | eq_refl => _ end] |- _] =>
        (destruct c in H)
          || (rewrite (UIP_refl _ _ c) in H)
          || (let Hii := fresh "Hii" in
              assert (Hii: c = eq_refl) by apply UIP; rewrite Hii in H; clear Hii)
      | [ |- context [match ?c with | eq_refl => _ end] ] =>
        (destruct c)
          || (rewrite (UIP_refl _ _ c))
          || (let Hii := fresh "Hii" in
              assert (Hii: c = eq_refl) by apply UIP; rewrite Hii; clear Hii)
    end.

Ltac destruct_existT :=
  repeat match goal with
           | [H: existT _ _ _ = existT _ _ _ |- _] =>
             (apply Eqdep.EqdepTheory.inj_pair2 in H; subst)
         end.

Notation "'nosimpl' t" := (match tt with tt => t end) (at level 10).

Notation Yes := (left _).
Notation "e1 ;; e2" := (if e1 then e2 else right _) (right associativity, at level 60).

Fixpoint string_of_nat (n: nat) :=
  match n with
    | O => "a"%string
    | S n' => append "a"%string (string_of_nat n')
  end.

Definition indexSymbol: string := "__"%string.

Definition withIndex str idx := 
  append (append (string_of_nat idx) indexSymbol) str.

Theorem withIndex_eq : withIndex = fun str idx =>
  append (append (string_of_nat idx) indexSymbol) str.
Proof.
  reflexivity.
Qed.

Global Opaque withIndex.

Notation "str '__' idx" := (withIndex str idx) (at level 0).

Axiom cheat: forall t, t.

Hint Extern 1 (_ /\ _) => repeat split.
Hint Extern 1 (NoDup _) => (repeat constructor; simpl; intro; intuition auto; discriminate).

