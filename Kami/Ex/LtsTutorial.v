Require Import Arith.


(** Syntax and semantics of processes *)

Inductive proc :=
| Done
| Send (ch v : nat) (p : proc)
| Recv (ch : nat) (p : nat -> proc)
| Dup (p : proc)
| Par (p1 p2 : proc)
| HideChannel (ch : nat) (p : proc).

Inductive action := Out | In.

Definition label : Type := option (action * nat * nat).

Definition channelOf (l : label) :=
  match l with
  | None => None
  | Some (_, ch, _) => Some ch
  end.

Inductive step : proc -> label -> proc -> Prop :=
| StepSend : forall ch v p,
    step (Send ch v p) (Some (Out, ch, v)) p
| StepRecv : forall ch v p,
    step (Recv ch p) (Some (In, ch, v)) (p v)
| StepDup : forall p,
    step (Dup p) None (Par p (Dup p))
| StepSendRecv : forall p1 p2 ch v p1' p2',
    step p1 (Some (Out, ch, v)) p1'
    -> step p2 (Some (In, ch, v)) p2'
    -> step (Par p1 p2) None (Par p1' p2')
| StepRecvSend : forall p1 p2 ch v p1' p2',
    step p1 (Some (In, ch, v)) p1'
    -> step p2 (Some (Out, ch, v)) p2'
    -> step (Par p1 p2) None (Par p1' p2')
| StepPar1 : forall p1 p2 l p1',
    step p1 l p1'
    -> step (Par p1 p2) l (Par p1' p2)
| StepPar2 : forall p1 p2 l p2',
    step p2 l p2'
    -> step (Par p1 p2) l (Par p1 p2')
| StepHide : forall ch p l p',
    step p l p'
    -> channelOf l <> Some ch
    -> step (HideChannel ch p) l (HideChannel ch p').

Hint Constructors step.

Definition good_simulation (R : proc -> proc -> Prop) :=
  forall p1 p2,
    R p1 p2
    -> forall l p1',
      step p1 l p1'
      -> (l = None
          /\ R p1' p2)
         \/ (exists p2',
                step p2 l p2'
                /\ R p1' p2').
                   
Definition refines (p1 p2 : proc) :=
  exists R, good_simulation R
            /\ R p1 p2.

Ltac refines R :=
  intros; exists R; unfold good_simulation in *; firstorder subst; eauto.

Theorem refines_refl : forall p,
    refines p p.
Proof.
  refines (@eq proc).
Qed.

Theorem refines_trans : forall p1 p2 p3,
    refines p1 p2
    -> refines p2 p3
    -> refines p1 p3.
Proof.
  destruct 1 as [R1], 1 as [R2].
  refines (fun x y => exists z, R1 x z /\ R2 z y).
  eapply H in H4; eauto; firstorder.
  eapply H0 in H4; eauto; firstorder.
Qed.

Ltac invert H := inversion H; clear H; subst; simpl in *.

Ltac inv :=
  match goal with
  | [ H : step _ _ _ |- _ ] => invert H
  end.

Ltac invertomatic :=
  inv;
    repeat match goal with
           | [ H1 : forall p1 p2, ?R p1 p2 -> _, _ : ?R ?a _, H2 : step ?a _ _ |- _ ] =>
             eapply H1 in H2; eauto
           end; firstorder (try discriminate); eauto 6.


(** * Example: adding three *)

Definition addThree :=
  Recv 0 (fun n => Send 1 (n + 3) Done).

Definition addOne :=
  Recv 0 (fun n => Send 2 (n + 1) Done).

Definition addTwo :=
  Recv 2 (fun n => Send 1 (n + 2) Done).

Definition addOneThenTwo :=
  HideChannel 2 (Par addOne addTwo).

Inductive Radder : proc -> proc -> Prop :=
| Ra0 : Radder addOneThenTwo addThree
| Ra1 : forall n, Radder (HideChannel 2 (Par (Send 2 (n + 1) Done) addTwo)) (Send 1 (n + 3) Done)
| Ra2 : forall n, Radder (HideChannel 2 (Par Done (Send 1 (n + 1 + 2) Done))) (Send 1 (n + 3) Done)
| Ra3 : Radder (HideChannel 2 (Par Done Done)) Done.

Hint Constructors Radder.

Theorem addOneThenTwo_ok :
  refines addOneThenTwo addThree.
Proof.
  refines Radder.
  invert H; repeat inv; intuition (try congruence); unfold addThree; eauto.
  rewrite <- plus_assoc; eauto.
Qed.


(** * The crucial composition theorem *)

Inductive Rpar (R1 R2 : proc -> proc -> Prop) : proc -> proc -> Prop :=
| Rp : forall p1 p1' p2 p2',
    R1 p1 p1'
    -> R2 p2 p2'
    -> Rpar R1 R2 (Par p1 p2) (Par p1' p2').

Hint Constructors Rpar.

Theorem refines_Par : forall p1 p2 p1' p2',
    refines p1 p1'
    -> refines p2 p2'
    -> refines (Par p1 p2) (Par p1' p2').
Proof.
  destruct 1 as [R1]; destruct 1 as [R2].
  refines (Rpar R1 R2).

  invert H3.
  invertomatic.
Qed.

(** * Refinement and hiding *)

Inductive Rhide ch (R : proc -> proc -> Prop) : proc -> proc -> Prop :=
| Rh : forall p p',
    R p p'
    -> Rhide ch R (HideChannel ch p) (HideChannel ch p').

Hint Constructors Rhide.

Theorem refines_HideChannel : forall ch p p',
    refines p p'
    -> refines (HideChannel ch p) (HideChannel ch p').
Proof.
  destruct 1 as [R].
  refines (Rhide ch R).

  invert H1.
  invertomatic.
Qed.

(** ** ...applied to a simple concrete example *)

Definition addSeven :=
  Recv 1 (fun n => Send 3 (n + 7) Done).
Definition addTen :=
  Recv 0 (fun n => Send 3 (n + 10) Done).
Definition addThreeThenSeven :=
  HideChannel 1 (Par addThree addSeven).

Inductive Radder' : proc -> proc -> Prop :=
| Ra'0 : Radder' (HideChannel 1 (Par addThree addSeven)) addTen
| Ra'1 : forall n, Radder' (HideChannel 1 (Par (Send 1 (n + 3) Done) addSeven)) (Send 3 (n + 10) Done)
| Ra'2 : forall n, Radder' (HideChannel 1 (Par Done (Send 3 (n + 3 + 7) Done))) (Send 3 (n + 10) Done)
| Ra'3 : Radder' (HideChannel 1 (Par Done Done)) Done.

Hint Constructors Radder'.

Lemma addThreeThenSeven_ok' :
  refines addThreeThenSeven addTen.
Proof.
  refines Radder'.
  invert H; repeat inv; intuition (try congruence); unfold addTen; eauto.
  rewrite <- plus_assoc; eauto.
Qed.

Theorem addThreeThenSeven_ok :
  refines (HideChannel 1 (Par addOneThenTwo addSeven)) addTen.
Proof.
  eapply refines_trans.
  apply refines_HideChannel.
  apply refines_Par.
  apply addOneThenTwo_ok.
  apply refines_refl.
  apply addThreeThenSeven_ok'.
Qed.


(** * Refinement and duplication *)

Inductive Rdup (R : proc -> proc -> Prop) : proc -> proc -> Prop :=
| RdNil : forall p p',
    R p p'
    -> Rdup R (Dup p) (Dup p')
| RdCons : forall p1 p1' p2 p2',
    R p1 p1'
    -> Rdup R p2 p2'
    -> Rdup R (Par p1 p2) (Par p1' p2').

Hint Constructors Rdup.

Lemma refines_Dup' : forall R : proc -> proc -> Prop,
  (forall p1 p2,
      R p1 p2
        -> forall l p1',
        step p1 l p1'
        -> (l = None /\ R p1' p2) \/ (exists p2', step p2 l p2' /\ R p1' p2'))
  -> forall p1 p2, Rdup R p1 p2
  -> forall l p1', step p1 l p1'
                   -> (l = None /\ Rdup R p1' p2)
                      \/ (exists p2', step p2 l p2' /\ Rdup R p1' p2').
Proof.
  induction 2; intros; invertomatic.
Qed.

Theorem refines_Dup : forall p p',
    refines p p'
    -> refines (Dup p) (Dup p').
Proof.
  destruct 1 as [R].
  refines (Rdup R).
  eauto using refines_Dup'.
Qed.

(** ** ...applied to the earlier concrete example *)

Theorem many_addThreeThenSeven_ok :
  refines (Dup (HideChannel 1 (Par addOneThenTwo addSeven))) (Dup addTen).
Proof.
  apply refines_Dup.
  apply addThreeThenSeven_ok.
Qed.
