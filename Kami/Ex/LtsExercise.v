Require Import LtsTutorial.

(* This set of exercises deals with the tiny language we defined with a labeled
 * transition system.  It is probably a good idea to use the tactics
 * demonstrated in the imported file. *)


(** * Some straightforward warm-up exercises *)

(** * Commutativity *)

Theorem refines_comm : forall p1 p2,
    refines (Par p1 p2) (Par p2 p1).
Proof.
Admitted.

(** * Associativity *)

Theorem refines_assoc : forall p1 p2 p3,
    refines (Par p1 (Par p2 p3)) (Par (Par p1 p2) p3).
Proof.
Admitted.

(** * Garbage-collecting processes that will never find rendezvous partners *)

Theorem dead_send : forall ch v p,
    refines (HideChannel ch (Send ch v p)) Done.
Proof.
Admitted.

Theorem dead_recv : forall ch p,
    refines (HideChannel ch (Recv ch p)) Done.
Proof.
Admitted.

(** * Removing inert processes from parallel composition *)

Theorem Done_left : forall p,
    refines (Par Done p) p.
Proof.
Admitted.

Theorem Done_right : forall p,
    refines (Par p Done) p.
Proof.
Admitted.


(** * One-step unrolling of duplication *)

(* Our proof of this one requires a little more thought, with a good choice of
 * lemma. *)

Theorem unroll_Dup : forall p,
    refines (Dup p) (Par p (Dup p)).
Proof.
Admitted.


(** * Dropping useless hiding *)

(* Here is a simple, conservative, syntactic predicate, which ensures that a
 * process can never use a particular channel.  Fun bonus exercise (not checked
 * in Coq): when could this predicate falsely declare that a subprocess of a
 * larger process might use a channel, when we can actually prove that it
 * couldn't happen? *)
Inductive ignoresChannel (ch : nat) : proc -> Prop :=
| IgnDone : ignoresChannel ch Done
| IgnSend : forall ch' v p,
    ch' <> ch
    -> ignoresChannel ch p
    -> ignoresChannel ch (Send ch' v p)
| IgnRecv : forall ch' p,
    ch' <> ch
    -> (forall v, ignoresChannel ch (p v))
    -> ignoresChannel ch (Recv ch' p)
| IgnDup : forall p,
    ignoresChannel ch p
    -> ignoresChannel ch (Dup p)
| IgnPar : forall p1 p2,
    ignoresChannel ch p1
    -> ignoresChannel ch p2
    -> ignoresChannel ch (Par p1 p2)
| IgnHideSame : forall p,
    ignoresChannel ch (HideChannel ch p)
| IgnHideDiff : forall ch' p,
    ignoresChannel ch p
    -> ignoresChannel ch (HideChannel ch' p).

Hint Constructors ignoresChannel.

(* Here is a related theorem, which we prove using a general lemma about
 * [ignoresChannel]. *)
Theorem drop_hiding : forall ch p,
    ignoresChannel ch p
    -> refines (HideChannel ch p) p.
Proof.
Admitted.


(** * One-shot interaction with a server that is ready for more interactions *)

(* Warning: this one was considerably more work for us to prove than were any of
 * the previous exercises!  Expect to choose several lemmas and probably at
 * least one auxiliary definition, beyond just the simulation relation. *)
Theorem oneshot : forall ch v p1 p2,
      ignoresChannel ch p1
      -> (forall v, ignoresChannel ch (p2 v))
      -> refines (HideChannel ch (Par (Send ch v p1) (Dup (Recv ch p2))))
                 (Par p1 (p2 v)).
Proof.
Admitted.


(** * Calling the add3 server once *)

(* Let's bring together some of those results to prove a simple refinement
 * without needing to define any new simulation relations. *)

Definition five_the_hard_way :=
  HideChannel 0 (Par (Send 0 2 Done) (Dup addThree)).

Definition five_the_easy_way :=
  Send 1 5 Done.

Theorem five_the_hard_way_ok :
  refines five_the_hard_way five_the_easy_way.
Proof.
Admitted.
