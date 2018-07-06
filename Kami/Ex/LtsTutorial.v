Inductive proc :=
| Done
| Send (ch v : nat) (p : proc)
| Recv (ch : nat) (p : nat -> proc)
| Dup (p : proc)
| Par (p1 p2 : proc).

Inductive action := Out | In.

Definition label : Type := option (action * nat * nat).

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
    -> step (Par p1 p2) l (Par p1 p2').

Hint Constructors step.

Definition good_simulation (R : proc -> proc -> Prop) :=
  forall p1 p2,
    R p1 p2
    -> forall l p1',
      step p1 l p1'
      -> exists p2',
        step p2 l p2'
        /\ R p1' p2'.
                   
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
