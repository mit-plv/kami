Require Import Coq.Program.Basics.

Lemma rmConj (P Q R: Prop): iff (P /\ Q -> R) (P -> Q -> R).
Proof.
  unfold impl; tauto.
Qed.

Lemma rmDisj (P Q R: Prop): iff (P \/ Q -> R) ((P -> R) /\ (Q -> R)).
Proof.
  unfold impl; tauto.
Qed.

Lemma dupConj (P Q R: Prop): iff (P -> (Q /\ R)) ((P -> Q) /\ (P -> R)).
Proof.
  unfold impl; tauto.
Qed.

Lemma bool_true a: iff (a = true -> False) (a = false).
Proof.
  destruct a; intuition discriminate.
Qed.

Lemma bool_false a: iff (a = false -> False) (a = true).
Proof.
  destruct a; intuition discriminate.
Qed.

Lemma quantConj A (P Q: A -> Prop): iff (forall a, P a /\ Q a) ((forall a, P a) /\ (forall a, Q a)).
Proof.
  split; intros; firstorder fail.
Qed.

#[global] Hint Rewrite rmConj rmDisj dupConj bool_true bool_false quantConj: basicLogic.


