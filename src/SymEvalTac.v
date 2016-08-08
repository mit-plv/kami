Require Import FunctionalExtensionality List String.
Require Import Lib.CommonTactics Lib.Word Lib.Struct Lib.FMap.
Require Import Lts.Syntax Lts.Semantics Lts.RefinementFacts Lts.SymEval.

Hint Rewrite @M.find_empty @M.find_add_1: SymEval.
Hint Rewrite @M.find_union: SymEval.
Hint Rewrite @M.union_empty_L @M.union_empty_R: SymEval.

Ltac SymEval'' H :=
  match type of H with
    | SemAction ?rs ?a ?rs' ?cs ?rv =>
      pattern rs', cs, rv; apply (SymSemAction_sound H); clear H
  end.

Ltac SymEval' :=
  match goal with
  | [ H : SemAction _ _ _ _ _ |- _ ] => SymEval'' H
  end.

Set Implicit Arguments.
Theorem sigT_eq: forall A (P: A -> Type) a v1 v2, existT P a v1 = existT P a v2 -> v1 = v2.
Proof.
  intros.
  destruct_existT.
  reflexivity.
Qed.

Lemma invSome: forall t (a b: t), Some a = Some b -> a = b.
Proof.
  intros t a b cond; subst; inv cond; reflexivity.
Qed.

Ltac SymEval_simpl :=
  simpl; intuition idtac; autorewrite with SymEval in *;
  repeat match goal with
           | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply sigT_eq in H
           | [ H : (_, _) = (_, _) |- _ ] => inv H
           | [ H : Some _ = Some _ |- _ ] => apply invSome in H
           | _ => discriminate
         end.

Ltac SymEval := SymEval'; SymEval_simpl.
