Require Import FunctionalExtensionality List String.
Require Import Lib.CommonTactics Lib.Word Lib.Struct Lib.FnMap.
Require Import Lts.Syntax Lts.Semantics Lts.Refinement Lts.SymEval.

Hint Rewrite @find_empty @complement_empty @complement_nil @find_add_1 : SymEval.
Hint Rewrite @disjUnion_In_1 using (clear; simpl; tauto) : SymEval.
Hint Rewrite @disjUnion_In_2 using (clear; try rewrite withIndex_eq; simpl; intuition discriminate) : SymEval.

Lemma disjUnion_empty : forall A ls, @disjUnion A empty empty ls = empty.
Proof.
  unfold disjUnion; intros.
  extensionality k.
  destruct (in_dec string_dec k ls); auto.
Qed.

Hint Rewrite @disjUnion_empty : SymEval.

(* Ltac SymEval'' H := *)
(*   match type of H with *)
(*   | LtsStep _ ?a _ ?b ?c ?d => *)
(*     pattern a, b, c, d; apply (SymLtsStep_sound H); clear H *)
(*   end. *)

(* Ltac SymEval' := *)
(*   match goal with *)
(*   | [ H : LtsStep _ _ _ _ _ _ |- _ ] => SymEval'' H *)
(*   end. *)

Ltac SymEval_simpl := simpl; intuition idtac; autorewrite with SymEval in *;
                      repeat match goal with
                             | [ H : {| objType := _; objVal := _ |} = {| objType := _; objVal := _ |} |- _ ] => apply typed_eq in H
                             | [ H : (_, _) = (_, _) |- _ ] => inv H
                             | [ H : Some _ = Some _ |- _ ] => inv H
                             | _ => discriminate
                             end.

Ltac SymEval := (* SymEval'; *) SymEval_simpl.

Ltac SymEval_Action H :=
  match type of H with
  | SemAction _ _ ?a ?b ?c =>
    pattern a, b, c; apply (@SymSemAction_sound _ _ _ (fun _ => None) _ _ _ H); clear H;
    SymEval_simpl
  end.
