Require Import Bool List String Structures.Equalities.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.StringBound Lib.ilist Lib.FMap Syntax Semantics.
Require Import FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.

Set Implicit Arguments.

Notation "m [ k |--> v ]" := (M.add k v m) (at level 0).
Notation "m [ k |-> v ]" := (m [k |--> {| objVal := v |}]) (at level 0).
Notation "v === m .[ k ]" := (M.find k m = Some {| objVal := v |}) (at level 70).
Notation "_=== m .[ k ]" := (M.find k m = None) (at level 70).

Notation "m ~{ k |-> v }" := ((fun a => if weq a k then v else m a) : type (Vector (Bit _) _)) (at level 0).

Fixpoint SymSemAction k (a : ActionT type k) (rs rsNotWritable rs' : RegsT) (cs : CallsT) (kf : RegsT -> CallsT -> type k -> Prop) : Prop :=
  match a with
  | MCall meth s marg cont =>
    forall mret,
      M.find meth cs = None
      /\ SymSemAction (cont mret) rs rsNotWritable rs' cs[meth |-> (evalExpr marg, mret)] kf
  | Let_ _ e cont =>
    SymSemAction (cont (evalExpr e)) rs rsNotWritable rs' cs kf
  | ReadReg r _ cont =>
    exists regV,
      regV === rs.[r]
      /\ SymSemAction (cont regV) rs rsNotWritable rs' cs kf
  | WriteReg r _ e cont =>
    match M.find r rsNotWritable with
    | Some _ => True
    | None =>
      match M.find r rs' with
      | None => SymSemAction cont rs rsNotWritable rs'[r |-> evalExpr e] cs kf
      | Some _ => False
      end
    end
  | IfElse p _ a a' cont =>
    if evalExpr p
    then SymSemAction a rs rsNotWritable rs' cs (fun rs'' cs' rv =>
                                                   SymSemAction (cont rv) rs rsNotWritable rs'' cs' kf)
    else SymSemAction a' rs rsNotWritable rs' cs (fun rs'' cs' rv =>
                                                    SymSemAction (cont rv) rs rsNotWritable rs'' cs' kf)
  | Assert_ p cont =>
    evalExpr p = true
    -> SymSemAction cont rs rsNotWritable rs' cs kf
                                 
  | Return e => kf rs' cs (evalExpr e)
  end.

Lemma double_find : forall T (v1 v2 : fullType type T) m k,
  v1 === m.[k]
  -> v2 === m.[k]
  -> v1 = v2.
Proof.
  intros.
  rewrite H in H0.
  injection H0; intro.
  apply inj_pair2 in H1.
  auto.
Qed.

Hint Immediate MF.Disj_union_1 MF.Disj_union_2 MF.Disj_add_1.

Lemma SymSemAction_sound' : forall k (a : ActionT type k) rs rsNotWritable rs' cs' rv,
  SemAction rs a rs' cs' rv
  -> forall rs'' cs kf, SymSemAction a rs rsNotWritable rs'' cs kf
    -> MF.Disj rs' rsNotWritable
    -> kf (MF.union rs'' rs') (MF.union cs cs') rv.
Proof.
Admitted.
(*
  induction 1; simpl; intuition.

  specialize (H0 mret); intuition.
  eapply IHSemAction in H3; auto.
  subst; rewrite union_add by assumption; auto.

  destruct H0; intuition.
  specialize (double_find rs _ HRegVal H2); intro; subst.
  apply IHSemAction; auto.

  subst.
  generalize (H1 r).
  unfold find at 2.
  intuition.
  rewrite find_add_1 in H3; discriminate.
  rewrite H3 in H0.
  destruct (rs'' r) eqn:Hrs''; intuition.
  apply IHSemAction in H0; eauto.
  rewrite union_add in * by assumption; auto.
  
  rewrite HTrue in *.
  subst.
  apply IHSemAction1 in H1; eauto.
  apply IHSemAction2 in H1; eauto.
  subst.
  repeat rewrite union_assoc; auto.

  rewrite HFalse in *.
  subst.
  apply IHSemAction1 in H1; eauto.
  apply IHSemAction2 in H1; eauto.
  subst.
  repeat rewrite union_assoc; auto.

  apply IHSemAction; auto.

  repeat rewrite union_empty_2; congruence.
Qed.
*)

Theorem SymSemAction_sound : forall k (a : ActionT type k) rs rsNotWritable rs' cs rv,
  SemAction rs a rs' cs rv
  -> forall kf, SymSemAction a rs rsNotWritable (M.empty _) (M.empty _) kf
    -> MF.Disj rs' rsNotWritable
    -> kf rs' cs rv.
Proof.
  intros.
  apply (SymSemAction_sound' H) in H0; auto.
Qed.

