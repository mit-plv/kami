Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Inline Lts.InlineFacts_2 Lts.DecompositionZero.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic Ex.ProcDec Ex.ProcDecInl.
Require Import Eqdep ProofIrrelevance.

Set Implicit Arguments.

(** TODO: Move to SemFacts.v *)
Lemma substepsInd_no_defs_substep:
  forall m (HnoDefs: getDefs m = nil)
         o u l,
    SubstepsInd m o u l ->
    exists ul calls,
      hide l = getLabel ul calls /\ Substep m o u ul calls.
Proof.
  admit.
Qed.

Lemma step_no_defs_substep:
  forall m (HnoDefs: getDefs m = nil)
         o u l,
    Step m o u l ->
    exists ul calls,
      l = getLabel ul calls /\
      Substep m o u ul calls.
Proof.
  intros; apply step_consistent in H; inv H.
  apply substepsInd_no_defs_substep; auto.
Qed.

(** End of lemmas which should be moved *)

Ltac kgetv k v m t f :=
  destruct (M.find k m) as [[[kind|] v]|]; [|exact f|exact f];
  destruct (decKind kind t); [subst|exact f].

(* TODO: "v" is not working *)
Ltac kexistv k v m t :=
  refine (exists v: fullType type (SyntaxKind t),
             M.find k m = Some (existT _ _ v) /\ _).

Ltac simpl_find :=
  repeat
    match goal with
    | [H1: M.find ?k ?m = _, H2: M.find ?k ?m = _ |- _] =>
      rewrite H1 in H2
    | [H: Some _ = Some _ |- _] => inv H
    end; destruct_existT.

Ltac invReify :=
  repeat (eexists; split; [findReify; simpl; eauto|]).

Ltac inv_contra :=
  try (exfalso; repeat autounfold with InvDefs in *; dest; subst;
       repeat
         (match goal with
          | [H: false = true |- _] => inversion H
          | [H: true = false |- _] => inversion H
          | [H: negb _ = true |- _] => apply negb_true_iff in H; subst
          | [H: negb _ = false |- _] => apply negb_false_iff in H; subst
          end; dest; try subst);
       fail).

Ltac inv_red :=
  repeat autounfold with InvDefs in *; dest;
  repeat
    (try match goal with
         | [H: ?t = ?t |- _] => clear H
         | [H: negb _ = true |- _] => apply negb_true_iff in H; subst
         | [H: negb _ = false |- _] => apply negb_false_iff in H; subst
         | [ |- context [weq ?w ?w] ] =>
           let n := fresh "n" in
           destruct (weq w w) as [|n]; [|elim n; reflexivity]
         | [H: (if ?c then true else false) = true |- _] => destruct c; [|inv H]
         | [H: (if ?c then true else false) = false |- _] => destruct c; [inv H|]
         end; dest; try subst).

Lemma rewrite_not_weq: forall sz (a b: word sz) (pf: a <> b), weq a b = right _ pf.
Proof.
  intros; destruct (weq a b); try solve [ elimtype False; auto ].
  f_equal; apply proof_irrelevance.
Qed.

Ltac inv_solve :=
  repeat
    (inv_red;
     repeat
       match goal with
       | [ |- _ /\ _ ] => split
       (* For optimized destruction of "weq" *)
       | [ |- context[weq ?w ?w] ] =>
         let H := fresh "H" in
         pose proof (@rewrite_weq _ w w eq_refl) as H; rewrite H; clear H
       | [ |- context[weq ?w1 ?w2] ] =>
         let H := fresh "H" in
         let Hr := fresh "Hr" in
         assert (w1 = w2) as H by reflexivity;
         pose proof (@rewrite_weq _ w1 w2 H) as Hr;
         rewrite Hr; clear Hr H
       | [ |- context[weq ?w1 ?w2] ] =>
         let H := fresh "H" in
         let Hr := fresh "Hr" in
         assert (w1 <> w2) as H by discriminate;
         pose proof (@rewrite_not_weq _ w1 w2 H) as Hr;
         rewrite Hr; clear Hr H
       (* Normal destruction of "weq": it's slow *)
       | [H: context [weq ?w1 ?w2] |- _] => destruct (weq w1 w2)
       | [ |- context [weq ?w1 ?w2] ] => destruct (weq w1 w2)
       | [ |- context [weq ?w ?w] ] =>
         let n := fresh "n" in
         destruct (weq w w) as [|n]; [|elim n; reflexivity]
       end;
     try subst;
     inv_contra;
     intuition auto).

Definition or3 (b1 b2 b3: Prop) := b1 \/ b2 \/ b3.
Tactic Notation "or3_fst" := left.
Tactic Notation "or3_snd" := right; left.
Tactic Notation "or3_thd" := right; right.
Ltac dest_or3 :=
  match goal with
  | [H: or3 _ _ _ |- _] => destruct H as [|[|]]
  end.

Section Invariants.
  Variables addrSize fifoSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable exec: ExecT 2 addrSize valSize rfIdx.

  Definition pdecInl := pdecInl fifoSize dec exec.

  Definition procDec_inv_0 (o: RegsT): Prop.
  Proof.
    kexistv "pc"%string pcv o (Bit addrSize).
    kexistv "rf"%string rfv o (Vector (Bit valSize) rfIdx).
    kexistv "stall"%string stallv o Bool.
    kexistv "Ins.empty"%string iev o Bool.
    kexistv "Ins.full"%string ifv o Bool.
    kexistv "Ins.enqP"%string ienqpv o (Bit fifoSize).
    kexistv "Ins.deqP"%string ideqpv o (Bit fifoSize).
    kexistv "Ins.elt"%string ieltv o (Vector (memAtomK addrSize valSize) fifoSize).
    kexistv "Outs.empty"%string oev o Bool.
    kexistv "Outs.full"%string ofv o Bool.
    kexistv "Outs.enqP"%string oenqpv o (Bit fifoSize).
    kexistv "Outs.deqP"%string odeqpv o (Bit fifoSize).
    kexistv "Outs.elt"%string oeltv o (Vector (memAtomK addrSize valSize) fifoSize).
    exact True.
  Defined.

  Definition fifo_empty_inv (fifoEmpty: bool) (fifoEnqP fifoDeqP: type (Bit fifoSize)): Prop :=
    fifoEmpty = true /\ fifoEnqP = fifoDeqP.
  
  Definition fifo_not_empty_inv (fifoEmpty: bool) (fifoEnqP fifoDeqP: type (Bit fifoSize)): Prop :=
    fifoEmpty = false /\ fifoEnqP = fifoDeqP ^+ $1.

  Definition mem_request_inv
             (pc: fullType type (SyntaxKind (Bit addrSize)))
             (rf: fullType type (SyntaxKind (Vector (Bit valSize) rfIdx)))
             (insEmpty: bool) (insElt: type (Vector (memAtomK addrSize valSize) fifoSize))
             (insDeqP: type (Bit fifoSize)): Prop.
  Proof.
    refine (if insEmpty then True else _).
    refine (_ /\ _ /\ _).
    - exact (insElt insDeqP ``"type" = dec _ rf pc ``"opcode").
    - exact (insElt insDeqP ``"addr" = dec _ rf pc ``"addr").
    - refine (if weq (insElt insDeqP ``"type") (evalConstT memLd) then _ else _).
      + exact (insElt insDeqP ``"value" = evalConstT (getDefaultConst (Bit valSize))).
      + refine (if weq (insElt insDeqP ``"type") (evalConstT memSt) then _ else True).
        exact (insElt insDeqP ``"value" = dec _ rf pc ``"value").
  Defined.

  Hint Unfold fifo_empty_inv fifo_not_empty_inv mem_request_inv: InvDefs.

  Definition procDec_inv_1 (o: RegsT): Prop.
  Proof.
    kexistv "pc"%string pcv o (Bit addrSize).
    kexistv "rf"%string rfv o (Vector (Bit valSize) rfIdx).
    kexistv "stall"%string stallv o Bool.
    kexistv "Ins.empty"%string iev o Bool.
    kexistv "Ins.enqP"%string ienqP o (Bit fifoSize).
    kexistv "Ins.deqP"%string ideqP o (Bit fifoSize).
    kexistv "Ins.elt"%string ieltv o (Vector (memAtomK addrSize valSize) fifoSize).
    kexistv "Outs.empty"%string oev o Bool.
    kexistv "Outs.enqP"%string oenqP o (Bit fifoSize).
    kexistv "Outs.deqP"%string odeqP o (Bit fifoSize).
    refine (or3 _ _ _).
    - exact (v1 = false /\ fifo_empty_inv v2 v3 v4 /\ fifo_empty_inv v6 v7 v8).
    - refine (_ /\ _).
      + exact (v1 = true /\ fifo_not_empty_inv v2 v3 v4 /\ fifo_empty_inv v6 v7 v8).
      + exact (mem_request_inv v v0 v2 v5 v4).
    - exact (v1 = true /\ fifo_empty_inv v2 v3 v4 /\ fifo_not_empty_inv v6 v7 v8).
  Defined.

  Lemma procDec_inv_0_ok':
    forall init n ll,
      init = initRegs (getRegInits (fst pdecInl)) ->
      Multistep (fst pdecInl) init n ll ->
      procDec_inv_0 n.
  Proof.
    admit.
    (* induction 2. *)

    (* - repeat subst. *)
    (*   simpl; unfold procDec_inv_0. *)
    (*   invReify; auto. *)

    (* - specialize (IHMultistep H); clear -IHMultistep HStep. *)
    (*   apply step_no_defs_substep in HStep; [|reflexivity]. *)
    (*   destruct HStep as [ul [calls ?]]; dest; subst. *)
    (*   inv H0; try (mred; fail); [|inv HIn]. *)
    (*   CommonTactics.dest_in. *)

    (*   + inv H; invertActionRep. *)
    (*     unfold procDec_inv_0 in *; dest. *)
    (*     invReify; simpl_find; auto. *)
    (*   + inv H0; invertActionRep. *)
    (*     unfold procDec_inv_0 in *; dest. *)
    (*     invReify; simpl_find; auto. *)
    (*   + inv H; invertActionRep. *)
    (*     unfold procDec_inv_0 in *; dest. *)
    (*     invReify; simpl_find; auto. *)
    (*   + inv H0; invertActionRep. *)
    (*     unfold procDec_inv_0 in *; dest. *)
    (*     invReify; simpl_find; auto. *)
    (*   + inv H; invertActionRep. *)
    (*     unfold procDec_inv_0 in *; dest. *)
    (*     invReify; simpl_find; auto. *)
    (*   + inv H0; invertActionRep. *)
    (*     unfold procDec_inv_0 in *; dest. *)
    (*     invReify; simpl_find; auto. *)
    (*   + inv H; invertActionRep. *)
    (*     unfold procDec_inv_0 in *; dest. *)
    (*     invReify; simpl_find; auto. *)
    (*   + inv H0; invertActionRep. *)
    (*     unfold procDec_inv_0 in *; dest. *)
    (*     invReify; simpl_find; auto. *)
  Qed.

  Lemma procDec_inv_0_ok:
    forall o,
      reachable o (fst pdecInl) ->
      procDec_inv_0 o.
  Proof.
    intros; inv H; inv H0.
    eapply procDec_inv_0_ok'; eauto.
  Qed.

  Lemma procDec_inv_1_ok':
    forall init n ll,
      init = initRegs (getRegInits (fst pdecInl)) ->
      Multistep (fst pdecInl) init n ll ->
      procDec_inv_1 n.
  Proof.
    admit.
    (* induction 2. *)

    (* - repeat subst. *)
    (*   simpl; unfold procDec_inv_1. *)
    (*   invReify. *)
    (*   or3_fst; inv_solve. *)

    (* - specialize (IHMultistep H); clear -IHMultistep HStep. *)
    (*   apply step_no_defs_substep in HStep; [|reflexivity]. *)
    (*   destruct HStep as [ul [calls ?]]; dest; subst. *)
    (*   inv H0; try (mred; fail); [|inv HIn]. *)
    (*   CommonTactics.dest_in. *)

    (*   + inv H; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify; simpl_find. *)
        
    (*     dest_or3; inv_contra. *)
    (*     or3_snd; repeat split; inv_solve. *)

    (*   + inv H0; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify; simpl_find. *)

    (*     dest_or3; inv_contra. *)
    (*     or3_snd; repeat split; inv_solve. *)
        
    (*   + inv H; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify; simpl_find. *)

    (*     dest_or3; inv_contra. *)
    (*     or3_fst; repeat split; inv_solve. *)
        
    (*   + inv H0; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify; simpl_find. *)

    (*     dest_or3; inv_contra. *)
    (*     or3_fst; repeat split; inv_solve. *)
        
    (*   + inv H; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify; simpl_find. *)

    (*     dest_or3; inv_contra. *)
    (*     or3_fst; repeat split; inv_solve. *)
        
    (*   + inv H0; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify; simpl_find. *)

    (*     dest_or3; inv_contra. *)
    (*     or3_fst; repeat split; inv_solve. *)

    (*   + inv H; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify; simpl_find. *)

    (*     dest_or3; inv_contra. *)
    (*     or3_thd; repeat split; inv_solve. *)

    (*   + inv H0; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify; simpl_find. *)

    (*     dest_or3; inv_contra. *)
    (*     or3_thd; repeat split; inv_solve. *)
  Qed.

  Lemma procDec_inv_1_ok:
    forall o,
      reachable o (fst pdecInl) ->
      procDec_inv_1 o.
  Proof.
    intros; inv H; inv H0.
    eapply procDec_inv_1_ok'; eauto.
  Qed.

End Invariants.

Hint Unfold procDec_inv_0 procDec_inv_1
     fifo_empty_inv fifo_not_empty_inv mem_request_inv: InvDefs.

