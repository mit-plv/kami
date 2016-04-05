Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Inline Lts.InlineFacts_2 Lts.DecompositionZero.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic Ex.ProcDec Ex.ProcDecInl.
Require Import Eqdep.

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

Ltac inv_red :=
  repeat autounfold with InvDefs in *; dest; simpl_find;
  repeat
    (match goal with
     (* Logic *)
     | [ |- ~ _ ] => intro
     | [H: _ \/ _ |- _] => destruct H
     | [ |- _ /\ _ ] => split
     | [H: ?t = ?t |- _] => clear H
     (* Reducing boolean conditions *)
     | [H: false = true |- _] => inversion H
     | [H: true = false |- _] => inversion H
     | [H: negb _ = true |- _] => apply negb_true_iff in H; subst
     | [H: negb _ = false |- _] => apply negb_false_iff in H; subst
     end; dest; try subst).

Ltac inv_solve :=
  abstract (
      inv_red;
      repeat
        (try
           match goal with
           (* Destruction *)
           | [H: context [weq ?w1 ?w2] |- _] => destruct (weq w1 w2)
           | [ |- context [weq ?w1 ?w2] ] => destruct (weq w1 w2)
           end;
         try subst;
         intuition idtac)
    ).

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

  Definition xor3 (b1 b2 b3: Prop) :=
    (b1 /\ (~ b2) /\ (~ b3)) \/
    ((~ b1) /\ b2 /\ (~ b3)) \/
    ((~ b1) /\ (~ b2) /\ b3).

  Definition fifo_empty_inv (fifoEmpty: bool) (fifoEnqP fifoDeqP: type (Bit fifoSize)): Prop :=
    fifoEmpty = true /\ fifoEnqP = fifoDeqP.
  
  Definition fifo_not_empty_inv (fifoEmpty: bool) (fifoEnqP fifoDeqP: type (Bit fifoSize)): Prop :=
    fifoEmpty = false /\ fifoEnqP = fifoDeqP ^+ $1.

  Hint Unfold xor3 fifo_empty_inv fifo_not_empty_inv: InvDefs.

  Definition procDec_inv_1 (o: RegsT): Prop.
  Proof.
    kexistv "stall"%string stallv o Bool.
    kexistv "Ins.empty"%string iev o Bool.
    kexistv "Ins.enqP"%string ienqP o (Bit fifoSize).
    kexistv "Ins.deqP"%string ideqP o (Bit fifoSize).
    kexistv "Outs.empty"%string oev o Bool.
    kexistv "Outs.enqP"%string oenqP o (Bit fifoSize).
    kexistv "Outs.deqP"%string odeqP o (Bit fifoSize).
    refine (xor3 _ _ _).
    - exact (v = false /\ fifo_empty_inv v0 v1 v2 /\ fifo_empty_inv v3 v4 v5).
    - exact (v = true /\ fifo_not_empty_inv v0 v1 v2 /\ fifo_empty_inv v3 v4 v5).
    - exact (v = true /\ fifo_empty_inv v0 v1 v2 /\ fifo_not_empty_inv v3 v4 v5).
  Defined.

  Definition procDec_inv_2 (o: RegsT): Prop.
  Proof.
    kexistv "pc"%string pcv o (Bit addrSize).
    kexistv "rf"%string rfv o (Vector (Bit valSize) rfIdx).
    kexistv "Ins.empty"%string iev o Bool.
    kexistv "Ins.elt"%string ieltv o (Vector (memAtomK addrSize valSize) fifoSize).
    kexistv "Ins.deqP"%string ideqP o (Bit fifoSize).
    refine (if v1 then True else _).
    refine (_ /\ _ /\ _).
    - exact (v2 v3 ``"type" = dec _ v0 v ``"opcode").
    - exact (v2 v3 ``"addr" = dec _ v0 v ``"addr").
    - refine (if weq (v2 v3 ``"type") (evalConstT memLd) then _ else _).
      + exact (v2 v3 ``"value" = evalConstT (getDefaultConst (Bit valSize))).
      + refine (if weq (v2 v3 ``"type") (evalConstT memSt) then _ else True).
        exact (v2 v3 ``"value" = dec _ v0 v ``"value").
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
    (*   left; inv_solve. *)

    (* - specialize (IHMultistep H); clear -IHMultistep HStep. *)
    (*   apply step_no_defs_substep in HStep; [|reflexivity]. *)
    (*   destruct HStep as [ul [calls ?]]; dest; subst. *)
    (*   inv H0; try (mred; fail); [|inv HIn]. *)
    (*   CommonTactics.dest_in. *)

    (*   + inv H; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify; simpl_find. *)
    (*     right; left; repeat split; inv_solve. *)
    (*   + inv H0; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify; simpl_find. *)
    (*     right; left; repeat split; inv_solve. *)
    (*   + inv H; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify; simpl_find. *)
    (*     left; repeat split; inv_solve. *)
    (*   + inv H0; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify; simpl_find. *)
    (*     left; repeat split; inv_solve. *)
    (*   + inv H; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify; simpl_find; auto. *)
    (*   + inv H0; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify; simpl_find; auto. *)
    (*   + inv H; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify; simpl_find. *)
    (*     right; right; repeat split; inv_solve. *)
    (*   + inv H0; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify; simpl_find. *)
    (*     right; right; repeat split; inv_solve. *)
  Qed.

  Lemma procDec_inv_1_ok:
    forall o,
      reachable o (fst pdecInl) ->
      procDec_inv_1 o.
  Proof.
    intros; inv H; inv H0.
    eapply procDec_inv_1_ok'; eauto.
  Qed.

  Lemma procDec_inv_2_ok':
    forall init n ll,
      init = initRegs (getRegInits (fst pdecInl)) ->
      Multistep (fst pdecInl) init n ll ->
      procDec_inv_2 n.
  Proof.
    admit.
  Qed.

  Lemma procDec_inv_2_ok:
    forall o,
      reachable o (fst pdecInl) ->
      procDec_inv_2 o.
  Proof.
    intros; inv H; inv H0.
    eapply procDec_inv_2_ok'; eauto.
  Qed.

End Invariants.

Hint Unfold xor3 procDec_inv_0 procDec_inv_1 procDec_inv_2
     fifo_empty_inv fifo_not_empty_inv: InvDefs.

