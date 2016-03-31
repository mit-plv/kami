Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Inline Lts.InlineFacts_2 Lts.DecompositionZero.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic Ex.ProcDec.
Require Import Eqdep.

Set Implicit Arguments.

(** TODO: Move to SemFacts.v *)
Lemma substepsInd_no_defs_substep:
  forall m (HnoDefs: getDefs m = nil)
         o u l,
    SubstepsInd m o u l ->
    wellHidden m (hide l) ->
    exists ul calls,
      hide l = getLabel ul calls /\ Substep m o u ul calls.
Proof.
  induction 2; simpl; intros.
  - exists (Meth None), (M.empty _).
    split; auto.
    constructor.
  - admit.
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

Ltac kexistv k v m t :=
  refine (exists v: fullType type (SyntaxKind t),
             M.find k m = Some (existT _ _ v) /\ _).

Section Invariants.
  Variables addrSize fifoSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable exec: ExecT 2 addrSize valSize rfIdx.

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

  Definition xor3 (b1 b2 b3: bool) :=
    (b1 && (negb b2) && (negb b3))
    || ((negb b1) && b2 && (negb b3))
    || ((negb b1) && (negb b2) && b3).
  
  Definition procDec_inv_1 (o: RegsT): Prop.
  Proof.
    kexistv "stall"%string stallv o Bool.
    kexistv "Ins.empty"%string iev o Bool.
    kexistv "Outs.empty"%string oev o Bool.
    exact (xor3 (negb v) (negb v0) (negb v1) = true).
  Defined.

  Definition pdec := pdecf fifoSize dec exec.
  Hint Unfold pdec: ModuleDefs. (* for kinline_compute *)

  Definition pdecInl: Modules * bool.
  Proof.
    remember (inlineF pdec) as inlined.
    kinline_compute_in Heqinlined.
    match goal with
    | [H: inlined = ?m |- _] =>
      exact m
    end.
  Defined.

  Lemma pdecInl_equal: pdecInl = inlineF pdec.
  Proof.
    admit.
    (* kinline_compute. *)
    (* reflexivity. *)
  Qed.

  Ltac simpl_find :=
    repeat
      match goal with
      | [H1: M.find ?k ?m = _, H2: M.find ?k ?m = _ |- _] =>
        rewrite H1 in H2
      | [H: Some _ = Some _ |- _] => inv H
      end; destruct_existT.

  Ltac invReify :=
    repeat (eexists; split; [findReify; simpl; eauto|]).

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
    (*   invReify; auto. *)

    (* - specialize (IHMultistep H); clear -IHMultistep HStep. *)
    (*   apply step_no_defs_substep in HStep; [|reflexivity]. *)
    (*   destruct HStep as [ul [calls ?]]; dest; subst. *)
    (*   inv H0; try (mred; fail); [|inv HIn]. *)
    (*   CommonTactics.dest_in. *)

    (*   + inv H; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify. *)
    (*     simpl_find. *)
    (*     rewrite H1 in H13; clear -H13. *)
    (*     destruct x7, x8; auto. *)

    (*   + inv H0; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify. *)
    (*     simpl_find. *)
    (*     rewrite H1 in H13; clear -H13. *)
    (*     destruct x7, x8; auto. *)

    (*   + inv H; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     invReify. *)
    (*     simpl_find. *)
    (*     admit. *)

    (*   + inv H0; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     repeat (eexists; split; [findReify; simpl; eauto|]). *)

    (*     simpl_find. *)
    (*     admit. *)

    (*   + inv H; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     repeat (eexists; split; [findReify; simpl; eauto|]). *)

    (*     simpl_find; auto. *)

    (*   + inv H0; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     repeat (eexists; split; [findReify; simpl; eauto|]). *)

    (*     simpl_find; auto. *)

    (*   + inv H; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     repeat (eexists; split; [findReify; simpl; eauto|]). *)

    (*     simpl_find. *)
    (*     admit. *)

    (*   + inv H0; invertActionRep. *)
    (*     unfold procDec_inv_1 in *; dest. *)
    (*     repeat (eexists; split; [findReify; simpl; eauto|]). *)

    (*     simpl_find. *)
    (*     admit. *)
  Qed.

  Lemma procDec_inv_1_ok:
    forall o,
      reachable o (fst pdecInl) ->
      procDec_inv_1 o.
  Proof.
    intros; inv H; inv H0.
    eapply procDec_inv_1_ok'; eauto.
  Qed.

  Lemma procDec_inv_0_ok':
    forall init n ll,
      init = initRegs (getRegInits (fst pdecInl)) ->
      Multistep (fst pdecInl) init n ll ->
      procDec_inv_0 n.
  Proof.
    admit.
    (* induction 2. *)

    (* - admit. *)
    (*   (* repeat subst. *) *)
    (*   (* simpl; unfold procDec_inv_0. *) *)
    (*   (* repeat (eexists; split; [findReify; simpl; auto|]). *) *)
    (*   (* auto. *) *)

    (* - specialize (IHMultistep H); clear -IHMultistep HStep. *)
    (*   apply step_no_defs_substep in HStep; [|reflexivity]. *)
    (*   destruct HStep as [ul [calls ?]]; dest; subst. *)

    (*   inv H0; try (mred; fail); [|inv HIn]. *)
    (*   CommonTactics.dest_in. *)

    (*   + admit. *)
    (*   + admit. *)
    (*   + admit. *)
    (*   + admit. *)
    (*   + admit. *)
    (*   + admit. *)
    (*   + admit. *)
    (*   + admit. *)
  Qed.

  Lemma procDec_inv_0_ok:
    forall o,
      reachable o (fst pdecInl) ->
      procDec_inv_0 o.
  Proof.
    intros; inv H; inv H0.
    eapply procDec_inv_0_ok'; eauto.
  Qed.

End Invariants.

