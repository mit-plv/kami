Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Inline Lts.InlineFacts_2 Lts.Decomposition.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic Ex.ProcDec.
Require Import Eqdep.

Set Implicit Arguments.

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
      
    (*   repeat ( *)
    (*       try eexists; *)
    (*       repeat rewrite M.find_add_2 by discriminate; *)
    (*       repeat rewrite M.find_add_1 by reflexivity). *)

    (* - specialize (IHMultistep H); clear -IHMultistep HStep. *)
    (*   admit. *)
  Qed.

  Lemma procDec_inv_0_ok:
    forall o,
      reachable o (fst pdecInl) ->
      procDec_inv_0 o.
  Proof.
    intros; inv H; inv H0.
    eapply procDec_inv_0_ok'; eauto.
  Qed.

  Lemma procDec_inv_1_ok:
    forall o,
      reachable o (fst pdecInl) ->
      procDec_inv_1 o.
  Proof.
    admit.
  Qed.

End Invariants.

