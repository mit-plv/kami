Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Inline Lts.InlineFacts_2 Lts.Tactics.
Require Import Ex.SC Ex.ProcDec.

Set Implicit Arguments.

Section Inlined.
  Variables addrSize fifoSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable execState: ExecStateT 2 addrSize valSize rfIdx.
  Variable execNextPc: ExecNextPcT 2 addrSize valSize rfIdx.

  Definition pdec := pdecf fifoSize dec execState execNextPc.
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

End Inlined.

