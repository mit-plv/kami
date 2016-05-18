Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Inline Lts.InlineFacts_2 Lts.DecompositionZero.
Require Import Lts.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo Ex.MemAtomic Ex.ProcDec Ex.ProcDecInl.
Require Import Eqdep ProofIrrelevance.

Set Implicit Arguments.

Section Invariants.
  Variables addrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT 2 addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT 2 addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT 2 addrSize lgDataBytes rfIdx.

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  Definition pdecInl := pdecInl fifoSize dec execState execNextPc.

  Definition procDec_inv_0 (o: RegsT): Prop.
  Proof.
    kexistv "pc"%string pcv o (Bit addrSize).
    kexistv "rf"%string rfv o (Vector (Data lgDataBytes) rfIdx).
    kexistv "stall"%string stallv o Bool.
    kexistv "Ins".."empty"%string iev o Bool.
    kexistv "Ins".."full"%string ifv o Bool.
    kexistv "Ins".."enqP"%string ienqpv o (Bit fifoSize).
    kexistv "Ins".."deqP"%string ideqpv o (Bit fifoSize).
    kexistv "Ins".."elt"%string ieltv o (Vector RqFromProc fifoSize).
    kexistv "Outs".."empty"%string oev o Bool.
    kexistv "Outs".."full"%string ofv o Bool.
    kexistv "Outs".."enqP"%string oenqpv o (Bit fifoSize).
    kexistv "Outs".."deqP"%string odeqpv o (Bit fifoSize).
    kexistv "Outs".."elt"%string oeltv o (Vector RsToProc fifoSize).
    exact True.
  Defined.
  Hint Unfold procDec_inv_0: InvDefs.

  Definition fifo_empty_inv (fifoEmpty: bool) (fifoEnqP fifoDeqP: type (Bit fifoSize)): Prop :=
    fifoEmpty = true /\ fifoEnqP = fifoDeqP.
  
  Definition fifo_not_empty_inv (fifoEmpty: bool) (fifoEnqP fifoDeqP: type (Bit fifoSize)): Prop :=
    fifoEmpty = false /\ fifoEnqP = fifoDeqP ^+ $1.

  Definition mem_request_inv
             (pc: fullType type (SyntaxKind (Bit addrSize)))
             (rf: fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx)))
             (insEmpty: bool) (insElt: type (Vector RqFromProc fifoSize))
             (insDeqP: type (Bit fifoSize)): Prop.
  Proof.
    refine (if insEmpty then True else _).
    refine (_ /\ _ /\ _).
    - refine (_ /\ _).
      + exact ((if weq (evalExpr (dec _ rf pc) ``"opcode") (evalConstT opLd)
                then false else true) = insElt insDeqP ``"op").
      + exact ((if weq (evalExpr (dec _ rf pc) ``"opcode") (evalConstT opSt)
                then true else false) = insElt insDeqP ``"op").
    - exact (insElt insDeqP ``"addr" = evalExpr (dec _ rf pc) ``"addr").
    - refine (if (insElt insDeqP ``"op") : bool then _ else _).
      + exact (insElt insDeqP ``"data" = evalExpr (dec _ rf pc) ``"value").
      + exact (insElt insDeqP ``"data" = evalConstT (getDefaultConst (Data lgDataBytes))).
  Defined.
  Hint Unfold fifo_empty_inv fifo_not_empty_inv mem_request_inv: InvDefs.

  Definition procDec_inv_1 (o: RegsT): Prop.
  Proof.
    kexistv "pc"%string pcv o (Bit addrSize).
    kexistv "rf"%string rfv o (Vector (Data lgDataBytes) rfIdx).
    kexistv "stall"%string stallv o Bool.
    kexistv "Ins".."empty"%string iev o Bool.
    kexistv "Ins".."enqP"%string ienqP o (Bit fifoSize).
    kexistv "Ins".."deqP"%string ideqP o (Bit fifoSize).
    kexistv "Ins".."elt"%string ieltv o (Vector RqFromProc fifoSize).
    kexistv "Outs".."empty"%string oev o Bool.
    kexistv "Outs".."enqP"%string oenqP o (Bit fifoSize).
    kexistv "Outs".."deqP"%string odeqP o (Bit fifoSize).
    refine (or3 _ _ _).
    - exact (v1 = false /\ fifo_empty_inv v2 v3 v4 /\ fifo_empty_inv v6 v7 v8).
    - refine (_ /\ _).
      + exact (v1 = true /\ fifo_not_empty_inv v2 v3 v4 /\ fifo_empty_inv v6 v7 v8).
      + exact (mem_request_inv v v0 v2 v5 v4).
    - exact (v1 = true /\ fifo_empty_inv v2 v3 v4 /\ fifo_not_empty_inv v6 v7 v8).
  Defined.
  Hint Unfold procDec_inv_1: InvDefs.

  Lemma procDec_inv_0_ok':
    forall init n ll,
      init = initRegs (getRegInits (fst pdecInl)) ->
      Multistep (fst pdecInl) init n ll ->
      procDec_inv_0 n.
  Proof.
    admit.
    (*
    induction 2.

    - kinv_magic.

    - kinvert.
      + kinv_magic.
      + kinv_magic.
      + kinv_magic.
      + kinv_magic.
      + kinv_magic.
      + kinv_magic.
      + kinv_magic.
      + kinv_magic.
      + kinv_magic.
      + kinv_magic.
     *)
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
    (*
    induction 2.

    - kinv_magic_with kinv_or3.
      or3_fst; kinv_magic.

    - kinvert.
      + kinv_magic_with kinv_or3.
      + kinv_magic_with kinv_or3.
      + kinv_magic_with kinv_or3.
        or3_snd; kinv_magic.
      + kinv_magic_with kinv_or3.
        or3_snd; kinv_magic.
      + kinv_magic_with kinv_or3.
        or3_fst; kinv_magic.
      + kinv_magic_with kinv_or3.
        or3_fst; kinv_magic.
      + kinv_magic_with kinv_or3.
        (* or3_fst; kinv_magic. *)
      + kinv_magic_with kinv_or3.
        or3_fst; kinv_magic.
      + kinv_magic_with kinv_or3.
        or3_thd; kinv_magic.
      + kinv_magic_with kinv_or3.
        or3_thd; kinv_magic.
     *)
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

Hint Unfold RqFromProc RsToProc: MethDefs.
Hint Unfold procDec_inv_0 procDec_inv_1
     fifo_empty_inv fifo_not_empty_inv mem_request_inv: InvDefs.

