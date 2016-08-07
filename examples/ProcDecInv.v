Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Lts.Syntax Lts.Semantics Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Inline Lts.InlineFacts Lts.DecompositionZero.
Require Import Lts.Tactics Lts.Notations.
Require Import Ex.MemTypes Ex.SC Ex.NativeFifo Ex.MemAtomic Ex.ProcDec Ex.ProcDecInl.
Require Import Eqdep ProofIrrelevance.

Set Implicit Arguments.

Section Invariants.
  Variables opIdx addrSize iaddrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT opIdx addrSize iaddrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize iaddrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize iaddrSize lgDataBytes rfIdx.

  Variables opLd opSt opHt: ConstT (Bit opIdx).
  Hypothesis (HldSt: (if weq (evalConstT opLd) (evalConstT opSt) then true else false) = false).

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  Definition pdecInl := pdecInl fifoSize dec execState execNextPc opLd opSt opHt.

  Definition procDec_inv_0 (o: RegsT): Prop.
  Proof.
    kexistv "pc"%string pcv o (Bit iaddrSize).
    kexistv "rf"%string rfv o (Vector (Data lgDataBytes) rfIdx).
    kexistv "stall"%string stallv o Bool.
    kexistv "rqFromProc"--"empty"%string iev o Bool.
    kexistv "rqFromProc"--"full"%string ifv o Bool.
    kexistv "rqFromProc"--"enqP"%string ienqpv o (Bit fifoSize).
    kexistv "rqFromProc"--"deqP"%string ideqpv o (Bit fifoSize).
    kexistv "rqFromProc"--"elt"%string ieltv o (Vector RqFromProc fifoSize).
    kexistv "rsToProc"--"empty"%string oev o Bool.
    kexistv "rsToProc"--"full"%string ofv o Bool.
    kexistv "rsToProc"--"enqP"%string oenqpv o (Bit fifoSize).
    kexistv "rsToProc"--"deqP"%string odeqpv o (Bit fifoSize).
    kexistv "rsToProc"--"elt"%string oeltv o (Vector RsToProc fifoSize).
    exact True.
  Defined.
  Hint Unfold procDec_inv_0: InvDefs.

  Definition fifo_empty_inv (fifoEmpty: bool) (fifoEnqP fifoDeqP: type (Bit fifoSize)): Prop :=
    fifoEmpty = true /\ fifoEnqP = fifoDeqP.
  
  Definition fifo_not_empty_inv (fifoEmpty: bool) (fifoEnqP fifoDeqP: type (Bit fifoSize)): Prop :=
    fifoEmpty = false /\ fifoEnqP = fifoDeqP ^+ $1.

  Definition mem_request_inv
             (pc: fullType type (SyntaxKind (Bit iaddrSize)))
             (rf: fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx)))
             (insEmpty: bool) (insElt: type (Vector RqFromProc fifoSize))
             (insDeqP: type (Bit fifoSize)): Prop.
  Proof.
    refine (if insEmpty then True else _).
    refine (_ /\ _ /\ _).
    - refine (_ /\ _).
      + exact ((if weq (evalExpr (dec _ rf pc) {| bindex := "opcode"%string |}) (evalConstT opLd)
                then false else true) = insElt insDeqP {| bindex := "op"%string |}).
      + exact ((if weq (evalExpr (dec _ rf pc) {| bindex := "opcode"%string |}) (evalConstT opSt)
                then true else false) = insElt insDeqP {| bindex := "op"%string |}).
    - exact (insElt insDeqP {| bindex := "addr"%string |} =
             evalExpr (dec _ rf pc) {| bindex := "addr"%string |}).
    - refine (if (insElt insDeqP {| bindex := "op"%string |}) : bool then _ else _).
      + exact (insElt insDeqP {| bindex := "data"%string |} =
               evalExpr (dec _ rf pc)
                        {| bindex := "value"%string |}).
      + exact (insElt insDeqP {| bindex := "data"%string |} =
               evalConstT (getDefaultConst (Data lgDataBytes))).
  Defined.
  Hint Unfold fifo_empty_inv fifo_not_empty_inv mem_request_inv: InvDefs.

  Definition procDec_inv_1 (o: RegsT): Prop.
  Proof.
    kexistv "pc"%string pcv o (Bit iaddrSize).
    kexistv "rf"%string rfv o (Vector (Data lgDataBytes) rfIdx).
    kexistv "stall"%string stallv o Bool.
    kexistv "rqFromProc"--"empty"%string iev o Bool.
    kexistv "rqFromProc"--"enqP"%string ienqP o (Bit fifoSize).
    kexistv "rqFromProc"--"deqP"%string ideqP o (Bit fifoSize).
    kexistv "rqFromProc"--"elt"%string ieltv o (Vector RqFromProc fifoSize).
    kexistv "rsToProc"--"empty"%string oev o Bool.
    kexistv "rsToProc"--"enqP"%string oenqP o (Bit fifoSize).
    kexistv "rsToProc"--"deqP"%string odeqP o (Bit fifoSize).
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
  Proof. (* SKIP_PROOF_ON
    induction 2.

    - kinv_magic_light.

    - kinvert.
      + kinv_magic_light.
      + kinv_magic_light.
      + kinv_magic_light.
      + kinv_magic_light.
      + kinv_magic_light.
      + kinv_magic_light.
      + kinv_magic_light.
      + kinv_magic_light.
      + kinv_magic_light.
      + kinv_magic_light.
        END_SKIP_PROOF_ON *) admit.
  Qed.

  Lemma procDec_inv_0_ok:
    forall o,
      reachable o (fst pdecInl) ->
      procDec_inv_0 o.
  Proof.
    intros; inv H; inv H0.
    eapply procDec_inv_0_ok'; eauto.
  Qed.

  Ltac procDec_inv_1_tac :=
    kinv_or3;
    repeat
      match goal with
      | [ |- _ /\ _ ] => split
      | [ |- exists _, _ ] => eexists
      end.

  Lemma procDec_inv_1_ok':
    forall init n ll,
      init = initRegs (getRegInits (fst pdecInl)) ->
      Multistep (fst pdecInl) init n ll ->
      procDec_inv_1 n.
  Proof. (* SKIP_PROOF_ON
    induction 2.

    - kinv_magic_light_with procDec_inv_1_tac.
      or3_fst; kinv_magic_light_with procDec_inv_1_tac.

    - kinvert.
      + mred.
      + mred.
      + kinv_magic_light_with kinv_or3.
        or3_snd; kinv_magic_light_with procDec_inv_1_tac.
        * kinv_finish.
        * kinv_finish.
      + kinv_magic_light_with kinv_or3.
        or3_snd; kinv_magic_light_with procDec_inv_1_tac.
        * kinv_finish.
        * kinv_finish.
      + kinv_magic_light_with kinv_or3.
        or3_fst; kinv_magic_light_with procDec_inv_1_tac.
      + kinv_magic_light_with kinv_or3.
        or3_fst; kinv_magic_light_with procDec_inv_1_tac.
      + kinv_magic_light_with kinv_or3.
        or3_fst; kinv_magic_light_with procDec_inv_1_tac.
      + kinv_magic_light_with kinv_or3.
        or3_fst; kinv_magic_light_with procDec_inv_1_tac.
      + kinv_magic_light_with kinv_or3.
        or3_thd; kinv_magic_light_with procDec_inv_1_tac.
      + kinv_magic_light_with kinv_or3.
        or3_thd; kinv_magic_light_with procDec_inv_1_tac.
        END_SKIP_PROOF_ON *) admit.
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

