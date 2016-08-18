Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StructNotation Lib.StringBound Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Specialize Kami.Inline Kami.InlineFacts Kami.Decomposition.
Require Import Kami.Tactics Kami.Notations.
Require Import Ex.MemTypes Ex.SC Ex.NativeFifo Ex.MemAtomic Ex.ProcDec Ex.ProcDecInl.
Require Import Eqdep ProofIrrelevance.

Set Implicit Arguments.

Section Invariants.
  Variables opIdx addrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT opIdx addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize lgDataBytes rfIdx.

  Variables opLd opSt opTh: ConstT (Bit opIdx).
  Hypothesis (HldSt: (if weq (evalConstT opLd) (evalConstT opSt) then true else false) = false).

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  Definition pdecInl := pdecInl fifoSize dec execState execNextPc opLd opSt opTh.

  Definition fifo_empty_inv (fifoEmpty: bool) (fifoEnqP fifoDeqP: type (Bit fifoSize)): Prop :=
    fifoEmpty = true /\ fifoEnqP = fifoDeqP.
  
  Definition fifo_not_empty_inv (fifoEmpty: bool) (fifoEnqP fifoDeqP: type (Bit fifoSize)): Prop :=
    fifoEmpty = false /\ fifoEnqP = fifoDeqP ^+ $1.

  Definition mem_request_inv
             (instRaw: fullType type (SyntaxKind (Data lgDataBytes)))
             (rf: fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx)))
             (insEmpty: bool) (insElt: type (Vector RqFromProc fifoSize))
             (insDeqP: type (Bit fifoSize)): Prop.
  Proof.
    refine (if insEmpty then True else _).
    refine (_ /\ _ /\ _).
    - refine (_ /\ _).
      + exact ((if weq (evalExpr (dec _ rf instRaw) ``"opcode") (evalConstT opLd)
                then false else true) = insElt insDeqP ``"op").
      + exact ((if weq (evalExpr (dec _ rf instRaw) ``"opcode") (evalConstT opSt)
                then true else false) = insElt insDeqP ``"op").
    - exact (insElt insDeqP ``"addr" = evalExpr (dec _ rf instRaw) ``"addr").
    - refine (if (insElt insDeqP ``"op") : bool then _ else _).
      + exact (insElt insDeqP ``"data" = evalExpr (dec _ rf instRaw) ``"value").
      + exact (insElt insDeqP ``"data" = evalConstT (getDefaultConst (Data lgDataBytes))).
  Defined.

  Definition fetch_request_inv
             (pc: fullType type (SyntaxKind (Bit addrSize)))
             (rf: fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx)))
             (insEmpty: bool) (insElt: type (Vector RqFromProc fifoSize))
             (insDeqP: type (Bit fifoSize)): Prop.
  Proof.
    refine (if insEmpty then True else _).
    refine (_ /\ _ /\ _).
    - exact (insElt insDeqP ``"op" = false).
    - exact (insElt insDeqP ``"addr" = pc).
    - exact (insElt insDeqP ``"data" = evalConstT (getDefaultConst (Data lgDataBytes))).
  Defined.
  Hint Unfold fifo_empty_inv fifo_not_empty_inv mem_request_inv fetch_request_inv: InvDefs.

  Definition procDec_inv (o: RegsT): Prop.
  Proof.
    kexistv "pc"%string pcv o (Bit addrSize).
    kexistv "rf"%string rfv o (Vector (Data lgDataBytes) rfIdx).
    kexistv "memStall"%string stallv o Bool.
    kexistv "fetch"%string fetchv o Bool.
    kexistv "fetched"%string fetchedv o (Data lgDataBytes).
    kexistv "fetchStall"%string fstallv o Bool.
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
    refine (_ \/ _).
    - (* fetch stage *)
      refine (fetchv = true /\ stallv = false /\ (or3 _ _ _)).
      + (* reqInstFetch *)
        exact (fstallv = false /\
               fifo_empty_inv iev ienqpv ideqpv /\
               fifo_empty_inv oev oenqpv odeqpv).
      + (* processLd *)
        refine (_ /\ _).
        * exact (fstallv = true /\
                 fifo_not_empty_inv iev ienqpv ideqpv /\
                 fifo_empty_inv oev oenqpv odeqpv).
        * exact (fetch_request_inv pcv rfv iev ieltv ideqpv).
      + (* repInstFetch *)
        exact (fstallv = true /\
               fifo_empty_inv iev ienqpv ideqpv /\
               fifo_not_empty_inv oev oenqpv odeqpv).
    - (* execute stage *)
      refine (fetchv = false /\ fstallv = false /\ (or3 _ _ _)).
      + (* reqLd/St *)
        exact (stallv = false /\
               fifo_empty_inv iev ienqpv ideqpv /\
               fifo_empty_inv oev oenqpv odeqpv).
      + (* processLd/St *)
        refine (_ /\ _).
        * exact (stallv = true /\
                 fifo_not_empty_inv iev ienqpv ideqpv /\
                 fifo_empty_inv oev oenqpv odeqpv).
        * exact (mem_request_inv fetchedv rfv iev ieltv ideqpv).
      + (* repLd/St *)
        exact (stallv = true /\
               fifo_empty_inv iev ienqpv ideqpv /\
               fifo_not_empty_inv oev oenqpv odeqpv).
  Defined.
  Hint Unfold procDec_inv: InvDefs.

  Ltac procDec_inv_tac :=
    kinv_or3;
    repeat
      match goal with
      | [ |- _ /\ _ ] => split
      | [ |- exists _, _ ] => eexists
      end.

  Lemma procDec_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits (fst pdecInl)) ->
      Multistep (fst pdecInl) init n ll ->
      procDec_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2.

    - kinv_magic_light_with procDec_inv_tac.
      left; repeat split; auto; or3_fst.
      kinv_magic_light_with procDec_inv_tac.

    - kinvert.
      + mred.
      + mred.
      + kinv_magic_light_with kinv_or3.
        left; repeat split; auto; or3_snd.
        kinv_magic_light_with procDec_inv_tac.
      + kinv_magic_light_with kinv_or3.
        right; repeat split; auto; or3_fst.
        kinv_magic_light_with procDec_inv_tac.
      + kinv_magic_light_with kinv_or3.
        right; repeat split; auto; or3_snd.
        kinv_magic_light_with procDec_inv_tac.
        * kinv_finish.
        * kinv_finish.
      + kinv_magic_light_with kinv_or3.
        right; repeat split; auto; or3_snd.
        kinv_magic_light_with procDec_inv_tac.
        * kinv_finish.
        * kinv_finish.
      + kinv_magic_light_with kinv_or3.
        left; repeat split; auto; or3_fst.
        kinv_magic_light_with procDec_inv_tac.
      + kinv_magic_light_with kinv_or3.
        left; repeat split; auto; or3_fst.
        kinv_magic_light_with procDec_inv_tac.
      + kinv_magic_light_with kinv_or3.
        left; repeat split; auto; or3_fst.
        kinv_magic_light_with procDec_inv_tac.
      + kinv_magic_light_with kinv_or3.
        left; repeat split; auto; or3_fst.
        kinv_magic_light_with procDec_inv_tac.
      + kinv_magic_light_with kinv_or3.
        * left; repeat split; auto; or3_thd.
          kinv_magic_light_with procDec_inv_tac.
        * right; repeat split; auto; or3_thd.
          kinv_magic_light_with procDec_inv_tac.
      + kinv_magic_light_with kinv_or3.
        * left; repeat split; auto; or3_thd.
          kinv_magic_light_with procDec_inv_tac.
        * right; repeat split; auto; or3_thd.
          kinv_magic_light_with procDec_inv_tac.

          END_SKIP_PROOF_ON *) admit.
  Qed.

  Lemma procDec_inv_ok:
    forall o,
      reachable o (fst pdecInl) ->
      procDec_inv o.
  Proof.
    intros; inv H; inv H0.
    eapply procDec_inv_ok'; eauto.
  Qed.

End Invariants.

Hint Unfold RqFromProc RsToProc: MethDefs.
Hint Unfold procDec_inv fifo_empty_inv fifo_not_empty_inv
     mem_request_inv fetch_request_inv: InvDefs.

