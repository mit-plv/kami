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
             (inst: fullType type (SyntaxKind (DecInstK opIdx addrSize lgDataBytes rfIdx)))
             (rf: fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx)))
             (insEmpty: bool) (insElt: type (Vector RqFromProc fifoSize))
             (insDeqP: type (Bit fifoSize)): Prop.
  Proof.
    refine (if insEmpty then True else _).
    refine (_ /\ _ /\ _).
    - refine (_ /\ _ /\ _).
      + exact ((if weq (inst ``"opcode") (evalConstT opLd)
                then false else true) = insElt insDeqP ``"op").
      + exact ((if weq (inst ``"opcode") (evalConstT opSt)
                then true else false) = insElt insDeqP ``"op").
      + exact (inst ``"opcode" = evalConstT opLd -> inst ``"reg" <> (natToWord _ 0)).
    - exact (insElt insDeqP ``"addr" = inst ``"addr").
    - refine (if (insElt insDeqP ``"op") : bool then _ else _).
      + exact (insElt insDeqP ``"data" = inst ``"value").
      + exact (insElt insDeqP ``"data" = evalConstT (getDefaultConst (Data lgDataBytes))).
  Defined.
  Hint Unfold fifo_empty_inv fifo_not_empty_inv mem_request_inv: InvDefs.

  Record procDec_inv (o: RegsT) : Prop :=
    { pcv : fullType type (SyntaxKind (Bit addrSize));
      Hpcv : M.find "pc"%string o = Some (existT _ _ pcv);
      rfv : fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx));
      Hrfv : M.find "rf"%string o = Some (existT _ _ rfv);
      pgmv : fullType type (SyntaxKind (Vector (Data lgDataBytes) addrSize));
      Hpgmv : M.find "pgm"%string o = Some (existT _ _ pgmv);

      stallv : fullType type (SyntaxKind Bool);
      Hstallv : M.find "stall"%string o = Some (existT _ _ stallv);
      iev : fullType type (SyntaxKind Bool);
      Hiev : M.find "rqFromProc"--"empty"%string o = Some (existT _ _ iev);
      ifv : fullType type (SyntaxKind Bool);
      Hifv : M.find "rqFromProc"--"full"%string o = Some (existT _ _ ifv);
      ienqpv : fullType type (SyntaxKind (Bit fifoSize));
      Hienqpv : M.find "rqFromProc"--"enqP"%string o = Some (existT _ _ ienqpv);
      ideqpv : fullType type (SyntaxKind (Bit fifoSize));
      Hideqpv : M.find "rqFromProc"--"deqP"%string o = Some (existT _ _ ideqpv);
      ieltv : fullType type (SyntaxKind (Vector RqFromProc fifoSize));
      Hieltv : M.find "rqFromProc"--"elt"%string o = Some (existT _ _ ieltv);
      oev : fullType type (SyntaxKind Bool);
      Hoev : M.find "rsToProc"--"empty"%string o = Some (existT _ _ oev);
      ofv : fullType type (SyntaxKind Bool);
      Hofv : M.find "rsToProc"--"full"%string o = Some (existT _ _ ofv);
      oenqpv : fullType type (SyntaxKind (Bit fifoSize));
      Hoenqpv : M.find "rsToProc"--"enqP"%string o = Some (existT _ _ oenqpv);
      odeqpv : fullType type (SyntaxKind (Bit fifoSize));
      Hodeqpv : M.find "rsToProc"--"deqP"%string o = Some (existT _ _ odeqpv);
      oeltv : fullType type (SyntaxKind (Vector RsToProc fifoSize));
      Hoeltv : M.find "rsToProc"--"elt"%string o = Some (existT _ _ oeltv);

      Hinv : or3
               (stallv = false /\
                fifo_empty_inv iev ienqpv ideqpv /\
                fifo_empty_inv oev oenqpv odeqpv)
               ((stallv = true /\
                 fifo_not_empty_inv iev ienqpv ideqpv /\
                 fifo_empty_inv oev oenqpv odeqpv) /\
                (mem_request_inv (evalExpr (dec _ rfv (pgmv pcv)))
                                 rfv iev ieltv ideqpv))
               (stallv = true /\
                fifo_empty_inv iev ienqpv ideqpv /\
                fifo_not_empty_inv oev oenqpv odeqpv)
    }.

  Ltac procDec_inv_old :=
    try match goal with
        | [H: procDec_inv _ |- _] => destruct H
        end;
    kinv_red; kinv_or3;
    (* decide the current state by giving contradictions for all other states *)
    kinv_red; kinv_contra.
    
  Ltac procDec_inv_new :=
    econstructor; (* let's prove that the invariant holds for the next state *)
    try (findReify; (reflexivity || eassumption); fail);
    kregmap_clear. (* for improving performance *)

  Ltac procDec_inv_tac := procDec_inv_old; procDec_inv_new.

  Ltac procDec_inv_next ph :=
    match ph with
    | 0 => or3_fst (* intact *)
    | 1 => or3_snd (* requested *)
    | 2 => or3_thd (* responded *)
    end; intuition idtac.

  Lemma procDec_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits (fst pdecInl)) ->
      Multistep (fst pdecInl) init n ll ->
      procDec_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2.

    - kinv_dest_custom procDec_inv_tac.
      procDec_inv_next 0.

    - kinvert.
      + mred.
      + mred.
      + kinv_dest_custom procDec_inv_tac.
        procDec_inv_next 1.
        * kinv_finish.
        * kinv_finish.
        * reflexivity.
      + kinv_dest_custom procDec_inv_tac.
        procDec_inv_next 0.
      + kinv_dest_custom procDec_inv_tac.
        procDec_inv_next 1.
        * kinv_finish.
        * kinv_finish.
        * kinv_finish.
        * reflexivity.
      + kinv_dest_custom procDec_inv_tac.
        procDec_inv_next 0.
      + kinv_dest_custom procDec_inv_tac.
        procDec_inv_next 0.
      + kinv_dest_custom procDec_inv_tac.
        procDec_inv_next 0.
      + kinv_dest_custom procDec_inv_tac.
        procDec_inv_next 0.
      + kinv_dest_custom procDec_inv_tac.
        procDec_inv_next 2.
      + kinv_dest_custom procDec_inv_tac.
        procDec_inv_next 2.

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
Hint Unfold fifo_empty_inv fifo_not_empty_inv mem_request_inv: InvDefs.

Ltac procDec_inv_old :=
  try match goal with
      | [H: procDec_inv _ _ _ _ _ |- _] => destruct H
      end;
  kinv_red; kinv_or3;
  (* decide the current state by giving contradictions for all other states *)
  kinv_red; kinv_contra.
    
