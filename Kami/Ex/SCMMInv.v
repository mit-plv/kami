Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.Indexer Lib.ilist Lib.Word Lib.Struct Lib.FMap.
Require Import Kami.Syntax Kami.Notations.
Require Import Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Inline Kami.InlineFacts.
Require Import Kami.Wf Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.SCMMInl.

Set Implicit Arguments.

Local Open Scope fmap.

Section Invariants.

  Variables addrSize iaddrSize fifoSize instBytes dataBytes rfIdx: nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT instBytes)
            (getLdDst: LdDstT instBytes rfIdx)
            (getLdAddr: LdAddrT addrSize instBytes)
            (getLdSrc: LdSrcT instBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize dataBytes)
            (getStAddr: StAddrT addrSize instBytes)
            (getStSrc: StSrcT instBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize dataBytes)
            (getStVSrc: StVSrcT instBytes rfIdx)
            (getSrc1: Src1T instBytes rfIdx)
            (getSrc2: Src2T instBytes rfIdx)
            (getDst: DstT instBytes rfIdx)
            (exec: ExecT iaddrSize instBytes dataBytes)
            (getNextPc: NextPcT iaddrSize instBytes dataBytes rfIdx)
            (alignInst: AlignInstT instBytes dataBytes)
            (isMMIO: IsMMIOT addrSize).

  Definition RqFromProc := MemTypes.RqFromProc dataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc dataBytes.

  Variable (init: ProcInit iaddrSize dataBytes rfIdx).
  Hypothesis (HinitRf: evalConstT init.(rfInit) $0 = $0).

  Definition scmmInl :=
    scmmInl getOptype getLdDst getLdAddr getLdSrc calcLdAddr
            getStAddr getStSrc calcStAddr getStVSrc
            getSrc1 getSrc2 getDst exec getNextPc alignInst isMMIO
            init.

  Definition scmm_inv_rf_zero
             (rfv: fullType type (SyntaxKind (Vector (Data dataBytes) rfIdx))) :=
    rfv $0 = $0.
  Hint Unfold scmm_inv_rf_zero: InvDefs.

  Inductive scmm_inv (o: RegsT) : Prop :=
  | ProcInv:
      forall
        (pcv: fullType type (SyntaxKind (Pc iaddrSize)))
        (Hpcv: o@["pc"] = Some (existT _ _ pcv))
        (rfv: fullType type (SyntaxKind (Vector (Data dataBytes) rfIdx)))
        (Hrfv: o@["rf"] = Some (existT _ _ rfv))
        (pinitv: fullType type (SyntaxKind Bool))
        (Hpinitv: o@["pinit"] = Some (existT _ _ pinitv))
        (pinitOfsv: fullType type (SyntaxKind (Bit iaddrSize)))
        (HpinitOfsv: o@["pinitOfs"] = Some (existT _ _ pinitOfsv))
        (pgmv: fullType type (SyntaxKind (Vector (Data instBytes) iaddrSize)))
        (Hpgmv: o@["pgm"] = Some (existT _ _ pgmv)),
        scmm_inv_rf_zero rfv ->
        scmm_inv o.

  Ltac scmm_inv_old :=
    try match goal with
        | [H: scmm_inv _ |- _] => destruct H
        end;
    kinv_red.
  
  Ltac scmm_inv_new :=
    try econstructor;
    try (try findReify; (reflexivity || eassumption); fail);
    kregmap_clear.

  Ltac scmm_inv_tac := scmm_inv_old; scmm_inv_new.
  
  Lemma scmm_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits (projT1 scmmInl)) ->
      Multistep (projT1 scmmInl) init n ll ->
      scmm_inv n.
  Proof.
    induction 2.

    - kinv_dest_custom scmm_inv_tac.

    - kinvert.
      + mred.
      + mred.
      + kinv_dest_custom scmm_inv_tac.
      + kinv_dest_custom scmm_inv_tac.
      + kinv_dest_custom scmm_inv_tac.
        * destruct (weq _ _); [exfalso; auto|assumption].
        * destruct (weq _ _); [exfalso; auto|assumption].
      + kinv_dest_custom scmm_inv_tac.
      + kinv_dest_custom scmm_inv_tac.
      + kinv_dest_custom scmm_inv_tac.
        destruct (weq _ _); [exfalso; auto|assumption].
      + kinv_dest_custom scmm_inv_tac.
  Qed.

  Lemma scmm_inv_ok:
    forall o,
      reachable o (projT1 scmmInl) ->
      scmm_inv o.
  Proof.
    intros; inv H; inv H0.
    eapply scmm_inv_ok'; eauto.
  Qed.
  
End Invariants.

