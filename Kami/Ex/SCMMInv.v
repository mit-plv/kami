Require Import Ascii Bool String List Lia.
Require Import Lib.CommonTactics Lib.Indexer Lib.ilist Lib.Word Lib.Struct Lib.FMap.
Require Import Kami.Syntax Kami.Notations.
Require Import Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Inline Kami.InlineFacts.
Require Import Kami.Wf Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.SCMMInl.

Set Implicit Arguments.

Local Open Scope fmap.

Section Invariants.
  Variables (addrSize maddrSize iaddrSize fifoSize instBytes dataBytes rfIdx: nat)
            (Hdb: {pdb & dataBytes = S pdb}).

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize instBytes dataBytes rfIdx)
            (ammio: AbsMMIO addrSize).

  Definition PgmInitNotMMIO :=
    forall iaddr: word iaddrSize,
      evalExpr (isMMIO _ (evalExpr (toAddr _ iaddr))) = false.

  Definition RqFromProc := MemTypes.RqFromProc dataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc dataBytes.

  Variable (procInit: ProcInit addrSize dataBytes rfIdx)
           (memInit: MemInit maddrSize).
  Hypotheses (HinitRf: evalConstT procInit.(rfInit) $0 = $0)
             (HpgmInit: PgmInitNotMMIO).

  Definition scmmInl :=
    scmmInl Hdb fetch dec exec ammio procInit memInit.

  Definition scmm_inv_rf_zero
             (rfv: fullType type (SyntaxKind (Vector (Data dataBytes) rfIdx))) :=
    rfv $0 = $0.
  #[local] Hint Unfold scmm_inv_rf_zero: InvDefs.

  Definition scmm_inv_pgm_init
             (initv: fullType type (SyntaxKind Bool))
             (ofsv: fullType type (SyntaxKind (Bit iaddrSize)))
             (pgmv: fullType type (SyntaxKind (Vector (Data instBytes) iaddrSize)))
             (memv: fullType type (SyntaxKind (Vector (Bit BitsPerByte) maddrSize))) :=
    initv = false ->
    forall iaddr,
      iaddr < ofsv ->
      pgmv iaddr = evalExpr (alignInst _ (combineBytes dataBytes (evalExpr (toAddr _ iaddr)) memv)).
  #[local] Hint Unfold scmm_inv_pgm_init: InvDefs.
        
  Inductive scmm_inv (o: RegsT) : Prop :=
  | ProcInv:
      forall (pcv: fullType type (SyntaxKind (Pc addrSize)))
             (Hpcv: o@["pc"] = Some (existT _ _ pcv))
             (rfv: fullType type (SyntaxKind (Vector (Data dataBytes) rfIdx)))
             (Hrfv: o@["rf"] = Some (existT _ _ rfv))
             (pinitv: fullType type (SyntaxKind Bool))
             (Hpinitv: o@["pinit"] = Some (existT _ _ pinitv))
             (pinitOfsv: fullType type (SyntaxKind (Bit iaddrSize)))
             (HpinitOfsv: o@["pinitOfs"] = Some (existT _ _ pinitOfsv))
             (pgmv: fullType type (SyntaxKind (Vector (Data instBytes) iaddrSize)))
             (Hpgmv: o@["pgm"] = Some (existT _ _ pgmv))
             (memv: fullType type (SyntaxKind (Vector (Bit BitsPerByte) maddrSize)))
             (Hmemv: o@["mem"] = Some (existT _ _ memv)),
        scmm_inv_rf_zero rfv ->
        scmm_inv_pgm_init pinitv pinitOfsv pgmv memv ->
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

  Lemma wlt_plus_1_back:
    forall {sz} (w1 w2: word sz),
      wnot w2 <> $0 ->
      w1 < w2 ^+ $1 ->
      w1 <> w2 ->
      w1 < w2.
  Proof.
    intros.
    assert (w2 < wones _).
    { apply lt_wlt.
      rewrite wones_pow2_minus_one.
      pose proof (wordToNat_bound w2).
      pose proof (NatLib.pow2_zero sz).
      assert (#w2 = NatLib.pow2 sz - 1 \/ (#w2 < NatLib.pow2 sz - 1)%nat) by lia.
      destruct H4; [|assumption].
      assert (natToWord sz (#w2) = natToWord sz (NatLib.pow2 sz - 1)) by congruence.
      rewrite natToWord_wordToNat, <-wones_natToWord in H5; subst.
      rewrite wnot_ones in H.
      exfalso; auto.
    }
    apply wlt_lt in H0.
    erewrite wordToNat_plusone in H0 by eassumption.
    apply lt_wlt.
    assert (#w1 <> #w2)
      by (intro Hx; elim H1; apply wordToNat_inj; assumption).
    lia.
  Qed.

  Lemma scmm_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits (projT1 scmmInl)) ->
      Multistep (projT1 scmmInl) init n ll ->
      scmm_inv n.
  Proof.
    induction 2.

    - kinv_dest_custom scmm_inv_tac.

      cbn; intros _ iaddr ?.
      exfalso.
      apply wlt_lt in H; rewrite wordToNat_wzero in H.
      lia.

    - kinvert.
      + mred.
      + mred.
      + kinv_dest_custom scmm_inv_tac.
        * exfalso.
          clear -HpgmInit Heqic.
          unfold ilist_to_fun_m in Heqic; simpl in Heqic.
          congruence.
        * intros.
          destruct (weq iaddr x0).
          { rewrite memLoadBytes_combineBytes.
            subst; reflexivity.
          }
          { apply H7.
            apply wlt_plus_1_back; auto.
          }

      + kinv_dest_custom scmm_inv_tac.
        * intros; discriminate.
        * intros; discriminate.
      + kinv_dest_custom scmm_inv_tac.
        * destruct (weq _ _); [exfalso; auto|assumption].
        * intros; discriminate.
        * destruct (weq _ _); [exfalso; auto|assumption].
        * intros; discriminate.
      + kinv_dest_custom scmm_inv_tac.
        * intros; discriminate.
        * intros; discriminate.
      + kinv_dest_custom scmm_inv_tac.
        * intros; discriminate.
        * intros; discriminate.
      + kinv_dest_custom scmm_inv_tac.
        * destruct (weq _ _); [exfalso; auto|assumption].
        * intros; discriminate.
      + kinv_dest_custom scmm_inv_tac.
        intros; discriminate.
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

