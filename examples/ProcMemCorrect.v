Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Specialize Kami.Tactics Kami.Duplicate Kami.ParamDup Kami.ModuleBoundEx.
Require Import Ex.SC Ex.ProcDec Ex.MemAtomic Ex.MemCache Ex.MemCacheSubst Ex.L1Cache.
Require Import Ex.FifoCorrect Ex.MemCorrect Ex.ProcDecSCN Kami.ParametricSyntax.
Require Import Ex.ProcFetchDecode Ex.ProcThreeStage Ex.ProcThreeStDec Ex.ProcFourStDec.

Set Implicit Arguments.

Section ProcMem.
  Variable FifoSize: nat. (* fifo *)
  Variables OpIdx RfIdx IAddrSize: nat. (* processor *)
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat. (* memory *)
  Variable Id: Kind.

  Definition AddrSize := L1Cache.AddrBits IdxBits TagBits LgNumDatas.
  Hint Unfold AddrSize: MethDefs.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT LgDataBytes)
            (getLdDst: LdDstT LgDataBytes RfIdx)
            (getLdAddr: LdAddrT AddrSize LgDataBytes)
            (getLdSrc: LdSrcT LgDataBytes RfIdx)
            (calcLdAddr: LdAddrCalcT AddrSize LgDataBytes)
            (getStAddr: StAddrT AddrSize LgDataBytes)
            (getStSrc: StSrcT LgDataBytes RfIdx)
            (calcStAddr: StAddrCalcT AddrSize LgDataBytes)
            (getStVSrc: StVSrcT LgDataBytes RfIdx)
            (getSrc1: Src1T LgDataBytes RfIdx)
            (getSrc2: Src2T LgDataBytes RfIdx)
            (getDst: DstT LgDataBytes RfIdx)
            (exec: ExecT AddrSize LgDataBytes)
            (getNextPc: NextPcT AddrSize LgDataBytes RfIdx)
            (alignPc: AlignPcT AddrSize IAddrSize)
            (predictNextPc: forall ty, fullType ty (SyntaxKind (Bit AddrSize)) -> (* pc *)
                                       Expr ty (SyntaxKind (Bit AddrSize))).

  Variable LgNumChildren: nat.
  Definition numChildren := (wordToNat (wones LgNumChildren)).

  Definition pdecN := pdecs getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                            getStAddr getStSrc calcStAddr getStVSrc
                            getSrc1 getSrc2 getDst exec getNextPc alignPc numChildren.
  Definition pmFifos :=
    modFromMeta
      ((fifoRqFromProc IdxBits TagBits LgNumDatas LgDataBytes (rsz FifoSize) LgNumChildren)
         +++ (fifoRsToProc LgDataBytes (rsz FifoSize) LgNumChildren)).
    
  Definition mcache := memCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize LgNumChildren.
  Definition scN := sc getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                       getStAddr getStSrc calcStAddr getStVSrc
                       getSrc1 getSrc2 getDst exec getNextPc alignPc numChildren.

  Lemma dropFirstElts_Interacting:
    Interacting pmFifos (modFromMeta mcache) (dropFirstElts LgNumChildren).
  Proof.
    repeat split; intros; apply dropFirstElts_Some.
    - exfalso; clear -H.
      unfold pmFifos in H; apply getCalls_modFromMeta_app in H.
      apply in_app_or in H; destruct H.
      + unfold modFromMeta, getCalls in H; simpl in H.
        rewrite app_nil_r in H; repeat rewrite getCallsM_app in H.
        repeat (apply in_app_or in H; destruct H);
          induction (wordToNat (wones LgNumChildren)); intuition.
      + unfold modFromMeta, getCalls in H; simpl in H.
        rewrite app_nil_r in H; repeat rewrite getCallsM_app in H.
        repeat (apply in_app_or in H; destruct H);
          induction (wordToNat (wones LgNumChildren)); intuition.
    - intro Hx; elim H0; clear H0.
      do 4 (apply getCalls_modFromMeta_app, in_or_app; left).
      unfold modFromMeta, getCalls; simpl.
      rewrite !app_nil_r; rewrite getCallsR_app.
      apply in_or_app; left.
      induction (wordToNat (wones LgNumChildren)).
      + left; inv Hx; intuition.
      + inv Hx.
        * clear IHn; simpl in *; left; auto.
        * do 3 right; simpl in *; apply IHn; auto.
    - intro Hx; elim H0; clear -Hx.
      unfold pmFifos; rewrite getDefs_modFromMeta_app.
      apply in_or_app; left.
      unfold modFromMeta, getDefs; simpl.
      repeat rewrite app_nil_r; repeat rewrite namesOf_app.
      do 2 (apply in_or_app; right).
      induction (wordToNat (wones LgNumChildren)); auto.
      inv Hx; [simpl; auto|right; apply IHn; auto].
    - clear -H.
      unfold mcache, memCache, MemCache.memCache, l1C, l1 in H.
      repeat (rewrite getDefs_modFromMeta_app in H;
              apply in_app_or in H; destruct H); auto;
        try (intro Hx;
             apply firstElts_SubList with
             (IdxBits:= IdxBits) (TagBits:= TagBits) (LgNumDatas:= LgNumDatas)
                                 (LgDataBytes:= LgDataBytes) (FifoSize:= FifoSize) in Hx;
             generalize dependent k; eapply DisjList_logic_inv; kdisj_dms).
  Qed.

  Theorem pdecN_mcache_refines_scN: (pdecN ++ pmFifos ++ modFromMeta mcache)%kami <<== scN.
  Proof. (* SKIP_PROOF_ON
    ketrans; [|apply pdecN_memAtomic_refines_scN with (fifoSize:= rsz FifoSize); auto].

    kmodular.
    - kdisj_edms_cms_ex numChildren.
    - kdisj_ecms_dms_ex numChildren.
    - krefl.
    - ketrans; [|apply ios_memAtomicWoQ_memAtomic].
      kmodular with (dropFirstElts LgNumChildren).
      + kdisj_edms_cms_ex (wordToNat (wones LgNumChildren)).
      + kdisj_ecms_dms_ex (wordToNat (wones LgNumChildren)).
      + apply dropFirstElts_Interacting.
      + ketrans_r; [apply modFromMeta_comm_1|].
        ketrans_l; [|apply duplicate_concatMod_comm_2; auto; [kvr|kvr|kequiv|kequiv]].
        replace (dropFirstElts LgNumChildren) with
        (compLabelMaps (dropFirstElts LgNumChildren) (@idElementwise _))
          by apply compLabelMaps_id_right.

        kmodularnp.
        * unfold dropFirstElts; rewrite dropN_dropPs.
          rewrite <-dropPs_nil_idElementwise.
          apply dropPs_disj.
          { apply DisjList_nil_2. }
          { eapply DisjList_SubList; [apply getExtMeths_meths|].
            apply DisjList_comm.
            apply DisjList_SubList with
            (l1:= getDefs (modFromMeta (fifoRqFromProc
                                          IdxBits TagBits LgNumDatas
                                          LgDataBytes (rsz FifoSize) LgNumChildren)));
              [apply firstElts_SubList|].
            apply DisjList_comm, DisjList_app_4.
            { kdisj_dms. }
            { kdisj_cms_dms. }
          }
        * ketrans_r; [apply sinModule_duplicate_1;
                      [kequiv|kvr|knodup_regs|apply fifoS_const_regs]|].
          apply duplicate_traceRefines_drop; auto; [kequiv|kvr| |].
          { vm_compute; tauto. }
          { rewrite <-Fifo.fifo_fifoS.
            apply fifo_refines_sfifo.
          }
        * apply sinModule_duplicate_1; [kequiv|kvr|knodup_regs|].
          apply fifoS_const_regs.
          
      + apply memCache_refines_memAtomic.
        
        END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  (* Abstract d2eElt *)
  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit RfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit AddrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Data LgDataBytes)) -> (* val1 *)
                Expr ty (SyntaxKind (Data LgDataBytes)) -> (* val2 *)
                Expr ty (SyntaxKind (Data LgDataBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Bit AddrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Bit AddrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind d2eElt)).
  Variables
    (d2eOpType: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit 2)))
    (d2eDst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                        Expr ty (SyntaxKind (Bit RfIdx)))
    (d2eAddr: forall ty, fullType ty (SyntaxKind d2eElt) ->
                         Expr ty (SyntaxKind (Bit AddrSize)))
    (d2eVal1 d2eVal2: forall ty, fullType ty (SyntaxKind d2eElt) ->
                                 Expr ty (SyntaxKind (Data LgDataBytes)))
    (d2eRawInst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                            Expr ty (SyntaxKind (Data LgDataBytes)))
    (d2eCurPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind (Bit AddrSize)))
    (d2eNextPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit AddrSize)))
    (d2eEpoch: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind Bool)).

  Hypotheses
    (Hd2eOpType: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eOpType _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr opType)
    (Hd2eDst: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eDst _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr dst)
    (Hd2eAddr: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eAddr _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr addr)
    (Hd2eVal1: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eVal1 _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr val1)
    (Hd2eVal2: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eVal2 _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr val2)
    (Hd2eRawInst: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eRawInst _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr rawInst)
    (Hd2eCurPc: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eCurPc _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr curPc)
    (Hd2eNextPc: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eNextPc _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr nextPc)
    (Hd2eEpoch: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eEpoch _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr epoch).

  (* Abstract f2dElt *)  
  Variable (f2dElt: Kind).
  Variable (f2dPack:
              forall ty,
                Expr ty (SyntaxKind (Data LgDataBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Bit AddrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Bit AddrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind f2dElt)).
  Variables
    (f2dRawInst: forall ty, fullType ty (SyntaxKind f2dElt) ->
                            Expr ty (SyntaxKind (Data LgDataBytes)))
    (f2dCurPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind (Bit AddrSize)))
    (f2dNextPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                           Expr ty (SyntaxKind (Bit AddrSize)))
    (f2dEpoch: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind Bool)).

  Hypotheses (Hf2dRawInst: forall rawInst curPc nextPc epoch,
                 evalExpr (f2dRawInst _ (evalExpr (f2dPack rawInst curPc nextPc epoch))) =
                 evalExpr rawInst)
             (Hf2dCurPc: forall rawInst curPc nextPc epoch,
                 evalExpr (f2dCurPc _ (evalExpr (f2dPack rawInst curPc nextPc epoch))) =
                 evalExpr curPc)
             (Hf2dNextPc: forall rawInst curPc nextPc epoch,
                 evalExpr (f2dNextPc _ (evalExpr (f2dPack rawInst curPc nextPc epoch))) =
                 evalExpr nextPc)
             (Hf2dEpoch: forall rawInst curPc nextPc epoch,
                 evalExpr (f2dEpoch _ (evalExpr (f2dPack rawInst curPc nextPc epoch))) =
                 evalExpr epoch).

  (* Abstract e2wElt *)  
  Variable (e2wElt: Kind).
  Variable (e2wPack:
              forall ty,
                Expr ty (SyntaxKind d2eElt) -> (* decInst *)
                Expr ty (SyntaxKind (Data LgDataBytes)) -> (* execVal *)
                Expr ty (SyntaxKind e2wElt)).
  Variables
    (e2wDecInst: forall ty, fullType ty (SyntaxKind e2wElt) ->
                            Expr ty (SyntaxKind d2eElt))
    (e2wVal: forall ty, fullType ty (SyntaxKind e2wElt) ->
                        Expr ty (SyntaxKind (Data LgDataBytes))).

  Hypotheses
    (He2wDecInst: forall decInst val,
        evalExpr (e2wDecInst _ (evalExpr (e2wPack decInst val))) = evalExpr decInst)
    (He2wVal: forall decInst val,
        evalExpr (e2wVal _ (evalExpr (e2wPack decInst val))) = evalExpr val).

  Definition p4stN := duplicate
                        (p4st getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                              getStAddr getStSrc calcStAddr getStVSrc
                              getSrc1 getSrc2 getDst exec getNextPc alignPc predictNextPc
                              d2ePack d2eOpType d2eDst d2eAddr d2eVal1 d2eVal2
                              d2eRawInst d2eCurPc d2eNextPc d2eEpoch
                              f2dPack f2dRawInst f2dCurPc f2dNextPc f2dEpoch
                              e2wPack e2wDecInst e2wVal) numChildren.

  Theorem p4stN_mcache_refines_scN: (p4stN ++ pmFifos ++ modFromMeta mcache)%kami <<== scN.
  Proof. (* SKIP_PROOF_ON
    ketrans; [|apply pdecN_mcache_refines_scN].
    kmodular.
    - kdisj_edms_cms_ex numChildren.
    - kdisj_ecms_dms_ex numChildren.
    - kduplicated.
      ketrans.
      + apply p4st_refines_p3st; auto.
      + apply p3st_refines_pdec; auto.
    - krefl.
      END_SKIP_PROOF_ON *) apply cheat.
  Qed.

End ProcMem.

