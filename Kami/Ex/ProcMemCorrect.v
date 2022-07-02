Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics Kami.ModuleBoundEx.
Require Import Ex.MemTypes Ex.MemAsync.
Require Import Ex.SC Ex.ProcDecSC Ex.ProcThreeStage Ex.ProcThreeStDec Ex.ProcFetchDecode.
Require Import Ex.ProcFourStDec.
Require Import Eqdep.

Set Implicit Arguments.

Section ProcFour.
  Variables (addrSize maddrSize iaddrSize instBytes dataBytes rfIdx: nat)
            (Hdb: {pdb & dataBytes = S pdb}).
  Variable fifoSize: nat.

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize instBytes dataBytes rfIdx)
            (ammio: AbsMMIO addrSize).

  Context {indexSize tagSize: nat}.
  Variables (getIndex: forall ty, fullType ty (SyntaxKind (Bit addrSize)) ->
                                  Expr ty (SyntaxKind (Bit indexSize)))
            (getTag: forall ty, fullType ty (SyntaxKind (Bit addrSize)) ->
                                Expr ty (SyntaxKind (Bit tagSize))).

  Variable (procInit: ProcInit addrSize dataBytes rfIdx)
           (memInit: MemInit maddrSize).

  Section AbsPipeline.

    (* Abstract f2dElt *)  
    Variable (f2dElt: Kind).
    Variable (f2dPack:
                forall ty,
                  Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                  Expr ty (SyntaxKind (Pc addrSize)) -> (* curPc *)
                  Expr ty (SyntaxKind (Pc addrSize)) -> (* nextPc *)
                  Expr ty (SyntaxKind Bool) -> (* epoch *)
                  Expr ty (SyntaxKind f2dElt)).
    Variables
      (f2dRawInst: forall ty, fullType ty (SyntaxKind f2dElt) ->
                              Expr ty (SyntaxKind (Data instBytes)))
      (f2dCurPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                            Expr ty (SyntaxKind (Pc addrSize)))
      (f2dNextPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                             Expr ty (SyntaxKind (Pc addrSize)))
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

    Hypothesis
      (Hf2dpackExt:
         forall rawInst1 curPc1 nextPc1 epoch1 rawInst2 curPc2 nextPc2 epoch2,
           evalExpr rawInst1 = evalExpr rawInst2 ->
           evalExpr curPc1 = evalExpr curPc2 ->
           evalExpr nextPc1 = evalExpr nextPc2 ->
           evalExpr epoch1 = evalExpr epoch2 ->
           evalExpr (f2dPack rawInst1 curPc1 nextPc1 epoch1) =
           evalExpr (f2dPack rawInst2 curPc2 nextPc2 epoch2)).

    (* Abstract d2eElt *)
    Variable (d2eElt: Kind).
    Variable (d2ePack:
                forall ty,
                  Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                  Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                  Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                  Expr ty (SyntaxKind (Array Bool dataBytes)) -> (* byteEn *)
                  Expr ty (SyntaxKind (Data dataBytes)) -> (* val1 *)
                  Expr ty (SyntaxKind (Data dataBytes)) -> (* val2 *)
                  Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                  Expr ty (SyntaxKind (Pc addrSize)) -> (* curPc *)
                  Expr ty (SyntaxKind (Pc addrSize)) -> (* nextPc *)
                  Expr ty (SyntaxKind Bool) -> (* epoch *)
                  Expr ty (SyntaxKind d2eElt)).
    Variables
      (d2eOpType: forall ty, fullType ty (SyntaxKind d2eElt) ->
                             Expr ty (SyntaxKind (Bit 2)))
      (d2eDst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind (Bit rfIdx)))
      (d2eAddr: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit addrSize)))
      (d2eByteEn: forall ty, fullType ty (SyntaxKind d2eElt) ->
                             Expr ty (SyntaxKind (Array Bool dataBytes)))
      (d2eVal1 d2eVal2: forall ty, fullType ty (SyntaxKind d2eElt) ->
                                   Expr ty (SyntaxKind (Data dataBytes)))
      (d2eRawInst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                              Expr ty (SyntaxKind (Data instBytes)))
      (d2eCurPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                            Expr ty (SyntaxKind (Pc addrSize)))
      (d2eNextPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                             Expr ty (SyntaxKind (Pc addrSize)))
      (d2eEpoch: forall ty, fullType ty (SyntaxKind d2eElt) ->
                            Expr ty (SyntaxKind Bool)).

  Hypotheses
    (Hd2eOpType: forall opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eOpType _ (evalExpr (d2ePack opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch))) = evalExpr opType)
    (Hd2eDst: forall opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eDst _ (evalExpr (d2ePack opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch))) = evalExpr dst)
    (Hd2eAddr: forall opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eAddr _ (evalExpr (d2ePack opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch))) = evalExpr addr)
    (Hd2eByteEn: forall opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eByteEn _ (evalExpr (d2ePack opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch))) = evalExpr byteEn)
    (Hd2eVal1: forall opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eVal1 _ (evalExpr (d2ePack opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch))) = evalExpr val1)
    (Hd2eVal2: forall opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eVal2 _ (evalExpr (d2ePack opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch))) = evalExpr val2)
    (Hd2eRawInst: forall opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eRawInst _ (evalExpr (d2ePack opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch))) = evalExpr rawInst)
    (Hd2eCurPc: forall opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eCurPc _ (evalExpr (d2ePack opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch))) = evalExpr curPc)
    (Hd2eNextPc: forall opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eNextPc _ (evalExpr (d2ePack opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch))) = evalExpr nextPc)
    (Hd2eEpoch: forall opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eEpoch _ (evalExpr (d2ePack opType dst addr byteEn val1 val2 rawInst curPc nextPc epoch))) = evalExpr epoch).
    
    (* Abstract e2wElt *)  
    Variable (e2wElt: Kind).
    Variable (e2wPack:
                forall ty,
                  Expr ty (SyntaxKind d2eElt) -> (* decInst *)
                  Expr ty (SyntaxKind (Data dataBytes)) -> (* execVal *)
                  Expr ty (SyntaxKind e2wElt)).
    Variables
      (e2wDecInst: forall ty, fullType ty (SyntaxKind e2wElt) ->
                              Expr ty (SyntaxKind d2eElt))
      (e2wVal: forall ty, fullType ty (SyntaxKind e2wElt) ->
                          Expr ty (SyntaxKind (Data dataBytes))).

    Hypotheses
      (He2wDecInst: forall decInst val,
          evalExpr (e2wDecInst _ (evalExpr (e2wPack decInst val))) = evalExpr decInst)
      (He2wVal: forall decInst val,
          evalExpr (e2wVal _ (evalExpr (e2wPack decInst val))) = evalExpr val).

    Definition p4st: Modules :=
      ProcFourStDec.p4st
        fetch dec exec getIndex getTag
        f2dPack f2dRawInst f2dCurPc f2dNextPc f2dEpoch
        d2ePack d2eOpType d2eDst d2eAddr d2eByteEn d2eVal1 d2eVal2
        d2eRawInst d2eCurPc d2eNextPc d2eEpoch
        e2wPack e2wDecInst e2wVal procInit.

    Definition iom: Modules :=
      MemAsync.iom addrSize dataBytes.

    Definition p4stf: Modules :=
      (p4st ++ iom)%kami.

    Definition pinst: Modules :=
      SC.pinst fetch dec exec procInit.

    Definition mm: Modules :=
      SC.mm Hdb memInit ammio.

    Definition p4mma: Modules :=
      (p4stf ++ mm)%kami.

    Definition scmm: Modules :=
      SC.scmm Hdb fetch dec exec ammio procInit memInit.
    
    Lemma p4stf_refines_pinst: p4stf <<== pinst.
    Proof.
      intros.
      ketrans; [|apply pdec_refines_pinst].
      kmodular.
      - ketrans; [apply p4st_refines_p3st; auto|].
        apply p3st_refines_pdec; auto.
      - krefl.
    Qed.

    Lemma p4mma_correct: p4mma <<== scmm.
    Proof.
      intros.
      kmodular.
      - apply p4stf_refines_pinst.
      - krefl.
    Qed.

  End AbsPipeline.

  Definition p4mm: Modules :=
    p4mma
      (@f2dPackI _ _) (@f2dRawInstI _ _) (@f2dCurPcI _ _)
      (@f2dNextPcI _ _) (@f2dEpochI _ _)
      (@d2ePackI _ _ _ _ _) (@d2eOpTypeI _ _ _ _ _) (@d2eDstI _ _ _ _ _) (@d2eAddrI _ _ _ _ _)
      (@d2eByteEnI _ _ _ _ _) (@d2eVal1I _ _ _ _ _) (@d2eVal2I _ _ _ _ _)
      (@d2eRawInstI _ _ _ _ _) (@d2eCurPcI _ _ _ _ _) (@d2eNextPcI _ _ _ _ _)
      (@d2eEpochI _ _ _ _ _) (@e2wPackI _ _ _ _ _) (@e2wDecInstI _ _ _ _ _) (@e2wValI _ _ _ _ _).

  Theorem p4mm_correct: p4mm <<== scmm.
  Proof.  (* SKIP_PROOF_ON
    intros; apply p4mma_correct; auto.
    intros.
    simpl; unfold ilist_to_fun_m; simpl.
    rewrite H, H0, H1, H2.
    reflexivity.
    END_SKIP_PROOF_ON *) apply cheat.
  Qed.

End ProcFour.

Goal True. idtac "Print Assumptions p4mm_correct:". Abort.
Print Assumptions p4mm_correct.
