Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics Kami.ModuleBoundEx.
Require Import Ex.MemTypes Ex.OneEltFifo Ex.NativeFifo Ex.MemAsync.
Require Import Ex.SC Ex.ProcDecSC Ex.ProcThreeStage Ex.ProcThreeStDec Ex.ProcFetchDecode.
Require Import Ex.ProcFourStDec.
Require Import Eqdep.

Set Implicit Arguments.

Section ProcFour.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.
  Variable fifoSize: nat.

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec iaddrSize instBytes dataBytes rfIdx)
            (ammio: AbsMMIO addrSize).

  Variable predictNextPc: forall ty, fullType ty (SyntaxKind (Pc iaddrSize)) -> (* pc *)
                                     Expr ty (SyntaxKind (Pc iaddrSize)).

  Variable (procInit: ProcInit iaddrSize dataBytes rfIdx)
           (memInit: MemInit addrSize dataBytes).

  Section AbsFIFO.
    
    (* Abstract d2eElt *)
    Variable (d2eElt: Kind).
    Variable (d2ePack:
                forall ty,
                  Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                  Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                  Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                  Expr ty (SyntaxKind (Data dataBytes)) -> (* val1 *)
                  Expr ty (SyntaxKind (Data dataBytes)) -> (* val2 *)
                  Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                  Expr ty (SyntaxKind (Pc iaddrSize)) -> (* curPc *)
                  Expr ty (SyntaxKind (Pc iaddrSize)) -> (* nextPc *)
                  Expr ty (SyntaxKind Bool) -> (* epoch *)
                  Expr ty (SyntaxKind d2eElt)).
    Variables
      (d2eOpType: forall ty, fullType ty (SyntaxKind d2eElt) ->
                             Expr ty (SyntaxKind (Bit 2)))
      (d2eDst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind (Bit rfIdx)))
      (d2eAddr: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit addrSize)))
      (d2eVal1 d2eVal2: forall ty, fullType ty (SyntaxKind d2eElt) ->
                                   Expr ty (SyntaxKind (Data dataBytes)))
      (d2eRawInst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                              Expr ty (SyntaxKind (Data instBytes)))
      (d2eCurPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                            Expr ty (SyntaxKind (Pc iaddrSize)))
      (d2eNextPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                             Expr ty (SyntaxKind (Pc iaddrSize)))
      (d2eEpoch: forall ty, fullType ty (SyntaxKind d2eElt) ->
                            Expr ty (SyntaxKind Bool)).

    (* Abstract f2dElt *)  
    Variable (f2dElt: Kind).
    Variable (f2dPack:
                forall ty,
                  Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                  Expr ty (SyntaxKind (Pc iaddrSize)) -> (* curPc *)
                  Expr ty (SyntaxKind (Pc iaddrSize)) -> (* nextPc *)
                  Expr ty (SyntaxKind Bool) -> (* epoch *)
                  Expr ty (SyntaxKind f2dElt)).
    Variables
      (f2dRawInst: forall ty, fullType ty (SyntaxKind f2dElt) ->
                              Expr ty (SyntaxKind (Data instBytes)))
      (f2dCurPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                            Expr ty (SyntaxKind (Pc iaddrSize)))
      (f2dNextPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                             Expr ty (SyntaxKind (Pc iaddrSize)))
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
                  Expr ty (SyntaxKind (Data dataBytes)) -> (* execVal *)
                  Expr ty (SyntaxKind e2wElt)).
    Variables
      (e2wDecInst: forall ty, fullType ty (SyntaxKind e2wElt) ->
                              Expr ty (SyntaxKind d2eElt))
      (e2wVal: forall ty, fullType ty (SyntaxKind e2wElt) ->
                          Expr ty (SyntaxKind (Data dataBytes))).

    Definition p4st: Modules :=
      ProcFourStDec.p4st
        fetch dec exec predictNextPc
        d2ePack d2eOpType d2eDst d2eAddr d2eVal1 d2eVal2
        d2eRawInst d2eCurPc d2eNextPc d2eEpoch
        f2dPack f2dRawInst f2dCurPc f2dNextPc f2dEpoch
        e2wPack e2wDecInst e2wVal procInit.

    Definition iom: Modules :=
      MemAsync.iom addrSize fifoSize dataBytes.

    Definition p4stf: Modules :=
      (p4st ++ iom)%kami.

    Definition pinst: Modules :=
      SC.pinst fetch dec exec procInit.

    Definition mm: Modules :=
      SC.mm memInit ammio.

    Definition p4mma: Modules :=
      (p4stf ++ mm)%kami.

    Definition scmm: Modules :=
      SC.scmm fetch dec exec ammio procInit memInit.
    
    Lemma p4stf_refines_pinst: p4stf <<== pinst.
    Proof.
      intros.
      ketrans; [|apply pdec_refines_pinst].
      kmodular.
      - ketrans; [apply p4st_refines_p3st|].
        apply p3st_refines_pdec.
      - krefl.
    Qed.

    Lemma p4mma_correct: p4mma <<== scmm.
    Proof.
      intros.
      kmodular.
      - apply p4stf_refines_pinst.
      - krefl.
    Qed.

  End AbsFIFO.

  Definition p4mm: Modules :=
    p4mma
      (@d2ePackI _ _ _ _ _) (@d2eOpTypeI _ _ _ _ _) (@d2eDstI _ _ _ _ _) (@d2eAddrI _ _ _ _ _)
      (@d2eVal1I _ _ _ _ _) (@d2eVal2I _ _ _ _ _) (@d2eRawInstI _ _ _ _ _) (@d2eCurPcI _ _ _ _ _)
      (@d2eNextPcI _ _ _ _ _) (@d2eEpochI _ _ _ _ _)
      (@f2dPackI _ _) (@f2dRawInstI _ _) (@f2dCurPcI _ _)
      (@f2dNextPcI _ _) (@f2dEpochI _ _)
      (@e2wPackI _ _ _ _ _) (@e2wDecInstI _ _ _ _ _) (@e2wValI _ _ _ _ _).

  Theorem p4mm_correct: p4mm <<== scmm.
  Proof.
    intros; apply p4mma_correct.
  Qed.

End ProcFour.

