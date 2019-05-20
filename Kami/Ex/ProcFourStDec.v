Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics Kami.ModuleBoundEx.
Require Import Ex.MemTypes Ex.OneEltFifo Ex.NativeFifo Ex.MemAsync.
Require Import Ex.SC Ex.ProcDec Ex.ProcThreeStage Ex.ProcThreeStDec Ex.ProcFDCorrect.
Require Import Eqdep.

Set Implicit Arguments.

Section ProcFDE.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec iaddrSize instBytes dataBytes rfIdx).

  Variable predictNextPc: forall ty, fullType ty (SyntaxKind (Pc iaddrSize)) -> (* pc *)
                                     Expr ty (SyntaxKind (Pc iaddrSize)).

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

  Variable (init: ProcInit iaddrSize dataBytes rfIdx).

  Definition fetchDecode := ProcFetchDecode.fetchDecode
                              fetch dec predictNextPc d2ePack
                              f2dPack f2dRawInst f2dCurPc f2dNextPc f2dEpoch
                              (pcInit init).

  Definition p4st := (fetchDecode
                        ++ regFile (rfInit init)
                        ++ scoreBoard rfIdx
                        ++ oneEltFifo d2eFifoName d2eElt
                        ++ oneEltFifoEx1 w2dFifoName (Pc iaddrSize)
                        ++ (executer exec d2eOpType d2eVal1 d2eVal2
                                     d2eRawInst d2eCurPc e2wPack)
                        ++ epoch
                        ++ oneEltFifo e2wFifoName e2wElt
                        ++ (wb exec d2eOpType d2eDst d2eAddr d2eVal1 d2eRawInst
                               d2eCurPc d2eNextPc d2eEpoch e2wDecInst e2wVal))%kami.

  Definition p3st := ProcThreeStage.p3st
                       fetch dec exec predictNextPc
                       d2ePack d2eOpType d2eDst d2eAddr d2eVal1 d2eVal2
                       d2eRawInst d2eCurPc d2eNextPc d2eEpoch
                       e2wPack e2wDecInst e2wVal init.

  Lemma p4st_refines_p3st: p4st <<== p3st.
  Proof. (* SKIP_PROOF_ON
    kmodular.
    - apply fetchDecode_refines_fetchNDecode; auto.
    - krefl.
      END_SKIP_PROOF_ON *) apply cheat.
  Qed.

End ProcFDE.

