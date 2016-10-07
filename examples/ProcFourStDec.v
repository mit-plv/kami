Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics Kami.ModuleBoundEx.
Require Import Ex.MemTypes Ex.NativeFifo Ex.MemAtomic.
Require Import Ex.SC Ex.ProcDec Ex.ProcThreeStage Ex.ProcThreeStDec Ex.ProcFDCorrect.
Require Import Eqdep.

Set Implicit Arguments.

Section ProcFDE.
  Variables addrSize lgDataBytes rfIdx: nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT lgDataBytes)
            (getLdDst: LdDstT lgDataBytes rfIdx)
            (getLdAddr: LdAddrT addrSize lgDataBytes)
            (getLdSrc: LdSrcT lgDataBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize lgDataBytes)
            (getStAddr: StAddrT addrSize lgDataBytes)
            (getStSrc: StSrcT lgDataBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize lgDataBytes)
            (getStVSrc: StVSrcT lgDataBytes rfIdx)
            (getSrc1: Src1T lgDataBytes rfIdx)
            (getSrc2: Src2T lgDataBytes rfIdx)
            (getDst: DstT lgDataBytes rfIdx)
            (exec: ExecT addrSize lgDataBytes)
            (getNextPc: NextPcT addrSize lgDataBytes rfIdx)
            (predictNextPc: forall ty, fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                       Expr ty (SyntaxKind (Bit addrSize))).

  (* Abstract d2eElt *)
  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* val1 *)
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* val2 *)
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* nextPc *)
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
                                 Expr ty (SyntaxKind (Data lgDataBytes)))
    (d2eRawInst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                            Expr ty (SyntaxKind (Data lgDataBytes)))
    (d2eCurPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind (Bit addrSize)))
    (d2eNextPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit addrSize)))
    (d2eEpoch: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind Bool)).

  (* Abstract f2dElt *)  
  Variable (f2dElt: Kind).
  Variable (f2dPack:
              forall ty,
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind f2dElt)).
  Variables
    (f2dRawInst: forall ty, fullType ty (SyntaxKind f2dElt) ->
                            Expr ty (SyntaxKind (Data lgDataBytes)))
    (f2dCurPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind (Bit addrSize)))
    (f2dNextPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                           Expr ty (SyntaxKind (Bit addrSize)))
    (f2dEpoch: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind Bool)).

  (* Abstract e2wElt *)  
  Variable (e2wElt: Kind).
  Variable (e2wPack:
              forall ty,
                Expr ty (SyntaxKind d2eElt) -> (* decInst *)
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* execVal *)
                Expr ty (SyntaxKind e2wElt)).
  Variables
    (e2wDecInst: forall ty, fullType ty (SyntaxKind e2wElt) ->
                            Expr ty (SyntaxKind d2eElt))
    (e2wVal: forall ty, fullType ty (SyntaxKind e2wElt) ->
                        Expr ty (SyntaxKind (Data lgDataBytes))).

  Definition fetchDecode := ProcFetchDecode.fetchDecode
                              getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                              getStAddr getStSrc calcStAddr getStVSrc
                              getSrc1 getSrc2 getDst predictNextPc d2ePack
                              f2dPack f2dRawInst f2dCurPc f2dNextPc f2dEpoch.

  Definition p4st := (fetchDecode
                        ++ regFile lgDataBytes rfIdx
                        ++ scoreBoard rfIdx
                        ++ oneEltFifo d2eFifoName d2eElt
                        ++ oneEltFifoEx1 w2dFifoName (Bit addrSize)
                        ++ (executer rfIdx exec d2eOpType d2eVal1 d2eVal2
                                     d2eRawInst d2eCurPc e2wPack)
                        ++ epoch
                        ++ oneEltFifo e2wFifoName e2wElt
                        ++ (wb "rqFromProc"%string "rsToProc"%string
                               getNextPc d2eOpType d2eDst d2eAddr d2eVal1 d2eRawInst
                               d2eCurPc d2eNextPc d2eEpoch e2wDecInst e2wVal))%kami.

  Definition p3st := ProcThreeStage.p3st getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                         getStAddr getStSrc calcStAddr getStVSrc
                                         getSrc1 getSrc2 getDst exec getNextPc predictNextPc
                                         d2ePack d2eOpType d2eDst d2eAddr d2eVal1 d2eVal2
                                         d2eRawInst d2eCurPc d2eNextPc d2eEpoch
                                         e2wPack e2wDecInst e2wVal.

  Lemma p4st_refines_p3st: p4st <<== p3st.
  Proof. (* SKIP_PROOF_ON
    kmodular.
    - kdisj_edms_cms_ex O.
    - kdisj_ecms_dms_ex O.
    - apply fetchDecode_refines_fetchNDecode.
    - krefl.
      END_SKIP_PROOF_ON *) apply cheat.
  Qed.

End ProcFDE.

