Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StructNotation Lib.StringBound Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics Kami.ModuleBoundEx.
Require Import Ex.MemTypes Ex.NativeFifo Ex.MemAtomic.
Require Import Ex.SC Ex.ProcDec Ex.ProcTwoStage Ex.ProcTwoStDec Ex.ProcFDCorrect.
Require Import Eqdep.

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
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* val *)
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
    (d2eVal: forall ty, fullType ty (SyntaxKind d2eElt) ->
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
  
  Definition fetchDecode := ProcFetchDecode.fetchDecode
                              getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                              getStAddr getStSrc calcStAddr getStVSrc
                              getSrc1 predictNextPc d2ePack
                              f2dPack f2dRawInst f2dCurPc f2dNextPc f2dEpoch.
  Definition p3st := (fetchDecode
                        ++ regFile lgDataBytes rfIdx
                        ++ scoreBoard rfIdx
                        ++ oneEltFifo d2eFifoName d2eElt
                        ++ oneEltFifoEx1 e2dFifoName (Bit addrSize)
                        ++ (executer "rqFromProc"%string "rsToProc"%string
                                     getSrc1 getSrc2 getDst exec getNextPc
                                     d2eOpType d2eDst d2eAddr d2eVal
                                     d2eRawInst d2eCurPc d2eNextPc d2eEpoch))%kami.

  Definition p2st := ProcTwoStage.p2st getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                       getStAddr getStSrc calcStAddr getStVSrc
                                       getSrc1 getSrc2 getDst exec getNextPc predictNextPc
                                       d2ePack d2eOpType d2eDst d2eAddr d2eVal
                                       d2eRawInst d2eCurPc d2eNextPc d2eEpoch.

  Lemma p3st_refines_p2st: p3st <<== p2st.
  Proof. (* SKIP_PROOF_ON
    kmodular.
    - kdisj_edms_cms_ex O.
    - kdisj_ecms_dms_ex O.
    - apply fetchDecode_refines_fetchNDecode.
    - krefl.
      END_SKIP_PROOF_ON *) admit.
  Qed.

End ProcFDE.

