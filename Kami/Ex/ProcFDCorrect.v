Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics.
Require Import Ex.MemTypes Ex.NativeFifo Ex.MemAtomic.
Require Import Ex.SC Ex.ProcDec Ex.ProcThreeStage Ex.ProcFetchDecode Ex.ProcFDInl Ex.ProcFDInv.
Require Import Eqdep.

Set Implicit Arguments.

Section FetchDecode.
  Variables addrSize iaddrSize dataBytes rfIdx: nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT dataBytes)
            (getLdDst: LdDstT dataBytes rfIdx)
            (getLdAddr: LdAddrT addrSize dataBytes)
            (getLdSrc: LdSrcT dataBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize dataBytes)
            (getStAddr: StAddrT addrSize dataBytes)
            (getStSrc: StSrcT dataBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize dataBytes)
            (getStVSrc: StVSrcT dataBytes rfIdx)
            (getSrc1: Src1T dataBytes rfIdx)
            (getSrc2: Src2T dataBytes rfIdx)
            (getDst: DstT dataBytes rfIdx)
            (exec: ExecT addrSize dataBytes)
            (getNextPc: NextPcT addrSize dataBytes rfIdx)
            (alignPc: AlignPcT addrSize iaddrSize)
            (predictNextPc: forall ty, fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                       Expr ty (SyntaxKind (Bit addrSize))).

  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit optypeBits)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val1 *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val2 *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind d2eElt)).

  Variable (f2dElt: Kind).
  Variable (f2dPack:
              forall ty,
                Expr ty (SyntaxKind (Data dataBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind f2dElt)).
  Variables
    (f2dRawInst: forall ty, fullType ty (SyntaxKind f2dElt) ->
                            Expr ty (SyntaxKind (Data dataBytes)))
    (f2dCurPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind (Bit addrSize)))
    (f2dNextPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                           Expr ty (SyntaxKind (Bit addrSize)))
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

  Variables (pcInit : ConstT (Bit addrSize))
            (pgmInit : ConstT (Vector (Data dataBytes) iaddrSize)).

  Definition fetchDecode := fetchDecode
                              getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                              getStAddr getStSrc calcStAddr getStVSrc
                              getSrc1 getSrc2 getDst alignPc predictNextPc d2ePack
                              f2dPack f2dRawInst f2dCurPc f2dNextPc f2dEpoch
                              pcInit pgmInit.
  Definition fetchNDecode := ProcThreeStage.fetchDecode
                               getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                               getStAddr getStSrc calcStAddr getStVSrc
                               getSrc1 getSrc2 getDst alignPc d2ePack predictNextPc
                               pcInit pgmInit.

  Hint Unfold fetchDecode: ModuleDefs. (* for kinline_compute *)
  Hint Extern 1 (ModEquiv type typeUT fetchDecode) => unfold fetchDecode. (* for kequiv *)
  Hint Extern 1 (ModEquiv type typeUT fetchNDecode) => unfold fetchNDecode. (* for kequiv *)

  Definition fetchDecode_ruleMap (o: RegsT): string -> option string :=
    "modifyPc" |-> "modifyPc";
      "decodeLd" |-> "instFetchLd";
      "decodeSt" |-> "instFetchSt";
      "decodeTh" |-> "instFetchTh";
      "decodeNm" |-> "instFetchNm"; ||.
  Hint Unfold fetchDecode_ruleMap: MethDefs.

  Definition fetchDecode_regMap (r: RegsT): RegsT :=
    (mlet pcv : (Bit addrSize) <- r |> "pc";
       mlet pgmv : (Vector (Data dataBytes) iaddrSize) <- r |> "pgm";
       mlet fev : Bool <- r |> "fEpoch";
       mlet f2dfullv : Bool <- r |> "f2d"--"full";
       mlet f2deltv : f2dElt <- r |> "f2d"--"elt";

       (["fEpoch" <- existT _ _ fev]
        +["pgm" <- existT _ _ pgmv]
        +["pc" <- existT _ (SyntaxKind (Bit addrSize))
               (if f2dfullv then evalExpr (f2dCurPc _ f2deltv)
                else pcv)])%fmap)%mapping.
  Hint Unfold fetchDecode_regMap: MapDefs.

  Definition fetchDecodeInl := ProcFDInl.fetchDecodeInl
                                 getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                 getStAddr getStSrc calcStAddr getStVSrc
                                 getSrc1 getSrc2 getDst alignPc predictNextPc d2ePack
                                 f2dPack f2dRawInst f2dCurPc f2dNextPc f2dEpoch
                                 pcInit pgmInit.

  Ltac f2d_abs_tac :=
    try rewrite Hf2dRawInst in *;
    try rewrite Hf2dCurPc in *;
    try rewrite Hf2dNextPc in *;
    try rewrite Hf2dEpoch in *.

  Ltac fetchDecode_dest_tac :=
    repeat match goal with
           | [H: context[fetchDecode_inv] |- _] => destruct H
           end;
    kinv_red.

  Definition fdConfig :=
    {| inlining := ITProvided fetchDecodeInl;
       decomposition := DTFunctional fetchDecode_regMap fetchDecode_ruleMap;
       invariants := IVCons fetchDecode_inv_ok IVNil
    |}.

  Theorem fetchDecode_refines_fetchNDecode:
    fetchDecode <<== fetchNDecode.
  Proof. (* SKIP_PROOF_ON
    kami_ok fdConfig fetchDecode_dest_tac f2d_abs_tac.
    END_SKIP_PROOF_ON *) apply cheat.
  Qed.

End FetchDecode.

