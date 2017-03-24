Require Import List String.
Require Import Lib.Word Kami.Syntax Kami.Semantics
        Kami.Notations Ex.IsaRv32 Lib.Struct.
Require Import Ex.ProcFetchDecode Ex.ProcThreeStage Ex.ProcFourStDec.

Require Import ExtrHaskellBasic ExtrHaskellNatInt ExtrHaskellString.
Require Import Compile.CompileToRtl Compile.Rtl.

Extraction Language Haskell.

Set Extraction Optimize.
Set Extraction KeepSingleton.
(* Unset Extraction AutoInline. *)

Definition predictNextPc ty (ppc: fullType ty (SyntaxKind (Bit rv32iAddrSize))) :=
  (#ppc + $4)%kami_expr.

Definition p4stKami :=
  p4st rv32iGetOptype rv32iGetLdDst rv32iGetLdAddr rv32iGetLdSrc rv32iCalcLdAddr
       rv32iGetStAddr rv32iGetStSrc rv32iCalcStAddr rv32iGetStVSrc
       rv32iGetSrc1 rv32iGetSrc2 rv32iGetDst rv32iExec rv32iNextPc
       rv32iAlignPc rv32iAlignAddr predictNextPc
       (@d2ePackI _ _ _) (@d2eOpTypeI _ _ _) (@d2eDstI _ _ _) (@d2eAddrI _ _ _)
       (@d2eVal1I _ _ _) (@d2eVal2I _ _ _) (@d2eRawInstI _ _ _) (@d2eCurPcI _ _ _)
       (@d2eNextPcI _ _ _) (@d2eEpochI _ _ _)
       (@f2dPackI _ _) (@f2dRawInstI _ _) (@f2dCurPcI _ _)
       (@f2dNextPcI _ _) (@f2dEpochI _ _)
       (@e2wPackI _ _ _) (@e2wDecInstI _ _ _) (@e2wValI _ _ _).

Definition p4stRtl := computeModule p4stKami (map (@attrName _) (getRules p4stKami)) nil.

Extraction "P4st.hs" p4stRtl.

