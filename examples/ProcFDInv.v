Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StructNotation Lib.StringBound Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Specialize Kami.Inline Kami.InlineFacts Kami.Decomposition.
Require Import Kami.Tactics Kami.Notations.
Require Import Ex.MemTypes Ex.SC Ex.NativeFifo Ex.MemAtomic Ex.ProcFetchDecode Ex.ProcFDInl.
Require Import Eqdep ProofIrrelevance.

Set Implicit Arguments.

Section Invariants.
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
            (execState: ExecStateT addrSize lgDataBytes rfIdx)
            (execNextPc: ExecNextPcT addrSize lgDataBytes rfIdx)
            (predictNextPc: forall ty, fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                       Expr ty (SyntaxKind (Bit addrSize))).

  (* Definition fetchDecodeInl := projT1 (fetchDecodeInl *)
  (*                                        getOptype getLdDst getLdAddr getLdSrc calcLdAddr *)
  (*                                        getStAddr getStSrc calcStAddr getStVSrc *)
  (*                                        getSrc1 predictNextPc). *)

  (* Record fetchDecode_inv (o: RegsT) : Prop := *)
  (*   { pcv0 : fullType type (SyntaxKind (Bit addrSize)); *)
  (*     Hpcv0 : M.find "pc"%string o = Some (existT _ _ pcv0); *)
  (*     pgmv1 : fullType type (SyntaxKind (Vector (Data lgDataBytes) addrSize)); *)
  (*     Hpgmv1 : M.find "pgm"%string o = Some (existT _ _ pgmv1); *)
  (*     fepochv0 : fullType type (SyntaxKind Bool); *)
  (*     Hfepochv0 : M.find "fEpoch"%string o = Some (existT _ _ fepochv0) }. *)

End Invariants.
