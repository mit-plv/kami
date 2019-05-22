Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics.
Require Import Ex.MemTypes Ex.NativeFifo Ex.MemAsync.
Require Import Ex.SC Ex.ProcDec Ex.ProcThreeStage Ex.ProcFetch Ex.ProcFInl
        Ex.ProcFetchDecode.
Require Import Eqdep.

Set Implicit Arguments.

Section Fetch.
  Variables addrSize iaddrSize instBytes dataBytes: nat.

  Variables (fetch: AbsFetch instBytes dataBytes)
            (predictNextPc:
               forall ty, fullType ty (SyntaxKind (Pc iaddrSize)) -> (* pc *)
                          Expr ty (SyntaxKind (Pc iaddrSize))).

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

  Variables (pcInit : ConstT (Pc iaddrSize)).

  Definition fetchICache: Modules :=
    fetchICache addrSize fetch predictNextPc f2dPack pcInit.
  Definition fetcher: Modules :=
    ProcFetchDecode.fetcher addrSize fetch predictNextPc f2dPack pcInit.

  Theorem fetchICache_refines_fetcher:
    fetchICache <<== fetcher.
  Proof.
  Admitted.

End Fetch.

