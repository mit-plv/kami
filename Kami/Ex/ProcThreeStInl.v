Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Inline Kami.InlineFacts Kami.Tactics Lib.CommonTactics.
Require Import Ex.SC Ex.MemTypes Ex.ProcThreeStage.

Set Implicit Arguments.

Section Inlined.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize iaddrSize instBytes dataBytes rfIdx).

  Variable predictNextPc: forall ty, fullType ty (SyntaxKind (Pc iaddrSize)) -> (* pc *)
                                     Expr ty (SyntaxKind (Pc iaddrSize)).

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

  Definition p3st := p3st fetch dec exec predictNextPc
                          d2ePack d2eOpType d2eDst d2eAddr d2eVal1 d2eVal2
                          d2eRawInst d2eCurPc d2eNextPc d2eEpoch
                          e2wPack e2wDecInst e2wVal init.
  Hint Unfold p3st: ModuleDefs. (* for kinline_compute *)

  Definition p3stInl: sigT (fun m: Modules => p3st <<== m).
  Proof. (* SKIP_PROOF_ON
    pose proof (inlineF_refines
                  (procThreeStage_ModEquiv getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                           getStAddr getStSrc calcStAddr getStVSrc
                                           getSrc1 getSrc2 getDst exec
                                           getNextPc alignPc alignInst predictNextPc
                                           d2ePack d2eOpType d2eDst d2eAddr d2eVal1 d2eVal2
                                           d2eRawInst d2eCurPc d2eNextPc d2eEpoch
                                           e2wPack e2wDecInst e2wVal init
                                           type typeUT)
                  (Reflection.noDupStr_NoDup (Struct.namesOf (getDefsBodies p3st)) eq_refl))
      as Him.
    unfold MethsT in Him; rewrite <-SemFacts.idElementwiseId in Him.
    match goal with
    | [H: context[inlineF ?m] |- _] => set m as origm in H at 2
    end.
    kinline_compute_in Him.
    unfold origm in *.
    specialize (Him eq_refl).
    exact (existT _ _ Him).
    END_SKIP_PROOF_ON *) apply cheat.
  Defined.

End Inlined.

