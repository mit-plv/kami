Require Import Bool String List.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Inline Kami.InlineFacts Kami.Tactics.
Require Import Ex.SC Ex.MemTypes Ex.ProcFetchDecode.

Set Implicit Arguments.

Section Inlined.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx).

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

  Variables (pcInit : ConstT (Pc iaddrSize)).

  Definition fetchDecode := fetchDecode fetch dec predictNextPc
                                        d2ePack f2dPack f2dRawInst f2dCurPc f2dNextPc f2dEpoch
                                        pcInit.
  Hint Unfold fetchDecode: ModuleDefs. (* for kinline_compute *)

  Definition fetchDecodeInl: sigT (fun m: Modules => fetchDecode <<== m).
  Proof.
    pose proof (inlineF_refines
                  (fetchDecode_ModEquiv fetch dec predictNextPc
                                        d2ePack f2dPack f2dRawInst f2dCurPc f2dNextPc f2dEpoch
                                        pcInit type typeUT)
                  (Reflection.noDupStr_NoDup (Struct.namesOf (getDefsBodies fetchDecode)) eq_refl))
      as Him.
    unfold MethsT in Him; rewrite <-SemFacts.idElementwiseId in Him.
    match goal with
    | [H: context[inlineF ?m] |- _] => set m as origm in H at 2
    end.
    kinline_compute_in Him.
    unfold origm in *.
    specialize (Him eq_refl).
    exact (existT _ _ Him).
  Defined.

End Inlined.
