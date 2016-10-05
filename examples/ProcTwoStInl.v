Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Inline Kami.InlineFacts Kami.Tactics.
Require Import Ex.SC Ex.ProcTwoStage.

Set Implicit Arguments.

Section Inlined.
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

  Definition p2st := p2st getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                          getStAddr getStSrc calcStAddr getStVSrc
                          getSrc1 execState execNextPc predictNextPc.
  Hint Unfold p2st: ModuleDefs. (* for kinline_compute *)

  Definition p2stInl: sigT (fun m: Modules => p2st <<== m).
  Proof.
    pose proof (inlineF_refines
                  (procTwoStage_ModEquiv getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                         getStAddr getStSrc calcStAddr getStVSrc
                                         getSrc1 execState execNextPc predictNextPc
                                         type typeUT)
                  (Reflection.noDupStr_NoDup (Struct.namesOf (getDefsBodies p2st)) eq_refl))
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

