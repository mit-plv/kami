Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Inline Kami.InlineFacts Kami.Tactics.
Require Import Ex.SC Ex.ProcFetchDecode.

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

  Definition fetchDecode := fetchDecode getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                        getStAddr getStSrc calcStAddr getStVSrc
                                        getSrc1 predictNextPc.
  Hint Unfold fetchDecode: ModuleDefs. (* for kinline_compute *)

  Definition fetchDecodeInl: sigT (fun m: Modules => fetchDecode <<== m).
  Proof. (* SKIP_PROOF_ON
    pose proof (inlineF_refines
                  (fetchDecode_ModEquiv getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                        getStAddr getStSrc calcStAddr getStVSrc
                                        getSrc1 predictNextPc type typeUT)
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
    END_SKIP_PROOF_ON *) admit.
  Defined.

End Inlined.
