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

  Axiom cheat: forall t, t.
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
    Require Import List Lib.Struct Kami.Syntax Kami.Notations Lib.StringEq Bool.
    Set Ltac Profiling.
    repeat autounfold with ModuleDefs in Him.
    repeat autounfold with MethDefs in Him.
    cbv [inlineF inline inlineDms inlineDms'
               inlineDmToMod inlineDmToRules inlineDmToRule
               inlineDmToDms inlineDmToDm inlineDm
               filterDms filter
               noInternalCalls noCalls
               noCallsRules noCallsDms noCallDm isLeaf
               getBody inlineArg
               appendAction getAttribute
               makeModule makeModule' max plus
               getRegInits getDefs getDefsBodies getRules namesOf
               map app attrName attrType
               getCalls getCallsR getCallsM getCallsA
               doReadField getLs VectorFacts.Vector_find
               ret arg fst snd projT1 projT2
               string_in string_eq ascii_eq
               eqb existsb andb orb negb] in Him.
    kstring_simpl.
    Show Ltac Profile.
    match type of Him with
    | context[SignatureT_dec ?s ?s] =>
      rewrite (signature_eq s) in Him; unfold eq_rect in Him
    end.

    try timeout 10 (kinline_compute_in Him).
    Show Ltac Profile.
    unfold origm in *.
    specialize (Him eq_refl).
    exact (existT _ _ Him).
  Defined.

End Inlined.

