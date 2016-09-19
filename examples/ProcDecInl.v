Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Inline Kami.InlineFacts Kami.Tactics.
Require Import Ex.SC Ex.ProcDec.

Set Implicit Arguments.

Section Inlined.
  Variables addrSize fifoSize lgDataBytes rfIdx: nat.

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
            (execNextPc: ExecNextPcT addrSize lgDataBytes rfIdx).

  Definition pdec := pdecf fifoSize getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                           getStAddr getStSrc calcStAddr getStVSrc
                           getSrc1 execState execNextPc.
  Hint Unfold pdec: ModuleDefs. (* for kinline_compute *)

  Definition pdecInl: Modules * bool.
  Proof.
    remember (inlineF pdec) as inlined.
    kinline_compute_in Heqinlined.
    match goal with
    | [H: inlined = ?m |- _] =>
      exact m
    end.
  Defined.

End Inlined.

