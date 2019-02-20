Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.Indexer Lib.ilist Lib.Word Lib.Struct.
Require Import Kami.Syntax Kami.Notations.
Require Import Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Inline Kami.InlineFacts.
Require Import Kami.Wf Kami.Tactics.
Require Import Ex.MemTypes Ex.SC.

Set Implicit Arguments.

Section Inlined.
  Variables addrSize iaddrSize fifoSize instBytes dataBytes rfIdx: nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT instBytes)
            (getLdDst: LdDstT instBytes rfIdx)
            (getLdAddr: LdAddrT addrSize instBytes)
            (getLdSrc: LdSrcT instBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize dataBytes)
            (getStAddr: StAddrT addrSize instBytes)
            (getStSrc: StSrcT instBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize dataBytes)
            (getStVSrc: StVSrcT instBytes rfIdx)
            (getSrc1: Src1T instBytes rfIdx)
            (getSrc2: Src2T instBytes rfIdx)
            (getDst: DstT instBytes rfIdx)
            (exec: ExecT addrSize instBytes dataBytes)
            (getNextPc: NextPcT addrSize instBytes dataBytes rfIdx)
            (alignPc: AlignPcT addrSize iaddrSize)
            (alignAddr: AlignAddrT addrSize)
            (isMMIO: IsMMIOT addrSize).

  Variable (init: ProcInit addrSize dataBytes rfIdx).
  
  Definition scmm := scmm getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                          getStAddr getStSrc calcStAddr getStVSrc
                          getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr
                          isMMIO init.
  Hint Unfold scmm: ModuleDefs. (* for kinline_compute *)

  Definition scmmInl: sigT (fun m: Modules => scmm <<== m).
  Proof.
    pose proof (inlineF_refines
                  (scmm_ModEquiv getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                 getStAddr getStSrc calcStAddr getStVSrc
                                 getSrc1 getSrc2 getDst exec
                                 getNextPc alignPc alignAddr
                                 isMMIO init type typeUT)
                  (Reflection.noDupStr_NoDup (Struct.namesOf (getDefsBodies scmm)) eq_refl))
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

