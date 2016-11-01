Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq.
Require Import Kami.Syntax Kami.ParametricSyntax Kami.Semantics Kami.SemFacts.
Require Import Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Specialize Kami.Tactics Kami.Duplicate.
Require Import Kami.ModuleBound Kami.ModuleBoundEx.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic.
Require Import Ex.ProcDec Ex.ProcDecInl Ex.ProcDecInv Ex.ProcDecSC.

Set Implicit Arguments.

Section ProcDecSCN.
  Variables addrSize iaddrSize fifoSize dataBytes rfIdx: nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT dataBytes)
            (getLdDst: LdDstT dataBytes rfIdx)
            (getLdAddr: LdAddrT addrSize dataBytes)
            (getLdSrc: LdSrcT dataBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize dataBytes)
            (getStAddr: StAddrT addrSize dataBytes)
            (getStSrc: StSrcT dataBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize dataBytes)
            (getStVSrc: StVSrcT dataBytes rfIdx)
            (getSrc1: Src1T dataBytes rfIdx)
            (getSrc2: Src2T dataBytes rfIdx)
            (getDst: DstT dataBytes rfIdx)
            (exec: ExecT addrSize dataBytes)
            (getNextPc: NextPcT addrSize dataBytes rfIdx)
            (alignPc: AlignPcT addrSize iaddrSize)
            (alignAddr: AlignAddrT addrSize).

  Variable n: nat.
  
  Definition pdecN := procDecM fifoSize getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                               getStAddr getStSrc calcStAddr getStVSrc
                               getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr n.
  Definition scN := sc getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                       getStAddr getStSrc calcStAddr getStVSrc
                       getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr n.

  Lemma pdecN_refines_scN: pdecN <<== scN.
  Proof. (* SKIP_PROOF_ON
    kmodular.
    - kdisj_edms_cms_ex n.
    - kdisj_ecms_dms_ex n.
    - kduplicated.
      apply pdec_refines_pinst; auto.
    - krefl.
      END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Definition procDecN := pdecs getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                               getStAddr getStSrc calcStAddr getStVSrc
                               getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr n.
  Definition memAtomic := memAtomic addrSize fifoSize dataBytes n.
  Definition pdecAN := (procDecN ++ memAtomic)%kami.

  Lemma pdecN_memAtomic_refines_scN: pdecAN <<== scN.
  Proof. (* SKIP_PROOF_ON
    ketrans; [|apply pdecN_refines_scN; auto].
    krewrite assoc left.
    kmodular_sim_l.
    - apply duplicate_regs_ConcatMod; auto; kvr.
    - apply duplicate_rules_ConcatMod; auto; kvr.
    - apply duplicate_defs_ConcatMod; auto; kvr.
      END_SKIP_PROOF_ON *) apply cheat.
  Qed.
  
End ProcDecSCN.

