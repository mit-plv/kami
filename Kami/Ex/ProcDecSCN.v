Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts.
Require Import Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Specialize Kami.Tactics Kami.Duplicate.
Require Import Kami.ModuleBound Kami.ModuleBoundEx.
Require Import Ex.SC Ex.Fifo Ex.MemAsync.
Require Import Ex.ProcDec Ex.ProcDecInl Ex.ProcDecInv Ex.ProcDecSC.

Set Implicit Arguments.

Section ProcDecSCN.
  Variables addrSize iaddrSize fifoSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec iaddrSize instBytes dataBytes rfIdx)
            (ammio: AbsMMIO addrSize).

  Variable (init: ProcInit iaddrSize dataBytes rfIdx).
  
  Definition scmm := scmm fetch dec exec ammio init.
  Definition pdec := pdec fifoSize fetch dec exec init.
  
  Definition memAsync := memAsync fifoSize dataBytes ammio.
  Definition pdecM := (pdec ++ memAsync)%kami.

  Lemma pdecM_refines_scmm: pdecM <<== scmm.
  Proof. (* SKIP_PROOF_ON
    krewrite assoc left.
    kmodulari n.
    - krewrite <- dup_dist left.
      kduplicated.
      apply pdec_refines_pinst; auto.
    - krefl.
      END_SKIP_PROOF_ON *) apply cheat.
  Qed.
  
End ProcDecSCN.

