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
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize iaddrSize instBytes dataBytes rfIdx)
            (ammio: AbsMMIO addrSize).

  Variable (procInit: ProcInit iaddrSize dataBytes rfIdx)
           (memInit: MemInit addrSize).

  Definition scmm := scmm fetch dec exec ammio procInit memInit.
  Definition pdec := ProcDec.pdec fetch dec exec procInit.
  
  Definition memAsync := memAsync dataBytes memInit ammio.
  Definition pdecM := (pdec ++ memAsync)%kami.

  Lemma pdecM_refines_scmm: pdecM <<== scmm.
  Proof. (* SKIP_PROOF_ON
    krewrite assoc left.
    kmodular.
    - apply pdec_refines_pinst.
    - krefl.
      END_SKIP_PROOF_ON *) apply cheat.
  Qed.
  
End ProcDecSCN.

