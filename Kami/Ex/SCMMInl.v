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

  Variables (fetch: AbsFetch instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec iaddrSize instBytes dataBytes rfIdx)
            (ammio: AbsMMIO addrSize).

  Variable (init: ProcInit iaddrSize dataBytes rfIdx).
  
  Definition scmm := scmm fetch dec exec ammio init.
  Hint Unfold scmm: ModuleDefs. (* for kinline_compute *)

  Definition scmmInl: sigT (fun m: Modules => scmm <<== m).
  Proof.
    pose proof (inlineF_refines
                  (scmm_ModEquiv fetch dec exec ammio init type typeUT)
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

