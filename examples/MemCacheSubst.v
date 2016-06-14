Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.FMap Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Semantics Lts.Refinement Lts.Notations.
Require Import Lts.Equiv Lts.Tactics Lts.Specialize Lts.Duplicate Lts.Substitute Lts.ModuleBound.
Require Import Ex.Msi Ex.MemTypes Ex.RegFile Ex.L1Cache Ex.ChildParent Ex.MemDir.
Require Import Ex.Fifo Ex.NativeFifo Ex.FifoCorrect Lts.ParametricEquiv Lts.ParametricInline.
Require Import Ex.MemCache.

Ltac knodup_regs :=
  repeat (* Separating NoDup proofs by small modules *)
    match goal with
    | [ |- NoDup (namesOf (getRegInits _)) ] =>
      progress (unfold getRegInits; fold getRegInits)
    | [ |- NoDup (namesOf (_ ++ _)) ] => unfold RegInitT; rewrite namesOf_app
    | [ |- NoDup (_ ++ _) ] => apply NoDup_DisjList; [| |kdisj_regs]
    | [ |- NoDup (namesOf (getRegInits ?m)) ] => unfold_head m
    end;
  repeat
    match goal with
    | _ => apply noDup_metaRegs
    | _ => noDup_tac
    end.

Lemma getCalls_flattened:
  forall m,
    getCalls (Syntax.Mod (getRegInits m) (getRules m) (getDefsBodies m)) =
    getCalls m.
Proof. reflexivity. Qed.

Section Refinement.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable FifoSize: nat.

  Variable n: nat. (* number of l1 caches (cores) *)

  Lemma memCache_refines_nmemCache:
    (modFromMeta (memCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize n))
      <<== (modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id n)).
  Proof.
    ketrans.

    - unfold MethsT; rewrite <-SemFacts.idElementwiseId.
      pose (fifosInMemCache IdxBits TagBits LgNumDatas LgDataBytes
                            Id (rsz FifoSize) n) as fifos.
      pose (nfifosInNMemCache IdxBits TagBits LgNumDatas LgDataBytes Id n) as nfifos.
      pose (othersInMemCache IdxBits TagBits LgNumDatas LgDataBytes Id n) as others.

      apply substitute_flattened_refines_interacting
      with (regs := getRegInits fifos)
             (rules := getRules fifos)
             (dms := getDefsBodies fifos)
             (sregs := getRegInits nfifos)
             (srules := getRules nfifos)
             (sdms := getDefsBodies nfifos)
             (regs' := getRegInits others)
             (rules' := getRules others)
             (dms' := getDefsBodies others);
        unfold fifos, nfifos, others; clear fifos nfifos others.
      + admit.
      + admit.
      + admit.
      + knodup_regs.
      + knodup_regs.
      + knodup_regs.
      + kdisj_regs.
      + kdisj_regs.
      + kdisj_dms.
      + kdisj_dms.
      + repeat rewrite getCalls_flattened; kdisj_cms.
      + repeat rewrite getCalls_flattened; kdisj_cms.
      + admit. (* DefCallSub for flattened modules *)
      + admit. (* ValidRegsModules for flattened modules *)
      + admit.
      + admit.
      + admit. (* EquivList *)
      + admit.
      + admit.

      + admit. (* Real substitution proof -- from fifos to nativeFifos *)

    - apply traceRefines_same_module_structure.
      + knodup_regs.
      + knodup_regs.
      + admit. (* EquivList *)
      + admit.
      + admit.

  Qed.

End Refinement.

