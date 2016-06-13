Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.FMap Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Semantics Lts.Refinement Lts.Notations.
Require Import Lts.Equiv Lts.Tactics Lts.Specialize Lts.Duplicate Lts.Substitute.
Require Import Ex.Msi Ex.MemTypes Ex.RegFile Ex.L1Cache Ex.ChildParent Ex.MemDir.
Require Import Ex.Fifo Ex.NativeFifo Ex.FifoCorrect Lts.ParametricEquiv Lts.ParametricInline.
Require Import Ex.MemCache.

Lemma getRegInits_makeModule_concat:
  forall mm1 mm2,
    getRegInits (ParametricSyntax.makeModule (mm1 +++ mm2)) =
    (getRegInits (ParametricSyntax.makeModule mm1))
      ++ (getRegInits (ParametricSyntax.makeModule mm2)).
Proof.
  intros; simpl; rewrite map_app.
  apply Concat.concat_app.
Qed.

Lemma noDup_metaRegs:
  forall mm,
    NoDup (map getMetaRegName (metaRegs mm)) ->
    NoDup (namesOf (getRegInits (ParametricSyntax.makeModule mm))).
Proof.
  admit.
Qed.

Ltac knodup_regs :=
  repeat (* Separating NoDup proofs by small modules *)
    match goal with
    | [ |- NoDup (namesOf (getRegInits _)) ] =>
      progress (unfold getRegInits; fold getRegInits)
    | [ |- NoDup (namesOf (getRegInits (ParametricSyntax.makeModule (_ +++ _)))) ] =>
      rewrite getRegInits_makeModule_concat
    | [ |- NoDup (namesOf (_ ++ _)) ] => unfold RegInitT; rewrite namesOf_app
    | [ |- NoDup (_ ++ _) ] => apply NoDup_DisjList; [| |kdisj_regs]
    | [ |- NoDup (namesOf (getRegInits ?m)) ] => unfold_head m
    end;
  repeat
    match goal with
    | _ => apply noDup_metaRegs
    | _ => noDup_tac
    end.

Section Refinement.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable FifoSize: nat.

  Variable n: nat. (* number of l1 caches (cores) *)

  Lemma memCache_refines_nmemCache:
    (ParametricSyntax.makeModule
       (memCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize n))
      <<== (ParametricSyntax.makeModule
              (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id n)).
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
             (dms' := getDefsBodies others).

      + kequiv.
      + kequiv.
      + kequiv.
      + kequiv.
      + kequiv.
      + kequiv.
  
    - apply traceRefines_same_module_structure.
      + knodup_regs.
      + knodup_regs.
      + admit.
      + admit.
      + admit.
        
  Qed.


End Refinement.

