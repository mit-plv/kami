Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.FMap Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.Concat.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Semantics Lts.Refinement Lts.Notations.
Require Import Lts.Equiv Lts.Wf Lts.ParametricWf Lts.Tactics Lts.Specialize.
Require Import Lts.Duplicate Lts.Substitute Lts.ModuleBound.
Require Import Ex.Msi Ex.MemTypes Ex.RegFile Ex.L1Cache Ex.ChildParent Ex.MemDir.
Require Import Ex.Fifo Ex.NativeFifo Ex.FifoCorrect Lts.ParametricEquiv Lts.ParametricInline.
Require Import Ex.MemCache.

Set Implicit Arguments.

(* fifo/nativeFifo facts *)

Lemma getDefs_fifo_nativeFifo:
  forall fifoName sz d1 {d2} (default: ConstT d2)  Hgood n,
    getDefs (modFromMeta (getMetaFromSinNat n (nativeFifoS fifoName default Hgood))) =
    getDefs (modFromMeta (getMetaFromSinNat n (fifoS fifoName sz d1 Hgood))).
Proof.
  intros; apply getDefs_sinModule_eq; reflexivity.
Qed.

Lemma getDefs_simpleFifo_nativeSimpleFifo:
  forall fifoName sz d1 {d2} (default: ConstT d2)  Hgood n,
    getDefs (modFromMeta (getMetaFromSinNat n (nativeSimpleFifoS fifoName default Hgood))) =
    getDefs (modFromMeta (getMetaFromSinNat n (simpleFifoS fifoName sz d1 Hgood))).
Proof.
  intros; apply getDefs_sinModule_eq; reflexivity.
Qed.

Ltac subList_app_tac :=
  repeat apply SubList_app_3;
  match goal with
  | _ => apply SubList_refl
  | _ => apply SubList_app_1; subList_app_tac
  | _ => apply SubList_app_2; subList_app_tac
  end.
Ltac equivList_app_tac := split; subList_app_tac.

Section Refinement.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable FifoSize: nat.

  Variable n: nat. (* number of l1 caches (cores) *)
    
  Lemma getDefs_fifos_nfifos:
    getDefs (nfifosInNMemCache IdxBits TagBits LgNumDatas
                               LgDataBytes Id n) =
    getDefs (fifosInMemCache IdxBits TagBits LgNumDatas LgDataBytes
                             Id FifoSize n).
  Proof.
    unfold nfifosInNMemCache, fifosInMemCache.
    repeat rewrite getDefs_modFromMeta_app.
    f_equal.
    f_equal; [|apply getDefs_simpleFifo_nativeSimpleFifo].
    f_equal; [|apply getDefs_simpleFifo_nativeSimpleFifo].
    f_equal; [|apply getDefs_simpleFifo_nativeSimpleFifo].
    f_equal; [|apply getDefs_simpleFifo_nativeSimpleFifo].
    apply getDefs_fifo_nativeFifo.
  Qed.

  Lemma getCalls_fifos_nfifos:
    getCalls (nfifosInNMemCache IdxBits TagBits LgNumDatas
                                LgDataBytes Id n) =
    getCalls (fifosInMemCache IdxBits TagBits LgNumDatas LgDataBytes
                              Id FifoSize n).
  Proof.
    admit.
  Qed.

  Lemma memCache_refines_nmemCache:
    (modFromMeta (memCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize n))
      <<== (modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id n)).
  Proof.
    ketrans.

    - unfold MethsT; rewrite <-SemFacts.idElementwiseId.
      pose (fifosInMemCache IdxBits TagBits LgNumDatas LgDataBytes
                            Id FifoSize n) as fifos.
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
      + kequiv.
      + kequiv.
      + kequiv.
      + knodup_regs.
      + knodup_regs.
      + knodup_regs.
      + kdisj_regs.
      + kdisj_regs.
      + kdisj_dms.
      + kdisj_dms.
      + repeat rewrite getCalls_flattened; kdisj_cms.
      + repeat rewrite getCalls_flattened; kdisj_cms.
      + split.
        * repeat rewrite getDefs_flattened.
          rewrite getDefs_fifos_nfifos.
          apply SubList_refl.
        * repeat rewrite getCalls_flattened.
          rewrite getCalls_fifos_nfifos.
          apply SubList_refl.
      + kvr.
      + kvr.
      + kvr.
      + unfold fifosInMemCache, othersInMemCache, memCache, l1C, childParentC.
        remember (_ +++ (fifoFromP _ _ _ _ _ _ _)) as fifos1; clear Heqfifos1.
        remember (_ +++ (fifoToC _ _ _ _ _ _ _)) as fifos2; clear Heqfifos2.
        remember (l1 _ _ _ _ _ _) as l1; clear Heql1.
        remember (childParent _ _ _ _ _ _) as childParent; clear HeqchildParent.
        remember (memDirC _ _ _ _ _ _) as memDirC; clear HeqmemDirC.
        simpl; repeat rewrite map_app, concat_app.
        equivList_app_tac.
      + unfold fifosInMemCache, othersInMemCache, memCache, l1C, childParentC.
        remember (_ +++ (fifoFromP _ _ _ _ _ _ _)) as fifos1; clear Heqfifos1.
        remember (_ +++ (fifoToC _ _ _ _ _ _ _)) as fifos2; clear Heqfifos2.
        remember (l1 _ _ _ _ _ _) as l1; clear Heql1.
        remember (childParent _ _ _ _ _ _) as childParent; clear HeqchildParent.
        remember (memDirC _ _ _ _ _ _) as memDirC; clear HeqmemDirC.
        simpl; repeat rewrite map_app, concat_app.
        equivList_app_tac.
      + unfold fifosInMemCache, othersInMemCache, memCache, l1C, childParentC.
        remember (_ +++ (fifoFromP _ _ _ _ _ _ _)) as fifos1; clear Heqfifos1.
        remember (_ +++ (fifoToC _ _ _ _ _ _ _)) as fifos2; clear Heqfifos2.
        remember (l1 _ _ _ _ _ _) as l1; clear Heql1.
        remember (childParent _ _ _ _ _ _) as childParent; clear HeqchildParent.
        remember (memDirC _ _ _ _ _ _) as memDirC; clear HeqmemDirC.
        simpl; repeat rewrite map_app, concat_app.
        equivList_app_tac.

      + admit. (* Real substitution proof -- from fifos to nativeFifos *)

    - apply traceRefines_same_module_structure.
      + knodup_regs.
      + knodup_regs.
      + unfold nfifosInNMemCache, othersInMemCache, nmemCache, nl1C, nchildParentC.
        remember (_ +++ (nfifoFromP _ _ _ _ _ _)) as fifos1; clear Heqfifos1.
        remember (_ +++ (nfifoToC _ _ _ _ _ _)) as fifos2; clear Heqfifos2.
        remember (l1 _ _ _ _ _ _) as l1; clear Heql1.
        remember (childParent _ _ _ _ _ _) as childParent; clear HeqchildParent.
        remember (memDirC _ _ _ _ _ _) as memDirC; clear HeqmemDirC.
        simpl; repeat rewrite map_app, concat_app.
        equivList_app_tac.
      + unfold nfifosInNMemCache, othersInMemCache, nmemCache, nl1C, nchildParentC.
        remember (_ +++ (nfifoFromP _ _ _ _ _ _)) as fifos1; clear Heqfifos1.
        remember (_ +++ (nfifoToC _ _ _ _ _ _)) as fifos2; clear Heqfifos2.
        remember (l1 _ _ _ _ _ _) as l1; clear Heql1.
        remember (childParent _ _ _ _ _ _) as childParent; clear HeqchildParent.
        remember (memDirC _ _ _ _ _ _) as memDirC; clear HeqmemDirC.
        simpl; repeat rewrite map_app, concat_app.
        equivList_app_tac.
      + unfold nfifosInNMemCache, othersInMemCache, nmemCache, nl1C, nchildParentC.
        remember (_ +++ (nfifoFromP _ _ _ _ _ _)) as fifos1; clear Heqfifos1.
        remember (_ +++ (nfifoToC _ _ _ _ _ _)) as fifos2; clear Heqfifos2.
        remember (l1 _ _ _ _ _ _) as l1; clear Heql1.
        remember (childParent _ _ _ _ _ _) as childParent; clear HeqchildParent.
        remember (memDirC _ _ _ _ _ _) as memDirC; clear HeqmemDirC.
        simpl; repeat rewrite map_app, concat_app.
        equivList_app_tac.

  Qed.

End Refinement.

