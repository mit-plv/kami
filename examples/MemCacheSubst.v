Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.FMap Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.Concat.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Semantics Lts.SemFacts Lts.Refinement.
Require Import Lts.Equiv Lts.ParametricEquiv Lts.Wf Lts.ParametricWf Lts.Tactics Lts.Specialize.
Require Import Lts.Duplicate Lts.ParamDup Lts.Notations Lts.Substitute Lts.ModuleBound.
Require Import Ex.Msi Ex.MemTypes Ex.RegFile Ex.L1Cache Ex.ChildParent Ex.MemDir.
Require Import Ex.Fifo Ex.NativeFifo Ex.FifoCorrect Ex.SimpleFifoCorrect Ex.MemCache.

Set Implicit Arguments.

(* fifo/nativeFifo facts *)

Lemma getDefs_fifo_nativeFifo:
  forall fifoName sz d1 {d2} (default: ConstT d2) Hgood n,
    getDefs (modFromMeta (getMetaFromSinNat n (nativeFifoS fifoName default Hgood))) =
    getDefs (modFromMeta (getMetaFromSinNat n (fifoS fifoName sz d1 Hgood))).
Proof.
  intros; apply getDefs_sinModule_eq; reflexivity.
Qed.

Lemma getDefs_simpleFifo_nativeSimpleFifo:
  forall fifoName sz d1 {d2} (default: ConstT d2) Hgood n,
    getDefs (modFromMeta (getMetaFromSinNat n (nativeSimpleFifoS fifoName default Hgood))) =
    getDefs (modFromMeta (getMetaFromSinNat n (simpleFifoS fifoName sz d1 Hgood))).
Proof.
  intros; apply getDefs_sinModule_eq; reflexivity.
Qed.

Lemma fifoS_const_regs:
  forall fifoName sz dType Hgood sr,
    In sr (sinRegs (fifoS fifoName sz dType Hgood)) ->
    forall i j, regGen sr i = regGen sr j.
Proof. intros; CommonTactics.dest_in; simpl; reflexivity. Qed.

Lemma nativeFifoS_const_regs:
  forall fifoName {dType} (default: ConstT dType) Hgood sr,
    In sr (sinRegs (nativeFifoS fifoName default Hgood)) ->
    forall i j, regGen sr i = regGen sr j.
Proof. intros; CommonTactics.dest_in; simpl; reflexivity. Qed.

Lemma simpleFifoS_const_regs:
  forall fifoName sz dType Hgood sr,
    In sr (sinRegs (simpleFifoS fifoName sz dType Hgood)) ->
    forall i j, regGen sr i = regGen sr j.
Proof. intros; CommonTactics.dest_in; simpl; reflexivity. Qed.

Lemma nativeSimpleFifoS_const_regs:
  forall fifoName {dType} (default: ConstT dType) Hgood sr,
    In sr (sinRegs (nativeSimpleFifoS fifoName default Hgood)) ->
    forall i j, regGen sr i = regGen sr j.
Proof. intros; CommonTactics.dest_in; simpl; reflexivity. Qed.

Section Refinement.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable FifoSize: nat.

  Variable n: nat. (* number of l1 caches (cores) *)

  Lemma fifos_refines_nfifos_memCache:
    (fifosInMemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize n)
      <<== (nfifosInNMemCache IdxBits TagBits LgNumDatas LgDataBytes Id n).
  Proof.
    ketrans; [apply modFromMeta_comm_1|].
    ketrans; [|apply modFromMeta_comm_2].
    kmodularn.
    
    - ketrans; [apply modFromMeta_comm_1|].
      ketrans; [|apply modFromMeta_comm_2].
      kmodularn.
      + ketrans; [apply modFromMeta_comm_1|].
        ketrans; [|apply modFromMeta_comm_2].
        kmodularn.
        * ketrans; [apply sinModule_duplicate_1; auto;
                    intros; eapply simpleFifoS_const_regs; eauto|].
          ketrans; [|apply sinModule_duplicate_2; auto;
                     intros; eapply nativeSimpleFifoS_const_regs; eauto].
          kduplicated.
          rewrite <-simpleFifo_simpleFifoS.
          rewrite <-nativeSimpleFifo_nativeSimpleFifoS.
          apply sfifo_refines_nsfifo.
        * ketrans; [apply sinModule_duplicate_1; auto;
                    intros; eapply simpleFifoS_const_regs; eauto|].
          ketrans; [|apply sinModule_duplicate_2; auto;
                     intros; eapply nativeSimpleFifoS_const_regs; eauto].
          kduplicated.
          rewrite <-simpleFifo_simpleFifoS.
          rewrite <-nativeSimpleFifo_nativeSimpleFifoS.
          apply sfifo_refines_nsfifo.
      + ketrans; [apply sinModule_duplicate_1; auto;
                  intros; eapply simpleFifoS_const_regs; eauto|].
        ketrans; [|apply sinModule_duplicate_2; auto;
                   intros; eapply nativeSimpleFifoS_const_regs; eauto].
        kduplicated.
        rewrite <-simpleFifo_simpleFifoS.
        rewrite <-nativeSimpleFifo_nativeSimpleFifoS.
        apply sfifo_refines_nsfifo.

    - ketrans; [apply modFromMeta_comm_1|].
      ketrans; [|apply modFromMeta_comm_2].
      kmodularn.
      + ketrans; [apply modFromMeta_comm_1|].
        ketrans; [|apply modFromMeta_comm_2].
        kmodularn.
        * unfold fifoRqFromC; rewrite <-fifo_fifoM.
          unfold nfifoRqFromC; rewrite <-nativeFifo_nativeFifoM.
          apply fifo_refines_nativefifo.
        * unfold fifoRsFromC; rewrite <-simpleFifo_simpleFifoM.
          unfold nfifoRsFromC; rewrite <-nativeSimpleFifo_nativeSimpleFifoM.
          apply sfifo_refines_nsfifo.
      + apply sfifo_refines_nsfifo.
  Qed.
    
  Lemma getDefs_fifos_nfifos:
    SubList (getDefs (nfifosInNMemCache IdxBits TagBits LgNumDatas LgDataBytes Id n))
            (getDefs (fifosInMemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize n)).
  Proof.
    replace (getDefs (fifosInMemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize n)) 
    with (getDefs (nfifosInNMemCache IdxBits TagBits LgNumDatas LgDataBytes Id n));
      [apply SubList_refl|].
    unfold nfifosInNMemCache, fifosInMemCache.
    repeat rewrite getDefs_modFromMeta_app.
    f_equal.
    f_equal; [|apply getDefs_simpleFifo_nativeSimpleFifo].
    f_equal; [|apply getDefs_simpleFifo_nativeSimpleFifo].
    apply getDefs_simpleFifo_nativeSimpleFifo.
  Qed.

  Ltac getCalls_fifos_nfifos_tac :=
    eapply SubList_trans; [apply getCalls_modFromMeta_app|];
    eapply SubList_trans; [|apply getCalls_modFromMeta_app];
    apply SubList_app_6.

  Lemma getCalls_fifos_nfifos:
    SubList (getCalls (nfifosInNMemCache IdxBits TagBits LgNumDatas LgDataBytes Id n))
            (getCalls (fifosInMemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize n)).
  Proof.
    unfold nfifosInNMemCache, fifosInMemCache.
    getCalls_fifos_nfifos_tac.
    - getCalls_fifos_nfifos_tac;
        [|apply SubList_refl'; apply getCalls_sinModule_eq; reflexivity].
      getCalls_fifos_nfifos_tac;
        [|apply SubList_refl'; apply getCalls_sinModule_eq; reflexivity].
      apply SubList_refl'; apply getCalls_sinModule_eq; reflexivity.
    - getCalls_fifos_nfifos_tac; [|vm_compute; tauto].
      getCalls_fifos_nfifos_tac; [|vm_compute; tauto].
      vm_compute; tauto.
  Qed.

  Ltac abstract_fifos_in_memCache :=
    unfold fifosInMemCache, othersInMemCache, memCache, l1C, childParentC;
    let m := fresh in
    set (_ +++ (fifoFromP _ _ _ _ _ _ _)) as m; clearbody m;
    let m := fresh in
    set (_ +++ (fifoToC _ _ _ _ _ _ _)) as m; clearbody m;
    let m := fresh in
    set (l1 _ _ _ _ _ _) as m; clearbody m;
    let m := fresh in
    set (childParent _ _ _ _ _ _) as m; clearbody m;
    let m := fresh in
    set (memDirC _ _ _ _ _ _) as m; clearbody m;
    simpl; repeat rewrite map_app, concat_app.

  Ltac abstract_fifos_in_nmemCache :=
    unfold nfifosInNMemCache, othersInMemCache, nmemCache, nl1C, nchildParentC;
    let m := fresh in
    set (_ +++ (nfifoFromP _ _ _ _ _ _)) as m; clearbody m;
    let m := fresh in
    set (_ +++ (nfifoToC _ _ _ _ _ _)) as m; clearbody m;
    let m := fresh in
    set (l1 _ _ _ _ _ _) as m; clearbody m;
    let m := fresh in
    set (childParent _ _ _ _ _ _) as m; clearbody m;
    let m := fresh in
    set (memDirC _ _ _ _ _ _) as m; clearbody m;
    simpl; repeat rewrite map_app, concat_app.

  Lemma memCache_refines_nmemCache:
    (modFromMeta (memCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize n))
      <<== (modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id n)).
  Proof.
    ketrans.

    - ksubst
        (fifosInMemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize n)
        (nfifosInNMemCache IdxBits TagBits LgNumDatas LgDataBytes Id n)
        (othersInMemCache IdxBits TagBits LgNumDatas LgDataBytes Id n).
      + split.
        * repeat rewrite getDefs_flattened; apply getDefs_fifos_nfifos.
        * repeat rewrite getCalls_flattened; apply getCalls_fifos_nfifos.
      + abstract_fifos_in_memCache; equivList_app_tac.
      + abstract_fifos_in_memCache; equivList_app_tac.
      + abstract_fifos_in_memCache; equivList_app_tac.
      + ketrans; [apply flatten_traceRefines_inv|].
        ketrans; [|apply flatten_traceRefines].
        apply fifos_refines_nfifos_memCache.

    - ksimilar.
      + abstract_fifos_in_nmemCache; equivList_app_tac.
      + abstract_fifos_in_nmemCache; equivList_app_tac.
      + abstract_fifos_in_nmemCache; equivList_app_tac.
  Qed.

End Refinement.

