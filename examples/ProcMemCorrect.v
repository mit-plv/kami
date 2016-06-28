Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.SemFacts Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Tactics Lts.Duplicate Lts.ParamDup.

Require Import Ex.SC Ex.ProcDec Ex.MemAtomic Ex.MemCache Ex.MemCacheSubst Ex.L1Cache.
Require Import Ex.FifoCorrect Ex.MemCorrect Ex.ProcDecSCN Lts.ParametricSyntax.

Set Implicit Arguments.

Lemma DisjList_logic_inv:
  forall (l1 l2: list string),
    DisjList l1 l2 ->
    (forall e, In e l1 -> In e l2 -> False).
Proof.
  unfold DisjList; intros.
  specialize (H e); destruct H; auto.
Qed.

Section ProcMem.
  Variable FifoSize: nat. (* fifo *)
  Variables RfIdx: nat. (* processor *)
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat. (* memory *)
  Variable Id: Kind.

  Definition AddrSize := L1Cache.AddrBits IdxBits TagBits LgNumDatas LgDataBytes.
  Hint Unfold AddrSize: MethDefs.
  
  Variable dec: DecT 2 AddrSize LgDataBytes RfIdx.
  Variable execState: ExecStateT 2 AddrSize LgDataBytes RfIdx.
  Variable execNextPc: ExecNextPcT 2 AddrSize LgDataBytes RfIdx.

  Variable LgNumChildren: nat.
  Definition numChildren := (wordToNat (wones LgNumChildren)).

  Definition pdecN := pdecs dec execState execNextPc numChildren.
  Definition pmFifos :=
    modFromMeta
      ((nfifoRqFromProc IdxBits TagBits LgNumDatas LgDataBytes LgNumChildren)
         +++ (nfifoRsToProc LgDataBytes LgNumChildren)).
    
  Definition mcache := memCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize LgNumChildren.
  Definition scN := sc dec execState execNextPc opLd opSt opHt numChildren.

  (* Lemmas about "dropFirstElts" *)
  Section DropFirstElts.
    Lemma firstElts_SubList:
      forall n,
        SubList
          (duplicateElt (Indexer.withPrefix "rqFromProc" "firstElt") (wordToNat (wones n)))
          (getDefs (modFromMeta (nfifoRqFromProc IdxBits TagBits LgNumDatas LgDataBytes n))).
    Proof.
      unfold modFromMeta, getDefs; simpl; intros.
      repeat rewrite namesOf_app.
      do 2 apply SubList_app_2; apply SubList_app_1.
      apply SubList_refl'.
      clear; induction (wordToNat (wones n)); [reflexivity|].
      simpl; f_equal; auto.
    Qed.

    Lemma dropFirstElts_Some:
      forall n k v,
        ~ In k (duplicateElt (Indexer.withPrefix "rqFromProc" "firstElt")
                             (wordToNat (wones n))) ->
        dropFirstElts n k v = Some v.
    Proof.
      unfold dropFirstElts; intros.
      rewrite dropN_dropPs.
      remember (dropPs _ _ _) as kv; destruct kv.
      - apply eq_sym, dropPs_Some in Heqkv; dest; subst; auto.
      - apply eq_sym, dropPs_None in Heqkv; elim H; auto.
    Qed.

    Lemma dropFirstElts_Interacting:
      Interacting pmFifos (modFromMeta mcache) (dropFirstElts LgNumChildren).
    Proof.
      repeat split; intros; apply dropFirstElts_Some.
      - exfalso; clear -H.
        unfold pmFifos in H; apply getCalls_modFromMeta_app in H.
        apply in_app_or in H; destruct H.
        + unfold modFromMeta, getCalls in H; simpl in H.
          rewrite app_nil_r in H; repeat rewrite getCallsM_app in H.
          repeat (apply in_app_or in H; destruct H);
            induction (wordToNat (wones LgNumChildren)); intuition.
        + unfold modFromMeta, getCalls in H; simpl in H.
          rewrite app_nil_r in H; repeat rewrite getCallsM_app in H.
          repeat (apply in_app_or in H; destruct H);
            induction (wordToNat (wones LgNumChildren)); intuition.
      - intro Hx; elim H0; clear H0.
        do 4 (apply getCalls_modFromMeta_app, in_or_app; left).
        unfold modFromMeta, getCalls; simpl.
        rewrite !app_nil_r; rewrite getCallsR_app.
        apply in_or_app; left.
        induction (wordToNat (wones LgNumChildren)).
        + left; inv Hx; intuition.
        + inv Hx.
          * clear IHn; simpl in *; left; auto.
          * do 3 right; simpl in *; apply IHn; auto.
      - intro Hx; elim H0; clear -Hx.
        unfold pmFifos; rewrite getDefs_modFromMeta_app.
        apply in_or_app; left.
        unfold modFromMeta, getDefs; simpl.
        repeat rewrite app_nil_r; repeat rewrite namesOf_app.
        do 2 (apply in_or_app; right).
        induction (wordToNat (wones LgNumChildren)); auto.
        inv Hx; [simpl; auto|right; apply IHn; auto].
      - clear -H.
        unfold mcache, memCache, MemCache.memCache, l1C, l1 in H.
        repeat (rewrite getDefs_modFromMeta_app in H;
                apply in_app_or in H; destruct H); auto;
          try (intro Hx; apply firstElts_SubList in Hx;
               generalize dependent k; apply DisjList_logic_inv;
               kdisj_dms).
    Qed.

  End DropFirstElts.

  Theorem pdecN_mcache_refines_scN: (pdecN ++ pmFifos ++ modFromMeta mcache)%kami <<== scN.
  Proof.
    ketrans; [|apply pdecN_memAtomic_refines_scN].

    kmodular_light.
    - admit. (* Disj extDefs calls *)
    - admit. (* Disj extCalls defs *)
    - kinteracting.
    - krefl.
    - ketrans; [|apply ios_memAtomicWoQ_memAtomic].
      apply traceRefines_modular_interacting with (vp:= dropFirstElts LgNumChildren);
        [kequiv|kequiv|kequiv|kequiv
         |kdisj_regs|kdisj_regs|kvr|kvr
         |kdisj_dms|kdisj_cms|kdisj_dms|kdisj_cms
         | | | | |].
      + admit. (* Disj extDefs calls *)
      + admit. (* Disj extCalls defs *)
      + apply dropFirstElts_Interacting.
      + ketrans_r; [apply modFromMeta_comm_1|].
        ketrans_l; [|apply duplicate_concatMod_comm_2; auto; [kvr|kvr|kequiv|kequiv]].
        replace (dropFirstElts LgNumChildren) with
        (compLabelMaps (dropFirstElts LgNumChildren) (@idElementwise _))
          by apply compLabelMaps_id_right.

        apply traceRefines_modular_noninteracting_p;
          [kequiv|kequiv|kequiv|kequiv
           |kdisj_regs|kdisj_regs|kvr|kvr
           |kdisj_dms|kdisj_cms|kdisj_dms|kdisj_cms
           | |knoninteracting|knoninteracting| |].
        * unfold dropFirstElts; rewrite dropN_dropPs.
          rewrite <-dropPs_nil_idElementwise.
          apply dropPs_disj.
          { apply DisjList_nil_2. }
          { (* TODO: need some automation *)
            eapply DisjList_SubList; [apply getExtMeths_meths|].
            apply DisjList_comm.
            apply DisjList_SubList with
            (l1:= getDefs (modFromMeta (nfifoRqFromProc IdxBits TagBits LgNumDatas
                                                        LgDataBytes LgNumChildren)));
              [apply firstElts_SubList|].
            apply DisjList_comm, DisjList_app_4.
            { kdisj_dms. }
            { kdisj_cms_dms. }
          }
        * ketrans_r;
            [apply sinModule_duplicate_1;
             [kequiv|kvr|knodup_regs|apply nativeFifoS_const_regs]|].
          apply duplicate_traceRefines_drop; auto; [kequiv|kvr| |].
          { vm_compute; tauto. }
          { rewrite <-NativeFifo.nativeFifo_nativeFifoS.
            apply nfifo_refines_nsfifo.
          }
        * apply sinModule_duplicate_1; [kequiv|kvr|knodup_regs|].
          apply nativeFifoS_const_regs with (default:= (getDefaultConst _)).
          
      + apply memCache_refines_memAtomic.
  Qed.

End ProcMem.

