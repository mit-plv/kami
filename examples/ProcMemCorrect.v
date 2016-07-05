Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.SemFacts Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Tactics Lts.Duplicate Lts.ParamDup Lts.ModuleBoundEx.
Require Import Ex.SC Ex.ProcDec Ex.MemAtomic Ex.MemCache Ex.MemCacheSubst Ex.L1Cache.
Require Import Ex.FifoCorrect Ex.MemCorrect Ex.ProcDecSCN Lts.ParametricSyntax.

Set Implicit Arguments.

Section ProcMem.
  Variable FifoSize: nat. (* fifo *)
  Variables OpIdx RfIdx: nat. (* processor *)
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat. (* memory *)
  Variable Id: Kind.

  Definition AddrSize := L1Cache.AddrBits IdxBits TagBits LgNumDatas.
  Hint Unfold AddrSize: MethDefs.
  
  Variable dec: DecT OpIdx AddrSize LgDataBytes RfIdx.
  Variable execState: ExecStateT OpIdx AddrSize LgDataBytes RfIdx.
  Variable execNextPc: ExecNextPcT OpIdx AddrSize LgDataBytes RfIdx.

  Variables opLd opSt opHt: ConstT (Bit OpIdx).

  Variable LgNumChildren: nat.
  Definition numChildren := (wordToNat (wones LgNumChildren)).

  Definition pdecN := pdecs dec execState execNextPc opLd opSt opHt numChildren.
  Definition pmFifos :=
    modFromMeta
      ((nfifoRqFromProc IdxBits TagBits LgNumDatas LgDataBytes LgNumChildren)
         +++ (nfifoRsToProc LgDataBytes LgNumChildren)).
    
  Definition mcache := memCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize LgNumChildren.
  Definition scN := sc dec execState execNextPc opLd opSt opHt numChildren.

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
        try (intro Hx;
             apply firstElts_SubList with
             (IdxBits:= IdxBits) (TagBits:= TagBits) (LgNumDatas:= LgNumDatas)
                                 (LgDataBytes:= LgDataBytes) in Hx;
             generalize dependent k; eapply DisjList_logic_inv; kdisj_dms).
  Qed.

  Theorem pdecN_mcache_refines_scN: (pdecN ++ pmFifos ++ modFromMeta mcache)%kami <<== scN.
  Proof. (* SKIP_PROOF_ON
    ketrans; [|apply pdecN_memAtomic_refines_scN].

    kmodular.
    - kdisj_edms_cms_ex (wordToNat (wones LgNumChildren)).
    - kdisj_ecms_dms_ex (wordToNat (wones LgNumChildren)).
    - krefl.
    - ketrans; [|apply ios_memAtomicWoQ_memAtomic].
      kmodular with (dropFirstElts LgNumChildren).
      + kdisj_edms_cms_ex (wordToNat (wones LgNumChildren)).
      + kdisj_ecms_dms_ex (wordToNat (wones LgNumChildren)).
      + apply dropFirstElts_Interacting.
      + ketrans_r; [apply modFromMeta_comm_1|].
        ketrans_l; [|apply duplicate_concatMod_comm_2; auto; [kvr|kvr|kequiv|kequiv]].
        replace (dropFirstElts LgNumChildren) with
        (compLabelMaps (dropFirstElts LgNumChildren) (@idElementwise _))
          by apply compLabelMaps_id_right.

        kmodularnp.
        * unfold dropFirstElts; rewrite dropN_dropPs.
          rewrite <-dropPs_nil_idElementwise.
          apply dropPs_disj.
          { apply DisjList_nil_2. }
          { eapply DisjList_SubList; [apply getExtMeths_meths|].
            apply DisjList_comm.
            apply DisjList_SubList with
            (l1:= getDefs (modFromMeta (nfifoRqFromProc IdxBits TagBits LgNumDatas
                                                        LgDataBytes LgNumChildren)));
              [apply firstElts_SubList|].
            apply DisjList_comm, DisjList_app_4.
            { kdisj_dms. }
            { kdisj_cms_dms. }
          }
        * ketrans_r; [apply sinModule_duplicate_1;
                      [kequiv|kvr|knodup_regs|apply nativeFifoS_const_regs]|].
          apply duplicate_traceRefines_drop; auto; [kequiv|kvr| |].
          { vm_compute; tauto. }
          { rewrite <-NativeFifo.nativeFifo_nativeFifoS.
            apply nfifo_refines_nsfifo.
          }
        * apply sinModule_duplicate_1; [kequiv|kvr|knodup_regs|].
          apply nativeFifoS_const_regs with (default:= (getDefaultConst _)).
          
      + apply memCache_refines_memAtomic.
        END_SKIP_PROOF_ON *) admit.
  Qed.

End ProcMem.

