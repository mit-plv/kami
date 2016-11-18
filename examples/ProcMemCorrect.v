Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Specialize Kami.Tactics Kami.Duplicate Kami.ParamDup Kami.ModuleBoundEx.
Require Import Ex.SC Ex.ProcDec Ex.MemAtomic Ex.MemCache Ex.MemCacheSubst Ex.L1Cache.
Require Import Ex.FifoCorrect Ex.MemCorrect Ex.ProcDecSCN Kami.ParametricSyntax.
Require Import Ex.ProcFetchDecode Ex.ProcThreeStage Ex.ProcThreeStDec Ex.ProcFourStDec.

Set Implicit Arguments.

Section ProcMem.
  Variable FifoSize: nat. (* fifo *)
  Variables OpIdx RfIdx IAddrSize: nat. (* processor *)
  Variables IdxBits TagBits LgNumDatas DataBytes: nat. (* memory *)
  Variable Id: Kind.

  Definition AddrSize := L1Cache.AddrBits IdxBits TagBits LgNumDatas.
  Hint Unfold AddrSize: MethDefs.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT DataBytes)
            (getLdDst: LdDstT DataBytes RfIdx)
            (getLdAddr: LdAddrT AddrSize DataBytes)
            (getLdSrc: LdSrcT DataBytes RfIdx)
            (calcLdAddr: LdAddrCalcT AddrSize DataBytes)
            (getStAddr: StAddrT AddrSize DataBytes)
            (getStSrc: StSrcT DataBytes RfIdx)
            (calcStAddr: StAddrCalcT AddrSize DataBytes)
            (getStVSrc: StVSrcT DataBytes RfIdx)
            (getSrc1: Src1T DataBytes RfIdx)
            (getSrc2: Src2T DataBytes RfIdx)
            (getDst: DstT DataBytes RfIdx)
            (exec: ExecT AddrSize DataBytes)
            (getNextPc: NextPcT AddrSize DataBytes RfIdx)
            (alignPc: AlignPcT AddrSize IAddrSize)
            (alignAddr: AlignAddrT AddrSize)
            (predictNextPc: forall ty, fullType ty (SyntaxKind (Bit AddrSize)) -> (* pc *)
                                       Expr ty (SyntaxKind (Bit AddrSize))).

  Variable LgNumChildren: nat.
  Definition numChildren := (wordToNat (wones LgNumChildren)).

  Definition pdecN := pdecs getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                            getStAddr getStSrc calcStAddr getStVSrc
                            getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr numChildren.
  Definition pmFifos :=
    modFromMeta
      ((fifoRqFromProc IdxBits TagBits LgNumDatas DataBytes (rsz FifoSize) LgNumChildren)
         +++ (fifoRsToProc DataBytes (rsz FifoSize) LgNumChildren)).
    
  Definition mcache := memCache IdxBits TagBits LgNumDatas DataBytes Id FifoSize LgNumChildren.
  Definition scN := sc getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                       getStAddr getStSrc calcStAddr getStVSrc
                       getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr numChildren.

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
                                 (DataBytes:= DataBytes) (FifoSize:= FifoSize) in Hx;
             generalize dependent k; eapply DisjList_logic_inv; kdisj_dms).
  Qed.

  Theorem pdecN_mcache_refines_scN: (pdecN ++ pmFifos ++ modFromMeta mcache)%kami <<== scN.
  Proof.
    ketrans; [|apply pdecN_memAtomic_refines_scN with (fifoSize:= rsz FifoSize); auto].

    kmodular.
    - kdisj_edms_cms_ex numChildren.
    - kdisj_ecms_dms_ex numChildren.
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
            (l1:= getDefs (modFromMeta (fifoRqFromProc
                                          IdxBits TagBits LgNumDatas
                                          DataBytes (rsz FifoSize) LgNumChildren)));
              [apply firstElts_SubList|].
            apply DisjList_comm, DisjList_app_4.
            { kdisj_dms. }
            { kdisj_cms_dms. }
          }
        * ketrans_r; [apply sinModule_duplicate_1;
                      [kequiv|kvr|knodup_regs|apply fifoS_const_regs]|].
          apply duplicate_traceRefines_drop; auto; [kequiv|kvr| |].
          { vm_compute; tauto. }
          { rewrite <-Fifo.fifo_fifoS.
            apply fifo_refines_sfifo.
          }
        * apply sinModule_duplicate_1; [kequiv|kvr|knodup_regs|].
          apply fifoS_const_regs.
          
      + apply memCache_refines_memAtomic.
  Qed.

  (** Module definitions for the last theorem:
   * note that struct definitions are now concretized.
   *)
  Definition p4stN :=
    duplicate
      (p4st getOptype getLdDst getLdAddr getLdSrc calcLdAddr
            getStAddr getStSrc calcStAddr getStVSrc
            getSrc1 getSrc2 getDst exec getNextPc
            alignPc alignAddr predictNextPc
            (@d2ePackI _ _ _) (@d2eOpTypeI _ _ _) (@d2eDstI _ _ _) (@d2eAddrI _ _ _)
            (@d2eVal1I _ _ _) (@d2eVal2I _ _ _) (@d2eRawInstI _ _ _) (@d2eCurPcI _ _ _)
            (@d2eNextPcI _ _ _) (@d2eEpochI _ _ _)
            (@f2dPackI _ _) (@f2dRawInstI _ _) (@f2dCurPcI _ _)
            (@f2dNextPcI _ _) (@f2dEpochI _ _)
            (@e2wPackI _ _ _) (@e2wDecInstI _ _ _) (@e2wValI _ _ _)) numChildren.

  Definition memCacheMod :=
    memCacheMod IdxBits TagBits LgNumDatas DataBytes Id FifoSize LgNumChildren.

  (** The final system:
   * p4stN (4-staged multicore processor) ++
   * pmFifos (fifos connecting the processor and memory) ++
   * memCacheMod (two-level cache-based memory)
   *)
  Definition p4stNMemCache := (p4stN ++ pmFifos ++ memCacheMod)%kami.

  Theorem p4stN_mcache_refines_scN: p4stNMemCache <<== scN.
  Proof.
    ketrans; [|apply pdecN_mcache_refines_scN].
    kmodular.
    - kdisj_edms_cms_ex numChildren.
    - kdisj_ecms_dms_ex numChildren.
    - kduplicated.
      ketrans.
      + apply p4st_refines_p3st; auto.
      + apply p3st_refines_pdec; auto.
    - kmodular.
      + kdisj_edms_cms_ex numChildren.
      + kdisj_ecms_dms_ex numChildren.
      + krefl.
      + apply memCacheMod_refines_memCache.
  Qed.

End ProcMem.

