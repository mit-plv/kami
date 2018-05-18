Require Import Kami.Ex.Timing.Specification.
Require Import List.
Require Import Notations.
Require Import Lib.Word.
Require Import Kami.Syntax Kami.Semantics.
Require Import Ex.IsaRv32 Ex.SC.
Require Import Lib.CommonTactics.
Require Import Logic.FunctionalExtensionality.

(** This file provides Gallina functions that perform simulated
    executions of RISC-V code with taint tracking.  Code that
    satisfies these taint checks provably satisfies the abstract-level
    hiding property in Specification.v.  Data within the taint-checker
    is represented as an option type, with None indicating tainted
    data that must not be used in ways that affect timing via memory
    access patterns or control flow. *)

Definition pseudoData := option data.

Definition pseudoRegfile := register -> pseudoData.

Definition prset (rf : pseudoRegfile) (r : register) (v : pseudoData) : pseudoRegfile :=
  if weqb r (wzero _)
  then rf
  else (fun r' => if weqb r' r then v else rf r').

Definition pseudoMemory := address -> pseudoData.

Definition taintBranchTaken (rf : pseudoRegfile) (inst : data) : option bool :=
  let r1 := evalExpr (getRs1E #inst)%kami_expr in
  let r2 := evalExpr (getRs2E #inst)%kami_expr in
  match rf r1, rf r2 with
  | Some v1, Some v2 => 
    let funct := evalExpr (getFunct3E #inst)%kami_expr in
    Some (if weqb funct rv32iF3BEQ
          then weqb v1 v2
          else if weqb funct rv32iF3BNE
               then negb (weqb v1 v2)
               else if weqb funct rv32iF3BLT
                    then weqb (split2 31 1 (v1 ^- v2)) $1
                    else if weqb funct rv32iF3BGE
                         then weqb (split2 31 1 (v1 ^- v2)) $0
                         else if weqb funct rv32iF3BLTU
                              then if wlt_dec v1 v2 then true else false
                              else if weqb funct rv32iF3BGEU
                                   then if wlt_dec v1 v2 then false else true
                                   else false)
  | _, _ => None
  end.

Definition taintNextPc (rf : pseudoRegfile) (pc : address) (inst : data) : option address :=
  let opcode := evalExpr (getOpcodeE #inst)%kami_expr in
  if weqb opcode rv32iOpJAL
  then Some (pc ^+ (split1 16 4 (wlshift (evalExpr (getOffsetUJE #inst)%kami_expr) 1)))
  else if weqb opcode rv32iOpJALR
       then match rf (evalExpr (getRs1E #inst)%kami_expr) with
            | Some v1 => Some ((split1 16 16 v1) ^+ (sext (evalExpr (getOffsetIE #inst)%kami_expr) 4))
            | None => None
            end
       else if weqb opcode rv32iOpBRANCH
            then match taintBranchTaken rf inst with
                 | Some taken => 
                   Some (pc ^+ if taken
                               then sext (wlshift (evalExpr (getOffsetSBE #inst)%kami_expr) 1) 4
                               else $4)
                 | None => None
                 end
            else Some (pc ^+ $4).

Definition taintStep (rf : pseudoRegfile) (pm : progMem) (pc : address) (mem : pseudoMemory) : option (pseudoRegfile * address * pseudoMemory) :=
  let inst := pm (evalExpr (rv32iAlignPc type pc)) in
  match (evalExpr (rv32iGetOptype type inst)) with
  | WO~0~0~0 (* opLd *) => 
    let addr := evalExpr (rv32iGetLdAddr type inst) in
    let dstIdx := evalExpr (rv32iGetLdDst type inst) in
    let srcIdx := evalExpr (rv32iGetLdSrc type inst) in
    let srcVal := rf srcIdx in
    match srcVal with
    | None => None
    | Some sv =>
      let laddr := evalExpr (rv32iCalcLdAddr type addr sv) in
      let laddr_aligned := evalExpr (rv32iAlignAddr type laddr) in
      let val := mem laddr_aligned in
      Some (prset rf dstIdx val, pc ^+ $4, mem)
    end
  | WO~0~0~1 (* opSt *) =>
    let addr := evalExpr (rv32iGetStAddr type inst) in
    let srcIdx := evalExpr (rv32iGetStSrc type inst) in
    let srcVal := rf srcIdx in
    match srcVal with
    | None => None
    | Some sv =>
      let vsrcIdx := evalExpr (rv32iGetStVSrc type inst) in
      let stVal := rf vsrcIdx in
      let saddr := evalExpr (rv32iCalcStAddr type addr sv) in
      let saddr_aligned := evalExpr (rv32iAlignAddr type saddr) in
      Some (rf, pc ^+ $4, (fun a => if weqb a saddr_aligned then stVal else mem a))
    end
  | WO~0~1~0 (* opTh *) => Some (rf, pc ^+ $4, mem)
  | WO~1~0~0 (* opFh *) =>
    let dst := evalExpr (rv32iGetDst type inst) in
    Some (prset rf dst None, pc ^+ $4, mem)
  | WO~0~1~1 (* opNm *) =>
    match taintNextPc rf pc inst with
    | None => None
    | Some nextPc =>
      let src1 := evalExpr (rv32iGetSrc1 type inst) in
      let src2 := evalExpr (rv32iGetSrc2 type inst) in
      let dst := evalExpr (rv32iGetDst type inst) in
      let execVal := match rf src1, rf src2 with
                     | Some val1, Some val2 => Some (evalExpr (rv32iExec type val1 val2 pc inst))
                     | _, _ => None
                     end in
      Some (prset rf dst execVal, nextPc, mem)
    end
  | _ => None
  end.

Definition transformable (pd1 pd2 : pseudoData) : bool :=
  match pd1, pd2 with
  | None, Some _ => false
  | Some val1, Some val2 => weqb val1 val2
  | _, _ => true
  end.

Fixpoint allTransformable (sz : nat) : (word sz -> pseudoData) -> (word sz -> pseudoData) -> bool :=
  match sz with
  | 0 => fun (tbl1 tbl2 : word 0 -> pseudoData) => transformable (tbl1 WO) (tbl2 WO)
  | S sz' => fun (tbl1 tbl2 : word (S sz') -> pseudoData) =>
               andb (allTransformable sz' (fun w => tbl1 (WS false w)) (fun w => tbl2 (WS false w)))
                    (allTransformable sz' (fun w => tbl1 (WS true w)) (fun w => tbl2 (WS true w)))
  end.

Definition rfTransformable := allTransformable 5.

Definition memTransformable := allTransformable 16.

Fixpoint safeUntil (fuel : nat) (rf : pseudoRegfile) (pm : progMem) (pc : address) (mem : pseudoMemory) (goalrf : pseudoRegfile) (goalpc : address) (goalmem : pseudoMemory) : bool :=
  match fuel with
  | S fuel' =>
    match taintStep rf pm pc mem with
    | None => false
    | Some (rf', pc', mem') =>
      if (weqb pc' goalpc && rfTransformable rf' goalrf && memTransformable mem' goalmem)%bool
      then true
      else safeUntil fuel' rf' pm pc' mem' goalrf goalpc goalmem
    end
  | 0 => false
  end.

Definition mask {sz} (ptbl : word sz -> pseudoData) (tbl : word sz -> data) : word sz -> data :=
  fun a => match ptbl a with
           | Some d => d
           | None => tbl a
           end.

Theorem at_equiv : forall sz pt1 pt2,
    allTransformable sz pt1 pt2 = true
    <-> forall w, transformable (pt1 w) (pt2 w) = true.
Proof.
  intuition idtac.
  - induction w; auto.
    apply (IHw (fun a => pt1 (WS b a)) (fun a => (pt2 (WS b a)))).
    simpl in H.
    rewrite Bool.andb_true_iff in H.
    destruct H; destruct b; auto.
  - induction sz; simpl; auto.
    rewrite Bool.andb_true_iff.
    auto.
Qed.

Lemma transformable_mask :
  forall sz pt1 pt2 t,
    allTransformable sz pt1 pt2 = true ->
    mask pt1 t = mask pt2 (mask pt1 t).
Proof.
  intros.
  extensionality w.
  rewrite at_equiv in H.
  specialize (H w).
  unfold mask.
  destruct (pt1 w); destruct (pt2 w);
    simpl in *;
    try rewrite weqb_true_iff in *;
    auto.
  discriminate.
Qed.

Definition abstractHiding_tainted prf pm pc pmem : Prop :=
  forall trace fhTrace rmask mmask,
    hasTrace (mask prf rmask) pm pc (mask pmem mmask) trace ->
    extractFhTrace trace = fhTrace ->
    forall fhTrace' rmask' mmask',
      length fhTrace = length fhTrace' ->
      exists trace',
        hasTrace (mask prf rmask') pm pc (mask pmem mmask') trace' /\
        censorTrace trace = censorTrace trace' /\
        extractFhTrace trace' = fhTrace'.

Lemma abstractHiding_tainted_normal :
  forall prf pm pc pmem,
    abstractHiding_tainted prf pm pc pmem ->
    forall rf mem,
      abstractHiding (mask prf rf) pm pc (mask pmem mem).
Proof.
  unfold abstractHiding.
  intros prf pm pc pmem Hat rf mem trace fhTrace Hht Het fhTrace' Hlen.
  eapply Hat; eauto.
Qed.

Lemma transformableHiding :
  forall rf pm pc mem rf' mem',
    rfTransformable rf rf' = true ->
    memTransformable mem mem' = true ->
    abstractHiding_tainted rf' pm pc mem' ->
    abstractHiding_tainted rf pm pc mem.
Proof.
  intros.
  unfold abstractHiding_tainted.
  intros.
  unfold rv32iRfIdx, rv32iAddrSize in *.
  replace (mask rf rmask) with (mask rf' (mask rf rmask)) in H2 by (apply eq_sym; apply transformable_mask; auto).
  replace (mask mem mmask) with (mask mem' (mask mem mmask)) in H2 by (apply eq_sym; apply transformable_mask; auto).
  specialize (H1 _ _ _ _ H2 H3 _ (mask rf rmask') (mask mem mmask') H4).
  unfold rv32iRfIdx, rv32iAddrSize in *.
  replace (mask rf' (mask rf rmask')) with (mask rf rmask') in H1 by (apply transformable_mask; auto).
  replace (mask mem' (mask mem mmask')) with (mask mem mmask') in H1 by (apply transformable_mask; auto).
  assumption.
Qed.

Lemma transformableStep : forall pm rf1 pc1 mem1 rf1' pc1' mem1' rf2' pc2' mem2',
    rfTransformable rf1 rf1' = true ->
    pc1 = pc1' ->
    memTransformable mem1 mem1' = true ->
    taintStep rf1' pm pc1' mem1' = Some (rf2', pc2', mem2') ->
    exists rf2 pc2 mem2,
      taintStep rf1 pm pc1 mem1 = Some (rf2, pc2, mem2) /\
      rfTransformable rf2 rf2' = true /\
      pc2 = pc2' /\
      memTransformable mem2 mem2' = true.
Proof.
  intros.
  subst.
  unfold rfTransformable, memTransformable in *.
  repeat rewrite at_equiv in *.
  unfold taintStep in *.
  do 7 (match goal with
        | [ H : match ?x with | _ => _ end = _ |- _ ] => destruct x
        | [ H : (if ?b then _ else _) = _ |- _ ] => destruct b
        end; try discriminate).
  - replace (taintNextPc rf1 pc1' (pm (evalExpr (rv32iAlignPc type pc1')))) with (taintNextPc rf1' pc1' (pm (evalExpr (rv32iAlignPc type pc1')))).
    + match goal with
      | [ H : match ?x with | _ => _ end = _ |- _ ] => destruct x
      end; try discriminate.
      match goal with
      | [ H : Some (?x, ?y, ?z) = Some (?x', ?y', ?z') |- _ ] => assert (x = x') by congruence; assert (y = y') by congruence; assert (z = z') by congruence; clear H; subst
      end.
      do 3 eexists; intuition idtac; try reflexivity; rewrite at_equiv; intros; auto.
      clear H1.
      unfold prset.
      match goal with
      | [ |- context[weqb ?x (wzero ?sz)] ] => destruct (weqb x (wzero sz))
      end; auto.
      match goal with
      | [ |- context[@weqb ?sz ?x ?y] ] => destruct (@weqb sz x y)
      end; auto.
      repeat match goal with
             | [ |- context[rf1 ?r] ] => assert (transformable (rf1 r) (rf1' r) = true) by auto; destruct (rf1 r); destruct (rf1' r)
             end; auto; unfold transformable in *; repeat rewrite weqb_true_iff in *; subst; auto.
      discriminate.
    + unfold taintNextPc in *.
      repeat match goal with
             | [ |- context[weqb (evalExpr (getOpcodeE ?i)) ?o] ] => destruct (weqb (evalExpr (getOpcodeE i)) o); auto
             end.
      * repeat match goal with
               | [ |- context[rf1 ?r] ] => assert (transformable (rf1 r) (rf1' r) = true) by auto; destruct (rf1 r); destruct (rf1' r)
               end; auto; unfold transformable in *; repeat rewrite weqb_true_iff in *; subst; auto; discriminate.
      * replace (taintBranchTaken rf1 (pm (evalExpr (rv32iAlignPc type pc1')))) with (taintBranchTaken rf1' (pm (evalExpr (rv32iAlignPc type pc1')))); auto.
        unfold taintBranchTaken in *.
        repeat match goal with
               | [ |- context[rf1 ?r] ] => assert (transformable (rf1 r) (rf1' r) = true) by auto; destruct (rf1 r); destruct (rf1' r)
               end; auto; unfold transformable in *; repeat rewrite weqb_true_iff in *; subst; auto; discriminate.
  - match goal with
    | [ H : match rf1' ?r with | _ => _ end = _ |- _ ] =>
      assert (transformable (rf1 r) (rf1' r) = true) by auto; destruct (rf1 r); destruct (rf1' r)
    end;
      auto;
      repeat match goal with
             | [ H : transformable _ _ = _ |- _ ] => unfold transformable in H
             end;
      repeat rewrite weqb_true_iff in *; subst; auto; try discriminate.
    match goal with
    | [ H : Some (?x, ?y, ?z) = Some (?x', ?y', ?z') |- _ ] => assert (x = x') by congruence; assert (y = y') by congruence; assert (z = z') by congruence; clear H; subst
    end.
    do 3 eexists; intuition idtac; try reflexivity; rewrite at_equiv; intros; auto.
    match goal with
    | [ |- context[@weqb ?sz ?x ?y] ] => destruct (@weqb sz x y); auto
    end.
  - match goal with
    | [ H : Some (?x, ?y, ?z) = Some (?x', ?y', ?z') |- _ ] => assert (x = x') by congruence; assert (y = y') by congruence; assert (z = z') by congruence; clear H; subst
    end.
    do 3 eexists; intuition idtac; try reflexivity; rewrite at_equiv; intros; auto.
  - match goal with
    | [ H : Some (?x, ?y, ?z) = Some (?x', ?y', ?z') |- _ ] => assert (x = x') by congruence; assert (y = y') by congruence; assert (z = z') by congruence; clear H; subst
    end.
    do 3 eexists; intuition idtac; try reflexivity; rewrite at_equiv; intros; auto.
    unfold prset.
    repeat match goal with
           | [ |- context[@weqb ?sz ?x ?y] ] => destruct (@weqb sz x y)
           end; auto.
  - match goal with
    | [ H : match rf1' ?r with | _ => _ end = _ |- _ ] =>
      assert (transformable (rf1 r) (rf1' r) = true) by auto; destruct (rf1 r); destruct (rf1' r)
    end;
      auto;
      repeat match goal with
             | [ H : transformable _ _ = _ |- _ ] => unfold transformable in H
             end;
      repeat rewrite weqb_true_iff in *; subst; auto; try discriminate.
    match goal with
    | [ H : Some (?x, ?y, ?z) = Some (?x', ?y', ?z') |- _ ] => assert (x = x') by congruence; assert (y = y') by congruence; assert (z = z') by congruence; clear H; subst
    end.
    do 3 eexists; intuition idtac; try reflexivity; rewrite at_equiv; intros; auto.
    unfold prset.
    repeat match goal with
           | [ |- context[@weqb ?sz ?x ?y] ] => destruct (@weqb sz x y); auto
           end.
Qed.

Lemma safeShift :
  forall fuel pm rf1 pc1 mem1 rf1' pc1' mem1' rf2 pc2 mem2 rf2' pc2' mem2',
    safeUntil fuel rf1 pm pc1 mem1 rf2 pc2 mem2 = true ->
    taintStep rf1 pm pc1 mem1 = Some (rf1', pc1', mem1') ->
    taintStep rf2 pm pc2 mem2 = Some (rf2', pc2', mem2') ->
    safeUntil fuel rf1' pm pc1' mem1' rf2' pc2' mem2' = true.
Proof.
  induction fuel; intros; simpl in *; try discriminate.
  rewrite H0 in H.
  match goal with
  | [ H : (if ?b then _ else _) = _ |- _ ] =>
    case_eq b;
      intros;
      match goal with
      | [ H' : ?b = _ |- _ ] => rewrite H' in H
      end
  end.
  - repeat rewrite Bool.andb_true_iff in *.
    intuition idtac.
    rewrite weqb_true_iff in *.
    subst.
    destruct (transformableStep _ _ _ _ _ _ _ _ _ _ H5 eq_refl H4 H1) as [rf' [pc' [mem' [Hts [Hrf [Hpc Hmem]]]]]].
    subst.
    rewrite Hts.
    rewrite (proj2 (weqb_true_iff _ _)) by reflexivity.
    rewrite Hrf.
    rewrite Hmem.
    reflexivity.
  - remember H as H' eqn:Heq; clear Heq.
    destruct fuel; simpl in H'; try discriminate.
    match goal with
    | [ H : match ?x with | _ => _ end = _ |- _ ] => case_eq x; intros; match goal with | [ H' : x = _ |- _ ] => rewrite H' in H end; simpl in H; try discriminate
    end.
    destruct p as [[? ?] ?].
    specialize (IHfuel _ _ _ _ _ _ _ _ _ _ _ _ _ H H3 H1).
    rewrite IHfuel.
    match goal with
    | [ |- (if ?b then _ else _) = _ ] => destruct b; auto
    end.
Qed.

Lemma stepSafeHiding : forall rf pm pc mem rf' pc' mem',
    taintStep rf pm pc mem = Some (rf', pc', mem') ->
    abstractHiding_tainted rf' pm pc' mem' ->
    abstractHiding_tainted rf pm pc mem.
Proof.
Admitted.

Theorem segmentSafeHiding : forall fuel rf pm pc mem goalrf goalpc goalmem,
    safeUntil fuel rf pm pc mem goalrf goalpc goalmem = true ->
    abstractHiding_tainted goalrf pm goalpc goalmem ->
    abstractHiding_tainted rf pm pc mem.
Proof.
  induction fuel; intros; try discriminate.
  simpl in H.
  case_eq (taintStep rf pm pc mem);
    intros;
    match goal with
    | [ H : taintStep _ _ _ _ = _ |- _ ] => rewrite H in *
    end;
    try discriminate.
  destruct p as [[? ?] ?].
  match goal with
  | [ H : (if ?b then _ else _) = _ |- _ ] =>
    case_eq b;
      intros;
      match goal with
      | [ H : b = _ |- _ ] => rewrite H in *
      end
  end; eapply stepSafeHiding; eauto.
  repeat rewrite Bool.andb_true_iff in *.
  intuition idtac.
  rewrite weqb_true_iff in *.
  subst.
  eapply transformableHiding; eauto.
Qed.

Theorem loopSafeHiding : forall fuel rf pm pc mem,
    safeUntil fuel rf pm pc mem rf pc mem = true ->
    abstractHiding_tainted rf pm pc mem.
Proof.
  unfold abstractHiding_tainted.
  intros fuel rf pm pc mem Hsafe trace fhTrace rmask mmask Hht.
  remember (mask rf rmask) as mrf.
  remember (mask mem mmask) as mmem.
  generalize rf mem rmask mmask Heqmrf Heqmmem fuel Hsafe fhTrace.
  clear rf mem rmask mmask Heqmrf Heqmmem fuel Hsafe fhTrace.
  induction Hht; intros.
  - exists nil; intuition idtac; auto.
    + constructor.
    + match goal with
      | [ H : extractFhTrace nil = _ |- _ ] => simpl in H; subst
      end.
      destruct fhTrace'; try discriminate.
      reflexivity.
  - match goal with
    | [ Hex : extractFhTrace _ = _, Hlen : length _ = length _ |- _ ] =>
      simpl in H;
        specialize (IHHht _ _ _ _ Heqmrf Heqmmem _ Hsafe _ Hex _ rmask' mmask' Hlen)
    end.
    destruct IHHht as [trace'' [Hht' [Hct' Hex']]].
    exists (Nop pc :: trace'').
    intuition idtac.
    + constructor; auto.
    + simpl; f_equal; auto.
  - remember Hsafe as Hsafe' eqn:Heq; clear Heq.
    destruct fuel; simpl in Hsafe; try discriminate.
    case_eq (taintStep rf0 pm pc mem0); intros;
      match goal with
      | [ H : taintStep rf0 pm pc mem0 = _ |- _ ] => rewrite H in Hsafe; try discriminate; remember H as Hts eqn:Heq; clear Heq
      end.
    destruct p as [[? ?] ?].
    unfold taintStep in Hts.
    match goal with
    | [ H : _ = inst |- _ ] => rewrite H in Hts
    end.
    match goal with
    | [ H : _ = opLd |- _ ] => rewrite H in Hts
    end.
    unfold opLd in *.
    fold srcIdx in Hts.
    assert (srcVal = (mask rf0 rmask) srcIdx) as HsrcVal by (unfold srcVal; congruence).
    unfold mask in HsrcVal.
    case_eq (rf0 srcIdx); intros;
      match goal with
      | [ H : rf0 srcIdx = _ |- _ ] => rewrite H in Hts; rewrite H in HsrcVal
      end; try discriminate.
    fold addr in Hts.
    rewrite <- HsrcVal in Hts.
    fold laddr in Hts.
    replace (evalExpr (rv32iCalcLdAddr type addr srcVal)) with laddr in Hts by (unfold laddr; congruence).
    fold laddr_aligned in Hts.
    fold dstIdx in Hts.
      match goal with
      | [ H : Some (?x, ?y, ?z) = Some (?x', ?y', ?z') |- _ ] => assert (x = x') by congruence; assert (y = y') by congruence; assert (z = z') by congruence; clear H; subst x' y' z'
      end.
      pose (safeShift _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe' H5 H5) as Hsafenew'; remember Hsafenew' as Hsafenew eqn:Heq; clear Heq Hsafenew'.
      clear Hsafe'.
      match goal with
      | [ H : safeUntil ?f ?rf ?pm ?pc ?mem ?rf ?pc ?mem = _,
              IH : forall _ _ _ _, _ -> _ -> forall _, safeUntil _ _ _ ?pc' _ _ _ _ = _ -> _ |- _ ] =>
        replace pc with pc' in H;
          [pose (fun rm mm Heq1 Heq2 => IHHht _ _ rm mm Heq1 Heq2 _ H) as IHinst'; remember IHinst' as IHinst eqn:Heq; clear IHinst' Heq|]
      end.
    + case_eq (mem0 laddr_aligned); intros.
      * specialize (IHinst rmask mmask).
        assert (rset rf dstIdx val = mask (prset rf0 dstIdx (mem0 laddr_aligned)) rmask).
        -- extensionality a.
           rewrite Heqmrf.
           rewrite H2.
           rewrite Heqmmem.
           unfold rset, mask, prset.
           destruct (weq dstIdx (wzero _)); try tauto.
           case_eq (weqb dstIdx (wzero _)); intros; try rewrite weqb_true_iff in *; try tauto.
           unfold evalExpr; fold evalExpr.
           rewrite H7.
           destruct (weq a dstIdx); case_eq (weqb a dstIdx); intros; try solve [ rewrite weqb_true_iff in *; tauto | unfold not in *; rewrite <- weqb_true_iff in *; congruence ].
           reflexivity.
        -- match goal with
           | [ H : extractFhTrace (_ :: _) = _ |- _ ] => simpl in H
           end.
           specialize (IHinst H8 Heqmmem _ H3 _ rmask' mmask' H4).
           destruct IHinst as [trace'0 [Hht' [Hct' Het']]].
           exists (Rd pc laddr_aligned val :: trace'0).
           intuition idtac.
           ++ pose (htLd inst val (mask rf0 rmask') pm pc (mask mem0 mmask') trace'0 H H0) as Hld.
              Opaque evalExpr.
              simpl in Hld.
              Transparent evalExpr.
              fold srcIdx in Hld.
              fold dstIdx in Hld.
              fold addr in Hld.
              replace (mask rf0 rmask' srcIdx) with srcVal in Hld by (unfold mask; rewrite H6; auto).
              replace (evalExpr (rv32iCalcLdAddr type addr srcVal)) with laddr in Hld by (unfold laddr; congruence).
              fold laddr_aligned in Hld.
              apply Hld; auto.
              ** subst.
                 unfold mask.
                 rewrite H7.
                 auto.
              ** match goal with
                 | [ H : hasTrace ?r _ ?c _ ?t |- hasTrace ?r' _ ?c' _ ?t ] => replace r' with r; [replace c' with c; auto|]
                 end.
                 --- subst rf.
                     clear - H0.
                     unfold rv32iGetOptype in H0.
                     unfold evalExpr in H0; fold evalExpr in H0.
                     repeat match goal with
                            | [ H : context[isEq ?k ?x ?y] |- _ ] => destruct (isEq k x y); try discriminate
                            end.
                     unfold rv32iNextPc.
                     unfold evalExpr; fold evalExpr.
                     repeat rewrite e.
                     repeat match goal with
                            | [ |- context[isEq ?k ?x ?y] ] => destruct (isEq k x y); try discriminate
                            end.
                     reflexivity.
                 --- subst val.
                     subst mem.
                     extensionality a.
                     unfold mask, prset, rset.
                     destruct (weq dstIdx (wzero _)); try tauto.
                     case_eq (weqb dstIdx (wzero _)); intros; try rewrite weqb_true_iff in *; try tauto.
                     unfold evalExpr; fold evalExpr.
                     rewrite H7.
                     destruct (weq a dstIdx); case_eq (weqb a dstIdx); intros; try solve [ rewrite weqb_true_iff in *; tauto | unfold not in *; rewrite <- weqb_true_iff in *; congruence ].
           ++ simpl.
              f_equal.
              auto.
      * specialize (IHinst (rset rmask dstIdx val) mmask).
        assert (rset rf dstIdx val = mask (prset rf0 dstIdx (mem0 laddr_aligned)) (rset rmask dstIdx val)).
        -- extensionality a.
           subst rf val mem.
           unfold rset, mask, prset.
           destruct (weq dstIdx (wzero _)); try tauto.
           case_eq (weqb dstIdx (wzero _)); intros; try rewrite weqb_true_iff in *; try tauto.
           unfold evalExpr; fold evalExpr.
           rewrite H7.
           destruct (weq a dstIdx); case_eq (weqb a dstIdx); intros; try solve [ rewrite weqb_true_iff in *; tauto | unfold not in *; rewrite <- weqb_true_iff in *; congruence ].
           reflexivity.
        -- match goal with
           | [ H : extractFhTrace (_ :: _) = _ |- _ ] => simpl in H
           end.
           specialize (IHinst H8 Heqmmem _ H3 _ (rset rmask' dstIdx (mmask' laddr_aligned)) mmask' H4).
           destruct IHinst as [trace'0 [Hht' [Hct' Het']]].
           exists (Rd pc laddr_aligned (mmask' laddr_aligned) :: trace'0).
           intuition idtac.
           ++ pose (htLd inst (mmask' laddr_aligned) (mask rf0 rmask') pm pc (mask mem0 mmask') trace'0 H H0) as Hld.
              Opaque evalExpr.
              simpl in Hld.
              Transparent evalExpr.
              fold srcIdx in Hld.
              fold dstIdx in Hld.
              fold addr in Hld.
              replace (mask rf0 rmask' srcIdx) with srcVal in Hld by (unfold mask; rewrite H6; auto).
              replace (evalExpr (rv32iCalcLdAddr type addr srcVal)) with laddr in Hld by (unfold laddr; congruence).
              fold laddr_aligned in Hld.
              apply Hld; auto.
              ** subst.
                 unfold mask.
                 rewrite H7.
                 auto.
              ** match goal with
                 | [ H : hasTrace ?r _ ?c _ ?t |- hasTrace ?r' _ ?c' _ ?t ] => replace r' with r; [replace c' with c; auto|]
                 end.
                 --- subst rf.
                     clear - H0.
                     unfold rv32iGetOptype in H0.
                     unfold evalExpr in H0; fold evalExpr in H0.
                     repeat match goal with
                            | [ H : context[isEq ?k ?x ?y] |- _ ] => destruct (isEq k x y); try discriminate
                            end.
                     unfold rv32iNextPc.
                     unfold evalExpr; fold evalExpr.
                     repeat rewrite e.
                     repeat match goal with
                            | [ |- context[isEq ?k ?x ?y] ] => destruct (isEq k x y); try discriminate
                            end.
                     reflexivity.
                 --- extensionality a.
                     unfold mask, prset, rset.
                     destruct (weq dstIdx (wzero _)); try tauto.
                     case_eq (weqb dstIdx (wzero _)); intros; try rewrite weqb_true_iff in *; try tauto.
                     unfold evalExpr; fold evalExpr.
                     rewrite H7.
                     destruct (weq a dstIdx); case_eq (weqb a dstIdx); intros; try solve [ rewrite weqb_true_iff in *; tauto | unfold not in *; rewrite <- weqb_true_iff in *; congruence ].
           ++ simpl.
              f_equal.
              auto.
    + clear - H0.
      unfold rv32iGetOptype in H0.
      unfold evalExpr in H0; fold evalExpr in H0.
      repeat match goal with
             | [ H : context[isEq ?k ?x ?y] |- _ ] => destruct (isEq k x y); try discriminate
             end.
      unfold rv32iNextPc.
      unfold evalExpr; fold evalExpr.
      repeat rewrite e.
      repeat match goal with
             | [ |- context[isEq ?k ?x ?y] ] => destruct (isEq k x y); try discriminate
             end.
      reflexivity.
      
Admitted.
