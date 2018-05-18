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

Ltac nextpc :=
  try match goal with
      | [ |- context[rv32iNextPc _ ?rf _ _] ] => subst rf
      end;
  match goal with
  | [ H : context[rv32iGetOptype] |- _ ] =>
    unfold rv32iGetOptype in H;
    unfold evalExpr in H; fold evalExpr in H
  end;
  repeat match goal with
         | [ H : context[isEq ?k ?x ?y] |- _ ] => destruct (isEq k x y); try discriminate
         end;
  unfold rv32iNextPc;
  unfold evalExpr; fold evalExpr;
  match goal with
  | [ H : context[getOpcodeE] |- _ ] => rewrite H
  end;
  repeat match goal with
         | [ |- context[isEq ?k ?x ?y] ] => destruct (isEq k x y); try discriminate
         end;
  reflexivity.

Ltac weqb_tauto :=
  match goal with
  | [ H : ?x = ?y, Hb : weqb ?x ?y = false |- _ ] => apply (proj2 (weqb_true_iff _ _)) in H; congruence
  | [ H : ?x <> ?y, Hb : weqb ?x ?y = true |- _ ] => rewrite weqb_true_iff in Hb; tauto
  end.

Ltac deq :=
  match goal with
  | [ |- context[isEq ?k ?x ?y] ] => destruct (isEq k x y); case_eq (weqb x y)
  | [ |- context[weq ?x ?y] ] => destruct (weq x y); case_eq (weqb x y)
  end; intros; try weqb_tauto; auto.

Lemma taintBranchTaken_correct : forall rf rmask inst,
    evalExpr (getOpcodeE #(inst)%kami_expr) = rv32iOpBRANCH ->
    taintBranchTaken rf inst = None
    \/ taintBranchTaken rf inst = Some (evalExpr (rv32iBranchTaken type (mask rf rmask) inst)).
Proof.
  intros.
  case_eq (taintBranchTaken rf inst); intuition idtac.
  right.
  rewrite <- H0.
  unfold taintBranchTaken in *.
  unfold rv32iBranchTaken.
  unfold evalExpr; fold evalExpr.
  match goal with
  | [ |- context[isEq (Bit 7) ?x ?y] ] => destruct (isEq (Bit 7) x y); try tauto
  end.
  unfold getRs1ValueE, getRs2ValueE.
  unfold evalExpr; fold evalExpr.
  unfold mask.
  destruct (rf (evalExpr (getRs1E #(inst)%kami_expr))); try discriminate.
  destruct (rf (evalExpr (getRs2E #(inst)%kami_expr))); try discriminate.
  repeat match goal with
         | [ |- context[isEq (Bit 3) ?x ?y] ] => destruct (isEq (Bit 3) x y); try tauto
         end;
    unfold evalConstT in *;
    try match goal with
        | [ H : ?x = ?y |- context[weqb ?x ?y] ] => repeat rewrite H in *
        end;
    repeat match goal with
           | [ |- context[weqb ?x ?y] ] =>
             try replace (weqb x y) with true in * by reflexivity;
               try replace (weqb x y) with false in * by reflexivity
           end; unfold evalUniBool, evalUniBit, evalBinBit, evalBinBitBool; auto; try deq.
  - destruct (wlt_dec d d0); auto.
  - repeat match goal with
           | [ H : ?x <> ?y |- context[weqb ?x ?y] ] =>
             case_eq (weqb x y); intros;
               try (rewrite weqb_true_iff in *; tauto);
               try match goal with
                   | [ H : weqb x y = _ |- _ ] => rewrite H
                   end
           end; auto.
Qed.
  
Lemma taintNextPc_correct : forall rf rmask pc inst,
    taintNextPc rf pc inst = None
    \/ taintNextPc rf pc inst = Some (evalExpr (rv32iNextPc type (mask rf rmask) pc inst)).
Proof.
  intros.
  case_eq (taintNextPc rf pc inst); intuition idtac.
  right.
  rewrite <- H.
  unfold taintNextPc in *.
  unfold rv32iNextPc.
  unfold evalExpr; fold evalExpr.
  repeat match goal with
         | [ |- context[isEq (Bit 7) ?x ?y] ] => destruct (isEq (Bit 7) x y)
         end;
    unfold evalConstT in *;
    try congruence;
    try match goal with
        | [ H : ?x = ?y |- context[weqb ?x ?y] ] => repeat rewrite H in *
        end;
    repeat match goal with
           | [ |- context[weqb ?x ?y] ] =>
             try replace (weqb x y) with true in * by reflexivity;
               try replace (weqb x y) with false in * by reflexivity
           end.
  - unfold getOffsetUJE.
    unfold evalExpr; fold evalExpr.
    unfold evalBinBit, evalUniBit.
    unfold rv32iAddrSize.
    match goal with
    | [ |- context[match ?x with _ => _ end] ] =>
      let x' := eval hnf in x in change x with x'; cbv beta iota
    end.
    eq_rect_simpl.
    reflexivity.
  - unfold getRs1ValueE.
    unfold evalExpr; fold evalExpr.
    unfold mask.
    destruct (rf (evalExpr (getRs1E #(inst)%kami_expr))); try discriminate.
    unfold getOffsetIE.
    unfold evalExpr; fold evalExpr.
    unfold evalBinBit, evalUniBit.
    unfold rv32iAddrSize.
    repeat match goal with
           | [ |- context[match ?x with _ => _ end] ] =>
             let x' := eval hnf in x in change x with x'; cbv beta iota
           end.
    eq_rect_simpl.
    reflexivity.
  - destruct (taintBranchTaken_correct rf rmask inst e); rewrite H0 in H; try discriminate.
    rewrite H0.
    unfold getOffsetSBE.
    unfold evalExpr; fold evalExpr.
    unfold evalUniBit, evalBinBit.
    destruct (evalExpr (rv32iBranchTaken type (mask rf rmask) inst)); auto.
    match goal with
    | [ |- context[match ?x with _ => _ end] ] =>
      let x' := eval hnf in x in change x with x'; cbv beta iota
    end.
    eq_rect_simpl.
    reflexivity.
  - repeat match goal with
           | [ H : ?x <> ?y |- context[weqb ?x ?y] ] =>
             case_eq (weqb x y); intros;
               try (rewrite weqb_true_iff in *; tauto);
               try match goal with
                   | [ H : weqb x y = _ |- _ ] => rewrite H
                   end
           end; auto.
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
      replace pc with pc' in H by nextpc;
        pose (fun rm mm Heq1 Heq2 => IHHht _ _ rm mm Heq1 Heq2 _ H) as IHinst'; remember IHinst' as IHinst eqn:Heq; clear IHinst' Heq
    end.
    case_eq (mem0 laddr_aligned); intros.
    + specialize (IHinst rmask mmask).
      assert (rset rf dstIdx val = mask (prset rf0 dstIdx (mem0 laddr_aligned)) rmask).
      * extensionality a.
        rewrite Heqmrf.
        rewrite H2.
        rewrite Heqmmem.
        unfold rset, mask, prset.
        unfold evalExpr; fold evalExpr.
        rewrite H7.
        repeat deq.
      * match goal with
        | [ H : extractFhTrace (_ :: _) = _ |- _ ] => simpl in H
        end.
        specialize (IHinst H8 Heqmmem _ H3 _ rmask' mmask' H4).
        destruct IHinst as [trace'0 [Hht' [Hct' Het']]].
        exists (Rd pc laddr_aligned val :: trace'0).
        intuition idtac; try solve [simpl; f_equal; auto].
        pose (htLd inst val (mask rf0 rmask') pm pc (mask mem0 mmask') trace'0 H H0) as Hld.
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
        -- subst.
           unfold mask.
           rewrite H7.
           auto.
        -- match goal with
           | [ H : hasTrace ?r _ ?c _ ?t |- hasTrace ?r' _ ?c' _ ?t ] => replace r' with r; [replace c' with c by nextpc; auto|]
           end.
           subst val.
           subst mem.
           extensionality a.
           unfold mask, prset, rset.
           unfold evalExpr; fold evalExpr.
           rewrite H7.
           repeat deq.
    + specialize (IHinst (rset rmask dstIdx val) mmask).
      assert (rset rf dstIdx val = mask (prset rf0 dstIdx (mem0 laddr_aligned)) (rset rmask dstIdx val)).
      * extensionality a.
        subst rf val mem.
        unfold rset, mask, prset.
        unfold evalExpr; fold evalExpr.
        rewrite H7.
        repeat deq.
      * match goal with
        | [ H : extractFhTrace (_ :: _) = _ |- _ ] => simpl in H
        end.
        specialize (IHinst H8 Heqmmem _ H3 _ (rset rmask' dstIdx (mmask' laddr_aligned)) mmask' H4).
        destruct IHinst as [trace'0 [Hht' [Hct' Het']]].
        exists (Rd pc laddr_aligned (mmask' laddr_aligned) :: trace'0).
        intuition idtac; try solve [simpl; f_equal; auto].
        pose (htLd inst (mmask' laddr_aligned) (mask rf0 rmask') pm pc (mask mem0 mmask') trace'0 H H0) as Hld.
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
        -- subst.
           unfold mask.
           rewrite H7.
           auto.
        -- match goal with
           | [ H : hasTrace ?r _ ?c _ ?t |- hasTrace ?r' _ ?c' _ ?t ] => replace r' with r; [replace c' with c by nextpc; auto|]
           end.
           extensionality a.
           unfold mask, prset, rset.
           unfold evalExpr; fold evalExpr.
           rewrite H7.
           repeat deq.
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
    rewrite H1 in Hts.
    unfold prset in Hts.
    rewrite (proj2 (weqb_true_iff _ _) eq_refl) in Hts.
    fold srcIdx in Hts.
    case_eq (rf0 srcIdx);
      intros;
      match goal with
      | [ H : rf0 srcIdx = _ |- _ ] => rewrite H in Hts
      end;
      try discriminate.
    match goal with
    | [ H : Some (?x, ?y, ?z) = Some (?x', ?y', ?z') |- _ ] => assert (x = x') by congruence; assert (y = y') by congruence; assert (z = z') by congruence; clear H; subst x' y' z'
    end.
    pose (safeShift _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe' H4 H4) as Hsafenew'; remember Hsafenew' as Hsafenew eqn:Heq; clear Heq Hsafenew'.
    clear Hsafe'.
    match goal with
    | [ H : safeUntil ?f ?rf ?pm ?pc ?mem ?rf ?pc ?mem = _,
            IH : forall _ _ _ _, _ -> _ -> forall _, safeUntil _ _ _ ?pc' _ _ _ _ = _ -> _ |- _ ] =>
      replace pc with pc' in H by nextpc;
        specialize (IH _ _ _ _ Heqmrf Heqmmem _ H)
    end.
    match goal with
    | [ H : extractFhTrace (_ :: _) = _ |- _ ] => simpl in H
    end.
    specialize (IHHht _ H2 _ rmask' mmask' H3).
    destruct IHHht as [trace'0 [Hht' [Hct' Het']]].
    exists (RdZ pc laddr_aligned :: trace'0).
    intuition idtac; try solve [simpl; f_equal; auto].
    pose (htLdZ inst (mask rf0 rmask') pm pc (mask mem0 mmask') trace'0 H H0 H1) as HldZ.
    Opaque evalExpr.
    simpl in HldZ.
    Transparent evalExpr.
    fold srcIdx in HldZ.
    fold addr in HldZ.
    replace (mask rf0 rmask' srcIdx) with srcVal in HldZ by (subst rf; unfold srcVal; unfold mask; rewrite H5; auto).
    replace (evalExpr (rv32iCalcLdAddr type addr srcVal)) with laddr in HldZ by (unfold laddr; congruence).
    fold laddr_aligned in HldZ.
    apply HldZ; auto.
    match goal with
    | [ H : hasTrace _ _ ?c _ ?t |- hasTrace _ _ ?c' _ ?t ] => replace c' with c by nextpc; auto
    end.
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
    | [ H : _ = opSt |- _ ] => rewrite H in Hts
    end.
    unfold opSt in *.
    fold srcIdx in Hts.
    assert (srcVal = (mask rf0 rmask) srcIdx) as HsrcVal by (unfold srcVal; congruence).
    unfold mask in HsrcVal.
    case_eq (rf0 srcIdx); intros;
      match goal with
      | [ H : rf0 srcIdx = _ |- _ ] => rewrite H in Hts; rewrite H in HsrcVal
      end; try discriminate.
    fold addr in Hts.
    rewrite <- HsrcVal in Hts.
    replace (evalExpr (rv32iCalcStAddr type addr srcVal)) with saddr in Hts by (unfold saddr; congruence).
    fold saddr_aligned in Hts.
    fold vsrcIdx in Hts.
    match goal with
    | [ H : Some (?x, ?y, ?z) = Some (?x', ?y', ?z') |- _ ] => assert (x = x') by congruence; assert (y = y') by congruence; assert (z = z') by congruence; clear H; subst x' y' z'
    end.
    pose (safeShift _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe' H3 H3) as Hsafenew'; remember Hsafenew' as Hsafenew eqn:Heq; clear Heq Hsafenew'.
    clear Hsafe'.
    match goal with
    | [ H : safeUntil ?f ?rf ?pm ?pc ?mem ?rf ?pc ?mem = _,
            IH : forall _ _ _ _, _ -> _ -> forall _, safeUntil _ _ _ ?pc' _ _ _ _ = _ -> _ |- _ ] =>
      replace pc with pc' in H by nextpc;
        pose (fun mm Heq2 => IHHht _ _ rmask mm Heqmrf Heq2 _ H) as IHinst'; remember IHinst' as IHinst eqn:Heq; clear IHinst' Heq
    end.
    case_eq (rf0 vsrcIdx); intros.
    + specialize (IHinst mmask).
      assert ((fun a : word rv32iAddrSize =>
                 if weq a saddr_aligned then stVal else mem a) =
              mask
                (fun a : word rv32iAddrSize =>
                   if weqb a saddr_aligned then rf0 vsrcIdx else mem0 a) mmask).
      * extensionality a.
        unfold stVal.
        subst mem rf.
        unfold mask.
        rewrite H5.
        deq.
      * match goal with
        | [ H : extractFhTrace (_ :: _) = _ |- _ ] => simpl in H
        end.
        specialize (IHinst H6 _ H1 _ rmask' mmask' H2).
        destruct IHinst as [trace'0 [Hht' [Hct' Het']]].
        exists (Wr pc saddr_aligned stVal :: trace'0).
        intuition idtac; try solve [simpl; f_equal; auto].
        pose (htSt inst (mask rf0 rmask') pm pc (mask mem0 mmask') trace'0 H H0) as Hst.
        Opaque evalExpr.
        simpl in Hst.
        Transparent evalExpr.
        fold vsrcIdx in Hst.
        fold srcIdx in Hst.
        replace (mask rf0 rmask' srcIdx) with srcVal in Hst by (unfold mask; rewrite H4; auto).
        fold addr in Hst.
        replace (evalExpr (rv32iCalcStAddr type addr srcVal)) with saddr in Hst by (unfold saddr; congruence).
        fold saddr_aligned in Hst.
        replace (mask rf0 rmask' vsrcIdx) with stVal in Hst by (unfold stVal; subst rf; unfold mask; rewrite H5; auto).
        apply Hst; auto.
        match goal with
        | [ H : hasTrace _ _ ?c ?m ?t |- hasTrace _ _ ?c' ?m' ?t ] => replace m' with m; [replace c' with c by nextpc; auto|]
        end.
        subst stVal rf.
        extensionality a.
        unfold mask.
        rewrite H5.
        deq.
    + specialize (IHinst (fun a => if weqb a saddr_aligned then stVal else mmask a)).
      assert ((fun a : word rv32iAddrSize =>
                 if weq a saddr_aligned then stVal else mem a) =
              mask
                (fun a : word rv32iAddrSize =>
                   if weqb a saddr_aligned then rf0 vsrcIdx else mem0 a)
                (fun a : word rv32iAddrSize =>
                   if weqb a saddr_aligned then stVal else mmask a)).
      * extensionality a.
        subst rf stVal mem.
        unfold mask.
        rewrite H5.
        deq.
      * match goal with
        | [ H : extractFhTrace (_ :: _) = _ |- _ ] => simpl in H
        end.
        specialize (IHinst H6 _ H1 _ rmask' (fun a => if weqb a saddr_aligned then rmask' vsrcIdx else mmask' a) H2).
        destruct IHinst as [trace'0 [Hht' [Hct' Het']]].
        exists (Wr pc saddr_aligned (rmask' vsrcIdx) :: trace'0).
        intuition idtac; try solve [simpl; f_equal; auto].
        pose (htSt inst (mask rf0 rmask') pm pc (mask mem0 mmask') trace'0 H H0) as Hst.
        Opaque evalExpr.
        simpl in Hst.
        Transparent evalExpr.
        fold vsrcIdx in Hst.
        fold srcIdx in Hst.
        replace (mask rf0 rmask' srcIdx) with srcVal in Hst by (unfold mask; rewrite H4; auto).
        fold addr in Hst.
        replace (evalExpr (rv32iCalcStAddr type addr srcVal)) with saddr in Hst by (unfold saddr; congruence).
        fold saddr_aligned in Hst.
        replace (mask rf0 rmask' vsrcIdx) with (rmask' vsrcIdx) in Hst by (unfold mask; rewrite H5; auto).
        apply Hst; auto.
        match goal with
        | [ H : hasTrace _ _ ?c ?m ?t |- hasTrace _ _ ?c' ?m' ?t ] => replace m' with m; [replace c' with c by nextpc; auto|]
        end.
        extensionality a.
        unfold mask.
        rewrite H5.
        deq.
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
    | [ H : _ = opTh |- _ ] => rewrite H in Hts
    end.
    unfold opTh in *.
    match goal with
    | [ H : Some (?x, ?y, ?z) = Some (?x', ?y', ?z') |- _ ] => assert (x = x') by congruence; assert (y = y') by congruence; assert (z = z') by congruence; clear H; subst x' y' z'
    end.
    pose (safeShift _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe' H3 H3) as Hsafenew'; remember Hsafenew' as Hsafenew eqn:Heq; clear Heq Hsafenew'.
    clear Hsafe'.
    match goal with
    | [ H : safeUntil ?f ?rf ?pm ?pc ?mem ?rf ?pc ?mem = _,
            IH : forall _ _ _ _, _ -> _ -> forall _, safeUntil _ _ _ ?pc' _ _ _ _ = _ -> _ |- _ ] =>
      replace pc with pc' in H by nextpc
    end.
    match goal with
    | [ H : extractFhTrace (_ :: _) = _ |- _ ] => simpl in H
    end.
    specialize (IHHht _ _ _ _ Heqmrf Heqmmem _ Hsafenew _ H1 _ rmask' mmask' H2).
    destruct IHHht as [trace'0 [Hht' [Hct' Het']]].
    exists (ToHost pc (mask rf0 rmask' srcIdx) :: trace'0).
    intuition idtac; try solve [simpl; f_equal; auto].
    constructor; auto.
    match goal with
    | [ H : hasTrace _ _ ?c _ ?t |- hasTrace _ _ ?c' _ ?t ] => replace c' with c by nextpc; auto
    end.
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
    | [ H : _ = opFh |- _ ] => rewrite H in Hts
    end.
    unfold opFh in *.
    match goal with
    | [ H : Some (?x, ?y, ?z) = Some (?x', ?y', ?z') |- _ ] => assert (x = x') by congruence; assert (y = y') by congruence; assert (z = z') by congruence; clear H; subst x' y' z'
    end.
    pose (safeShift _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe' H3 H3) as Hsafenew'; remember Hsafenew' as Hsafenew eqn:Heq; clear Heq Hsafenew'.
    clear Hsafe'.
    match goal with
    | [ H : safeUntil ?f ?rf ?pm ?pc ?mem ?rf ?pc ?mem = _,
            IH : forall _ _ _ _, _ -> _ -> forall _, safeUntil _ _ _ ?pc' _ _ _ _ = _ -> _ |- _ ] =>
      replace pc with pc' in H by nextpc
    end.
    match goal with
    | [ H : extractFhTrace (_ :: _) = _ |- _ ] => simpl in H
    end.
    assert (rset rf dst val = mask (prset rf0 dst None) (rset rmask dst val)).
    + subst rf.
      extensionality a.
      unfold prset, rset, mask.
      unfold evalExpr; fold evalExpr.
      repeat deq.
    + destruct fhTrace; try discriminate.
      match goal with
      | [ H : _ :: _ = _ :: _ |- _ ] => inv H
      end.
      match goal with
      | [ H : length (_ :: _) = length ?ft |- _ ] => destruct ft; simpl in H; inv H
      end.
      specialize (IHHht _ _ _ _ H4 eq_refl _ Hsafenew _ eq_refl _ (rset rmask' dst d0) mmask' H1).
      destruct IHHht as [trace'0 [Hht' [Hct' Het']]].
      exists (FromHost pc d0 :: trace'0).
      intuition idtac; try solve [simpl; f_equal; auto].
      econstructor; auto.
      match goal with
      | [ H : hasTrace ?r _ ?c _ ?t |- hasTrace ?r' _ ?c' _ ?t ] => replace c' with c by nextpc; replace r' with r; auto
      end.
      fold dst.
      extensionality a.
      unfold prset, rset, mask.
      unfold evalExpr; fold evalExpr.
      repeat deq.
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
    | [ H : _ = opNm |- _ ] => rewrite H in Hts
    end.
    unfold opNm in *.
    destruct (taintNextPc_correct rf0 rmask pc inst); rewrite H5 in Hts; try discriminate.
    unfold rv32iGetDst in Hts.
    unfold evalExpr in Hts; fold evalExpr in Hts.
    rewrite H1 in Hts.
    unfold evalConstT in Hts.
    destruct (isEq (Bit 7) rv32iOpBRANCH rv32iOpBRANCH); try congruence.
    unfold prset in Hts.
    replace (weqb $0 (wzero rv32iRfIdx)) with true in Hts by reflexivity.
    match goal with
    | [ H : Some (?x, ?y, ?z) = Some (?x', ?y', ?z') |- _ ] => assert (x = x') by congruence; assert (y = y') by congruence; assert (z = z') by congruence; clear H; subst x' y' z'
    end.
    pose (safeShift _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe' H4 H4) as Hsafenew'; remember Hsafenew' as Hsafenew eqn:Heq; clear Heq Hsafenew'.
    clear Hsafe'.
    match goal with
    | [ H : extractFhTrace (_ :: _) = _ |- _ ] => simpl in H
    end.
    subst rf.
    specialize (IHHht _ _ _ _ eq_refl Heqmmem _ Hsafenew _ H2 _ rmask' mmask' H3).
    destruct IHHht as [trace'0 [Hht' [Hct' Het']]].
    exists (Branch pc (evalExpr (rv32iBranchTaken type (mask rf0 rmask') inst)) :: trace'0).
    destruct (taintBranchTaken_correct rf0 rmask inst H1);
    destruct (taintBranchTaken_correct rf0 rmask' inst H1);
      try match goal with
          | [ Hbt : taintBranchTaken rf0 inst = None,
                    Hnp : taintNextPc rf0 pc inst = Some _,
                          Hob : evalExpr (getOpcodeE _) = _ |- _ ] => unfold taintNextPc in Hnp; rewrite Hbt in Hnp; rewrite Hob in Hnp; discriminate
          end.
    intuition idtac.
    + econstructor; eauto.
      match goal with
      | [ H : hasTrace _ _ ?c _ ?t |- hasTrace _ _ ?c' _ ?t ] => replace c' with c; auto
      end.
      destruct (taintNextPc_correct rf0 rmask' pc inst); congruence.
    + Opaque evalExpr.
      simpl; f_equal; auto.
      congruence.
      Transparent evalExpr.
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
    | [ H : _ = opNm |- _ ] => rewrite H in Hts
    end.
    unfold opNm in *.
    destruct (taintNextPc_correct rf0 rmask pc inst); rewrite H5 in Hts; try discriminate.
    fold dst src1 src2 in Hts.
    match goal with
    | [ H : Some (?x, ?y, ?z) = Some (?x', ?y', ?z') |- _ ] => assert (x = x') by congruence; assert (y = y') by congruence; assert (z = z') by congruence; clear H; subst x' y' z'
    end.
    pose (safeShift _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe' H4 H4) as Hsafenew'; remember Hsafenew' as Hsafenew eqn:Heq; clear Heq Hsafenew'.
    clear Hsafe'.
    match goal with
    | [ H : extractFhTrace (_ :: _) = _ |- _ ] => simpl in H
    end.
    case_eq (rf0 src1); case_eq (rf0 src2); intros;
      match goal with
      | [ H1 : rf0 src1 = _, H2 : rf0 src2 = _ |- _ ] => rewrite H1 in Hsafenew; try rewrite H2 in Hsafenew
      end.
    + assert (rset rf dst execVal = mask (prset rf0 dst (Some execVal)) rmask).
      * subst rf.
        extensionality a.
        unfold rset, prset, mask.
        unfold evalExpr; fold evalExpr.
        repeat deq.
      * replace (evalExpr (rv32iExec type d0 d pc inst)) with execVal in Hsafenew.
        -- subst rf.
           specialize (IHHht (prset rf0 dst (Some execVal)) _ rmask _ H8 Heqmmem _ Hsafenew _ H2 _ rmask' mmask' H3).
           destruct IHHht as [trace'0 [Hht' [Hct' Het']]].
           exists (Nm pc :: trace'0).
           intuition idtac; try solve [simpl; f_equal; auto].
           econstructor; eauto.
           match goal with
           | [ H : hasTrace ?r _ ?c _ ?t |- hasTrace ?r' _ ?c' _ ?t ] => replace c' with c; [replace r' with r; auto|]
           end.
           ++ extensionality a.
              fold src1 src2 dst.
              unfold execVal, val1, val2, rset, prset, mask.
              repeat rewrite H6.
              repeat rewrite H7.
              unfold evalExpr; fold evalExpr.
              repeat deq.
           ++ destruct (taintNextPc_correct rf0 rmask' pc inst); congruence.
        -- unfold execVal, val1, val2.
           subst rf.
           unfold mask.
           rewrite H6.
           rewrite H7.
           reflexivity.
    + assert (rset rf dst execVal = mask (prset rf0 dst None) (rset rmask dst execVal)).
      * subst rf.
        extensionality a.
        unfold rset, prset, mask.
        unfold evalExpr; fold evalExpr.
        repeat deq.
      * subst rf.
        specialize (IHHht _ _ _ _ H8 Heqmmem _ Hsafenew _ H2 _ (rset rmask' dst (evalExpr (rv32iExec type d (rmask' src2) pc inst))) mmask' H3).
        destruct IHHht as [trace'0 [Hht' [Hct' Het']]].
        exists (Nm pc :: trace'0).
        intuition idtac; try solve [simpl; f_equal; auto].
        econstructor; eauto.
        match goal with
        | [ H : hasTrace ?r _ ?c _ ?t |- hasTrace ?r' _ ?c' _ ?t ] => replace c' with c; [replace r' with r; auto|]
        end.
        ++ extensionality a.
           fold src1 src2 dst.
           unfold val2, rset, prset, mask.
           repeat rewrite H6.
           repeat rewrite H7.
           unfold evalExpr; fold evalExpr.
           repeat deq.
        ++ destruct (taintNextPc_correct rf0 rmask' pc inst); congruence.
    + assert (rset rf dst execVal = mask (prset rf0 dst None) (rset rmask dst execVal)).
      * subst rf.
        extensionality a.
        unfold rset, prset, mask.
        unfold evalExpr; fold evalExpr.
        repeat deq.
      * subst rf.
        specialize (IHHht _ _ _ _ H8 Heqmmem _ Hsafenew _ H2 _ (rset rmask' dst (evalExpr (rv32iExec type (rmask' src1) d pc inst))) mmask' H3).
        destruct IHHht as [trace'0 [Hht' [Hct' Het']]].
        exists (Nm pc :: trace'0).
        intuition idtac; try solve [simpl; f_equal; auto].
        econstructor; eauto.
        match goal with
        | [ H : hasTrace ?r _ ?c _ ?t |- hasTrace ?r' _ ?c' _ ?t ] => replace c' with c; [replace r' with r; auto|]
        end.
        ++ extensionality a.
           fold src1 src2 dst.
           unfold val1, rset, prset, mask.
           repeat rewrite H6.
           repeat rewrite H7.
           unfold evalExpr; fold evalExpr.
           repeat deq.
        ++ destruct (taintNextPc_correct rf0 rmask' pc inst); congruence.
    + assert (rset rf dst execVal = mask (prset rf0 dst None) (rset rmask dst execVal)).
      * subst rf.
        extensionality a.
        unfold rset, prset, mask.
        unfold evalExpr; fold evalExpr.
        repeat deq.
      * subst rf.
        specialize (IHHht _ _ _ _ H8 Heqmmem _ Hsafenew _ H2 _ (rset rmask' dst (evalExpr (rv32iExec type (rmask' src1) (rmask' src2) pc inst))) mmask' H3).
        destruct IHHht as [trace'0 [Hht' [Hct' Het']]].
        exists (Nm pc :: trace'0).
        intuition idtac; try solve [simpl; f_equal; auto].
        econstructor; eauto.
        match goal with
        | [ H : hasTrace ?r _ ?c _ ?t |- hasTrace ?r' _ ?c' _ ?t ] => replace c' with c; [replace r' with r; auto|]
        end.
        ++ extensionality a.
           fold src1 src2 dst.
           unfold rset, prset, mask.
           repeat rewrite H6.
           repeat rewrite H7.
           unfold evalExpr; fold evalExpr.
           repeat deq.
        ++ destruct (taintNextPc_correct rf0 rmask' pc inst); congruence.
Qed.
