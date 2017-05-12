Require Import Kami.Kami.
Require Import Lib.Indexer.

Set Implicit Arguments.
Set Asymmetric Patterns.

Open Scope string.

(** * Kami: A Platform for High-Level Parametric Hardware Specification and its Modular Verification *)

(** Welcome to the Kami tutorial! This tutorial consists of following sections:
 * 1) An introduction to the Kami language and its semantics
 * 2) Refinement / specifications as Kami modules
 * _) ...
 * _) Proving the correctness of a 3-stage pipelined system
 *)

Variable dataSize: nat.

Definition enq1 :=
  MethodSig ("fifo1" -- "enq") (Bit dataSize): Void.

Definition stage1 :=
  MODULE {
    Register "data" : Bit dataSize <- Default

    with Rule "produce" :=
      Read data <- "data";
      Call enq1(#data);
      Write "data" <- #data + $1;
      Retv
  }.

(** For proof automation *)
Hint Unfold enq1 : MethDefs.
Hint Unfold stage1 : ModuleDefs.

Definition deq1 :=
  MethodSig ("fifo1" -- "deq") (): Bit dataSize.
Definition enq2 :=
  MethodSig ("fifo2" -- "enq") (Bit dataSize): Void.

Definition stage2 :=
  MODULE {
    Rule "doDouble" :=
      Call data <- deq1();
      LET doubled <- $2 * #data;
      Call enq2(#doubled);
      Retv
  }.

Hint Unfold deq1 enq2 : MethDefs.
Hint Unfold stage2 : ModuleDefs.

Definition deq2 :=
  MethodSig ("fifo2" -- "deq") (): Bit dataSize.
Definition sendAcc :=
  MethodSig "sendAcc" (Bit dataSize): Void.

Definition stage3 :=
  MODULE {
    Register "acc" : Bit dataSize <- Default

    with Rule "consume" :=
      Call data <- deq2();
      Read acc <- "acc";
      LET nacc <- #acc + #data;
      Call sendAcc(#nacc);
      Write "acc" <- #nacc;
      Retv
  }.

Hint Unfold deq2 sendAcc : MethDefs.
Hint Unfold stage3 : ModuleDefs.

Require Import Fifo.

Definition fifo1 := simpleFifo "fifo1" 8 (Bit dataSize).
Definition fifo2 := simpleFifo "fifo2" 8 (Bit dataSize).
Hint Unfold fifo1 fifo2 : ModuleDefs.

Definition impl :=
  (stage1 ++ fifo1 ++ stage2 ++ fifo2 ++ stage3)%kami.
Hint Unfold impl : ModuleDefs.

Definition spec :=
  MODULE {
    Register "data" : Bit dataSize <- Default
    with Register "acc" : Bit dataSize <- Default

    with Rule "accDoubles" :=
      Read data <- "data";
      LET doubled <- $2 * #data;
      Read acc <- "acc";
      LET nacc <- #acc + #doubled;
      Call sendAcc(#nacc);
      Write "acc" <- #nacc;
      Write "data" <- #data + $1;
      Retv
  }.
Hint Unfold spec : ModuleDefs.

(** Well-formedness *)
Lemma stage1_PhoasWf: ModPhoasWf stage1.
Proof. kequiv. Qed.
Lemma stage2_PhoasWf: ModPhoasWf stage2.
Proof. kequiv. Qed.
Lemma stage3_PhoasWf: ModPhoasWf stage3.
Proof. kequiv. Qed.
Hint Resolve stage1_PhoasWf stage2_PhoasWf stage3_PhoasWf.

Lemma impl_PhoasWf: ModPhoasWf impl.
Proof. kequiv. Qed.
Hint Resolve impl_PhoasWf.

Lemma stage1_RegsWf: ModRegsWf stage1.
Proof. kvr. Qed.
Lemma stage2_RegsWf: ModPhoasWf stage2.
Proof. kvr. Qed.
Lemma stage3_RegsWf: ModPhoasWf stage3.
Proof. kvr. Qed.
Hint Resolve stage1_RegsWf stage2_RegsWf stage3_RegsWf.

Lemma impl_RegsWf: ModRegsWf impl.
Proof. kvr. Qed.
Hint Resolve impl_RegsWf.

(** * Correctness proof *)
Require Import Kami.ModuleBoundEx.

Theorem impl_ok: impl <<== spec.
Abort.

(* TODO: hide *)
Ltac kmodular :=
  try (unfold MethsT; rewrite <-SemFacts.idElementwiseId);
  apply traceRefines_modular_interacting with
  (vp := idElementwise (A:=_));
  [ kequiv | kequiv | kequiv | kequiv
   | kdisj_regs_ex O | kdisj_regs_ex O | kvr | kvr
   | kdisj_dms_ex O | kdisj_cms_ex O | kdisj_dms_ex O | kdisj_cms_ex O
   | kdisj_edms_cms_ex O | kdisj_ecms_dms_ex O
   | kinteracting | | ].

Ltac knoninteracting :=
  split; [ kdisj_dms_cms_ex O | kdisj_cms_dms_ex O ].

Ltac kmodularn :=
  try (unfold MethsT; rewrite <- SemFacts.idElementwiseId);
  apply traceRefines_modular_noninteracting;
   [ kequiv | kequiv | kequiv | kequiv
     | kdisj_regs_ex O | kdisj_regs_ex O | kvr | kvr
     | kdisj_dms_ex O | kdisj_cms_ex O | kdisj_dms_ex O | kdisj_cms_ex O
     | knoninteracting | knoninteracting
     | | ].

(** Changing fifos to native fifos *)
Require Import NativeFifo SimpleFifoCorrect.
           
Definition nfifo1 :=
  @nativeSimpleFifo "fifo1" (Bit dataSize) Default.
Definition nfifo2 :=
  @nativeSimpleFifo "fifo2" (Bit dataSize) Default.
Hint Unfold nfifo1 nfifo2 : ModuleDefs.

Definition intSpec1 :=
  ((stage1 ++ nfifo1 ++ stage2) ++ fifo2 ++ stage3)%kami.
Hint Unfold intSpec1 : ModuleDefs.

Lemma intSpec1_PhoasWf: ModPhoasWf intSpec1.
Proof. kequiv. Qed.
Hint Resolve intSpec1_PhoasWf.

Lemma intSpec1_RegsWf: ModRegsWf intSpec1.
Proof. kvr. Qed.
Hint Resolve intSpec1_RegsWf.

Theorem impl_intSpec1: impl <<== intSpec1.
Proof.
  ktrans ((stage1 ++ fifo1 ++ stage2) ++ fifo2 ++ stage3)%kami;
    [ksimilar; vm_compute; intuition idtac|].

  kmodular.
  - kmodular.
    + krefl.
    + kmodular.
      * apply sfifo_refines_nsfifo.
      * krefl.
  - krefl.
Qed.

Section PipelineInv.
  Variables (next: word dataSize -> word dataSize)
            (f: word dataSize -> word dataSize).

  (* NOTE:
   * for the complete proof, we need the following property:
   * [forall w1 w2, f w1 = f w2 -> f (next w1) = f (next w2)].
   * This is weaker than "one-to-one" property of [f].
   *)
  Fixpoint pipeline_inv (l: list (type (Bit dataSize))) :=
    match l with
    | nil => True
    | h1 :: t1 =>
      match t1 with
      | nil => True
      | h2 :: t2 =>
        (exists if1 if2,
            h1 = f if1 /\ h2 = f if2 /\ if2 = next if1) /\
        pipeline_inv t1
      end
    end.

  Lemma pipeline_inv_enq:
    forall e d,
      pipeline_inv (e ++ [f d]) ->
      pipeline_inv ((e ++ [f d]) ++ [f (next d)]).
  Proof.
    induction e; simpl; intros.
    - split; do 2 eexists; eauto.
    - destruct e; simpl in *; dest; subst.
      + repeat split.
        * rewrite H1.
          apply IHe; auto.
        * apply IHe; auto.
      + split; [do 2 eexists; eauto|].
        destruct e; simpl in *; dest; subst.
        * apply IHe; repeat split.
          do 2 eexists; eauto.
        * apply IHe; eauto.
  Qed.

  Lemma pipeline_inv_deq:
    forall e h d,
      pipeline_inv ((h :: e) ++ [d]) ->
      pipeline_inv (e ++ [d]).
  Proof.
    induction e; simpl; intros; auto.
    dest; auto.
  Qed.

End PipelineInv.

Definition spec12 :=
  MODULE {
    Register "data" : Bit dataSize <- Default

    with Rule "produceDouble" :=
      Read data <- "data";
      LET doubled <- $2 * #data;
      Call enq2(#doubled);
      Write "data" <- #data + $1;
      Retv
  }.
Hint Unfold spec12 : ModuleDefs.
Lemma spec12_PhoasWf: ModPhoasWf spec12.
Proof. kequiv. Qed.
Hint Resolve spec12_PhoasWf.
Lemma spec12_RegsWf: ModRegsWf spec12.
Proof. kvr. Qed.
Hint Resolve spec12_RegsWf.

Definition impl12 := (stage1 ++ nfifo1 ++ stage2)%kami.
Hint Unfold impl12 : ModuleDefs.
Lemma impl12_PhoasWf: ModPhoasWf impl12.
Proof. kequiv. Qed.
Hint Resolve impl12_PhoasWf.
Lemma impl12_RegsWf: ModRegsWf impl12.
Proof. kvr. Qed.
Hint Resolve impl12_RegsWf.

Definition impl12Inl: Modules * bool.
Proof.
  remember (inlineF impl12) as inlined.
  kinline_compute_in Heqinlined.
  match goal with
  | [H: inlined = ?m |- _] =>
    exact m
  end.
Defined.

Definition impl12_regMap (ir sr: RegsT): Prop.
  kexistv "data" datav ir (Bit dataSize).
  kexistnv "fifo1"--"elt" eltv ir (listEltK (Bit dataSize) type).
  refine (sr = (["data" <- existT _ (SyntaxKind (Bit dataSize)) _]%fmap)).
  refine (hd datav eltv).
Defined.
Hint Unfold impl12_regMap: MethDefs.

Definition next12 := fun w : word dataSize => w ^+ $1.
Opaque next12.
Definition f12 := fun w : word dataSize => w.
Opaque f12.

Record impl12_inv (o: RegsT) : Prop :=
  { datav : fullType type (SyntaxKind (Bit dataSize));
    Hdatav : M.find "data" o = Some (existT _ _ datav);
    eltv : fullType type (listEltK (Bit dataSize) type);
    Heltv : M.find "fifo1"--"elt"%string o = Some (existT _ _ eltv);

    Hinv : pipeline_inv next12 f12 (eltv ++ [datav])
  }.
Hint Unfold pipeline_inv: InvDefs.

Ltac impl12_inv_old :=
  try match goal with
      | [H: impl12_inv _ |- _] => destruct H
      end;
  kinv_red.

Ltac impl12_inv_new :=
  econstructor;
  try (findReify; (reflexivity || eassumption); fail);
  kregmap_clear.

Ltac impl12_inv_tac := impl12_inv_old; impl12_inv_new.

Lemma impl12_inv_ok':
  forall init n ll,
    init = initRegs (getRegInits (fst impl12Inl)) ->
    Multistep (fst impl12Inl) init n ll ->
    impl12_inv n.
Proof.
  induction 2; [kinv_dest_custom impl12_inv_tac; simpl; auto|].
  kinvert.
  - mred.
  - mred.
  - kinv_dest_custom impl12_inv_tac.
    change (x ^+ $1) with (next12 x).
    fold (pipeline_inv next12 f12) in *.
    change x with (f12 x) in Hinv.
    change x with (f12 x) at 1.
    change (next12 x) with (f12 (next12 x)).
    apply pipeline_inv_enq; auto.
  - kinv_dest_custom impl12_inv_tac.
    destruct x; [inv H3|]; subst.
    fold (pipeline_inv next12 f12) in *.
    eapply pipeline_inv_deq; eauto.
Qed.

Lemma impl12_inv_ok:
  forall o,
    reachable o (fst impl12Inl) ->
    impl12_inv o.
Proof.
  intros; inv H; inv H0.
  eapply impl12_inv_ok'; eauto.
Qed.

Lemma impl12_ok: impl12 <<== spec12.
Proof.
  kinline_left inlined.

  kdecomposeR_nodefs impl12_regMap.
  kinv_add impl12_inv_ok.
  kinv_add_end.
  
  kinvert.
  + kinv_action_dest.
    kinv_regmap_red.
    eexists; exists None; split; kinv_constr.
    kinv_eq.
    destruct x0; auto.
  + kinv_action_dest.
    destruct Hr; dest.
    kinv_regmap_red.
    eexists; exists (Some "produceDouble"); split; kinv_constr.
    * kinv_eq.
      destruct x; [inv H2|reflexivity].
    * destruct x as [|hd tl]; [inv H2|].
      kinv_eq.
      simpl in Hinv.
      destruct tl; dest; subst; simpl in *; dest; subst; auto.
Qed.

Theorem impl_ok: impl <<== spec.
Proof.
  ketrans; [apply impl_intSpec1|].
  ktrans (spec12 ++ fifo2 ++ stage3)%kami.
  - kmodular.
    + apply impl12_ok.
    + krefl.
  - 
Abort.


Definition impl123 := (spec12 ++ nfifo2 ++ stage3)%kami.
Hint Unfold impl123 : ModuleDefs.
Lemma impl123_PhoasWf: ModPhoasWf impl123.
Proof. kequiv. Qed.
Hint Resolve impl123_PhoasWf.
Lemma impl123_RegsWf: ModRegsWf impl123.
Proof. kvr. Qed.
Hint Resolve impl123_RegsWf.

Definition impl123Inl: Modules * bool.
Proof.
  remember (inlineF impl123) as inlined.
  kinline_compute_in Heqinlined.
  match goal with
  | [H: inlined = ?m |- _] =>
    exact m
  end.
Defined.

Definition next123 := fun w : word dataSize => w ^+ $1.
Definition f123 := fun w : word dataSize => $2 ^* w.

Lemma next_f_consistent:
  forall w1 w2,
    f123 w1 = f123 w2 ->
    f123 (next123 w1) = f123 (next123 w2).
Proof.
  unfold f123, next123; intros.
  rewrite 2! wmult_comm with (x:= $2).
  repeat rewrite wmult_plus_distr.
  f_equal.
  rewrite 2! wmult_comm with (y:= $2).
  auto.
Qed.
Hint Immediate next_f_consistent.
Opaque next123 f123.

Record impl123_inv (o: RegsT) : Prop :=
  { datav : fullType type (SyntaxKind (Bit dataSize));
    Hdatav : M.find "data" o = Some (existT _ _ datav);
    eltv : fullType type (listEltK (Bit dataSize) type);
    Heltv : M.find "fifo2"--"elt"%string o = Some (existT _ _ eltv);

    Hinv : pipeline_inv next123 f123 (eltv ++ [$2 ^* datav])
  }.
Hint Unfold pipeline_inv: InvDefs.

Ltac impl123_inv_old :=
  try match goal with
      | [H: impl123_inv _ |- _] => destruct H
      end;
  kinv_red.

Ltac impl123_inv_new :=
  econstructor;
  try (findReify; (reflexivity || eassumption); fail);
  kregmap_clear.

Ltac impl123_inv_tac := impl123_inv_old; impl123_inv_new.

Lemma impl123_inv_ok':
  forall init n ll,
    init = initRegs (getRegInits (fst impl123Inl)) ->
    Multistep (fst impl123Inl) init n ll ->
    impl123_inv n.
Proof.
  induction 2; [kinv_dest_custom impl123_inv_tac; simpl; auto|].
  
  kinvert.
  - mred.
  - mred.
  - kinv_dest_custom impl123_inv_tac.
    change (x ^+ $1) with (next123 x).
    fold (pipeline_inv next123 f123) in *.
    change ($2 ^* x) with (f123 x) in Hinv.
    change ($2 ^* x) with (f123 x).
    change ($2 ^* next123 x) with (f123 (next123 x)).
    apply pipeline_inv_enq; auto.
  - kinv_dest_custom impl123_inv_tac.
    destruct x; [inv H3|]; subst.
    fold (pipeline_inv next123 f123) in *.
    eapply pipeline_inv_deq; eauto.
Qed.

Lemma impl123_inv_ok:
  forall o,
    reachable o (fst impl123Inl) ->
    impl123_inv o.
Proof.
  intros; inv H; inv H0.
  eapply impl123_inv_ok'; eauto.
Qed.

Definition impl123_regMap (ir sr: RegsT): Prop.
  kexistv "data" datav ir (Bit dataSize).
  kexistv "acc" accv ir (Bit dataSize).
  kexistnv "fifo2"--"elt" eltv ir (listEltK (Bit dataSize) type).
  refine (
      exists sdatav,
        sr = (["acc" <- existT _ (SyntaxKind (Bit dataSize)) accv]
              +["data" <- existT _ (SyntaxKind (Bit dataSize)) sdatav]
             )%fmap /\
        $2 ^* sdatav = hd ($2 ^* datav) eltv).
Defined.
Hint Unfold impl123_regMap: MethDefs.

Lemma impl123_ok: impl123 <<== spec.
Proof.
  kinline_left inlined.

  kdecomposeR_nodefs impl123_regMap.
  kinv_add impl123_inv_ok.
  kinv_add_end.
  
  kinvert.
  + kinv_action_dest.
    kinv_regmap_red.
    eexists; exists None; split; kinv_constr.
    kinv_eq.
    destruct x0; auto.
  + kinv_action_dest.
    destruct Hr; dest.
    kinv_regmap_red.
    eexists; exists (Some "accDoubles"); split; kinv_constr.
    * simpl; destruct x; [inv H2|].
      simpl in *; subst.
      reflexivity.
    * kinv_eq.
      destruct x; [inv H2|].
      simpl in *; subst.
      reflexivity.
    * destruct x as [|hd tl]; [inv H2|].
      change ($2 ^* (x5 ^+ $ (1))) with (f123 (next123 x5)).
      simpl in Hinv.
      destruct tl; simpl in *; dest; subst; auto.
      rewrite H1; auto.
Qed.

