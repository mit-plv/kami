Require Import Kami.
(* begin hide *)
Require Import Kami.Synthesize.
Require Import Ex.Fifo Ex.NativeFifo Ex.SimpleFifoCorrect.
Require Import Ext.BSyntax.
Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
(* end hide *)

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

Open Scope string.

(*+ Kami: A Platform for High-Level Parametric Hardware Specification and its Modular Verification +*)

(*! Welcome to the Kami in-depth tutorial! This tutorial consists of following sections:
 * 1) Kami language: syntax and semantics
 * 2) Refinement between Kami modules
 * 3) A case study: proving the correctness of a 3-stage pipelined system
 * 4) Demo: simulating a Kami program (with the Bluespec simulator)
 !*)

(******************************************************************************)

(*+ Language Syntax +*)

(** Kami has its own syntax, which is very similar to Bluespec's. It uses shallow embedding with respect to variable binding and has fancy notations built with "Notation" in Coq. *)

(** A module consists of registers, rules, and methods. *)
Print Mod.

(** Rules are executed by a global rule scheduler. Methods are executed by method calls, which can be called by other modules once they are composed. *)

(** A rule or a method is defined as a sequence of actions. *)
Print ActionT.
Print Expr.

(** Here is a simple Kami module. *)
Definition kamiModule :=
  MODULE {
    Register "data" : Bit 8 <- Default

    with Rule "produce" :=
      Read data <- "data";
      Call (MethodSig ("fifo1" -- "enq") (Bit 8): Void)(#data);
      Write "data" <- #data + $1;
      Retv

    with Method "setData" (d: Bit 8) : Void :=
      Write "data" <- #d;
      Retv
  }.

(******************************************************************************)

(*+ Semantics +*)

(** Denotational semantics for [Expr] *)
Print evalExpr.

(** Operational semantics for [Action] *)
Print SemAction.

(**
 * A global rule scheduler tries to execute as many simultaneous rules as possible with the following conditions:
 * 1) Any two rules should not conflict in terms of register writes and method calls.
 * 2) A scheduled rule should satisfy assertions (guards).
 * 3) [One-rule-at-a-time semantics] In order to execute {r1, r2, ..., rn} simultaneously,
 *    there should exist a permutation of {ri} s.t. 
 *    (r1 | r2 | ... | rn)(s) = (r1 (r2 (... (rn(s)) ...))).
 *)

(** Label *)
Print LabelT.

(** Substep: semantics for a single rule or a method *)
Print Substep.

(** Substeps: for zero-or-one rule and multiple methods *)
Print SubstepsInd.

(** Step: lifted from [SubstepsInd], all internal communication is hidden *)
Print StepInd.

(** Multistep: (Step)^* *)
Print Multistep.

(** Behavior: [Multistep] started from the initial state *)
Print Behavior.

(******************************************************************************)

(*+ Trace Refinement +*)

Print traceRefines.
(** Let's just ignore p-mapping for now. *)

(** Reflexivity and transitivity *)
Check traceRefines_refl.
Check traceRefines_trans.

(** Commutativity and associativity w.r.t. module combination *)
Check traceRefines_comm.
Check traceRefines_assoc_1.
Check traceRefines_assoc_2.

(** Modular refinement *)
Check traceRefines_modular_noninteracting.
(* Check traceRefines_modular_interacting. *)

(******************************************************************************)

(*+ A case study: a 3-stage pipelined system +*)

(*! The first stage !*)

Section DataSizeAbs.

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
#[local] Hint Unfold enq1 : MethDefs.
#[local] Hint Unfold stage1 : ModuleDefs.

(******************************************************************************)

(*! The second stage !*)

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

#[local] Hint Unfold deq1 enq2 : MethDefs.
#[local] Hint Unfold stage2 : ModuleDefs.

(******************************************************************************)

(*! The third stage !*)

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

#[local] Hint Unfold deq2 sendAcc : MethDefs.
#[local] Hint Unfold stage3 : ModuleDefs.

(******************************************************************************)

(*! Fifos: the most fundamental hardware component for asynchronicity !*)

Definition fifo1 := simpleFifo "fifo1" 8 (Bit dataSize).
Definition fifo2 := simpleFifo "fifo2" 8 (Bit dataSize).
#[local] Hint Unfold fifo1 fifo2 : ModuleDefs.

Definition impl :=
  (stage1 ++ fifo1 ++ stage2 ++ fifo2 ++ stage3)%kami.
  #[local] Hint Unfold impl : ModuleDefs.

(******************************************************************************)

(*! What is the spec of this pipelined system? !*)

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
#[local] Hint Unfold spec : ModuleDefs.

(******************************************************************************)

(*! Well-formedness (for some properties) !*)

(** PHOAS well-formedness *)
Lemma stage1_PhoasWf: ModPhoasWf stage1.
Proof. kequiv. Qed.
Lemma stage2_PhoasWf: ModPhoasWf stage2.
Proof. kequiv. Qed.
Lemma stage3_PhoasWf: ModPhoasWf stage3.
Proof. kequiv. Qed.
#[local] Hint Resolve stage1_PhoasWf stage2_PhoasWf stage3_PhoasWf.
Lemma impl_PhoasWf: ModPhoasWf impl.
Proof. kequiv. Qed.
#[local] Hint Resolve impl_PhoasWf.

(** Well-formedness for valid register uses *)
Lemma stage1_RegsWf: ModRegsWf stage1.
Proof. kvr. Qed.
Lemma stage2_RegsWf: ModRegsWf stage2.
Proof. kvr. Qed.
Lemma stage3_RegsWf: ModRegsWf stage3.
Proof. kvr. Qed.
#[local] Hint Resolve stage1_RegsWf stage2_RegsWf stage3_RegsWf.

Lemma impl_RegsWf: ModRegsWf impl.
Proof. kvr. Qed.
#[local] Hint Resolve impl_RegsWf.

(******************************************************************************)

(*+ Correctness proof +*)

Theorem impl_ok: impl <<== spec.
Abort.

(******************************************************************************)

(*+ Substituting fifos with native-fifos +*)

(** Why? The fifo implementation is not simple to deal with. *)
Check simpleFifo.

Definition nfifo1 :=
  @nativeSimpleFifo "fifo1" (Bit dataSize) Default.
Definition nfifo2 :=
  @nativeSimpleFifo "fifo2" (Bit dataSize) Default.

Definition intSpec1 :=
  ((stage1 ++ nfifo1 ++ stage2) ++ fifo2 ++ stage3)%kami.
#[local] Hint Unfold intSpec1 : ModuleDefs.

(* begin hide *)
#[local] Hint Unfold nfifo1 nfifo2 : ModuleDefs.
Lemma intSpec1_PhoasWf: ModPhoasWf intSpec1.
Proof. kequiv. Qed.
#[local] Hint Resolve intSpec1_PhoasWf.
Lemma intSpec1_RegsWf: ModRegsWf intSpec1.
Proof. kvr. Qed.
#[local] Hint Resolve intSpec1_RegsWf.
(* end hide *)

Theorem impl_intSpec1: impl <<== intSpec1.
Proof.
  ktrans ((stage1 ++ fifo1 ++ stage2) ++ fifo2 ++ stage3)%kami.

  - ksimilar; vm_compute; tauto.
  - kmodular.
    + kmodular.
      * krefl.
      * kmodular.
        -- apply sfifo_refines_nsfifo.
        -- krefl.
    + krefl.
Qed.

(******************************************************************************)

(*+ Generic invariants for pipelined systems +*)

Section PipelineInv.
  Variables (next: word dataSize -> word dataSize)
            (f: word dataSize -> word dataSize).

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

  (** Inversion theorems: for [enq] and [deq] *)
  
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
    forall e h,
      pipeline_inv (h :: e) ->
      pipeline_inv e.
  Proof.
    induction e; simpl; intros; auto.
    dest; auto.
  Qed.

End PipelineInv.

(******************************************************************************)

(*+ Merging the first two stages +*)

Definition impl12 := (stage1 ++ nfifo1 ++ stage2)%kami.

(* begin hide *)
#[local] Hint Unfold impl12 : ModuleDefs.
Lemma impl12_PhoasWf: ModPhoasWf impl12.
Proof. kequiv. Qed.
#[local] Hint Resolve impl12_PhoasWf.
Lemma impl12_RegsWf: ModRegsWf impl12.
Proof. kvr. Qed.
#[local] Hint Resolve impl12_RegsWf.
(* end hide *)

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

(* begin hide *)
#[local] Hint Unfold spec12 : ModuleDefs.
Lemma spec12_PhoasWf: ModPhoasWf spec12.
Proof. kequiv. Qed.
#[local] Hint Resolve spec12_PhoasWf.
Lemma spec12_RegsWf: ModRegsWf spec12.
Proof. kvr. Qed.
#[local] Hint Resolve spec12_RegsWf.
(* end hide *)

Lemma impl12_ok: impl12 <<== spec12.
Abort.

(******************************************************************************)

(*+ Inlining +*)

Definition impl12Inl: {m: Modules & impl12 <<== m}.
Proof.
  kinline_refine impl12.
Defined.

Eval simpl in projT1 impl12Inl.

(******************************************************************************)

(*+ Proving the invariant for [impl12] +*)

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
#[local] Hint Unfold pipeline_inv: InvDefs.

(* begin hide *)
Ltac impl12_inv_dest_tac :=
  try match goal with
      | [H: impl12_inv _ |- _] => destruct H
      end;
  kinv_red.

Ltac impl12_inv_constr_tac :=
  econstructor;
  try (findReify; (reflexivity || eassumption); fail);
  kregmap_clear.

Ltac impl12_inv_tac :=
  impl12_inv_dest_tac; impl12_inv_constr_tac.
(* end hide *)

Lemma impl12_inv_ok':
  forall init n ll,
    init = initRegs (getRegInits (projT1 impl12Inl)) ->
    Multistep (projT1 impl12Inl) init n ll ->
    impl12_inv n.
Proof.
  induction 2; [kinv_dest_custom impl12_inv_tac; simpl; auto|].
  kinvert.
  - mred.
  - mred.
  - kinv_dest_custom impl12_inv_tac.
    fold (pipeline_inv next12 f12) in *.
    fold (@app (word dataSize)) in *.
    change (x ^+ $1) with (next12 x).
    change x with (f12 x) in Hinv.
    change x with (f12 x) at 1.
    change (next12 x) with (f12 (next12 x)).
    apply pipeline_inv_enq; auto.
  - kinv_dest_custom impl12_inv_tac.
    fold (pipeline_inv next12 f12) in *.
    destruct x; [discriminate|]; subst.
    eapply pipeline_inv_deq; eauto.
Qed.

Lemma impl12_inv_ok:
  forall o,
    reachable o (projT1 impl12Inl) ->
    impl12_inv o.
Proof.
  intros.
  inv H.
  inv H0.
  eapply impl12_inv_ok'; eauto.
Qed.

(******************************************************************************)

(*+ Proving refinement by decomposition  +*)

Definition impl12_regMap (ir sr: RegsT): Prop.
  kexistv "data" datav ir (Bit dataSize).
  kexistnv "fifo1"--"elt" eltv ir (listEltK (Bit dataSize) type).
  refine (sr = (["data" <- existT _ _ (hd datav eltv)]%fmap)).
Defined.
#[local] Hint Unfold impl12_regMap: MethDefs.

Definition impl12_ruleMap (o: RegsT): string -> option string :=
  "doDouble" |-> "produceDouble"; ||.
#[local] Hint Unfold impl12_ruleMap: MethDefs.

Lemma impl12_ok: impl12 <<== spec12.
Proof.
  kinline_refine_left impl12Inl.

  kdecomposeR_nodefs impl12_regMap impl12_ruleMap.
  kinv_add impl12_inv_ok.
  kinv_add_end.
  
  kinvert.
  + kinv_magic_with impl12_inv_dest_tac idtac.
    destruct x0; auto.
  + kinv_magic_with impl12_inv_dest_tac idtac.
    * destruct x; [discriminate|reflexivity].
    * destruct x as [|hd tl]; [discriminate|].
      simpl in Hinv.
      destruct tl; dest;
        subst; simpl in *; dest; subst; auto.
Qed.

(******************************************************************************)

(*+ What we've done so far +*)

Theorem impl_ok: impl <<== spec.
Proof.
  ketrans; [apply impl_intSpec1|].
  ktrans (spec12 ++ fifo2 ++ stage3)%kami.
  - kmodular.
    + apply impl12_ok.
    + krefl.
  - (* ?! *)
Abort.

(******************************************************************************)

(*+ Pipeline merging, once more +*)

Definition impl123 := (spec12 ++ nfifo2 ++ stage3)%kami.

(* begin hide *)
#[local] Hint Unfold impl123 : ModuleDefs.
Lemma impl123_PhoasWf: ModPhoasWf impl123.
Proof. kequiv. Qed.
#[local] Hint Resolve impl123_PhoasWf.
Lemma impl123_RegsWf: ModRegsWf impl123.
Proof. kvr. Qed.
#[local] Hint Resolve impl123_RegsWf.
(* end hide *)

Definition impl123Inl: {m: Modules & impl123 <<== m}.
Proof.
  kinline_refine impl123.
Defined.

Definition next123 := fun w : word dataSize => w ^+ $1.
Definition f123 := fun w : word dataSize => $2 ^* w.

(** We need this consistency lemma for this time. *)
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
#[local] Hint Immediate next_f_consistent.
Opaque next123 f123.

Record impl123_inv (o: RegsT) : Prop :=
  { datav : fullType type (SyntaxKind (Bit dataSize));
    Hdatav : M.find "data" o = Some (existT _ _ datav);
    eltv : fullType type (listEltK (Bit dataSize) type);
    Heltv : M.find "fifo2"--"elt"%string o = Some (existT _ _ eltv);

    Hinv : pipeline_inv next123 f123 (eltv ++ [$2 ^* datav])
  }.
#[local] Hint Unfold pipeline_inv: InvDefs.

(* begin hide *)
Ltac impl123_inv_dest_tac :=
  try match goal with
      | [H: impl123_inv _ |- _] => destruct H
      end;
  kinv_red.

Ltac impl123_inv_constr_tac :=
  econstructor;
  try (findReify; (reflexivity || eassumption); fail);
  kregmap_clear.

Ltac impl123_inv_tac :=
  impl123_inv_dest_tac; impl123_inv_constr_tac.
(* end hide *)

Lemma impl123_inv_ok':
  forall init n ll,
    init = initRegs (getRegInits (projT1 impl123Inl)) ->
    Multistep (projT1 impl123Inl) init n ll ->
    impl123_inv n.
Proof.
  induction 2; [kinv_dest_custom impl123_inv_tac; simpl; auto|].
  
  kinvert.
  - mred.
  - mred.
  - kinv_dest_custom impl123_inv_tac.
    fold (pipeline_inv next123 f123) in *.
    fold (@app (word dataSize)) in *.
    change (x ^+ $1) with (next123 x).
    change ($2 ^* x) with (f123 x) in Hinv.
    change ($2 ^* x) with (f123 x).
    change ($2 ^* next123 x) with (f123 (next123 x)).
    apply pipeline_inv_enq; auto.
  - kinv_dest_custom impl123_inv_tac.
    fold (pipeline_inv next123 f123) in *.
    destruct x; [discriminate|]; subst.
    eapply pipeline_inv_deq; eauto.
Qed.

Lemma impl123_inv_ok:
  forall o,
    reachable o (projT1 impl123Inl) ->
    impl123_inv o.
Proof.
  intros.
  inv H.
  inv H0.
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
#[local] Hint Unfold impl123_regMap: MethDefs.

Definition impl123_ruleMap (o: RegsT): string -> option string :=
  "consume" |-> "accDoubles"; ||.
#[local] Hint Unfold impl123_ruleMap: MethDefs.

Lemma impl123_ok: impl123 <<== spec.
Proof.
  kinline_refine_left impl123Inl.

  kdecomposeR_nodefs impl123_regMap impl123_ruleMap.
  kinv_add impl123_inv_ok.
  kinv_add_end.
  
  kinvert.
  + kinv_magic_with impl123_inv_dest_tac idtac.
    destruct x0; auto.
  + kinv_magic_with impl123_inv_dest_tac idtac.
    * simpl; destruct x; [discriminate|].
      simpl in *; subst.
      reflexivity.
    * destruct x; [discriminate|].
      simpl in *; subst.
      reflexivity.
    * destruct x as [|hd tl]; [discriminate|].
      change ($2 ^* (x5 ^+ $ (1))) with (f123 (next123 x5)).
      simpl in Hinv.
      destruct tl; simpl in *; dest; subst; auto.
      rewrite H1; auto.
Qed.

(******************************************************************************)

(*+ The final proof +*)

Theorem impl_ok: impl <<== spec.
Proof.
  ketrans; [apply impl_intSpec1|].
  ktrans (spec12 ++ fifo2 ++ stage3)%kami.
  - kmodular.
    + apply impl12_ok.
    + krefl.
  - ktrans (spec12 ++ nfifo2 ++ stage3)%kami.
    + kmodular; [krefl|].
      kmodular; [|krefl].
      apply sfifo_refines_nsfifo.
    + unfold MethsT; rewrite <-SemFacts.idElementwiseId.
      apply impl123_ok.
Qed.

End DataSizeAbs.

(******************************************************************************)

(*+ Extraction +*)

Extraction Language OCaml.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

Print impl.

Definition targetProcB := ModulesSToBModules (getModuleS (impl 32)).

(* Extraction "../Ext/Ocaml/Target.ml" targetProcB. *)

