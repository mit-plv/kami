Require Import Arith.Peano_dec Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct.
Require Import Lib.FMap Lib.Indexer Lib.StringBound.
Require Import Syntax Semantics SemFacts Equiv Refinement Tactics DecompositionOne.
Require Import Ex.Fifo Ex.NativeFifo.

Section Facts.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.
  Variable default: ConstT dType.

  Definition fifo := fifo fifoName sz dType.
  Definition nfifo := @nativeFifo fifoName dType default.
  Hint Unfold fifo nfifo: ModuleDefs.

  Notation "^ s" := (fifoName .. s) (at level 0).

  Fixpoint fifo_nfifo_elt_not_full
           (eltv : word sz -> type dType)
           (enqPv : word sz)
           (edSub : nat): list (type dType) :=
    match edSub with
    | O => nil
    | S ed =>
      (eltv (enqPv ^- (natToWord sz edSub)))
        :: (fifo_nfifo_elt_not_full eltv enqPv ed)
    end.

  Definition fifo_nfifo_eta (r: RegsT): option (sigT (fullType type)).
  Proof.
    kgetv ^"elt"%string eltv r (Vector dType sz) (None (A:= sigT (fullType type))).
    kgetv ^"empty"%string emptyv r Bool (None (A:= sigT (fullType type))).
    kgetv ^"full"%string fullv r Bool (None (A:= sigT (fullType type))).
    kgetv ^"enqP"%string enqPv r (Bit sz) (None (A:= sigT (fullType type))).
    kgetv ^"deqP"%string deqPv r (Bit sz) (None (A:= sigT (fullType type))).

    refine (Some (existT _ (listEltK dType type) _)).
    destruct (weq enqPv deqPv).
    - refine (if fullv then _ else _).
      + exact ((eltv deqPv) :: (fifo_nfifo_elt_not_full eltv enqPv (wordToNat (wones sz)))).
      + exact nil.
    - exact (fifo_nfifo_elt_not_full eltv enqPv (wordToNat (enqPv ^- deqPv))).
  Defined.
  Hint Unfold fifo_nfifo_eta: MethDefs.

  Definition fifo_nfifo_theta (r: RegsT): RegsT :=
    match fifo_nfifo_eta r with
    | Some er => M.add ^"elt" er (M.empty _)
    | None => M.empty _
    end.
  Hint Unfold fifo_nfifo_theta: MethDefs.
  
  Definition fifo_nfifo_ruleMap (_: RegsT) (r: string): option string := Some r.
  Hint Unfold fifo_nfifo_ruleMap: MethDefs.

  Definition fifo_inv_0 (o: RegsT): Prop.
  Proof.
    kexistv ^"elt"%string eltv o (Vector dType sz).
    kexistv ^"empty"%string emptyv o Bool.
    kexistv ^"full"%string fullv o Bool.
    kexistv ^"enqP"%string enqPv o (Bit sz).
    kexistv ^"deqP"%string deqPv o (Bit sz).
    exact True.
  Defined.
  Hint Unfold fifo_inv_0: InvDefs.

  Lemma fifo_inv_0_ok':
    forall init n ll,
      init = initRegs (getRegInits fifo) ->
      Multistep fifo init n ll ->
      fifo_inv_0 n.
  Proof.
    induction 2.

    - simpl in H; kinv_magic.

    - specialize (IHMultistep H); subst; clear H0.
      apply step_consistent in HStep; inv HStep.

      clear HWellHidden; induction HSubSteps; [auto|subst].
      inv H; [mred|mred|inv HInRules|].

      inv H0.
      rewrite M.union_comm with (m1:= u) by auto.
      rewrite <-M.union_assoc.
      generalize dependent (M.union u n); intros.

      clear H H1.
      CommonTactics.dest_in; simpl in *; invertActionRep.

      + kinv_magic.
      + kinv_magic.
      + kinv_magic.
  Qed.

  Lemma fifo_inv_0_ok:
    forall o,
      reachable o fifo ->
      fifo_inv_0 o.
  Proof.
    intros; inv H; inv H0.
    eapply fifo_inv_0_ok'; eauto.
  Qed.

  Lemma fifo_refines_nativefifo: fifo <<== nfifo.
  Proof.
    admit.
    (* apply decompositionOne with (eta:= fifo_nfifo_eta) *)
    (*                               (ruleMap:= fifo_nfifo_ruleMap) *)
    (*                               (specRegName:= ^"elt"); *)
    (*   [unfold theta; kdecompose_regmap_init; kinv_finish| | | | | |]. *)

    (* - kequiv. *)
    (* - unfold theta; kdecompose_regmap_init; kinv_finish. *)
    (* - auto. *)
    (* - auto. *)
    (* - intros; inv H0; inv HInRules. *)
    (* - intros; inv H0. *)
    (*   CommonTactics.dest_in; simpl in *; invertActionRep. *)
    (*   + admit. *)
    (*   + admit. *)
    (*   + admit. *)

    (* - intros; subst. *)
    (*   inv H0; inv H1; inv H3; inv H4. *)
    (*   + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto. *)
    (*   + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto. *)
    (*   + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto. *)
    (*   + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto. *)
    (*   + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto. *)
    (*   + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto. *)
    (*   + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto. *)
    (*   + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto. *)
    (*   + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto. *)
    (*   + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto. *)
    (*   + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto. *)
    (*   + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto. *)
    (*   + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto. *)
    (*   + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto. *)
    (*   + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto. *)
    (*   + clear HIn1 HIn2. *)
    (*     admit. *)
    (*     (* CommonTactics.dest_in. *) *)
  Qed.
  
End Facts.

