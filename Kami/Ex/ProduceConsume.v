Require Import Ascii Bool String List.
Require Import Lib.FMap Lib.CommonTactics Lib.Indexer Lib.ilist Lib.Word Lib.Struct.
Require Import Kami.Syntax Kami.Semantics Kami.Notations.
Require Import Kami.Wf Kami.Inline Kami.InlineFacts Kami.Tactics Kami.ModuleBoundEx.
Require Import Ex.Fifo Ex.NativeFifo Ex.SimpleFifoCorrect.

Set Implicit Arguments.

Section ProduceConsume.
  Variable itemSize : nat.

  Definition p2cEnq := MethodSig "p2c"--"enq"(Bit itemSize) : Void.
  Definition p2cDeq := MethodSig "p2c"--"deq"(Void) : Bit itemSize.

  Definition convey := MethodSig "convey"(Bit itemSize) : Void.
  
  Definition producer :=
    MODULE {
        Register "item" : Bit itemSize <- Default

        with Rule "produce" :=
          Read item <- "item";
          Call p2cEnq(#item);
          Write "item" <- #item + $1;
          Retv
      }.

  Definition consumer :=
    MODULE {
        Rule "consume" :=
          Call item <- p2cDeq();
          Call convey(#item);
          Retv
      }.

  Variable fs : nat.
  Definition fifoSize := rsz fs.

  Definition pdcsImpl := (producer ++ (simpleFifo "p2c" fifoSize (Bit itemSize)) ++ consumer)%kami.
  Definition pdcsInterm :=
    (producer ++ (@nativeSimpleFifo "p2c" (Bit itemSize) Default) ++ consumer)%kami.

  Definition pdcsSpec :=
    MODULE {
        Register "item" : Bit itemSize <- Default

        with Rule "pdcs" :=
          Read item : Bit itemSize <- "item";
          Write "item" <- #item + $1;
          Call convey(#item);
          Retv
      }.

  Hint Unfold p2cEnq p2cDeq convey: MethDefs.
  Hint Unfold producer consumer pdcsImpl pdcsInterm pdcsSpec: ModuleDefs.

  Lemma producer_pwf:
    ModPhoasWf producer.
  Proof. kequiv. Qed.
  Hint Resolve producer_pwf.

  Lemma consumer_pwf:
    ModPhoasWf consumer.
  Proof. kequiv. Qed.
  Hint Resolve consumer_pwf.

  Lemma pdcsInterm_pwf:
    ModPhoasWf pdcsInterm.
  Proof. kequiv. Qed.
  Hint Resolve pdcsInterm_pwf.

  Lemma pdcsImpl_pwf:
    ModPhoasWf pdcsImpl.
  Proof. kequiv. Qed.
  Hint Resolve pdcsImpl_pwf.
  
  Lemma pdcsSpec_pwf:
    ModPhoasWf pdcsSpec.
  Proof. kequiv. Qed.
  Hint Resolve pdcsSpec_pwf.

  Definition pdcsIntermInl: Modules * bool.
  Proof.
    remember (inlineF pdcsInterm) as inlined.
    kinline_compute_in Heqinlined.
    match goal with
    | [H: inlined = ?m |- _] =>
      exact m
    end.
  Defined.

  (** Invariant *)

  Fixpoint elt_incremental_inv (l: list (type (Bit itemSize))) :=
    match l with
    | nil => True
    | h1 :: t1 =>
      match t1 with
      | nil => True
      | h2 :: t2 => h2 = h1 ^+ $1 /\ elt_incremental_inv t1
      end
    end.

  Definition elt_item_inv (itemv: fullType type (SyntaxKind (Bit itemSize)))
             (eltv: fullType type (listEltK (Bit itemSize) type)) :=
    match eltv with
    | nil => True
    | h :: t => itemv = h ^+ (natToWord _ (length t)) ^+ $1
    end.
  
  Record pdcs_inv (o: RegsT) : Prop :=
    { itemv : fullType type (SyntaxKind (Bit itemSize));
      Hitemv : M.find "item"%string o = Some (existT _ _ itemv);
      eltv : fullType type (listEltK (Bit itemSize) type);
      Heltv : M.find "p2c"--"elt"%string o = Some (existT _ _ eltv);

      Hinv : elt_item_inv itemv eltv /\ elt_incremental_inv eltv
    }.
  Hint Unfold elt_incremental_inv elt_item_inv: InvDefs.

  Ltac pdcs_inv_old :=
    try match goal with
        | [H: pdcs_inv _ |- _] => destruct H
        end;
    kinv_red.
  
  Ltac pdcs_inv_new :=
    econstructor; (* let's prove that the invariant holds for the next state *)
    try (findReify; (reflexivity || eassumption); fail);
    kregmap_clear. (* for improving performance *)

  Ltac pdcs_inv_tac := pdcs_inv_old; pdcs_inv_new.

  Lemma pdcs_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits (fst pdcsIntermInl)) ->
      Multistep (fst pdcsIntermInl) init n ll ->
      pdcs_inv n.
  Proof.
    induction 2; [kinv_dest_custom pdcs_inv_tac; auto|].
    
    kinvert.
    - mred.
    - mred.

    - kinv_dest_custom pdcs_inv_tac.
      clear -H6 H7; induction x0.
      + split; auto.
        simpl; rewrite <-wplus_assoc, <-natToWord_plus; reflexivity.
      + subst; split.
        * rewrite app_length; simpl.
          f_equal.
          rewrite <-wplus_assoc; f_equal.
          rewrite <-natToWord_plus; reflexivity.
        * destruct x0.
          { simpl; split; auto.
            rewrite <-wplus_assoc, <-natToWord_plus; reflexivity.
          }
          { dest; subst.
            specialize (IHx0 H0); clear H0; split; auto.
            apply IHx0; simpl.
            f_equal.
            rewrite <-wplus_assoc; f_equal.
            rewrite <-natToWord_plus; reflexivity.
          }

    - kinv_dest_custom pdcs_inv_tac.
      destruct x; [inv H3|]; subst.
      clear -H8; induction x; auto.
      dest; subst; split; auto.
      simpl; f_equal.
      rewrite <-wplus_assoc; f_equal.
      rewrite <-natToWord_plus; reflexivity.
  Qed.

  Lemma pdcs_inv_ok:
    forall o,
      reachable o (fst pdcsIntermInl) ->
      pdcs_inv o.
  Proof.
    intros; inv H; inv H0.
    eapply pdcs_inv_ok'; eauto.
  Qed.

  (** Refinement *)
  Definition pdcs_regMap (ir: RegsT) (sr: RegsT): Prop.
    kexistv "item"%string itemv ir (Bit itemSize).
    kexistnv "p2c"--"elt"%string eltv ir (listEltK (Bit itemSize) type).
    refine (sr = (["item" <- existT _ (SyntaxKind (Bit itemSize)) _]%fmap)).
    refine (match eltv with
            | nil => itemv
            | helt :: _ => helt
            end).
  Defined.
  Hint Unfold pdcs_regMap: MapDefs.
  
  Theorem pdcs_impl_refines_spec: pdcsImpl <<== pdcsSpec.
  Proof.
    ktrans pdcsInterm.
    - kmodular.
      + kdisj_edms_cms_ex 0.
      + kdisj_ecms_dms_ex 0.
      + krefl.
      + kmodular.
        * kdisj_edms_cms_ex 0.
        * kdisj_ecms_dms_ex 0.
        * apply sfifo_refines_nsfifo.
        * krefl.
    - kinline_left im.
      try (unfold MethsT; rewrite <-SemFacts.idElementwiseId).
      kdecomposeR_nodefs pdcs_regMap.
      kinv_add pdcs_inv_ok.
      kinv_add_end.
      kinvert.
      + kinv_action_dest.
        kinv_red.
        kinv_regmap_red.
        eexists; exists None; split; kinv_constr.
        kinv_eq.
        destruct x0; auto.
      + kinv_action_dest.
        kinv_red.
        destruct Hr; dest.
        kinv_regmap_red.
        eexists; exists (Some "pdcs"%string); split; kinv_constr.
        * kinv_eq.
          destruct x; [inv H2|reflexivity].
        * destruct x as [|hd tl]; [inv H2|].
          kinv_eq.
          destruct tl; dest; auto; subst.
          simpl; rewrite <-wplus_assoc, <-natToWord_plus; reflexivity.
  Qed.

End ProduceConsume.

