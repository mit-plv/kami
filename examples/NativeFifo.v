Require Import Arith.Peano_dec Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv.
Require Import Ex.Fifo.

Set Implicit Arguments.

Section NativeFifo.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.
  Variable default: ConstT dType.

  Notation "^ s" := (fifoName .. s) (at level 0).

  Definition listEltT ty := list (ty dType).
  Definition listEltK ty := @NativeKind (listEltT ty) nil.
  Definition listElt ty := (^"elt" :: (@NativeConst (listEltT ty) nil nil))%struct.

  Definition listIsFull {ty} (l: fullType ty (listEltK ty)) :=
    if eq_nat_dec (length l) (sz - 1) then true else false.
  Definition listIsEmpty {ty} (l: fullType ty (listEltK ty)) :=
    if eq_nat_dec (length l) 1 then true else false.
  Definition listEnq {ty} (a: ty dType) (l: fullType ty (listEltK ty)) :=
    a :: l.
  Definition listDeq {ty} (l: fullType ty (listEltK ty)) :=
    match l with
    | nil => nil
    | h :: t => t
    end.
  Definition listFirstElt {ty} (l: fullType ty (listEltK ty)): Expr ty (SyntaxKind dType) :=
    match l with
    | nil => ($$default)%kami
    | h :: t => (#h)%kami
    end.

  (* defined methods *)
  Definition nativeEnq {ty} : forall (d: ty dType), ActionT ty Void := fun d =>
    (Read isFull <- ^"full";
     Assert !#isFull;
     ReadN elt : listEltK ty <- ^"elt";
     Write ^"elt" <- (Var _ (listEltK ty) (listEnq d elt));
     Write ^"empty" <- $$false;
     Write ^"full" <- $$(listIsFull elt);
     Retv)%kami.

  Definition nativeDeq {ty} : ActionT ty dType :=
    (Read isEmpty <- ^"empty";
     Assert !#isEmpty;
     ReadN elt : listEltK ty <- ^"elt";
     Write ^"full" <- $$false;
     Write ^"empty" <- $$(listIsEmpty elt);
     Write ^"elt" <- (Var _ (listEltK ty) (listDeq elt));
     Ret (listFirstElt elt))%kami.

  Definition nativeFirstElt {ty} : ActionT ty dType :=
    (Read isEmpty <- ^"empty";
     Assert !#isEmpty;
     ReadN elt : listEltK ty <- ^"elt";
     Ret (listFirstElt elt))%kami.

  Definition nativeFifo := MODULE {
    RegisterN ^"elt" : listEltK type <- (NativeConst nil nil)
    with Register ^"empty" : Bool <- true
    with Register ^"full" : Bool <- Default

    with Method ^"enq"(d : dType) : Void := (nativeEnq d)
    with Method ^"deq"() : dType := nativeDeq
    with Method ^"firstElt"() : dType := nativeFirstElt
  }.

  Definition nativeSimpleFifo := MODULE {
    RegisterN ^"elt" : listEltK type <- (NativeConst nil nil)
    with Register ^"empty" : Bool <- true
    with Register ^"full" : Bool <- Default

    with Method ^"enq"(d : dType) : Void := (nativeEnq d)
    with Method ^"deq"() : dType := nativeDeq
  }.

End NativeFifo.

Hint Unfold nativeFifo nativeSimpleFifo : ModuleDefs.
Hint Unfold listEltT listEltK listElt
     listIsFull listIsEmpty listEnq listDeq listFirstElt
     nativeEnq nativeDeq nativeFirstElt: MethDefs.

Require Import Decomposition Refinement Tactics Lib.FMap.

Section Facts.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.
  Variable default: ConstT dType.

  Definition fifo := fifo fifoName sz dType.
  Definition nfifo := @nativeFifo fifoName sz dType default.
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

  Definition fifo_nfifo_regMap (r: RegsT): RegsT.
  Proof.
    kgetv ^"elt"%string eltv r (Vector dType sz) (M.empty (sigT (fullType type))).
    kgetv ^"empty"%string emptyv r Bool (M.empty (sigT (fullType type))).
    kgetv ^"full"%string fullv r Bool (M.empty (sigT (fullType type))).
    kgetv ^"enqP"%string enqPv r (Bit sz) (M.empty (sigT (fullType type))).
    kgetv ^"deqP"%string deqPv r (Bit sz) (M.empty (sigT (fullType type))).

    refine (M.add ^"elt" (existT _ (listEltK dType type) _) _).
    - destruct (weq enqPv deqPv).
      + refine (if fullv then _ else _).
        * exact ((eltv deqPv) :: (fifo_nfifo_elt_not_full eltv enqPv (wordToNat (wones sz)))).
        * exact nil.
      + exact (fifo_nfifo_elt_not_full eltv enqPv (wordToNat (enqPv ^- deqPv))).
    - exact (M.add ^"empty" (existT _ _ emptyv) (M.add ^"full" (existT _ _ fullv) (M.empty _))).
  Defined.
  Hint Unfold fifo_nfifo_regMap: MethDefs.
  
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
    apply stepRefinement with (theta:= fifo_nfifo_regMap) (ruleMap:= fifo_nfifo_ruleMap);
      [kdecompose_regmap_init; kinv_finish|].

    intros.
    pose proof (@fifo_inv_0_ok o H).
    
    exists (fifo_nfifo_regMap u).
    split.

    - apply step_consistent; apply step_consistent in H0.
      inv H0.
      match goal with
      | [ |- StepInd _ _ _ ?l ] =>
        replace l with (hide l0) by admit
      end.
      constructor; [|admit].

      clear HWellHidden.

      induction HSubSteps; [constructor|subst].
      inv H0.

      + econstructor.
        * eassumption.
        * apply EmptyRule.
        * admit.
        * mred.
        * reflexivity.
      + econstructor.
        * eassumption.
        * apply EmptyMeth.
        * unfold CanCombineUUL; repeat split; auto.
          destruct (annot l); auto.
        * mred.
        * reflexivity.
      + inv HInRules.
      + CommonTactics.dest_in; simpl in *.
        * invertActionRep.
          econstructor.
          { eassumption. }
          { apply SingleMeth.
            { left; reflexivity. }
            { simpl.
              instantiate (1:= WO).
              instantiate (1:= M.empty _).
              instantiate (2:= argV).
              repeat econstructor.
              { kinv_red.
                kregmap_red.
                reflexivity.
              }
              { kinv_finish. }
              { kinv_red.
                kregmap_red.
                reflexivity.
              }
            }
          }
          { admit. }
          { admit. }
          { reflexivity. }
        * admit.
        * admit.

    - apply step_consistent in H0; inv H0.
      clear HWellHidden.
      induction HSubSteps; [reflexivity|].
      admit.
    
  Abort.

End Facts.

