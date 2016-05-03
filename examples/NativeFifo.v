Require Import Arith.Peano_dec Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv.
Require Import Ex.Fifo.

Set Implicit Arguments.

Section NativeFifo.
  Variable fifoName: string.
  Variable dType: Kind.
  Variable default: ConstT dType.

  Notation "^ s" := (fifoName .. s) (at level 0).

  Definition listEltT ty := list (ty dType).
  Definition listEltK ty := @NativeKind (listEltT ty) nil.
  Definition listElt ty := (^"elt" :: (@NativeConst (listEltT ty) nil nil))%struct.

  Definition listIsEmpty {ty} (l: fullType ty (listEltK ty)) :=
    if eq_nat_dec (length l) 1 then ConstBool true else ConstBool false.
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
    (ReadN elt : listEltK ty <- ^"elt";
     Write ^"elt" <- (Var _ (listEltK ty) (listEnq d elt));
     Retv)%kami.

  Definition nativeDeq {ty} : ActionT ty dType :=
    (ReadN elt : listEltK ty <- ^"elt";
     Assert !$$(listIsEmpty elt);
     Write ^"elt" <- (Var _ (listEltK ty) (listDeq elt));
     Ret (listFirstElt elt))%kami.

  Definition nativeFirstElt {ty} : ActionT ty dType :=
    (ReadN elt : listEltK ty <- ^"elt";
     Assert !$$(listIsEmpty elt);
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
     listIsEmpty listEnq listDeq listFirstElt
     nativeEnq nativeDeq nativeFirstElt: MethDefs.

Require Import SemFacts Decomposition Refinement Tactics Lib.Struct Lib.FMap.

(* Inductive SubstepsDet: list (Attribute (Action Void)) -> *)
(*                        list DefMethT -> RegsT -> UpdatesT -> LabelT -> Prop := *)
(* | SDEmptyMeth: forall o, SubstepsDet nil nil o (M.empty _) *)
(*                                      {| annot := None; defs := M.empty _; calls := M.empty _ |} *)
(* | SDEmptyRule: forall rules o, *)
(*     rules <> nil -> *)
(*     SubstepsDet rules nil o (M.empty _) *)
(*                 {| annot := Some None; *)
(*                    defs := M.empty _; calls := M.empty _ |} *)
(* | SDAddRule: forall (rules: list (Attribute (Action Void))) dms o pu pl, *)
(*     SubstepsDet nil dms o pu pl -> *)
(*     forall rn rb ru rul rcs, *)
(*       In (rn :: rb)%struct rules -> *)
(*       SemAction o (rb type) ru rcs WO -> *)
(*       rul = Rle (Some rn) -> *)
(*       CanCombineUUL pu pl ru rcs rul -> *)
(*       forall u l, *)
(*         u = M.union pu ru -> *)
(*         l = mergeLabel (getLabel rul rcs) pl -> *)
(*         SubstepsDet rules dms o u l *)
(* | SDSkipRule: forall rules dms o pu pl, *)
(*     rules <> nil -> *)
(*     SubstepsDet nil dms o pu pl -> *)
(*     SubstepsDet rules dms o pu pl *)
(* | SDAddMeth: forall dms o pu pl, *)
(*     SubstepsDet nil dms o pu pl -> *)
(*     forall (dm: DefMethT) du dul dcs argV retV, *)
(*       SemAction o (projT2 (attrType dm) type argV) du dcs retV -> *)
(*       dul = (Meth (Some (attrName dm :: existT SignT (projT1 (attrType dm)) (argV, retV))%struct)) -> *)
(*       CanCombineUUL pu pl du dcs dul -> *)
(*       forall u l, *)
(*         u = M.union pu du -> *)
(*         l = mergeLabel (getLabel dul dcs) pl -> *)
(*         SubstepsDet nil (dm :: dms) o u l *)
(* | SDSkipMeth: forall dms o pu pl, *)
(*     SubstepsDet nil dms o pu pl -> *)
(*     forall dm, SubstepsDet nil (dm :: dms) o pu pl. *)

(* Lemma substepsInd_implies_substepsDet: *)
(*   forall m o u l, *)
(*     SubstepsInd m o u l -> *)
(*     SubstepsDet (getRules m) (getDefsBodies m) o u l. *)
(* Proof. *)
(*   admit. *)
(* Qed. *)

(* Lemma substepsInd_substep_meth: *)
(*   forall m o u l, *)
(*     SubstepsInd m o u l -> *)
(*     annot l = None -> *)
(*     u = M.empty _ /\ l = {| annot := None; defs := M.empty _; calls := M.empty _ |} \/ *)
(*     exists u1 l1 u2 ul2 cs2, *)
(*       SubstepsInd m o u1 l1 /\ annot l1 = None /\ *)
(*       Substep m o u2 ul2 cs2 /\ match ul2 with Meth (Some _)  => True | _ => False end /\ *)
(*       CanCombineUUL u1 l1 u2 cs2 ul2 /\ *)
(*       u = M.union u1 u2 /\ *)
(*       l = mergeLabel (getLabel ul2 cs2) l1. *)
(* Proof. *)
(*   admit. *)
(* Qed. *)

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

  Lemma liftPLabel_id:
    forall r l,
      liftPLabel id (fun _ rl => Some rl) r l = l.
  Proof.
    unfold liftPLabel; intros.
    destruct l as [[[|]|] d c]; auto.
  Qed.

  (* TODO: better to find a lemma (or an ltac) to generate 2^n subgoals *)
  Lemma fifo_refines_nativefifo: fifo <<== nfifo.
  Proof.
    admit.
    (* apply stepRefinement with (theta:= fifo_nfifo_regMap) (ruleMap:= fifo_nfifo_ruleMap); *)
    (*   [kdecompose_regmap_init; kinv_finish|]. *)

    (* intros; pose proof (@fifo_inv_0_ok o H). *)

    (* apply step_consistent in H0; inv H0. *)
    (* clear HWellHidden. *)

    (* (* apply substepsInd_substep_meth in HSubSteps; auto; clear H0. *) *)
    (* Opaque liftPLabel hide mergeLabel getLabel. *)
    (* apply substepsInd_implies_substepsDet in HSubSteps. *)
    (* repeat *)
    (*   lazymatch goal with *)
    (*   | [H: False |- _] => inv H *)
    (*   | [H: In _ _ |- _] => inv H; fail *)
    (*   | [H: _ <> _ |- _] => elim H; reflexivity *)
    (*   | [H: SubstepsDet _ _ _ _ _ |- _] => inv H; simpl in * *)
    (*   end. *)
    (* Transparent liftPLabel hide mergeLabel getLabel. *)

    (* - exfalso. *)
    (*   invertActionRep. *)
    (*   clear -H6; inv H6; dest; clear -H. *)
    (*   eapply M.Disj_find_union_3 with (k:= ^"full"); [exact H| |]. *)
    (*   + findeq. *)
    (*   + findeq. *)
      
    (* - exfalso. *)
    (*   invertActionRep. *)
    (*   clear -H6; inv H6; dest; clear -H. *)
    (*   eapply M.Disj_find_union_3 with (k:= ^"full"); [exact H| |]. *)
    (*   + findeq. *)
    (*   + findeq. *)
      
    (* - invertActionRep. *)
    (*   clear H6 H9. *)
    (*   kregmap_red. *)
    (*   kinv_red. *)
    (*   eexists; split. *)
    (*   + rewrite idElementwiseId. *)
    (*     rewrite liftPLabel_id. *)
    (*     apply step_consistent. *)
    (*     constructor. *)
    (*     eapply SubstepsCons. *)
    (*     * eapply SubstepsCons. *)
    (*       { eapply SubstepsNil. } *)
    (*       { eapply SingleMeth. *)
    (*         { left; reflexivity. } *)
    (*         { instantiate (4:= argV). *)
    (*           repeat econstructor. *)
    (*           { rewrite M.find_add_2 by discriminate. *)
    (*             rewrite M.find_add_2 by discriminate. *)
    (*             rewrite M.find_add_1 by reflexivity. *)
    (*             reflexivity. *)
    (*           } *)
    (*           { reflexivity. } *)
    (*           { rewrite M.find_add_1 by reflexivity. *)
    (*             reflexivity. *)
    (*           } *)
    (*         } *)
    (*       } *)
    (*       { repeat split; simpl; auto. *)
    (*         intro Hx; eapply M.F.P.F.empty_in_iff; eauto. *)
    (*       } *)
    (*       { reflexivity. } *)
    (*       { reflexivity. } *)
    (*     * eapply SingleMeth. *)
    (*       { right; right; left; reflexivity. } *)
    (*       { instantiate (4:= argV0). *)
    (*         repeat econstructor. *)
    (*         { rewrite M.find_add_2 by discriminate. *)
    (*           rewrite M.find_add_1 by reflexivity. *)
    (*           reflexivity. *)
    (*         } *)
    (*         { reflexivity. } *)
    (*         { rewrite M.find_add_1 by reflexivity. *)
    (*           reflexivity. *)
    (*         } *)
    (*       } *)
    (*     * repeat split; simpl; auto. *)
    (*       intro Hx. admit. *)
    (*     * reflexivity. *)
    (*     * kinv_red; simpl. *)
    (*       f_equal. *)
    (*       meqReify. *)
    (*       admit. *)
    (*     * unfold wellHidden, hide; simpl. *)
    (*       mred; split; auto. *)
    (*       unfold getCalls; simpl. *)
    (*       apply M.KeysDisj_empty. *)
      
    (* - admit. *)
    (* - admit. *)
    (* - admit. *)
    (* - admit. *)
    (* - exists (M.empty _); split; auto. *)
    (*   admit. *)
  Qed.

End Facts.

