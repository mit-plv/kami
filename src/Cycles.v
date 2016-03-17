Require Import Bool List String.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.FMap Program.Equality.
Require Import Syntax.
Require Export SemanticsExprAction Semantics SemFacts SemOp2 Wf.

Set Implicit Arguments.

Section GivenModule.
  Variable m: Modules.

  Definition getConst k :=
    match k as k' return fullType typeUT k' with
    | SyntaxKind _ => tt
    | NativeKind _ c' => c'
    end.

  Inductive ActionCycle:
    forall k,
      ActionT type k -> list string -> Prop :=
  | CycleMCallExt
      meth s (marg: Expr type (SyntaxKind (arg s)))
      retK
      (cont: type (ret s) -> ActionT type retK)
      called
      (HNotInDefs: ~ In meth (getDefs m))
      (HSemActionOp: forall mret, ActionCycle (cont mret) called):
      ActionCycle (MCall meth s marg cont) called
  | CycleLet
      k (e: Expr type k) retK
      (cont: fullType type k -> ActionT type retK)
      called
      (HSemActionOp: forall mret, ActionCycle (cont mret) called):
      ActionCycle (Let_ e cont) called
  | CycleReadReg
      (r: string) regT
      retK (cont: fullType type regT -> ActionT type retK)
      called
      (HSemActionOp: forall mret, ActionCycle (cont mret) called):
      ActionCycle (ReadReg r _ cont) called
  | CycleWriteReg
      (r: string) k
      (e: Expr type k)
      retK
      (cont: ActionT type retK)
      called
      (HSemActionOp: ActionCycle cont called):
      ActionCycle (WriteReg r e cont) called
  | CycleIfElse
      (p: Expr type (SyntaxKind Bool)) k1
      (a a': ActionT type k1)
      k2 (cont: type k1 -> ActionT type k2)
      called
      (HActionIf: ActionCycle a called)
      (HActionElse: ActionCycle a' called)
      (HSemActionOp: forall mret, ActionCycle (cont mret) called):
      ActionCycle (IfElse p a a' cont) called
  | CycleAssertTrue
      (p: Expr type (SyntaxKind Bool)) k2
      (cont: ActionT type k2)
      called
      (HSemActionOp: ActionCycle cont called):
      ActionCycle (Assert_ p cont) called
  | CycleReturn
      k (e: Expr type (SyntaxKind k)) called:
      ActionCycle (Return e) called
  | CycleCallInt
      meth s (marg: Expr type (SyntaxKind (arg s)))
      retK
      (cont: type (ret s) -> ActionT type retK)
      called
      (HSemActionOp: forall mret, ActionCycle (cont mret) called)
      (HMethDisj: ~ In meth called)
      (HMethOp: MethCycle (meth :: called)):
      ActionCycle (MCall meth s marg cont) called
  with
  MethCycle: list string -> Prop :=
  |  MethCycleIntro
       meth body
       (HInDefs: In (meth :: body)%struct (getDefsBodies m))
       called
       (HSemActionOp: forall marg, ActionCycle (projT2 body type marg) (meth :: called))
       calledFinal
       (HCalledFinal: calledFinal = meth :: called):
       MethCycle calledFinal.

  Scheme ActionCycle_ind_2 := Induction for ActionCycle Sort Prop
                              with MethCycle_ind_2 := Induction for MethCycle Sort Prop.

  Definition mutual_cycle_ind P P0 :=
    fun h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
      conj (@ActionCycle_ind_2 P P0 h1 h2 h3 h4 h5 h6 h7 h8 h9)
           (@MethCycle_ind_2 P P0 h1 h2 h3 h4 h5 h6 h7 h8 h9).

  Definition NoModulesCycle := forall meth, In meth (getDefs m) -> MethCycle (meth :: nil).

  Variable noModulesCycle: NoModulesCycle.
  Variable wfModules: WfModules type m.

  Record MethOpRec :=
    { mAttr: Attribute (sigT MethodT);
      mUpd: UpdatesT;
      mDefs: MethsT;
      mCalls: MethsT
    }.

  Variable o: RegsT.
  
  Inductive StepAnnot: UpdatesT -> LabelT -> LabelT -> Prop :=
  | StepAnnotIntro u lHide l
      (HLHide: lHide = hide l)
      (HWellHidden: wellHidden m lHide)
      (HSubstepsInd: SubstepsInd m o u l):
      StepAnnot u lHide l.

  Theorem StepAnnot_implies_StepInd u lHide l:
    StepAnnot u lHide l -> StepInd m o u lHide.
  Proof.
    intros.
    induction H.
    subst.
    constructor; intuition.
  Qed.

  Theorem StepInd_implies_StepAnnot u lHide:
    StepInd m o u lHide -> exists l, StepAnnot u lHide l /\ lHide = hide l.
  Proof.
    intros.
    induction H.
    exists l; intuition.
    constructor; intuition.
  Qed.
  
(*
  Theorem stepToSemActionOp u meth s argval lHide l:
    StepAnnot u lHide l ->
    annot lHide = None ->
    defs lHide = M.add meth (existT _ s argval) (M.empty _) ->
    MethOp m o meth argval u (defs l) (calls l).
  Proof.
    intros.
    destruct lHide; simpl in *.
    dependent destruction H;
      destruct l as [a ds cs]; simpl in *; subst.
    unfold wellHidden in *; simpl in *; dest.
    assert (sth: M.MapsTo meth (existT _ _ argval) ds).
    {  clear - H1.
       match goal with
       | H: ?m1 = ?m2 |- _ => assert (M.Equal m1 m2) by (rewrite H; intuition)
       end.
       pose proof (proj1 (@M.F.P.F.Equal_mapsto_iff _ _ _) H meth (existT _ _ argval)).
       apply proj2 in H0.
       assert (sth2: M.MapsTo meth (existT _ _ argval)
                              (M.add meth (existT _ _ argval) (M.empty _))) by
           (apply M.F.P.F.add_mapsto_iff; intuition).
       specialize (H0 sth2).
       apply M.subtractKV_mapsto in H0; intuition.
    }
    assert (sth2:
              exists u' ds' cs' u'' cs'',
                SubstepsInd m o u' {| annot := None; defs := ds'; calls := cs' |} /\
                Substep m o u'' (Meth (Some (meth :: existT _ _ argval)%struct)) cs'' /\
                M.Disj u'' u' /\
                M.Disj cs'' cs' /\
                ~ M.In meth ds' /\
                u = M.union u'' u' /\
                ds = M.add meth (existT _ _ argval) ds' /\
                cs = M.union cs'' cs').
    { clear - HSubstepsInd sth.
      dependent induction HSubstepsInd.
      - apply M.F.P.F.empty_mapsto_iff in sth; intuition.
      - dependent destruction l; simpl in *.
        dependent destruction sul; simpl in *.
        inv H2; rewrite M.union_empty_L in *.
        destruct annot; discriminate.
        inv H2.
        destruct o0.
        destruct a.
        apply M.mapsto_union in sth.
        destruct sth.
        specialize (IHHSubstepsInd argval defs calls eq_refl).
        apply M.F.P.F.add_mapsto_iff in H1.
        destruct H1; dest.
        subst.
        subst.
        inv H2.
    }
      pose proof (
      destruct H0.
      
      eapply M.F.P.F.Equal_mapsto_iff in H.
      rewrite H1.
      subst.
      assert (M.Equal (
      findeq.
      rewrite M.subtractKV_mapsto in H1.
    rewrite H1 in HWellHidden.
    unfold hide in *; simpl in *.
    True.
    exists (mr: list MethOpRec),
      
    True.
  Proof.
    intros.
    inv H0; inv H.
    induction HSubSteps.
    eapply wfDms_dms in H1.
    inv H.
*)

  (*
  Theorem wellHiddenEmptySubstepsNotRule o ss:
    substepsComb ss ->
    wellHidden m (hide (foldSSLabel ss)) ->
    match hide (foldSSLabel ss) with
    | {| annot := Some r |} => ss = {| substep := EmptyRule m o |} :: nil
    | {| annot := None; defs := ds; calls := cs |} => ds = M.empty _
    end.
  Proof.
    dependent induction ss; simpl in *; intros.
    - rewrite M.subtractKV_empty_1; intuition.
    - dependent destruction H.
      specialize (IHss H).

          o u r cs:
    Step m o u {| annot := Some r; defs := M.empty _; calls := cs |} ->
    u = M.empty _ /\ cs = M.empty _.
   *)
End GivenModule.

  
