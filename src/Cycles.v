Require Import Bool List String.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.FMap Program.Equality.
Require Import Syntax.
Require Export SemanticsExprAction Semantics SemFacts.

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

  
