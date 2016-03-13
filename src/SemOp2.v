Require Import Bool List String.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.FMap.
Require Import Syntax.
Require Export SemanticsExprAction Semantics SemFacts SemOp.

Set Implicit Arguments.

Section GivenModule.
  Variable m: Modules.
  Variable o: RegsT.

  Inductive SubstepComb:
    UpdatesT -> UnitLabel (* firing point *) ->
    MethsT (* internal defs *) -> MethsT (* calls *) -> Prop :=
  | SSCStart
      u l cs
      (Hss: Substep m o u l cs):
      SubstepComb u l (M.empty _) cs
  | SSCComb
      u l ids cs
      (Hssc: SubstepComb u l ids cs)
      meth ar (Hmeth: M.find meth cs = Some ar)
      u' cs'
      (Hss: Substep m o u' (Meth (Some (meth :: ar)%struct)) cs')
      (HDisjRegs: M.Disj u u')
      (HDisjCalls: M.Disj cs cs')
      (HDisjIds: ~ M.In meth ids)
      u'' cs'' ids''
      (HUEq: u'' = M.union u u')
      (HIdsEq: ids'' = M.add meth ar ids)
      (HCsEq: cs'' = M.union (M.remove meth cs) cs'):
      SubstepComb u'' l ids'' cs''.

  Inductive SubstepFull: UpdatesT -> UnitLabel -> MethsT -> MethsT -> Prop :=
  | SSFIntro
      u l ids cs
      (HSubstepComb: SubstepComb u l ids cs)
      (HNoInternalCalls: M.KeysDisj cs (getDefs m)):
      SubstepFull u l ids cs.

  Inductive StepFull: UpdatesT -> LabelT -> Prop :=
  | SFNil:
      StepFull (M.empty _) emptyMethLabel
  | SFCons:
      forall pu pl,
        StepFull pu pl ->
        forall nu nul nids ncs,
          SubstepFull nu nul nids ncs ->
          CanCombineUL pu nu pl (getLabel nul ncs) ->
          forall u l,
            u = M.union pu nu ->
            l = mergeLabel pl (getLabel nul ncs) ->
            StepFull u l.

End GivenModule.

  
