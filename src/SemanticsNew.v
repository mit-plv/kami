Require Import Lib.FMap Lib.Struct.
Require Import Syntax Semantics Refinement.

Require Import String List.

Definition bothNotRule (rm1 rm2 : bool) : Prop :=
  rm1 = false \/ rm2 = false.

Inductive CanCombine : (RegsT * LabelT) -> (RegsT * LabelT) -> Prop :=
  MkCanCombine : forall u1 rm1 ds1 cs1 u2 rm2 ds2 cs2,
    MF.Disj u1 u2 -> MF.Disj ds1 ds2 -> MF.Disj cs1 cs2 -> bothNotRule rm1 rm2
   -> CanCombine (u1, (rm1, ds1, cs1)) (u2, (rm2, ds2, cs2)).

Definition mergeLabel (l1 l2 : LabelT) : LabelT := match l1, l2 with
  (rm1, ds1, cs1), (rm2, ds2, cs2) =>
    (orb rm1 rm2, MF.union ds1 ds2, MF.union cs1 cs2)
  end.

Definition equivalent (l1 l2 : LabelT) (p : LabelT -> LabelT) :=
   l1 = p l2.

Local Open Scope string.

Inductive UnitStep : Modules -> RegsT -> RegsT -> LabelT -> Type :=
| EmptyStep : forall
   (regInits : list RegInitT)
   (rules : list (Attribute (Action Void)))
   (meths : list DefMethT)
   (oRegs : RegsT)
   (ruleMeth : bool),
   MF.InDomain oRegs (namesOf regInits)
   -> UnitStep (Mod regInits rules meths) oRegs (M.empty _)
        (ruleMeth, M.empty _, M.empty _)
| SingleRule : 
  forall (ruleName : string) (ruleBody : Action (Bit 0))
   (regInits : list RegInitT)
   (rules : list (Attribute (Action Void)))
   (meths : list DefMethT)
  , In (ruleName :: ruleBody)%struct rules ->
  forall (oRegs news : RegsT) (calls : CallsT)
  (retV : type (Bit 0)),
  SemAction oRegs (ruleBody type) news calls retV ->
   MF.InDomain oRegs (namesOf regInits) ->
  UnitStep (Mod regInits rules meths) oRegs news
       (true, M.empty _, calls)
| SingleMeth : forall 
   (regInits : list RegInitT)
   (rules : list (Attribute (Action Void)))
   (meths : list DefMethT)
   (oRegs : RegsT)
   (calls : CallsT) (news : RegsT) 
   (meth : DefMethT)
   (argV : type (arg (objType (attrType meth))))
   (retV : type (ret (objType (attrType meth))))
   (udefs : CallsT),
   SemAction oRegs (objVal (attrType meth) type argV) news calls retV ->
   udefs = M.add meth {|
                 objType := objType (attrType meth);
                 objVal := (argV, retV) |} (M.empty _) ->
   MF.InDomain oRegs (namesOf regInits) ->
   UnitStep (Mod regInits rules meths) oRegs news
      (false, udefs, calls)
| LeftIntro : forall (m1 m2 : Modules)
    (oRegs1 oRegs2 oRegs news : RegsT)
    (l : LabelT),
    MF.InDomain oRegs2 (namesOf (getRegInits m2)) ->
    UnitStep m1 oRegs1 news l ->
    oRegs = MF.union oRegs1 oRegs2 ->
    UnitStep (ConcatMod m1 m2) oRegs news l
| RightIntro : forall (m1 m2 : Modules)
    (oRegs1 oRegs2 oRegs news : RegsT)
    (l : LabelT),
    MF.InDomain oRegs1 (namesOf (getRegInits m1)) ->
    UnitStep m2 oRegs2 news l ->
    oRegs = MF.union oRegs1 oRegs2 ->
    UnitStep (ConcatMod m1 m2) oRegs news l.

Inductive UnitSteps (m : Modules) (o : RegsT) : RegsT -> LabelT -> Type :=
 | UnitSteps1 : forall {u l}, UnitStep m o u l -> UnitSteps m o u l
 | UnitStepsUnion : forall {u1 u2 : RegsT} {l1 l2 : LabelT}, 
    UnitSteps m o u1 l1 -> UnitSteps m o u2 l2 
    -> CanCombine (u1, l1) (u2, l2)
    -> UnitSteps m o (MF.union u1 u2) (mergeLabel l1 l2).

Definition subtractKV {A : Type}
  (deceqA : forall x y : A, sumbool (x = y) (x <> y))
  (m1 m2 : M.t A) : M.t A :=
    M.fold (fun k2 v2 m1' => match M.find k2 m1' with
    | None => m1'
    | Some v1 => if deceqA v1 v2 then 
       M.remove k2 m1' else m1' 
    end) m2 m1.

Definition signIsEq : forall (l1 l2 : Typed SignT),
  sumbool (l1 = l2) (l1 <> l2).
Proof. intros. destruct l1, l2. 
destruct (SignatureT_dec objType objType0).
- induction e. destruct objType, objVal, objVal0.
  destruct (isEq arg t t1). induction e.
  destruct (isEq ret t0 t2). induction e. left. reflexivity.
  right. unfold not. intros. apply typed_eq in H.
  inversion H. apply n in H1. assumption.
  right. unfold not. intros. apply typed_eq in H.
  inversion H. apply n in H1. assumption.
- right. unfold not. intros. inversion H. apply n in H1.
  assumption.
Qed.

Definition hide (l : LabelT) : LabelT := match l with
  (rm, ds, cs) => (rm, subtractKV signIsEq ds cs, subtractKV signIsEq cs ds)
  end.

Definition wellHidden (l : LabelT) (m : Modules) := match l with
  (rm, ds, cs) =>
      MF.NotOnDomain ds (getCmsMod m)
    /\ MF.NotOnDomain cs (getDmsMod m)
  end.

Inductive Step (m : Modules) (o u : RegsT) : LabelT -> Type :=
  MkStep : forall {l l': LabelT}, UnitSteps m o u l
   -> l' = hide l -> wellHidden l' m 
   -> Step m o u l'.

Inductive MultiStep (m : Modules) (regs : RegsT) : RegsT -> list LabelT -> Prop :=
| MSNil : MultiStep m regs regs nil
| MSMulti : forall regs' labels, MultiStep m regs regs' labels
   -> forall l u, Step m regs' u l
   -> forall (regs'' : RegsT), regs'' = update regs' u
   -> MultiStep m regs regs'' (l :: labels).

Inductive Behavior (m : Modules) : RegsT -> list LabelT -> Prop :=
 MkBehavior : forall newRegs labels
   , MultiStep m (initRegs (getRegInits m)) newRegs labels
   -> Behavior m newRegs labels.

Definition TraceRefines (mimpl mspec : Modules) (f : LabelT -> LabelT)
  := forall simp limp,        Behavior mimpl simp         limp ->
     exists (sspec : RegsT),  Behavior mspec sspec (map f limp).

Set Implicit Arguments.

Ltac destruct_match := 
match goal with
| [ |- context[ match ?e with | _ => _ end ]] => 
   let x := fresh "eqn" in destruct e eqn:x
end.

Lemma union_disj_reorder {A : Type} : forall (m m1 m2 : M.t A),
  MF.Disj m1 m2 -> MF.union m2 (MF.union m1 m)
                = MF.union m1 (MF.union m2 m).
Proof.
intros. apply M.leibniz. unfold M.Equal. intros k.
repeat rewrite MF.find_union.
destruct (H k) as [H0 | H0];
apply MF.F.P.F.not_find_in_iff in H0;
repeat rewrite H0; destruct_match; reflexivity.
Qed.

Section Decomposition.
  Variable rulesImp rulesSpec: list string.
  Variable dmsImp dmsSpec: list DefMethT.
  Variable imp spec: Modules.
  Variable stateMap: RegsT -> RegsT.
  Variable ruleMap: string -> string.
  Variable p : LabelT -> LabelT.

  Hypothesis pmerge : forall (ds1 ds2 cs1 cs2 : CallsT) (rm1 rm2 : bool)
    , let l1 := (rm1, ds1, cs1) in let l2 := (rm2, ds2, cs2) in
       MF.Disj ds1 ds2 -> MF.Disj cs1 cs2
     -> bothNotRule rm1 rm2
     -> mergeLabel (p l1) (p l2) = p (mergeLabel l1 l2).

  Hypothesis phide : forall (l : LabelT), p (hide l) = hide (p l).

  Hypothesis pwellHidden : forall (l : LabelT), 
   wellHidden (hide l) imp -> wellHidden (p (hide l)) spec.

  Variable T : forall {oImp nImp lImp}, UnitStep imp oImp nImp lImp -> (RegsT * LabelT).

  Fixpoint Ts {oImp nImp lImp} (steps : UnitSteps imp oImp nImp lImp)
      : RegsT * LabelT
      := match steps with
    | UnitSteps1 _ _ step => T step
    | UnitStepsUnion _ _ _ _ step1 step2 canCombine => 
      let (u1, l1) := Ts step1 in
      let (u2, l2) := Ts step2 in
      (MF.union u1 u2, mergeLabel l1 l2)
    end.

  Let Ts' {oImp nImp lImp} (step : Step imp oImp nImp lImp)
      : RegsT * LabelT
      := match step with
    | MkStep _ _ steps _ _  => Ts steps
    end.

  Hypothesis stateMapBeginsWell :
    stateMap (initRegs (getRegInits imp)) = initRegs (getRegInits spec).

  Hypothesis stateMapModular : forall (oImp u1 u2 uSpec1 uSpec2 : RegsT),
    MF.Disj u1 u2 -> MF.Disj uSpec1 uSpec2
  -> update (stateMap oImp) uSpec1 = stateMap (update oImp u1)
  -> update (stateMap oImp) uSpec2 = stateMap (update oImp u2)
  -> update (stateMap oImp) (MF.union uSpec1 uSpec2) 
  = stateMap (update oImp (MF.union u1 u2)).

  Hypothesis consistentSubstepMap : forall {oImp lImp nImp}
   , (exists ruleLabel, Behavior imp oImp ruleLabel)
   -> forall (step : UnitStep imp oImp nImp lImp)
   , match T step with (nSpec, lSpec) =>
      let oSpec := stateMap oImp in
        (update oSpec nSpec = stateMap (update oImp nImp)
      /\ equivalent lSpec lImp p)
      * UnitStep spec oSpec nSpec lSpec
     end.

  Hypothesis specShouldCombine : forall {oImp} 
  , (exists ruleLabel, Behavior imp oImp ruleLabel)
  -> forall {nImp1 lImp1} (step1 : UnitStep imp oImp nImp1 lImp1)
      {nImp2 lImp2} (step2 : UnitStep imp oImp nImp2 lImp2)
  , CanCombine (nImp1, lImp1) (nImp2, lImp2)
  -> CanCombine (T step1) (T step2).

  Lemma canCombineLeft : forall {t u1 u2 l1 l2},
    CanCombine t (MF.union u1 u2, mergeLabel l1 l2)
  -> CanCombine t (u1, l1).
  Proof. 
    intros.
    destruct l1 as [[rm1 ds1] cs1].
    destruct l2 as [[rm2 ds2] cs2].
    inversion H; clear H; subst. 
    constructor; try (eapply MF.Disj_union_1; eassumption).
    unfold bothNotRule in *. destruct rm1; intuition.
  Qed.

  Lemma canCombineRight : forall {t u1 u2 l1 l2},
    CanCombine t (MF.union u1 u2, mergeLabel l1 l2)
  -> CanCombine t (u2, l2).
  Proof.
    intros.
    destruct l1 as [[rm1 ds1] cs1].
    destruct l2 as [[rm2 ds2] cs2].
    inversion H; clear H; subst. 
    constructor; try (eapply MF.Disj_union_2; eassumption).
    unfold bothNotRule in *. destruct rm1; intuition.
  Qed.

  Lemma canCombineMerge : forall {t u1 u2 l1 l2},
    CanCombine t (u1, l1)
  -> CanCombine t (u2, l2)
  -> CanCombine t (MF.union u1 u2, mergeLabel l1 l2).
  Proof. 
    intros. destruct t as [uL [[rmL csL] dsL]]. 
    destruct (mergeLabel l1 l2) as [[rm1 cs] ds] eqn:labeleqn.
    inversion H; inversion H0; inversion labeleqn; subst.
    econstructor. apply MF.Disj_union; assumption.
    apply MF.Disj_union; assumption.
    apply MF.Disj_union; assumption.
    unfold bothNotRule in *; destruct rmL, rm2, rm4; intuition.
  Qed.  

  Lemma canCombineSym : forall {t1 t2},
    CanCombine t1 t2 -> CanCombine t2 t1.
  Proof. 
   intros t1 t2 H;
   inversion H; clear H; subst; 
   constructor; eauto using MF.Disj_comm.
   unfold bothNotRule in *.
   destruct rm1, rm2; intuition.
  Qed. 

  Lemma specShouldCombines : forall {oImp} 
  , (exists ruleLabel, Behavior imp oImp ruleLabel)
  -> forall {nImp1 lImp1} (step1 : UnitSteps imp oImp nImp1 lImp1)
      {nImp2 lImp2} (step2 : UnitSteps imp oImp nImp2 lImp2)
  , CanCombine (nImp1, lImp1) (nImp2, lImp2)
  -> CanCombine (Ts step1) (Ts step2).
  Proof. 
    intros oImp H nImp1 lImp1 US1. induction US1.
    - intros nImp2 lImp2 US2. induction US2.
      + apply specShouldCombine; assumption.
      + intros.
        simpl in IHUS2_1, IHUS2_2.
        pose proof (IHUS2_1 (canCombineLeft H0)) as H21.
        pose proof (IHUS2_2 (canCombineRight H0)) as H22.
        simpl. destruct (Ts US2_1). destruct (Ts US2_2).
        apply canCombineMerge; assumption.
    - simpl in *. intros. apply canCombineSym.
      destruct (Ts US1_1). destruct (Ts US1_2).
      apply canCombineMerge; apply canCombineSym;
      [apply IHUS1_1 | apply IHUS1_2]; try assumption;
      apply canCombineSym in H0;
      apply canCombineSym. 
      eapply canCombineLeft; eassumption.
      eapply canCombineRight; eassumption.    
  Qed.
  
Require CommonTactics.

  Lemma consistentUnitStepsMap : forall oImp lImp nImp
    , (exists ruleLabel, Behavior imp oImp ruleLabel)
      -> forall (steps : UnitSteps imp oImp nImp lImp)
      , let (nSpec, lSpec) := Ts steps in
        let oSpec := stateMap oImp in
        (update oSpec nSpec = stateMap (update oImp nImp)
         /\ equivalent lSpec lImp p)
        * UnitSteps spec oSpec nSpec lSpec.
  Proof.
    intros.
    induction steps; intros.
    - pose proof (consistentSubstepMap H u0). simpl in *.
      destruct (T u0) as [uSpec lSpec].
      intuition. constructor. assumption.
  - pose proof (specShouldCombines H steps1 steps2 c).
    simpl in *.
    destruct (Ts steps1) as [uSpec1 lSpec1].
    destruct (Ts steps2) as [uSpec2 lSpec2].
    intuition. 
    CommonTactics.inv c. CommonTactics.inv H0.
    apply stateMapModular; assumption.
    unfold equivalent in *. subst.
    CommonTactics.inv c.
    apply pmerge; assumption.
    apply UnitStepsUnion. assumption. assumption.
    unfold equivalent in *.
    assumption.
    Qed.
  
  Lemma consistentStepMap : forall oImp lImp nImp
    , (exists ruleLabel, Behavior imp oImp ruleLabel)
      -> forall (step : Step imp oImp nImp lImp)
      , let (nSpec, lSpec) := Ts' step in
        let oSpec := stateMap oImp in
        (update oSpec nSpec = stateMap (update oImp nImp))
        * Step spec oSpec nSpec (p lImp).
  Proof. 
    intros.
    destruct step eqn:stepeqn.
    pose proof (consistentUnitStepsMap H u). simpl in *.
    destruct (Ts u) as [nSpec lSpec]. 
    intuition.  
    econstructor. eassumption.
    unfold equivalent in *. rewrite e.
    rewrite H1. apply phide.
    unfold equivalent in *. subst.
    apply (pwellHidden _ w).
  Qed. 

  Theorem decomposition : TraceRefines imp spec p.
  Proof.
    unfold TraceRefines. intros.
    exists (stateMap simp).
    pose proof H.
    constructor. 
    inversion H0; clear H0; subst.
    induction H1.
    - rewrite <- stateMapBeginsWell. apply MSNil.
    - assert (Behavior imp regs' labels).
      constructor. assumption.
      pose proof (consistentStepMap (ex_intro _ labels H2) X).
      destruct (Ts' X) eqn:Ts'X.
      destruct X0 as [HT1 HT2].
      apply MSMulti with (regs' := stateMap regs') (u := r).
      apply IHMultiStep. assumption.
      assumption.
      rewrite H0. rewrite <- HT1. reflexivity.
  Qed.

End Decomposition.