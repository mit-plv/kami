Require Import Lib.CommonTactics Lib.FMap Lib.Struct.
Require Import Syntax Semantics Refinement.
Require Import String List.

Set Implicit Arguments.

Record LabelTP {A : Type} :=
  { ruleMeth : option A
  ; dms : CallsT
  ; cms : CallsT
  }.

Arguments LabelTP : clear implicits.

Definition LabelT := LabelTP True.
Definition RuleLabelT := LabelTP string.

Definition mapLabelTP {A B : Type} (f : A -> B) (l : LabelTP A)
: LabelTP B :=
  match l with
    | Build_LabelTP rm dms cms => Build_LabelTP (option_map f rm) dms cms
  end.

Definition NotBothRule (rm1 rm2 : option string) : Prop :=
  rm1 = None \/ rm2 = None.

Definition CanCombine (ul1 ul2: RegsT * RuleLabelT) : Prop :=
  MF.Disj (fst ul1) (fst ul2) /\
  NotBothRule (ruleMeth (snd ul1)) (ruleMeth (snd ul2)) /\
  MF.Disj (dms (snd ul1)) (dms (snd ul2)) /\
  MF.Disj (cms (snd ul1)) (cms (snd ul2)).

Definition mergeLabel {A : Type} (l1 l2 : LabelTP A) : LabelTP A := 
  match l1, l2 with
      Build_LabelTP rm1 ds1 cs1, Build_LabelTP rm2 ds2 cs2 =>
      Build_LabelTP (match rm1 with | Some r => Some r | None => rm2 end) 
                    (MF.union ds1 ds2) 
                    (MF.union cs1 cs2)
  end.

Definition equivalent {A : Type} (l1 l2 : LabelTP A)
           (p : LabelTP A -> LabelTP A) :=
  l1 = p l2.

Local Open Scope string.

Inductive UnitStep : Modules -> RegsT -> RegsT -> RuleLabelT -> Type :=
| EmptyStep :
    forall (regInits : list RegInitT)
           (rules : list (Attribute (Action Void)))
           (meths : list DefMethT)
           (oRegs : RegsT),
      MF.InDomain oRegs (namesOf regInits) ->
      UnitStep (Mod regInits rules meths) oRegs (M.empty _)
               (Build_LabelTP None (M.empty _) (M.empty _))
| SingleRule : 
  forall (ruleName : string) (ruleBody : Action (Bit 0))
         (regInits : list RegInitT)
         (rules : list (Attribute (Action Void)))
         (meths : list DefMethT),
    In (ruleName :: ruleBody)%struct rules ->
    forall (oRegs news : RegsT) (calls : CallsT)
           (retV : type (Bit 0)),
      SemAction oRegs (ruleBody type) news calls retV ->
      MF.InDomain oRegs (namesOf regInits) ->
      UnitStep (Mod regInits rules meths) oRegs news
               (Build_LabelTP (Some ruleName) (M.empty _) calls)
| SingleMeth :
    forall (regInits : list RegInitT)
           (rules : list (Attribute (Action Void)))
           (meths : list DefMethT)
           (oRegs : RegsT)
           (calls : CallsT) (news : RegsT) 
           (meth : DefMethT),
      In meth meths ->
      forall (argV : type (arg (objType (attrType meth))))
             (retV : type (ret (objType (attrType meth))))
             (udefs : CallsT),
        SemAction oRegs (objVal (attrType meth) type argV) news calls retV ->
        udefs = M.add meth {|
                        objType := objType (attrType meth);
                        objVal := (argV, retV) |} (M.empty _) ->
        MF.InDomain oRegs (namesOf regInits) ->
        UnitStep (Mod regInits rules meths) oRegs news
                 (Build_LabelTP None udefs calls)
| LeftIntro :
    forall (m1 m2 : Modules)
           (oRegs1 oRegs2 oRegs news : RegsT)
           (l : RuleLabelT),
      MF.InDomain oRegs2 (namesOf (getRegInits m2)) ->
      UnitStep m1 oRegs1 news l ->
      oRegs = MF.union oRegs1 oRegs2 ->
      UnitStep (ConcatMod m1 m2) oRegs news l
| RightIntro :
    forall (m1 m2 : Modules)
           (oRegs1 oRegs2 oRegs news : RegsT)
           (l : RuleLabelT),
      MF.InDomain oRegs1 (namesOf (getRegInits m1)) ->
      UnitStep m2 oRegs2 news l ->
      oRegs = MF.union oRegs1 oRegs2 ->
      UnitStep (ConcatMod m1 m2) oRegs news l.

Inductive UnitSteps (m : Modules) (o : RegsT) : RegsT -> RuleLabelT -> Type :=
| UnitSteps1 : forall {u l}, UnitStep m o u l -> UnitSteps m o u l
| UnitStepsUnion : forall {u1 u2 : RegsT} {l1 l2 : RuleLabelT}, 
                     UnitSteps m o u1 l1 -> UnitSteps m o u2 l2 
                     -> CanCombine (u1, l1) (u2, l2)
                     -> UnitSteps m o (MF.union u1 u2) (mergeLabel l1 l2).

Definition signIsEq :
  forall (l1 l2 : Typed SignT), sumbool (l1 = l2) (l1 <> l2).
Proof.
  intros. destruct l1, l2. 
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

Definition hide {A : Type} (l : LabelTP A) : LabelTP A :=
  match l with
      Build_LabelTP rm ds cs => 
      Build_LabelTP rm (MF.subtractKV signIsEq ds cs)
                    (MF.subtractKV signIsEq cs ds)
  end.

Definition wellHidden {A : Type} (l : LabelTP A) (m : Modules) :=
  match l with
      Build_LabelTP rm ds cs =>
      MF.NotOnDomain ds (getCmsMod m)
      /\ MF.NotOnDomain cs (getDmsMod m)
  end.

Inductive Step (m : Modules) (o u : RegsT) : RuleLabelT -> Type :=
  MkStep : forall {l l': RuleLabelT},
             UnitSteps m o u l ->
             l' = hide l -> wellHidden l' m ->
             Step m o u l'.

Inductive MultiStep (m : Modules) (regs : RegsT) : RegsT -> list RuleLabelT -> Prop :=
| MSNil : MultiStep m regs regs nil
| MSMulti :
    forall regs' labels,
      MultiStep m regs regs' labels ->
      forall l u,
        Step m regs' u l ->
        forall (regs'' : RegsT),
          regs'' = update regs' u ->
          MultiStep m regs regs'' (l :: labels).

Inductive Behavior (m : Modules) : RegsT -> list LabelT -> Prop :=
  MkBehavior :
    forall newRegs labels labels',
      MultiStep m (initRegs (getRegInits m)) newRegs labels ->
      labels' = (List.map (mapLabelTP (fun _ => I)) labels) ->
      Behavior m newRegs labels'.

Definition TraceRefines (mimpl mspec : Modules) (f : LabelT -> LabelT) :=
  forall simp limp,        Behavior mimpl simp         limp ->
  exists (sspec : RegsT),  Behavior mspec sspec (map f limp).

Section Decomposition.
  Variable rulesImp rulesSpec: list string.
  Variable dmsImp dmsSpec: list DefMethT.
  Variable imp spec: Modules.
  Variable stateMap: RegsT -> RegsT.
  Variable ruleMap: string -> string.
  Variable p : (CallsT * CallsT) -> (CallsT * CallsT).

  Definition pMod {A : Type} (f : A -> A) (l : LabelTP A) : LabelTP A
    := match l with
    | Build_LabelTP rm dm cm => let (dm', cm') := p (dm, cm) in
       Build_LabelTP (option_map f rm) dm' cm'
    end.

  Definition pRL := pMod ruleMap.

  Hypothesis pmerge : forall (ds1 ds2 cs1 cs2 : CallsT) (rm1 rm2 : option string)
    , let l1 := Build_LabelTP rm1 ds1 cs1 in 
      let l2 := Build_LabelTP rm2 ds2 cs2 in
       MF.Disj ds1 ds2 -> MF.Disj cs1 cs2
     -> NotBothRule rm1 rm2
     -> mergeLabel (pRL l1) (pRL l2) = pRL (mergeLabel l1 l2).

  Hypothesis phide : forall (l : RuleLabelT), pRL (hide l) = hide (pRL l).

  Hypothesis pwellHidden : forall (l : RuleLabelT), 
   wellHidden (hide l) imp -> wellHidden (pRL (hide l)) spec.

  Variable T : forall {oImp nImp lImp}, UnitStep imp oImp nImp lImp 
             -> (RegsT * RuleLabelT).

  Fixpoint Ts {oImp nImp lImp} (steps : UnitSteps imp oImp nImp lImp)
      : RegsT * RuleLabelT
      := match steps with
    | UnitSteps1 _ _ step => T step
    | UnitStepsUnion _ _ _ _ step1 step2 canCombine => 
      let (u1, l1) := Ts step1 in
      let (u2, l2) := Ts step2 in
      (MF.union u1 u2, mergeLabel l1 l2)
    end.

  Let Ts' {oImp nImp lImp} (step : Step imp oImp nImp lImp)
      : RegsT * RuleLabelT
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
      /\ equivalent lSpec lImp pRL)
      * UnitStep spec oSpec nSpec lSpec
     end.

  Hypothesis specShouldCombine : forall {oImp} 
  , (exists ruleLabel, Behavior imp oImp ruleLabel)
  -> forall {nImp1 lImp1} (step1 : UnitStep imp oImp nImp1 lImp1)
      {nImp2 lImp2} (step2 : UnitStep imp oImp nImp2 lImp2)
  , CanCombine (nImp1, lImp1) (nImp2, lImp2)
  -> CanCombine (T step1) (T step2).

  Lemma pBeforeAfter : forall (l : RuleLabelT),
    pMod id (mapLabelTP (fun _ : string => I) l) =
     mapLabelTP (fun _ : string => I) (pRL l).
  Proof. intros. unfold pRL, pMod.
  destruct l. simpl.
  destruct (p (dms0, cms0)). simpl.
  destruct ruleMeth0; simpl; unfold id; reflexivity.
  Qed.

  Lemma canCombineLeft :
    forall {t u1 u2 l1 l2},
      CanCombine t (MF.union u1 u2, mergeLabel l1 l2) ->
      CanCombine t (u1, l1).
  Proof. 
    intros.
    destruct l1 as [rm1 ds1 cs1].
    destruct l2 as [rm2 ds2 cs2].
    unfold CanCombine in H; dest; simpl in *.
    constructor; try (eapply MF.Disj_union_1; eassumption).
    unfold NotBothRule in *.
    destruct rm1.
    - simpl; destruct H0; [|discriminate].
      repeat split.
      + left; auto.
      + eapply MF.Disj_union_1; eauto.
      + eapply MF.Disj_union_1; eauto.
    - repeat split.
      + right; auto.
      + eapply MF.Disj_union_1; eauto.
      + eapply MF.Disj_union_1; eauto.
  Qed.

  Lemma canCombineRight :
    forall {t u1 u2 l1 l2},
      CanCombine t (MF.union u1 u2, mergeLabel l1 l2) ->
      CanCombine t (u2, l2).
  Proof.
    intros.
    destruct l1 as [rm1 ds1 cs1].
    destruct l2 as [rm2 ds2 cs2].
    unfold CanCombine in H; dest; simpl in *.
    constructor; try (eapply MF.Disj_union_2; eassumption).
    unfold NotBothRule in *.
    destruct rm1.
    - simpl; destruct H0; [|discriminate].
      repeat split.
      + left; auto.
      + eapply MF.Disj_union_2; eauto.
      + eapply MF.Disj_union_2; eauto.
    - simpl; destruct H0.
      + repeat split.
        * left; auto.
        * eapply MF.Disj_union_2; eauto.
        * eapply MF.Disj_union_2; eauto.
      + repeat split.
        * right; auto.
        * eapply MF.Disj_union_2; eauto.
        * eapply MF.Disj_union_2; eauto.
  Qed.

  Lemma canCombineMerge : forall {t u1 u2 l1 l2},
    CanCombine t (u1, l1)
  -> CanCombine t (u2, l2)
  -> CanCombine t (MF.union u1 u2, mergeLabel l1 l2).
  Proof.
    admit.
    (* intros. destruct t as [uL [rmL csL dsL]].  *)
    (* destruct (mergeLabel l1 l2) as [rm1 cs ds] eqn:labeleqn. *)
    (* inversion H; inversion H0; inversion labeleqn; subst. *)
    (* econstructor. apply MF.Disj_union; assumption. *)
    (* apply MF.Disj_union; assumption. *)
    (* apply MF.Disj_union; assumption. *)
    (* unfold NotBothRule in *; destruct rmL, rm2, rm4; intuition. *)
  Qed.  

  Lemma canCombineSym : forall {t1 t2},
    CanCombine t1 t2 -> CanCombine t2 t1.
  Proof.
    admit.
   (* intros t1 t2 H; *)
   (* inversion H; clear H; subst;  *)
   (* constructor; eauto using MF.Disj_comm. *)
   (* unfold NotBothRule in *. *)
   (* destruct rm1, rm2; intuition. *)
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
         /\ equivalent lSpec lImp pRL)
        * UnitSteps spec oSpec nSpec lSpec.
  Proof.
    admit.
  (*   intros. *)
  (*   induction steps; intros. *)
  (*   - pose proof (consistentSubstepMap H u0). simpl in *. *)
  (*     destruct (T u0) as [uSpec lSpec]. *)
  (*     intuition. constructor. assumption. *)
  (* - pose proof (specShouldCombines H steps1 steps2 c). *)
  (*   simpl in *. *)
  (*   destruct (Ts steps1) as [uSpec1 lSpec1]. *)
  (*   destruct (Ts steps2) as [uSpec2 lSpec2]. *)
  (*   intuition.  *)
  (*   CommonTactics.inv c. CommonTactics.inv H0. *)
  (*   apply stateMapModular; assumption. *)
  (*   unfold equivalent in *. subst. *)
  (*   CommonTactics.inv c. *)
  (*   apply pmerge; assumption. *)
  (*   apply UnitStepsUnion. assumption. assumption. *)
  (*   unfold equivalent in *. *)
  (*   assumption. *)
  Qed.
  
  Lemma consistentStepMap : forall oImp lImp nImp
    , (exists ruleLabel, Behavior imp oImp ruleLabel)
      -> forall (step : Step imp oImp nImp lImp)
      , let (nSpec, lSpec) := Ts' step in
        let oSpec := stateMap oImp in
        (update oSpec nSpec = stateMap (update oImp nImp))
        * Step spec oSpec nSpec (pRL lImp).
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

  Theorem decomposition : TraceRefines imp spec (pMod id).
  Proof.
    unfold TraceRefines. intros.
    exists (stateMap simp).
    pose proof H.
    inversion H0; clear H0; subst.
    econstructor.
    Focus 2. instantiate (1 := map pRL labels).
    repeat rewrite map_map. apply map_ext.
    intros. apply pBeforeAfter.
    induction H1.
    - rewrite <- stateMapBeginsWell. apply MSNil.
    - assert (Behavior imp regs' (map (mapLabelTP (fun _ : string => I)) labels)).
      econstructor. eassumption. reflexivity.
      pose proof (consistentStepMap (ex_intro _ _ H2) X).
      destruct (Ts' X) eqn:Ts'X.
      destruct X0 as [HT1 HT2].
      apply MSMulti with (regs' := stateMap regs') (u := r).
      apply IHMultiStep. assumption.
      assumption.
      rewrite H0. rewrite <- HT1. reflexivity.
  Qed.

End Decomposition.