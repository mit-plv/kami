Require Import Bool List String.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.FMap.
Require Import Syntax.
Require Export SemanticsExprAction Semantics.

Set Implicit Arguments.

Section GivenModule.
  Variable m: Modules.
  Variable oldRegs: RegsT.

  Definition UpdatesT := RegsT.

  Inductive SemActionSmall:
    forall k, ActionT type k -> RegsT -> MethsT -> type k -> Prop :=
  | SASMCallExt
      meth s (marg: Expr type (SyntaxKind (arg s)))
      (mret: type (ret s))
      retK (fret: type retK)
      (cont: type (ret s) -> ActionT type retK)
      (HNotIn: ~ In meth (getDefs m))
      newRegs (calls: MethsT) acalls
      (HAcalls: acalls = M.add meth (existT _ _ (evalExpr marg, mret)) calls)
      (HSemAction: SemActionSmall (cont mret) newRegs calls fret):
      SemActionSmall (MCall meth s marg cont) newRegs acalls fret
  | SASMCallInt
      meth methBody
      (marg: Expr type (SyntaxKind (arg (projT1 methBody))))
      (mret: type (ret (projT1 methBody)))
      retK (fret: type retK)
      (cont: type (ret (projT1 methBody)) -> ActionT type retK)
      (HIn: In (meth :: methBody)%struct (getDefsBodies m))
      cnewRegs ccalls
      (HCallee: SemActionSmall ((projT2 methBody) type (evalExpr marg))
                               cnewRegs ccalls mret)
      newRegs (calls: MethsT)
      (HSemAction: SemActionSmall (cont mret) newRegs calls fret):
      SemActionSmall (MCall meth (projT1 methBody) marg cont)
                     (M.union cnewRegs newRegs) (M.union ccalls calls) fret
  | SASLet
      k (e: Expr type k) retK (fret: type retK)
      (cont: fullType type k -> ActionT type retK) newRegs calls
      (HSemActionSmall: SemActionSmall (cont (evalExpr e)) newRegs calls fret):
      SemActionSmall (Let_ e cont) newRegs calls fret
  | SASReadReg
      (r: string) regT (regV: fullType type regT)
      retK (fret: type retK) (cont: fullType type regT -> ActionT type retK)
      newRegs calls
      (HRegVal: M.find r oldRegs = Some (existT _ regT regV))
      (HSemActionSmall: SemActionSmall (cont regV) newRegs calls fret):
      SemActionSmall (ReadReg r _ cont) newRegs calls fret
  | SASWriteReg
      (r: string) k
      (e: Expr type k)
      retK (fret: type retK)
      (cont: ActionT type retK) newRegs calls anewRegs
      (HANewRegs: anewRegs = M.add r (existT _ _ (evalExpr e)) newRegs)
      (HSemActionSmall: SemActionSmall cont newRegs calls fret):
      SemActionSmall (WriteReg r e cont) anewRegs calls fret
  | SASIfElseTrue
      (p: Expr type (SyntaxKind Bool)) k1
      (a: ActionT type k1)
      (a': ActionT type k1)
      (r1: type k1)
      k2 (cont: type k1 -> ActionT type k2)
      newRegs1 newRegs2 calls1 calls2 (r2: type k2)
      (HTrue: evalExpr p = true)
      (HAction: SemActionSmall a newRegs1 calls1 r1)
      (HSemActionSmall: SemActionSmall (cont r1) newRegs2 calls2 r2)
      unewRegs ucalls
      (HUNewRegs: unewRegs = M.union newRegs1 newRegs2)
      (HUCalls: ucalls = M.union calls1 calls2):
      SemActionSmall (IfElse p a a' cont) unewRegs ucalls r2
  | SASIfElseFalse
      (p: Expr type (SyntaxKind Bool)) k1
      (a: ActionT type k1)
      (a': ActionT type k1)
      (r1: type k1)
      k2 (cont: type k1 -> ActionT type k2)
      newRegs1 newRegs2 calls1 calls2 (r2: type k2)
      (HFalse: evalExpr p = false)
      (HAction: SemActionSmall a' newRegs1 calls1 r1)
      (HSemActionSmall: SemActionSmall (cont r1) newRegs2 calls2 r2)
      unewRegs ucalls
      (HUNewRegs: unewRegs = M.union newRegs1 newRegs2)
      (HUCalls: ucalls = M.union calls1 calls2):
      SemActionSmall (IfElse p a a' cont) unewRegs ucalls r2
  | SASAssertTrue
      (p: Expr type (SyntaxKind Bool)) k2
      (cont: ActionT type k2) newRegs2 calls2 (r2: type k2)
      (HTrue: evalExpr p = true)
      (HSemActionSmall: SemActionSmall cont newRegs2 calls2 r2):
      SemActionSmall (Assert_ p cont) newRegs2 calls2 r2
  | SASReturn
      k (e: Expr type (SyntaxKind k)) evale
      (HEvalE: evale = evalExpr e):
      SemActionSmall (Return e) (M.empty _) (M.empty _) evale.

  Theorem inversionSemActionSmall
          k a news calls retC
          (evalA: @SemActionSmall k a news calls retC):
    match a with
    | MCall meth s e c =>
      (In meth (getDefs m) /\
       exists methBody mret cnewRegs ccalls nnewRegs ncalls
              (Hsig: s = projT1 methBody),
         In (meth :: methBody)%struct (getDefsBodies m) /\
         SemActionSmall ((projT2 methBody) type
                                           match Hsig with
                                             eq_refl => (evalExpr e)
                                           end) cnewRegs ccalls mret /\
         SemActionSmall (c (match eq_sym Hsig with eq_refl => mret end)) nnewRegs ncalls retC /\
         news = M.union cnewRegs nnewRegs /\
         calls = M.union ccalls ncalls) \/
      (~ In meth (getDefs m) /\
       exists mret pcalls,
         SemActionSmall (c mret) news pcalls retC /\
         calls = M.add meth (existT _ _ (evalExpr e, mret)) pcalls)
    | Let_ _ e cont =>
      SemActionSmall (cont (evalExpr e)) news calls retC
    | ReadReg r k c =>
      exists rv,
      M.find r oldRegs = Some (existT _ k rv) /\
      SemActionSmall (c rv) news calls retC
    | WriteReg r _ e a =>
      exists pnews,
      SemActionSmall a pnews calls retC /\
      news = M.add r (existT _ _ (evalExpr e)) pnews
    | IfElse p _ aT aF c =>
      exists news1 calls1 news2 calls2 r1,
      match evalExpr p with
      | true =>
        SemActionSmall aT news1 calls1 r1 /\
        SemActionSmall (c r1) news2 calls2 retC /\
        news = M.union news1 news2 /\
        calls = M.union calls1 calls2
      | false =>
        SemActionSmall aF news1 calls1 r1 /\
        SemActionSmall (c r1) news2 calls2 retC /\
        news = M.union news1 news2 /\
        calls = M.union calls1 calls2
      end
    | Assert_ e c =>
      SemActionSmall c news calls retC /\
      evalExpr e = true
    | Return e =>
      retC = evalExpr e /\
      news = M.empty _ /\
      calls = M.empty _
    end.
  Proof.
    destruct evalA; eauto; repeat eexists.
    - right; repeat eexists; eauto.
    - left; split.
      + unfold getDefs, namesOf in *.
        replace meth with (attrName (meth :: methBody)%struct) by reflexivity.
        apply in_map; auto.
      + repeat eexists; eauto.
        * instantiate (1:= mret).
          instantiate (1:= eq_refl).
          simpl; auto.
        * simpl; auto.
    - destruct (evalExpr p); eauto; try discriminate.
    - destruct (evalExpr p); eauto; try discriminate.
  Qed.

  Inductive SubstepSmall: UpdatesT -> LabelT -> Prop :=
  | SSSEmptyRule:
      SubstepSmall (M.empty _) emptyRuleLabel
  | SSSEmptyMeth:
      SubstepSmall (M.empty _) emptyMethLabel
  | SSSRule:
      forall k (a: Action Void)
             (HInRules: List.In {| attrName := k; attrType := a |} (getRules m))
             u cs (HAction: SemActionSmall (a type) u cs WO),
        SubstepSmall u {| annot := Some (Some k);
                          defs := M.empty _;
                          calls := cs |}
  | SSSMeth:
      forall (f: DefMethT)
             (HIn: In f (getDefsBodies m))
             (HNotIn: ~ In (attrName f) (getCalls m))
             u cs argV retV
             (HAction: SemActionSmall ((projT2 (attrType f)) type argV) u cs retV),
        SubstepSmall u {| annot := None;
                          defs := M.add (attrName f) (existT _ _ (argV, retV)) (M.empty _);
                          calls := cs |}.

  Inductive SubstepsSmall: UpdatesT -> LabelT -> Prop :=
  | SSSNil:
      SubstepsSmall (M.empty _) emptyMethLabel
  | SSSCons:
      forall pu pl,
        SubstepsSmall pu pl ->
        forall nu nl,
          CanCombineUL pu nu pl nl ->
          SubstepSmall nu nl ->
          SubstepsSmall (M.union pu nu) (mergeLabel nl pl).

  Inductive StepSmall: UpdatesT -> LabelT -> Prop :=
  | StepSmallIntro: forall u l (HSubSteps: SubstepsSmall u l),
      StepSmall u l.

End GivenModule.

Ltac invertActionSmall H := apply inversionSemActionSmall in H; simpl in H; dest; try subst.
Ltac invertActionSmallFirst :=
  match goal with
  | [H: SemActionSmall _ _ _ _ _ _ |- _] => invertActionSmall H
  end.
Ltac invertActionSmallRep :=
  repeat
    match goal with
    | [H: SemActionSmall _ _ _ _ _ _ |- _] => invertActionSmall H
    | [H: if ?c
          then
            SemActionSmall _ _ _ _ _ _ /\ _ /\ _ /\ _
          else
            SemActionSmall _ _ _ _ _ _ /\ _ /\ _ /\ _ |- _] =>
      let ic := fresh "ic" in
      (remember c as ic; destruct ic; dest; subst)
    end.

Section Consistency.

  Variable m: Modules.

  Lemma semActionSmall_calls:
    forall o {retK} (a: ActionT type retK) u cs retv,
      SemActionSmall m o a u cs retv ->
      M.KeysDisj cs (getDefs m).
  Proof.
    induction 1; simpl; intros; subst; auto.
    - apply M.KeysDisj_add; auto.
    - apply M.KeysDisj_union; auto.
    - apply M.KeysDisj_union; auto.
    - apply M.KeysDisj_union; auto.
    - apply M.KeysDisj_empty.
  Qed.

  Lemma substepSmall_calls:
    forall o u l,
      SubstepSmall m o u l ->
      M.KeysDisj (calls l) (getDefs m).
  Proof.
    induction 1; simpl; intros.
    - apply M.KeysDisj_empty.
    - apply M.KeysDisj_empty.
    - eapply semActionSmall_calls; exact HAction.
    - eapply semActionSmall_calls; exact HAction.
  Qed.

  Lemma substepsSmall_calls:
    forall o u l,
      SubstepsSmall m o u l ->
      M.KeysDisj (calls l) (getDefs m).
  Proof.
    induction 1; simpl; intros.
    - apply M.KeysDisj_empty.
    - apply substepSmall_calls in H1.
      destruct nl, pl; simpl in *.
      apply M.KeysDisj_union; auto.
  Qed.

  Lemma stepSmall_calls:
    forall o u l,
      StepSmall m o u l ->
      M.KeysDisj (calls l) (getDefs m).
  Proof. induction 1; eapply substepsSmall_calls; eauto. Qed.

  Lemma semActionSmall_implies_substepsInd_meth:
    forall o (f: DefMethT) u cs argV retV,
      SemActionSmall m o (projT2 (attrType f) type argV) u cs retV ->
      In f (getDefsBodies m) ->
      exists ol,
        {| annot := None;
           defs := M.add
                     f
                     (existT SignT (projT1 (attrType f)) (argV, retV))
                     (M.empty (sigT SignT));
           calls := cs |} = hide ol /\
        SubstepsInd m o u ol.
  Proof.
    admit.
  Qed.

  Lemma semActionSmall_implies_substepsInd_rule:
    forall o k (a: Action Void) u cs,
      SemActionSmall m o (a type) u cs WO ->
      In (k :: a)%struct (getRules m) ->
      exists ol,
        {| annot := Some (Some k);
           defs := M.empty (sigT SignT);
           calls := cs |} = hide ol /\
        SubstepsInd m o u ol.
  Proof.
    admit.
  Qed.
  
  Lemma substepSmall_implies_substepsInd:
    forall o u l,
      SubstepSmall m o u l ->
      wellHidden m l /\
      exists ol, l = hide ol /\ SubstepsInd m o u ol.
  Proof.
    induction 1.
    - repeat split.
      + apply M.KeysDisj_empty.
      + apply M.KeysDisj_empty.
      + exists emptyRuleLabel; repeat split; auto.
        eapply SubstepsCons.
        * apply SubstepsNil.
        * apply EmptyRule.
        * repeat split; auto.
        * meq.
        * reflexivity.
    - repeat split.
      + apply M.KeysDisj_empty.
      + apply M.KeysDisj_empty.
      + exists emptyMethLabel; repeat split; auto.
        constructor.
    - repeat split; simpl.
      + apply M.KeysDisj_empty.
      + simpl; eapply semActionSmall_calls; eauto.
        exact HAction.
      + pose proof (semActionSmall_implies_substepsInd_rule _ _ HAction HInRules).
        destruct H as [ol ?]; dest.
        exists ol; repeat split; auto.
    - repeat split; simpl.
      + simpl; apply M.KeysDisj_add; auto.
        apply M.KeysDisj_empty.
      + simpl; eapply semActionSmall_calls; eauto.
      + pose proof (semActionSmall_implies_substepsInd_meth _ _ HAction HIn).
        destruct H as [ol ?]; dest.
        exists ol; repeat split; auto.
  Qed.

  Lemma substepsSmall_implies_substepsInd:
    forall o u l,
      SubstepsSmall m o u l ->
      wellHidden m l /\
      exists ol, l = hide ol /\ SubstepsInd m o u ol.
  Proof.
    induction 1;
      [repeat split; try apply M.KeysDisj_empty;
       exists emptyMethLabel; repeat split; try (constructor; auto; fail)|].

    clear H.
    apply substepSmall_implies_substepsInd in H1.
    destruct H1 as [? [sol ?]], IHSubstepsSmall as [? [pol ?]]; dest; subst.

    split.
    - admit.
    - exists (mergeLabel pol sol); split.
      + inv H0; inv H3; dest.
        admit.
      + admit.
  Qed.

  Lemma stepSmall_implies_Step:
    forall o u l,
      StepSmall m o u l -> Step m o u l.
  Proof.
    intros; inv H.
    apply step_consistent.
    apply substepsSmall_implies_substepsInd in HSubSteps.
    dest; subst.
    constructor; auto.
  Qed.

  Lemma stepSmall_consistent:
    forall o u l,
      StepSmall m o u l <-> Step m o u l.
  Proof.
    intros; split; intros.
    - apply stepSmall_implies_Step; auto.
    - admit.
  Qed.
    
End Consistency.

