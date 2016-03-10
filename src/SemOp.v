Require Import Bool List String.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.FMap.
Require Import Syntax.
Require Export SemanticsExprAction Semantics SemFacts.

Set Implicit Arguments.

Section GivenModule.
  Variable m: Modules.
  Variable oldRegs: RegsT.

  Inductive SemActionOp:
    forall k, ActionT type k -> UpdatesT -> MethsT -> MethsT -> type k -> Prop :=
  | SASMCallExt
      meth s (marg: Expr type (SyntaxKind (arg s)))
      (mret: type (ret s))
      retK (fret: type retK)
      (cont: type (ret s) -> ActionT type retK)
      (HNotIn: ~ In meth (getDefs m))
      newRegs (cs icalls: MethsT) acalls
      (HNotCalled: ~ M.In meth cs) (* forces no double-call within an action, but necessary *)
      (HAcalls: acalls = M.add meth (existT _ _ (evalExpr marg, mret)) cs)
      (HSemAction: SemActionOp (cont mret) newRegs cs icalls fret):
      SemActionOp (MCall meth s marg cont) newRegs acalls icalls fret
  | SASMCallInt
      meth methBody
      (marg: Expr type (SyntaxKind (arg (projT1 methBody))))
      (mret: type (ret (projT1 methBody)))
      retK (fret: type retK)
      (cont: type (ret (projT1 methBody)) -> ActionT type retK)
      (HIn: In (meth :: methBody)%struct (getDefsBodies m))
      cnewRegs ccalls cicalls 
      (HCallee: SemActionOp ((projT2 methBody) type (evalExpr marg))
                            cnewRegs ccalls cicalls mret)
      newRegs (cs icalls: MethsT)
      (HSemAction: SemActionOp (cont mret) newRegs cs icalls fret)
      (Hnews: M.Disj cnewRegs newRegs)
      (Hcalls: M.Disj ccalls cs)
      (Hicalls: M.Disj cicalls icalls)
      (Hmethnin1: ~ M.In meth icalls)
      (Hmethnin2: ~ M.In meth cicalls):
      SemActionOp (MCall meth (projT1 methBody) marg cont)
                  (M.union cnewRegs newRegs) (M.union ccalls cs)
                  (M.union cicalls (M.add meth (existT _ _ (evalExpr marg, mret)) icalls))
                  fret
  | SASLet
      k (e: Expr type k) retK (fret: type retK)
      (cont: fullType type k -> ActionT type retK) newRegs cs icalls
      (HSemActionOp: SemActionOp (cont (evalExpr e)) newRegs cs icalls fret):
      SemActionOp (Let_ e cont) newRegs cs icalls fret
  | SASReadReg
      (r: string) regT (regV: fullType type regT)
      retK (fret: type retK) (cont: fullType type regT -> ActionT type retK)
      newRegs cs icalls
      (HRegVal: M.find r oldRegs = Some (existT _ regT regV))
      (HSemActionOp: SemActionOp (cont regV) newRegs cs icalls fret):
      SemActionOp (ReadReg r _ cont) newRegs cs icalls fret
  | SASWriteReg
      (r: string) k
      (e: Expr type k)
      retK (fret: type retK)
      (cont: ActionT type retK) newRegs cs icalls anewRegs
      (HNotWritten: ~ M.In r newRegs) (* it implies well-formedness *)
      (HANewRegs: anewRegs = M.add r (existT _ _ (evalExpr e)) newRegs)
      (HSemActionOp: SemActionOp cont newRegs cs icalls fret):
      SemActionOp (WriteReg r e cont) anewRegs cs icalls fret
  | SASIfElseTrue
      (p: Expr type (SyntaxKind Bool)) k1
      (a: ActionT type k1)
      (a': ActionT type k1)
      (r1: type k1)
      k2 (cont: type k1 -> ActionT type k2)
      newRegs1 newRegs2 calls1 calls2 icalls1 icalls2 (r2: type k2)
      (HTrue: evalExpr p = true)
      (HAction: SemActionOp a newRegs1 calls1 icalls1 r1)
      (HSemActionOp: SemActionOp (cont r1) newRegs2 calls2 icalls2 r2)
      unewRegs ucalls icalls
      (HUNewRegs: unewRegs = M.union newRegs1 newRegs2)
      (HregsDisj: M.Disj newRegs1 newRegs2)
      (HUCalls: ucalls = M.union calls1 calls2)
      (HcallsDisj: M.Disj calls1 calls2)
      (Hicalls: icalls = M.union icalls1 icalls2)
      (HicallsDisj: M.Disj icalls1 icalls2):
      SemActionOp (IfElse p a a' cont) unewRegs ucalls icalls r2
  | SASIfElseFalse
      (p: Expr type (SyntaxKind Bool)) k1
      (a: ActionT type k1)
      (a': ActionT type k1)
      (r1: type k1)
      k2 (cont: type k1 -> ActionT type k2)
      newRegs1 newRegs2 calls1 calls2 icalls1 icalls2 (r2: type k2)
      (HFalse: evalExpr p = false)
      (HAction: SemActionOp a' newRegs1 calls1 icalls1 r1)
      (HSemActionOp: SemActionOp (cont r1) newRegs2 calls2 icalls2 r2)
      unewRegs ucalls icalls
      (HUNewRegs: unewRegs = M.union newRegs1 newRegs2)
      (HregsDisj: M.Disj newRegs1 newRegs2)
      (HUCalls: ucalls = M.union calls1 calls2)
      (HcallsDisj: M.Disj calls1 calls2)
      (Hicalls: icalls = M.union icalls1 icalls2)
      (HicallsDisj: M.Disj icalls1 icalls2):
      SemActionOp (IfElse p a a' cont) unewRegs ucalls icalls r2
  | SASAssertTrue
      (p: Expr type (SyntaxKind Bool)) k2
      (cont: ActionT type k2) newRegs2 calls2 icalls2 (r2: type k2)
      (HTrue: evalExpr p = true)
      (HSemActionOp: SemActionOp cont newRegs2 calls2 icalls2 r2):
      SemActionOp (Assert_ p cont) newRegs2 calls2 icalls2 r2
  | SASReturn
      k (e: Expr type (SyntaxKind k)) evale
      (HEvalE: evale = evalExpr e):
      SemActionOp (Return e) (M.empty _) (M.empty _) (M.empty _) evale.

  Theorem inversionSemActionOp
          k a news cs icalls retC
          (evalA: @SemActionOp k a news cs icalls retC):
    match a with
    | MCall meth s e c =>
      (In meth (getDefs m) /\
       exists methBody mret cnewRegs ccalls cicalls nnewRegs ncalls nicalls,
         In (meth :: existT _ s methBody)%struct (getDefsBodies m) /\
         SemActionOp (methBody type (evalExpr e)) cnewRegs ccalls cicalls mret /\
         SemActionOp (c mret)
                     nnewRegs ncalls nicalls retC /\
         news = M.union cnewRegs nnewRegs /\
         cs = M.union ccalls ncalls /\
         icalls = M.union cicalls (M.add meth (existT _ _ (evalExpr e, mret)) nicalls) /\
         M.Disj cnewRegs nnewRegs /\
         M.Disj ccalls ncalls /\
         M.Disj cicalls nicalls /\
         ~ M.In meth cicalls /\
         ~ M.In meth nicalls) \/
      (~ In meth (getDefs m) /\
       exists mret pcalls,
         SemActionOp (c mret) news pcalls icalls retC /\
         ~ M.In meth pcalls /\
         cs = M.add meth (existT _ _ (evalExpr e, mret)) pcalls)
    | Let_ _ e cont =>
      SemActionOp (cont (evalExpr e)) news cs icalls retC
    | ReadReg r k c =>
      exists rv,
      M.find r oldRegs = Some (existT _ k rv) /\
      SemActionOp (c rv) news cs icalls retC
    | WriteReg r _ e a =>
      exists pnews,
      SemActionOp a pnews cs icalls retC /\
      ~ M.In r pnews /\
      news = M.add r (existT _ _ (evalExpr e)) pnews
    | IfElse p _ aT aF c =>
      exists news1 calls1 icalls1 news2 calls2 icalls2 r1,
      match evalExpr p with
      | true =>
        SemActionOp aT news1 calls1 icalls1 r1 /\
        SemActionOp (c r1) news2 calls2 icalls2 retC /\
        news = M.union news1 news2 /\
        cs = M.union calls1 calls2 /\
        icalls = M.union icalls1 icalls2 /\
        M.Disj icalls1 icalls2
      | false =>
        SemActionOp aF news1 calls1 icalls1 r1 /\
        SemActionOp (c r1) news2 calls2 icalls2 retC /\
        news = M.union news1 news2 /\
        cs = M.union calls1 calls2 /\
        icalls = M.union icalls1 icalls2 /\
        M.Disj icalls1 icalls2
      end
    | Assert_ e c =>
      SemActionOp c news cs icalls retC /\
      evalExpr e = true
    | Return e =>
      retC = evalExpr e /\
      news = M.empty _ /\
      cs = M.empty _ /\
      icalls = M.empty _
    end.
  Proof.
    destruct evalA; eauto; repeat eexists.
    - right; repeat eexists; eauto.
    - left; split.
      + unfold getDefs, namesOf in *.
        replace meth with (attrName (meth :: methBody)%struct) by reflexivity.
        apply in_map; auto.
      + repeat eexists; eauto.
        destruct methBody; auto.
    - destruct (evalExpr p); eauto; try discriminate.
    - destruct (evalExpr p); eauto; try discriminate.
  Qed.

  Inductive SubstepOp: UpdatesT -> LabelT -> MethsT ->Prop :=
  | SSSEmptyRule:
      forall u l ics,
        u = M.empty _ ->
        l = emptyRuleLabel ->
        ics = M.empty _ ->
        SubstepOp u l ics
  | SSSEmptyMeth:
      forall u l ics,
        u = M.empty _ ->
        l = emptyMethLabel ->
        ics = M.empty _ ->
        SubstepOp u l ics
  | SSSRule:
      forall k (a: Action Void)
             (HInRules: List.In {| attrName := k; attrType := a |} (getRules m))
             u cs ics (HAction: SemActionOp (a type) u cs ics WO) ndefs,
        ndefs = M.empty _ ->
        SubstepOp u {| annot := Some (Some k);
                       defs := ndefs;
                       calls := cs |} ics
  | SSSMeth:
      forall (f: DefMethT)
             (HIn: In f (getDefsBodies m))
             (HNotIn: ~ In (attrName f) (getCalls m))
             u cs ics argV retV
             (HAction: SemActionOp ((projT2 (attrType f)) type argV) u cs ics retV)
             adefs,
        adefs = M.add (attrName f) (existT _ _ (argV, retV)) (M.empty _) ->
        SubstepOp u {| annot := None;
                       defs := adefs;
                       calls := cs |} ics.

  Inductive SubstepsOp: UpdatesT -> LabelT -> MethsT -> Prop :=
  | SSSNil:
      SubstepsOp (M.empty _) emptyMethLabel (M.empty _)
  | SSSCons:
      forall pu pl pics,
        SubstepsOp pu pl pics ->
        forall nu nl nics,
          CanCombineUL pu nu pl nl ->
          M.Disj pics nics ->
          SubstepOp nu nl nics ->
          SubstepsOp (M.union pu nu) (mergeLabel pl nl) (M.union pics nics).

  Inductive StepOp: UpdatesT -> LabelT -> Prop :=
  | StepOpIntro: forall u l ics (HSubSteps: SubstepsOp u l ics),
      StepOp u l.

End GivenModule.

Ltac invertActionOp H := apply inversionSemActionOp in H; simpl in H; dest; try subst.
Ltac invertActionOpFirst :=
  match goal with
  | [H: SemActionOp _ _ _ _ _ _ _ |- _] => invertActionOp H
  end.
Ltac invertActionOpRep :=
  repeat
    match goal with
    | [H: SemActionOp _ _ _ _ _ _ _ |- _] => invertActionOp H
    | [H: if ?c
          then
            SemActionOp _ _ _ _ _ _ _ /\ _ /\ _ /\ _
          else
            SemActionOp _ _ _ _ _ _ _ /\ _ /\ _ /\ _ |- _] =>
      let ic := fresh "ic" in
      (remember c as ic; destruct ic; dest; subst)
    end.

Section Facts.
  Variable m: Modules.

  Lemma semActionOp_icalls:
    forall o {retK} (a: ActionT type retK) u cs ics retv,
      SemActionOp m o a u cs ics retv ->
      M.KeysSubset ics (getDefs m).
  Proof.
    induction 1; simpl; intros; subst; auto.
    - apply M.KeysSubset_union; auto.
      apply M.KeysSubset_add; auto.
      unfold getDefs, namesOf.
      induction (getDefsBodies m).
      + intuition.
      + simpl in *.
        destruct HIn; subst.
        * intuition.
        * specialize (IHl H1).
          intuition.
    - apply M.KeysSubset_union; auto.
    - apply M.KeysSubset_union; auto.
    - apply M.KeysSubset_empty; auto.
  Qed.

  Lemma semActionOp_calls:
    forall o {retK} (a: ActionT type retK) u cs ics retv,
      SemActionOp m o a u cs ics retv ->
      M.KeysDisj cs (getDefs m).
  Proof.
    induction 1; simpl; intros; subst; auto.
    - apply M.KeysDisj_add; auto.
    - apply M.KeysDisj_union; auto.
    - apply M.KeysDisj_union; auto.
    - apply M.KeysDisj_union; auto.
    - apply M.KeysDisj_empty.
  Qed.

  Lemma substepOp_calls:
    forall o u l ics,
      SubstepOp m o u l ics ->
      M.KeysDisj (calls l) (getDefs m).
  Proof.
    induction 1; simpl; subst; intros.
    - apply M.KeysDisj_empty.
    - apply M.KeysDisj_empty.
    - eapply semActionOp_calls; exact HAction.
    - eapply semActionOp_calls; exact HAction.
  Qed.

  Lemma substepsOp_calls:
    forall o u l ics,
      SubstepsOp m o u l ics ->
      M.KeysDisj (calls l) (getDefs m).
  Proof.
    induction 1; simpl; intros.
    - apply M.KeysDisj_empty.
    - apply substepOp_calls in H2.
      destruct nl, pl; simpl in *.
      apply M.KeysDisj_union; auto.
  Qed.

  Lemma stepOp_calls:
    forall o u l,
      StepOp m o u l ->
      M.KeysDisj (calls l) (getDefs m).
  Proof. induction 1; eapply substepsOp_calls; eauto. Qed.

End Facts.

Require Import Wf Program.Equality StaticDynamic Equiv.

Section Consistency.
  Variable m: Modules.
  Hypothesis (Hwfm: WfModules type m).
  Variable mEquiv: ModEquiv type typeUT m.
  Variable o: RegsT.

  Lemma SemActionOp_implies_SemActionSubsteps:
    forall k (a: ActionT type k) u ecs ics retv,
      SemActionOp m o a u ecs ics retv ->
      exists u1 cs1 u2 l2,
        SemAction o a u1 cs1 retv /\
        SubstepsInd m o u2 l2 /\
        M.Disj u1 u2 /\
        M.Disj cs1 (calls l2) /\
        u = M.union u1 u2 /\
        (forall k v, M.MapsTo k v ics <-> (M.MapsTo k v cs1 \/ M.MapsTo k v (calls l2)) /\
                                          (M.MapsTo k v (defs l2))) /\
        (forall k v, M.MapsTo k v ecs <-> (M.MapsTo k v cs1 \/ M.MapsTo k v (calls l2)) /\
                                          ~ (M.In k (defs l2))).
  Proof.
    intros ? ? ? ? ? ? so.
    dependent induction so; subst; dest.
    - exists x.
      exists (M.add meth (existT _ _ (evalExpr marg, mret)) x0).
      exists x1.
      exists x2.
      intuition.
      + econstructor; eauto.
      + apply M.Disj_add_1; try assumption.
        unfold not; intros.
        apply M.MapsToIn2 in H6; dest.
        specialize (H5 meth x3).
        destruct H5.
        assert (sth: M.In meth (defs x2) -> False).
        { intros.
          apply staticDynDefsSubstepsInd with (x := meth) in H0.
          intuition.
          intuition.
        }
        assert (sth2: M.MapsTo meth x3 cs) by intuition.
        apply M.MapsToIn1 in sth2.
        intuition.
      + specialize (H4 k v); specialize (H5 k v).
        apply H4 in H6.
        dest.
        destruct H6; [ left | right; assumption].
        apply M.F.P.F.add_mapsto_iff; try assumption.
        destruct (string_dec meth k); subst; [left | right; intuition].
        constructor;
        try reflexivity.
        assert (sth: M.MapsTo k v icalls) by intuition.
        apply semActionOp_icalls in so.
        apply M.MapsToIn1 in sth.
        specialize (so _ sth).
        intuition.
      + apply H4 in H6; dest.
        intuition.
      + apply M.F.P.F.add_mapsto_iff in H6.
        destruct H6; dest.
        * subst.
          apply M.MapsToIn1 in H8.
          apply staticDynDefsSubstepsInd with (x := k) in H0.
          intuition.
          intuition.
        * specialize (H4 k v); intuition.
      + specialize (H4 k v); intuition.
      + apply M.F.P.F.add_mapsto_iff in H6.
        destruct H6; dest; subst.
        left; apply M.F.P.F.add_mapsto_iff; intuition.
        apply H5 in H7; dest.
        destruct H3; try assumption.
        left.
        apply M.F.P.F.add_mapsto_iff.
        right; intuition.
        intuition.
      + apply M.F.P.F.add_mapsto_iff in H6; destruct H6; dest; subst.
        apply staticDynDefsSubstepsInd with (x := k) in H0; intuition.
        apply H5 in H8; intuition.
      + apply M.F.P.F.add_mapsto_iff.
        apply M.F.P.F.add_mapsto_iff in H6.
        destruct H6; [left | right]; intuition.
        specialize (H5 k v); intuition.
      + apply M.F.P.F.add_mapsto_iff.
        assert (sth: M.MapsTo k v cs) by (specialize (H5 k v); intuition).
        destruct (string_dec meth k); subst; [left | right]; intuition.
        apply M.MapsToIn1 in sth.
        intuition.
    - admit.
    - exists x; exists x0; exists x1; exists x2.
      intuition.
      econstructor; eauto.
    - exists x; exists x0; exists x1; exists x2.
      intuition.
      econstructor; eauto.
    - exists (M.add r (existT _ _ (evalExpr e)) x).
      exists x0.
      exists x1; exists x2.
      intuition.
      + econstructor; eauto.
      + subst; dest_disj; solve_disj.
        unfold not; intros.
        
    - exists (M.union x3 x).
      exists (M.union x4 x0).
      exists (M.union x5 x1).
      exists (mergeLabel x6 x2).
      intuition.
      + econstructor; eauto.
      + admit.
      + subst.
        dest_disj.
        solve_disj.
      + admit.
      + subst; meq.
      + apply M.mapsto_union in H13; dest.
        unfold mergeLabel; destruct x6, x2; simpl.
        destruct H13; dest.
        * apply H11 in H13; simpl in *; dest.
          { destruct H13.
            - left; apply M.mapsto_union; auto.
            - right; apply M.mapsto_union; auto.
          }
        * apply H4 in H14; simpl in *; dest.
          { destruct H14.
            - left; apply M.mapsto_union.
              right; constructor; unfold not; intros; auto.
              admit.
            - right; apply M.mapsto_union.
              right; constructor; unfold not; intros; auto.
              admit.
          } 
              
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
    - admit.
    - exists x; exists x0; exists x1; exists x2.
      intuition.
      econstructor; eauto.
    - repeat (econstructor; eauto); intros; simpl in *; dest.
      apply M.F.P.F.empty_mapsto_iff in H0; intuition.
      apply M.F.P.F.empty_mapsto_iff in H; intuition.
      destruct H;
        apply M.F.P.F.empty_mapsto_iff in H; intuition.
  Qed.

  Lemma step_implies_StepOp:
    forall o u l,
      Step m o u l -> StepOp m o u l.
  Proof.
    admit.
  Qed.
    
End Consistency.

