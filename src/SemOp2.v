Require Import Bool List String.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.FMap Program.Equality.
Require Import Syntax.
Require Export SemanticsExprAction Semantics SemFacts.

Set Implicit Arguments.

Section GivenModule.
  Variable m: Modules.
  Variable o: RegsT.

  Inductive SemActionOp:
    forall k,
      ActionT type k ->
      UpdatesT -> MethsT -> type k ->
      UpdatesT -> MethsT -> MethsT -> Prop :=
  | SASMCallExt
      meth s (marg: Expr type (SyntaxKind (arg s)))
      (mret: type (ret s))
      retK (fret: type retK)
      (cont: type (ret s) -> ActionT type retK)
      u cs retK u' ds' cs'
      (HNotInDefs: ~ In meth (getDefs m))
      (HSemActionOp: SemActionOp (cont mret) u cs retK u' ds' cs'):
      SemActionOp (MCall meth s marg cont) u (M.add meth (existT _ _ (evalExpr marg, mret)) cs)
                  retK u' ds' cs'
  | SASLet
      k (e: Expr type k) retK (fret: type retK)
      (cont: fullType type k -> ActionT type retK)
      u cs retK u' ds' cs'
      (HSemActionOp: SemActionOp (cont (evalExpr e)) u cs retK u' ds' cs'):
      SemActionOp (Let_ e cont) u cs retK u' ds' cs'
  | SASReadReg
      (r: string) regT (regV: fullType type regT)
      retK (fret: type retK) (cont: fullType type regT -> ActionT type retK)
      (HRegVal: M.find r o = Some (existT _ regT regV))
      u cs retK u' ds' cs'
      (HSemActionOp: SemActionOp (cont regV) u cs retK u' ds' cs'):
      SemActionOp (ReadReg r _ cont) u cs retK u' ds' cs'
  | SASWriteReg
      (r: string) k
      (e: Expr type k)
      retK (fret: type retK)
      (cont: ActionT type retK)
      u cs retK u' ds' cs'
      (HNotInRegs: ~ M.In r u)
      (HSemActionOp: SemActionOp cont u cs retK u' ds' cs'):
      SemActionOp (WriteReg r e cont) (M.add r (existT _ _ (evalExpr e)) u) cs retK u' ds' cs'
  | SASIfElseTrue
      (p: Expr type (SyntaxKind Bool)) k1
      (a a': ActionT type k1)
      k2 (cont: type k1 -> ActionT type k2) r
      (HTrue: evalExpr p = true)
      u1 cs1 retK1 u1' ds1' cs1'
      (HAction: SemActionOp a u1 cs1 retK1 u1' ds1' cs1')
      u2 cs2 retK2 u2' ds2' cs2'
      (HSemActionOp: SemActionOp (cont r) u2 cs2 retK2 u2' ds2' cs2'):
      SemActionOp (IfElse p a a' cont) (M.union u1 u2) (M.union cs1 cs2) retK2
                  (M.union u1' u2') (M.union ds1' ds2') (M.union cs1' cs2')
  | SASIfElseFalse
      (p: Expr type (SyntaxKind Bool)) k1
      (a a': ActionT type k1)
      k2 (cont: type k1 -> ActionT type k2) r
      (HTrue: evalExpr p = false)
      u1 cs1 retK1 u1' ds1' cs1'
      (HAction: SemActionOp a' u1 cs1 retK1 u1' ds1' cs1')
      u2 cs2 retK2 u2' ds2' cs2'
      (HSemActionOp: SemActionOp (cont r) u2 cs2 retK2 u2' ds2' cs2'):
      SemActionOp (IfElse p a a' cont) (M.union u1 u2) (M.union cs1 cs2) retK2
                  (M.union u1' u2') (M.union ds1' ds2') (M.union cs1' cs2')
  | SASAssertTrue
      (p: Expr type (SyntaxKind Bool)) k2
      (cont: ActionT type k2)
      (HTrue: evalExpr p = true)
      u cs retK u' ds' cs'
      (HSemActionOp: SemActionOp cont u cs retK u' ds' cs'):
      SemActionOp (Assert_ p cont) u cs retK u' ds' cs'
  | SASReturn
      k (e: Expr type (SyntaxKind k)):
      SemActionOp (Return e) (M.empty _) (M.empty _) (evalExpr e) (M.empty _) (M.empty _)
                  (M.empty _)
  | SASMCallInt
      meth s (marg: Expr type (SyntaxKind (arg s)))
      (mret: type (ret s))
      retK (fret: type retK)
      (cont: type (ret s) -> ActionT type retK)
      u cs retK u' ds' cs'
      (HSemActionOp: SemActionOp (cont mret) u cs retK u' ds' cs')
      u1 ds1 cs1
      (HMethOp: MethOp meth (evalExpr marg, mret) u1 ds1 cs1):
      SemActionOp (MCall meth s marg cont) u (M.add meth (existT _ _ (evalExpr marg, mret)) cs)
                  retK (M.union u' u1) (M.union ds' ds1) (M.union cs' cs1)
  with
  MethOp: string -> forall ar,
      SignT ar -> UpdatesT -> MethsT -> MethsT -> Prop :=
  |  MethOpIntro
       meth body arval
       (HInDefs: In (meth :: body)%struct (getDefsBodies m))
       u cs retK u' ds' cs'
       (HUDisj: M.Disj u u')
       (HCsDisj: M.Disj cs cs')
       (HDsDisj: ~ M.In meth ds')
       (HSemActionOp: SemActionOp (projT2 body type (fst arval)) u cs retK u' ds' cs')
       uFinal csFinal dsFinal
       (HUFinal: uFinal = M.union u u')
       (HCsFinal: csFinal = M.union cs cs')
       (HDsFinal: dsFinal = (M.add meth (existT _ _ arval) ds')):
          MethOp meth arval uFinal csFinal dsFinal.

  Scheme SemActionOp_ind_2 := Induction for SemActionOp Sort Prop
                              with MethOp_ind_2 := Induction for MethOp Sort Prop.

  Definition mutual_op_ind P P0 :=
    fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
      conj (@SemActionOp_ind_2 P P0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
           (@MethOp_ind_2 P P0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).

  About mutual_op_ind.

  Inductive RuleOp: string -> forall ss, substepsComb (m := m) (o := o) ss -> Prop :=
  | RuleOpIntro rle body
                (HInRules: In (rle :: body)%struct (getRules m))
                (sRec: SubstepRec m o)
                (HSRecRule: unitAnnot sRec = Rle (Some rle))
                ss (ssComb: substepsComb ss)
                u cs retK
                (HSemActionOp: SemActionOp (body type) ssComb u cs retK)
                (ssCombFinal: substepsComb (sRec :: ss)):
      RuleOp rle ssCombFinal.

  Theorem wellHiddenSizeLe1:
    (forall k (a: ActionT type k) ss (ssComb: substepsComb ss) u cs retK,
        SemActionOp a ssComb u cs retK ->
        SemAction o a u cs retK /\
        (*M.Disj cs (calls (foldSSLabel ss)) /\*)
        defs (foldSSLabel ss) =
        M.restrict (M.union cs (calls (foldSSLabel ss))) (getDefs m)) /\
    (forall meth ar (arval: SignT ar) ss (ssComb: substepsComb ss),
        MethOp meth arval ssComb ->
        ~ M.In meth (calls (foldSSLabel ss)) /\
        defs (foldSSLabel ss) = M.add meth (existT _ _ arval)
                                      (M.restrict (calls (foldSSLabel ss)) (getDefs m))).
  Proof.
    apply mutual_op_ind; intros; subst; try rewrite foldSSLabelDist, mergeLabel; dest.
    - constructor.
      econstructor; eauto.
      repeat rewrite M.restrict_union in *.
      repeat rewrite M.restrict_add_not_in.
      rewrite M.restrict_union in H0.
      intuition.
      intuition.
    - constructor.
      apply SemMCall with (mret := mret) (calls := cs); intuition.
      econstructor; eauto.
      repeat rewrite foldSSLabelDist.
      case_eq (foldSSLabel ss); case_eq (foldSSLabel ss'); intros; simpl in *.
      rewrite H2, H3 in *; simpl in *.
      subst.
      repeat rewrite M.restrict_union.
      rewrite <- M.restrict_add_in.
      subst.
      rewrite M.restrict_union.
      rewrite <- M.restrict_union.
      rewrite M.union_assoc.
      rewrite M.restrict_union in *.
      subst.
      repeat f_equal.
      rewrite M.restrict_union 
      
      rewrite <- M.restrict_add_in.
      rewrite M.restrict_union.
      rewrite H0.
      rewrite M.restrict_union.
      rewrite H0.
      unfold mergeLabel.
      rewrite M.restrict_union in H1.
      intuition.
      intuition.
      
      try constructor.
    - econstructor; eauto.
    - repeat rewrite M.restrict_union in *.
      repeat rewrite M.restrict_add_not_in.
      rewrite M.restrict_union in H0.
      intuition.
      intuition.
    - econstructor; eauto.
    - 
      repeat rewrite M.restrict_union in *.
      f_equal.
      repeat rewrite M.restrict_add_in.
      rewrite M.restrict_union in H1.
      intuition.
      intuition.
      M.ext y.
      rewrite M.restrict_find.
      rewrite M.restrict_add.
      dependent destruction HSemAction.
      exists x, (M.add meth (existT _ _ (evalExpr marg, mret)) x0), x1.
      constructor.
      + apply SemMCall.
      admit.
      try (eexists, eauto).
    - apply inversionSemAction in H0; dest.
      dependent destruction H0.
      specialize (H _ _ _ H0).
      eapply H; eauto.
    - 
    repeat match goal with
           | |- context [foldSSLabel ?P] => destruct (foldSSLabel P)
           end; simpl in *. rewrite M.restrict_union; subst; reflexivity.
    repeat match goal with
           | |- context [foldSSLabel ?P] => destruct (foldSSLabel P)
           end; simpl in *; rewrite M.restrict_union; subst; reflexivity.
    repeat match goal with
           | |- context [foldSSLabel ?P] => destruct (foldSSLabel P)
           end; simpl in *; rewrite M.restrict_union; subst; reflexivity.
    simpl.
    unfold addLabelLeft, mergeLabel.
    destruct (getSLabel sRec), (foldSSLabel ss); simpl in *.
    rewrite M.restrict_union; subst. reflexivity.
      subst.
        subst; reflexivity.
    intuition.
      try destruct (foldSSLabel ss), (foldSSLabel ss'); simpl in *.
    - unfold
    - admit.
    - admit.
    - admit.
    - simpl in *.
      unfold addLabelLeft.
    - dependent destruction HSubstepOp'; subst.

    (forall ss (ssComb: substepsComb ss) k (a: ActionT type k),
        SemActionOp a ssComb -> defs (foldSSLabel ss) = M.empty _) /\
    (forall ss (ssComb: substepsComb ss) meth ar (arval: SignT ar),
        MethOp meth arval ssComb ->
        defs (foldSSLabel ss) = M.add meth (existT _ _ arval) (M.empty _)).
  Proof.
    apply mutual_ind.

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
    - subst.
      dest_disj.
      pose proof
           (SubstepsCons H7 (SingleMeth m (meth :: methBody)%struct HIn (evalExpr marg) H6))
        as sstep.
      simpl in *.
      assert (cc: CanCombineUUL
                    x5 x6 x3 x4
                    (Meth (Some (meth :: existT _ _ (evalExpr marg, mret))%struct))).
      { unfold CanCombineUUL.
        intuition.
        destruct x6 as [a6 d6 c6]; simpl in *.
        destruct a6; intros; simpl in *.
        - admit.
        - 
                                                  
      exists x.
      exists (M.add meth (existT _ _ (evalExpr marg, mret)) x0).
      exists (M.union x1 (M.union x3 x5)).
      exists (M.x2.
      intuition.
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
        apply M.in_union_R with (m' := x) in H3.
        intuition.
      + rewrite M.union_add.
        rewrite H3.
        reflexivity.
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

