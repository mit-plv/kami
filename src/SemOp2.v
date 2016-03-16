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
      (HSemActionOp: SemActionOp cont u cs retK u' ds' cs'):
      SemActionOp (WriteReg r e cont) (M.add r (existT _ _ (evalExpr e)) u) cs retK u' ds' cs'
  | SASIfElseTrue
      (p: Expr type (SyntaxKind Bool)) k1
      (a a': ActionT type k1)
      k2 (cont: type k1 -> ActionT type k2)
      (HTrue: evalExpr p = true)
      u1 cs1 retK1 u1' ds1' cs1'
      (HAction: SemActionOp a u1 cs1 retK1 u1' ds1' cs1')
      u2 cs2 retK2 u2' ds2' cs2'
      (HSemActionOp: SemActionOp (cont retK1) u2 cs2 retK2 u2' ds2' cs2')
      (HUDisj: M.Disj u1' u2')
      (HDsDisj: M.Disj ds1' ds2')
      (HCsDisj: M.Disj cs1' cs2')
      (HCsDisj': M.Disj cs1' cs2):
      SemActionOp (IfElse p a a' cont) (M.union u1 u2) (M.union cs1 cs2) retK2
                  (M.union u1' u2') (M.union ds1' ds2') (M.union cs1' cs2')
  | SASIfElseFalse
      (p: Expr type (SyntaxKind Bool)) k1
      (a a': ActionT type k1)
      k2 (cont: type k1 -> ActionT type k2)
      (HTrue: evalExpr p = false)
      u1 cs1 retK1 u1' ds1' cs1'
      (HAction: SemActionOp a' u1 cs1 retK1 u1' ds1' cs1')
      u2 cs2 retK2 u2' ds2' cs2'
      (HSemActionOp: SemActionOp (cont retK1) u2 cs2 retK2 u2' ds2' cs2')
      (HUDisj: M.Disj u1' u2')
      (HDsDisj: M.Disj ds1' ds2')
      (HCsDisj: M.Disj cs1' cs2')
      (HCsDisj': M.Disj cs1' cs2):
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
      (HMethOp: MethOp meth (evalExpr marg, mret) u1 ds1 cs1)
      (HMethNotIn: ~ M.In meth cs')
      (HDisj1: M.Disj u' u1)
      (HDisj2: M.Disj ds' ds1)
      (HDisj3: M.Disj cs' cs1):
      SemActionOp (MCall meth s marg cont) u
                  (M.add meth (existT _ _ (evalExpr marg, mret)) cs)
                  retK (M.union u' u1) (M.union ds' ds1) (M.union cs' cs1)
  with
  MethOp: string -> forall ar,
      SignT ar -> UpdatesT -> MethsT -> MethsT -> Prop :=
  |  MethOpIntro
       meth body arval
       (HInDefs: In (meth :: body)%struct (getDefsBodies m))
       u cs u' ds' cs'
       (HUDisj: M.Disj u u')
       (HCsDisj: M.Disj cs cs')
       (HDsDisj: ~ M.In meth ds')
       (HSemActionOp: SemActionOp (projT2 body type (fst arval)) u cs (snd arval) u' ds' cs')
       uFinal csFinal dsFinal
       (HUFinal: uFinal = M.union u u')
       (HCsFinal: csFinal = M.union cs cs')
       (HDsFinal: dsFinal = (M.add meth (existT _ _ arval) ds')):
          MethOp meth arval uFinal dsFinal csFinal.

  Scheme SemActionOp_ind_2 := Induction for SemActionOp Sort Prop
                              with MethOp_ind_2 := Induction for MethOp Sort Prop.

  Definition mutual_op_ind P P0 :=
    fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
      conj (@SemActionOp_ind_2 P P0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
           (@MethOp_ind_2 P P0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).

  (*
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
   *)

  
  Theorem SubstepsIndComb u1 l1:
    SubstepsInd m o u1 l1 ->
    forall u2 l2,
      SubstepsInd m o u2 l2 ->
      M.Disj u1 u2 ->
      M.Disj (defs l1) (defs l2) ->
      M.Disj (calls l1) (calls l2) ->
      (annot l1 = None \/ annot l2 = None) ->
      SubstepsInd m o (M.union u1 u2) (mergeLabel l1 l2).
  Proof.
    intros s.
    dependent induction s; intros.
    - rewrite M.union_empty_L; simpl.
      destruct l2; simpl in *.
      repeat rewrite M.union_empty_L.
      assumption.
    - specialize (IHs _ _ H3).
      subst.
      unfold CanCombineUUL in H0; dest.
      destruct l; simpl in *.
      destruct sul; simpl in *.
      destruct l2, annot; simpl in *.
      + intuition.
      + destruct H7; try discriminate.
        subst.
        dest_disj.
        rewrite M.union_empty_L.
        apply M.Disj_comm in H0.
        rewrite M.union_comm with (m1 := u) (m2 := su); auto.
        repeat rewrite <- M.union_assoc.
        apply M.Disj_comm in H7.
        apply M.Disj_comm in H10.
        apply M.Disj_comm in H9.
        specialize (IHs H7 H10 H9 (or_introl eq_refl)).
        clear H3.
        econstructor; eauto.
        constructor.
        solve_disj.
        simpl.
        constructor; solve_disj.
      + destruct l2; simpl in *.
        dest_disj; simpl in *.
        apply M.Disj_comm in H8.
        apply M.Disj_comm in H10.
        destruct o0; simpl in *.
        * destruct a.
          dest_disj; simpl in *.
          specialize (IHs H8 (M.Disj_comm H11) H10 H7).
          rewrite M.union_comm with (m1 := u) (m2 := su); auto.
          repeat rewrite <- M.union_assoc.
          rewrite M.union_add.
          rewrite M.union_empty_L.
          clear H3.
          econstructor; eauto.
          constructor; simpl in *.
          solve_disj.
          constructor; solve_disj.
          destruct annot, annot0; try discriminate; unfold not; intros;
            apply M.union_In in H3; intuition.
        * dest_disj; simpl in *.
          specialize (IHs H8 (M.Disj_comm H11) H10 H7).
          rewrite M.union_comm with (m1 := u) (m2 := su); auto.
          repeat rewrite <- M.union_assoc.
          rewrite M.union_empty_L.
          clear H3.
          econstructor; eauto.
          constructor; simpl in *.
          solve_disj.
          constructor; solve_disj.
          destruct annot, annot0; try discriminate; auto.
  Qed.
  
  Theorem wellHiddenSizeLe1:
    (forall k (a: ActionT type k) u cs retK u' ds' cs',
        SemActionOp a u cs retK u' ds' cs' ->
        SemAction o a u cs retK /\
        SubstepsInd m o u' {| annot := None; defs := ds'; calls := cs' |} /\
        ds' = M.restrict (M.union cs cs') (getDefs m)) /\
    (forall meth ar (arval: SignT ar) u ds cs,
        MethOp meth arval u ds cs ->
        SubstepsInd m o u {| annot := None; defs := ds; calls := cs|} /\
        ds = M.add meth (existT _ _ arval)
                   (M.restrict cs (getDefs m))).
  Proof.
    apply mutual_op_ind; intros; subst; try rewrite foldSSLabelDist, mergeLabel; dest.
    - repeat (econstructor; eauto).
      rewrite M.restrict_union.
      rewrite M.restrict_add_not_in;
        try rewrite <- M.restrict_union; auto.
    - repeat (econstructor; eauto).
    - repeat (econstructor; eauto).
    - repeat (econstructor; eauto).
    - constructor.
      econstructor; eauto.
      constructor.
      apply (SubstepsIndComb H3 H1); auto.
      rewrite M.restrict_union.
      subst.
      repeat rewrite <- M.restrict_union.
      f_equal.
      repeat rewrite M.union_assoc.
      rewrite <- M.union_assoc with (m1 := cs1) (m2 := cs1') (m3 := cs2).
      rewrite <- M.union_assoc with (m1 := cs1) (m2 := cs2) (m3 := cs1').
      rewrite M.union_comm with (m1 := cs1') (m2 := cs2); intuition.
    - constructor.
      eapply SemIfElseFalse; eauto.
      constructor.
      apply (SubstepsIndComb H3 H1); auto.
      rewrite M.restrict_union.
      subst.
      repeat rewrite <- M.restrict_union.
      f_equal.
      repeat rewrite M.union_assoc.
      rewrite <- M.union_assoc with (m1 := cs1) (m2 := cs1') (m3 := cs2).
      rewrite <- M.union_assoc with (m1 := cs1) (m2 := cs2) (m3 := cs1').
      rewrite M.union_comm with (m1 := cs1') (m2 := cs2); intuition.
    - repeat (econstructor; eauto).
    - repeat (econstructor; eauto).
    - constructor.
      econstructor; eauto.
      constructor.
      apply (SubstepsIndComb H2 H0 HDisj1 HDisj2 HDisj3 (or_introl eq_refl)).
      subst; simpl in *.
      repeat rewrite M.restrict_union.
      admit.
    - constructor.
      pose proof (SubstepsCons H0 (SingleMeth m _ HInDefs _ H)) as sth.
      simpl in *.
      assert (sth2: CanCombineUUL u' {| annot := None; defs := ds'; calls := cs' |} u cs
                                  (Meth (Some (meth :: existT _ _ (fst arval, snd arval))%struct))).
      { unfold CanCombineUUL.
        dest_disj.
        constructor.
        solve_disj.
        constructor.
        solve_disj.
        intuition.
      }
      specialize (sth sth2 _ _ eq_refl eq_refl).
      rewrite M.union_add in sth.
      rewrite M.union_empty_L in sth.
      destruct arval; simpl in *.
      rewrite M.union_comm;
        assumption.
      subst; reflexivity.
  Qed.

  (*
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
   *)

End GivenModule.

  
