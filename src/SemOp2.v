Require Import Bool List String.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.FMap Program.Equality.
Require Import Syntax.
Require Export SemanticsExprAction Semantics SemFacts.

Set Implicit Arguments.

Lemma add_union_empty
      A k (v: A) m:
  M.add k v m = M.union (M.add k v (M.empty _)) m.
Proof.
  rewrite M.union_add.
  rewrite M.union_empty_L.
  reflexivity.
Qed.

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
      (HMethNotIn: ~ M.In meth cs)
      (HMethNotIn': ~ M.In meth cs')
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

  Theorem semActionOp_implies_semAction_substeps:
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
      rewrite M.restrict_add_in.
      rewrite <- M.restrict_union.
      f_equal.
      rewrite add_union_empty.
      rewrite add_union_empty with (m := cs).
      rewrite M.union_assoc.
      rewrite M.union_assoc.
      f_equal.
      rewrite M.union_comm with (m2 := cs).
      rewrite <- M.union_assoc with (m3 := cs').
      rewrite M.union_comm with (m1 := (M.add meth _ _)) (m2 := cs').
      rewrite <- M.union_assoc; reflexivity.
      apply M.Disj_add_1.
      apply M.Disj_empty_1.
      intuition.
      apply M.Disj_add_1.
      apply M.Disj_empty_1.
      intuition.
      dependent destruction HMethOp.
      clear - HInDefs.
      unfold getDefs, namesOf.
      assert (sth: meth = attrName (Kind := sigT MethodT) (meth :: body)%struct) by reflexivity.
      rewrite sth.
      apply in_map.
      intuition.
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
  Theorem semAction_substeps_implies_semActionOp:
    forall k (a: ActionT type k) u cs retK,
      SemAction o a u cs retK ->
      forall u' ds' cs',
        SubstepsInd m o u' {| annot := None; defs := ds'; calls := cs' |} ->
        ds' = M.restrict (M.union cs cs') (getDefs m) ->
        SemActionOp a u cs retK u' ds' cs'.
  Proof.
    intros k a u cs retK sa.
    dependent induction sa; intros.
    - destruct (in_dec string_dec meth (getDefs m)).
      + 
      + rewrite M.restrict_union in H0.
        rewrite HAcalls in H0.
        rewrite M.restrict_add_not_in in H0; auto.
        rewrite <- M.restrict_union in H0.
        specialize (IHsa H H0).
        rewrite HAcalls.
        econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - rewrite HANewRegs.
      econstructor; eauto.
    - rewrite HUNewRegs.
      rewrite HUCalls.
      specialize (IHsa1 H).
      econstructor; eauto.

      eapply IHsa.
        pose proof (SASMCallExt meth s marg mret fret cont n IHsa).
        econstructor; eauto.
        
    induction 1; intros.
    - specialize (IHSemAction H0).
    /\
    (forall meth ar (arval: SignT ar) u ds cs,
        SubstepsInd m o u {| annot := None; defs := ds; calls := cs|} ->
        ds = M.add meth (existT _ _ arval)
                   (M.restrict cs (getDefs m)) ->
        MethOp meth arval u ds cs
    ).
  Proof.
    intros.

*)
End GivenModule.

  
