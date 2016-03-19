Require Import Bool List String.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.FMap.
Require Import Syntax.
Require Export SemanticsExprAction Semantics SemFacts.

Set Implicit Arguments.

Section BigSem.
  Variable m: Modules.
  Variable o: RegsT.

  Inductive SemActionBig:
    forall k, ActionT type k -> list (SubstepRec m o) -> type k -> Prop :=
  | SABMCassInt
      meth body
      (marg: Expr type (SyntaxKind (arg (projT1 body))))
      (mret: type (ret (projT1 body)))
      retK (fret: type retK)
      (cont: type (ret (projT1 body)) -> ActionT type retK)
      (HIn: In (meth :: body)%struct (getDefsBodies m))
      css retv (HCont: SemActionBig (cont mret) css retv)
      mss (HBig: SemActionBig (projT2 body type (evalExpr marg)) mss mret)
      ul (Hul: ul = Meth (Some (meth :: (existT _ _ (evalExpr marg, mret)))%struct))
      u cs (HSubstep: Substep m o u ul cs)
      bss (Hbss: bss = {| upd := u; unitAnnot := ul; cms := cs; substep := HSubstep |} :: mss)
      (HCombine: substepsComb (bss ++ css)):
      SemActionBig (MCall meth (projT1 body) marg cont) (bss ++ css) retv
  | SABMCassExt
      meth s (marg: Expr type (SyntaxKind (arg s)))
      (mret: type (ret s))
      retK (fret: type retK)
      (cont: type (ret s) -> ActionT type retK)
      (HNotInDefs: ~ In meth (getDefs m))
      css retv (HSemActionBig: SemActionBig (cont mret) css retv):
      SemActionBig (MCall meth s marg cont) css retv
  | SABLet
      k (e: Expr type k) retK (fret: type retK)
      (cont: fullType type k -> ActionT type retK)
      css retv (HSemActionBig: SemActionBig (cont (evalExpr e)) css retv):
      SemActionBig (Let_ e cont) css retv
  | SABReadReg
      (r: string) regT (regV: fullType type regT)
      retK (fret: type retK) (cont: fullType type regT -> ActionT type retK)
      (HRegVal: M.find r o = Some (existT _ regT regV))
      css retv (HSemActionBig: SemActionBig (cont regV) css retv):
      SemActionBig (ReadReg r _ cont) css retv
  | SABWriteReg
      (r: string) k
      (e: Expr type k)
      retK (fret: type retK)
      (cont: ActionT type retK)
      css retv (HSemActionBig: SemActionBig cont css retv):
      SemActionBig (WriteReg r e cont) css retv
  | SABIfElseTrue
      (p: Expr type (SyntaxKind Bool)) k1
      (a a': ActionT type k1)
      k2 (cont: type k1 -> ActionT type k2)
      (HTrue: evalExpr p = true)
      tss retvt (HAction: SemActionBig a tss retvt)
      css retv (HSemActionBig: SemActionBig (cont retvt) css retv)
      (HCombine: substepsComb (tss ++ css)):
      SemActionBig (IfElse p a a' cont) (tss ++ css) retv
  | SABIfElseFalse
      (p: Expr type (SyntaxKind Bool)) k1
      (a a': ActionT type k1)
      k2 (cont: type k1 -> ActionT type k2)
      (HTrue: evalExpr p = false)
      fss retvf (HAction: SemActionBig a' fss retvf)
      css retv (HSemActionBig: SemActionBig (cont retvf) fss retv)
      (HCombine: substepsComb (fss ++ css)):
      SemActionBig (IfElse p a a' cont) (fss ++ css) retv
  | SABAssertTrue
      (p: Expr type (SyntaxKind Bool)) k2
      (cont: ActionT type k2)
      (HTrue: evalExpr p = true)
      css retv (HSemActionBig: SemActionBig cont css retv):
      SemActionBig (Assert_ p cont) css retv
  | SABReturn
      k (e: Expr type (SyntaxKind k)):
      SemActionBig (Return e) nil (evalExpr e).

  Inductive SubstepBig: UnitLabel -> list (SubstepRec m o) -> Prop :=
  | SBRule
      k (a: Action Void)
      (HInRules: In {| attrName := k; attrType := a |} (getRules m))
      u cs (HSubstep: Substep m o u (Rle (Some k)) cs)
      bss (HActionBig: SemActionBig (a type) bss WO)
      ss (Hss: ss = {| upd := u; unitAnnot := Rle (Some k);
                       cms := cs; substep := HSubstep |} :: bss):
      SubstepBig (Rle (Some k)) ss
  | SBMeth
      (f: DefMethT) (HIn: In f (getDefsBodies m))
      bss marg mret (HActionBig: SemActionBig (projT2 (attrType f) type marg) bss mret)
      ul (Hul: ul = Meth (Some ((attrName f) :: (existT _ _ (marg, mret)))%struct))
      u cs (HSubstep: Substep m o u ul cs)
      ss (Hss: ss = {| upd := u; unitAnnot := ul; cms := cs; substep := HSubstep |} :: bss):
      SubstepBig ul ss.

  Inductive SubstepsBig: list UnitLabel -> list (SubstepRec m o) -> Prop :=
  | SSBNil: SubstepsBig nil nil
  | SSBCons
      ull sss (Hss: SubstepsBig ull sss)
      ul ss (Hs: SubstepBig ul ss)
      (HCombine: substepsComb (ss ++ sss)):
      SubstepsBig (ul :: ull) (ss ++ sss).

  Inductive StepBig: list UnitLabel -> UpdatesT -> LabelT -> Prop :=
  | StepIntro
      ull sss (HSubsteps: SubstepsBig ull sss)
      u (Hu: u = foldSSUpds sss)
      l (Hl: l = hide (foldSSLabel sss)):
      StepBig ull u l.

  Definition toUnitLabelsD (meths: MethsT) :=
    M.fold (fun m ar l => (Meth (Some (m :: ar)%struct)) :: l)
           meths nil.
  
  Definition toUnitLabels (l: LabelT) :=
    match annot l with
    | Some (Some s) => Rle (Some s) :: (toUnitLabelsD (defs l))
    | _ => toUnitLabelsD (defs l)
    end.

End BigSem.

Section Relaxed.
  Variable m: Modules.
  Variable o: RegsT.

  Inductive SemActionRelaxed:
    forall k, ActionT type k -> list (SubstepRec m o) -> type k -> Prop :=
  | SARMCassInt
      meth body
      (marg: Expr type (SyntaxKind (arg (projT1 body))))
      (mret: type (ret (projT1 body)))
      retK (fret: type retK)
      (cont: type (ret (projT1 body)) -> ActionT type retK)
      (HIn: In (meth :: body)%struct (getDefsBodies m))
      css retv (HCont: SemActionRelaxed (cont mret) css retv)
      mss (HRelaxed: SemActionRelaxed (projT2 body type (evalExpr marg)) mss mret)
      ul (Hul: ul = Meth (Some (meth :: (existT _ _ (evalExpr marg, mret)))%struct))
      u cs (HSubstep: Substep m o u ul cs)
      bss (Hbss: bss = {| upd := u; unitAnnot := ul; cms := cs; substep := HSubstep |} :: mss)
      (HCombine: substepsComb (bss ++ css)):
      SemActionRelaxed (MCall meth (projT1 body) marg cont) (bss ++ css) retv
  | SARMCassExt
      meth s (marg: Expr type (SyntaxKind (arg s)))
      (mret: type (ret s))
      retK (fret: type retK)
      (cont: type (ret s) -> ActionT type retK)
      (* (HNotInDefs: ~ In meth (getDefs m)) *) (* a relaxed point *)
      css retv (HSemActionRelaxed: SemActionRelaxed (cont mret) css retv):
      SemActionRelaxed (MCall meth s marg cont) css retv
  | SARLet
      k (e: Expr type k) retK (fret: type retK)
      (cont: fullType type k -> ActionT type retK)
      css retv (HSemActionRelaxed: SemActionRelaxed (cont (evalExpr e)) css retv):
      SemActionRelaxed (Let_ e cont) css retv
  | SARReadReg
      (r: string) regT (regV: fullType type regT)
      retK (fret: type retK) (cont: fullType type regT -> ActionT type retK)
      (HRegVal: M.find r o = Some (existT _ regT regV))
      css retv (HSemActionRelaxed: SemActionRelaxed (cont regV) css retv):
      SemActionRelaxed (ReadReg r _ cont) css retv
  | SARWriteReg
      (r: string) k
      (e: Expr type k)
      retK (fret: type retK)
      (cont: ActionT type retK)
      css retv (HSemActionRelaxed: SemActionRelaxed cont css retv):
      SemActionRelaxed (WriteReg r e cont) css retv
  | SARIfElseTrue
      (p: Expr type (SyntaxKind Bool)) k1
      (a a': ActionT type k1)
      k2 (cont: type k1 -> ActionT type k2)
      (HTrue: evalExpr p = true)
      tss retvt (HAction: SemActionRelaxed a tss retvt)
      css retv (HSemActionRelaxed: SemActionRelaxed (cont retvt) css retv)
      (HCombine: substepsComb (tss ++ css)):
      SemActionRelaxed (IfElse p a a' cont) (tss ++ css) retv
  | SARIfElseFalse
      (p: Expr type (SyntaxKind Bool)) k1
      (a a': ActionT type k1)
      k2 (cont: type k1 -> ActionT type k2)
      (HTrue: evalExpr p = false)
      fss retvf (HAction: SemActionRelaxed a' fss retvf)
      css retv (HSemActionRelaxed: SemActionRelaxed (cont retvf) fss retv)
      (HCombine: substepsComb (fss ++ css)):
      SemActionRelaxed (IfElse p a a' cont) (fss ++ css) retv
  | SARAssertTrue
      (p: Expr type (SyntaxKind Bool)) k2
      (cont: ActionT type k2)
      (HTrue: evalExpr p = true)
      css retv (HSemActionRelaxed: SemActionRelaxed cont css retv):
      SemActionRelaxed (Assert_ p cont) css retv
  | SARReturn
      k (e: Expr type (SyntaxKind k)):
      SemActionRelaxed (Return e) nil (evalExpr e).

  Inductive SubstepRelaxed: UnitLabel -> list (SubstepRec m o) -> Prop :=
  | SRRule
      k (a: Action Void)
      (HInRules: In {| attrName := k; attrType := a |} (getRules m))
      u cs (HSubstep: Substep m o u (Rle (Some k)) cs)
      bss (HActionRelaxed: SemActionRelaxed (a type) bss WO)
      ss (Hss: ss = {| upd := u; unitAnnot := Rle (Some k);
                       cms := cs; substep := HSubstep |} :: bss):
      SubstepRelaxed (Rle (Some k)) ss
  | SRMeth
      (f: DefMethT) (HIn: In f (getDefsBodies m))
      bss marg mret (HActionRelaxed: SemActionRelaxed (projT2 (attrType f) type marg) bss mret)
      ul (Hul: ul = Meth (Some ((attrName f) :: (existT _ _ (marg, mret)))%struct))
      u cs (HSubstep: Substep m o u ul cs)
      ss (Hss: ss = {| upd := u; unitAnnot := ul; cms := cs; substep := HSubstep |} :: bss):
      SubstepRelaxed ul ss.

  Inductive SubstepsRelaxed: list UnitLabel -> list (SubstepRec m o) -> Prop :=
  | SSRNil: SubstepsRelaxed nil nil
  | SSRCons
      ull sss (Hss: SubstepsRelaxed ull sss)
      ul ss (Hs: SubstepRelaxed ul ss)
      (HCombine: substepsComb (ss ++ sss)):
      SubstepsRelaxed (ul :: ull) (ss ++ sss).

  Inductive StepRelaxed: list UnitLabel -> UpdatesT -> LabelT -> Prop :=
  | StepRIntro
      ull sss (HSubsteps: SubstepsRelaxed ull sss)
      u (Hu: u = foldSSUpds sss)
      l (Hl: l = hide (foldSSLabel sss)):
      StepRelaxed ull u l.

End Relaxed.

Section Consistency.

  Lemma substeps_implies_stepRelaxed:
    forall m o (ss: Substeps m o),
      substepsComb ss ->
      SubstepsRelaxed (toUnitLabels (hide (foldSSLabel ss))) ss.
  Proof.
    admit.
  Qed.

  Lemma relaxed_to_big:
    forall m o (ss: Substeps m o) ull,
      SubstepsRelaxed ull ss ->
      wellHidden m (hide (foldSSLabel ss)) ->
      SubstepsBig ull ss.
  Proof.
    admit.
  Qed.

  Lemma step_implies_StepBig:
    forall m o u l,
      Step m o u l ->
      (* TODO: need a nocycle condition *)
      StepBig m o (toUnitLabels l) u l.
  Proof.
    intros; inv H.
    econstructor; eauto.
    apply relaxed_to_big; auto.
    apply substeps_implies_stepRelaxed; auto.
  Qed.

  (* Lemma decomposition_big: *)
  (*   forall m o *)
  (*          (Hss: forall ul (ss: list (SubstepRec m o)), *)
  (*              SubstepBig ul ss -> *)
  (*              Step m o (foldSSUpds ss) (hide (mergeLabel (getLabel ul (M.empty _)) *)
  (*                                                         (foldSSLabel ss)))) *)
  (*          ull u l *)
  (*          (HStepBig: StepBig m o ull u l), *)
  (*     Step m o u l. *)
  (* Proof. *)
    
End Consistency.

