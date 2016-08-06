Require Import Bool List String Structures.Equalities.
Require Import Lib.Struct Lib.Word Lib.CommonTactics.
Require Import Lib.StringBound Lib.ilist Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Wf.
Require Import Lts.ParametricSyntax Lib.Indexer.
Require Import FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.

Set Implicit Arguments.

(* Well-formedness w.r.t. valid register uses (read/writes) *)
Section ValidRegs.
  Variable type: Kind -> Type.

  Section Regs.
    Variable regs: list MetaReg.

    Inductive ValidRegsSinAction:
      forall {retT}, SinActionT type retT -> Prop :=
    | SVRMCall:
        forall name sig ar {retT} cont,
          (forall t, ValidRegsSinAction (cont t)) ->
          ValidRegsSinAction (SMCall (lretT:= retT) name sig ar cont)
    | SVRLet:
        forall {argT retT} ar cont,
          (forall t, ValidRegsSinAction (cont t)) ->
          ValidRegsSinAction (SLet_ (lretT':= argT) (lretT:= retT) ar cont)
    | SVRReadReg:
        forall {retT} c reg k cont,
          In (OneReg c reg) regs ->
          (forall t, ValidRegsSinAction (cont t)) ->
          ValidRegsSinAction (SReadReg (lretT:= retT) reg k cont)
    | SVRWriteReg:
        forall {writeT retT} c reg e cont,
          In (OneReg c reg) regs ->
          ValidRegsSinAction cont ->
          ValidRegsSinAction (SWriteReg (k:= writeT) (lretT:= retT)
                                        reg e cont)
    | SVRIfElse:
        forall {retT1 retT2} ce (ta fa: SinActionT type retT1)
               (cont: type retT1 -> SinActionT type retT2),
          ValidRegsSinAction ta ->
          ValidRegsSinAction fa ->
          (forall t, ValidRegsSinAction (cont t)) ->
          ValidRegsSinAction (SIfElse ce ta fa cont)
    | SVRAssert:
        forall {retT} e cont,
          ValidRegsSinAction cont ->
          ValidRegsSinAction (SAssert_ (lretT:= retT) e cont)
    | SVRReturn:
        forall {retT} (e: Expr type (SyntaxKind retT)),
          ValidRegsSinAction (SReturn e).

    Section Gen.
      Variables (A: Type)
                (strA: A -> string)
                (ls: list A)
                (genK: Kind).

      Inductive ValidRegsGenAction:
        forall {retT}, GenActionT genK type retT -> Prop :=
      | GVRMCall:
          forall name sig ar {retT} cont,
            (forall t, ValidRegsGenAction (cont t)) ->
            ValidRegsGenAction (GMCall (lretT:= retT) name sig ar cont)
      | GVRIndex:
          forall {retT} cont,
            (forall t, ValidRegsGenAction (cont t)) ->
            ValidRegsGenAction (GIndex (lretT:= retT) cont)
      | GVRLet:
          forall {argT retT} ar cont,
            (forall t, ValidRegsGenAction (cont t)) ->
            ValidRegsGenAction (GLet_ (lretT':= argT) (lretT:= retT) ar cont)
      | GVRReadRegO:
          forall {retT} c reg k cont,
            In (OneReg c reg) regs ->
            (forall t, ValidRegsGenAction (cont t)) ->
            ValidRegsGenAction (GReadReg (lretT:= retT) {| isRep:= false; nameRec:= reg |} k cont)
      | GVRReadRegR:
          forall {retT} Hgood1 Hgood2 getConstK reg
                 (HnoDup: NoDup ls) k cont,
            In (RepReg strA Hgood1 Hgood2 getConstK reg HnoDup) regs ->
            (forall t, ValidRegsGenAction (cont t)) ->
            ValidRegsGenAction (GReadReg (lretT:= retT) {| isRep:= true; nameRec:= reg |} k cont)
      | GVRWriteRegO:
          forall {writeT retT} c reg e cont,
            In (OneReg c reg) regs ->
            ValidRegsGenAction cont ->
            ValidRegsGenAction (GWriteReg (k:= writeT) (lretT:= retT)
                                          {| isRep:= false; nameRec:= reg |} e cont)
      | GVRWriteRegR:
          forall {writeT retT} Hgood1 Hgood2 getConstK reg
                 (HnoDup: NoDup ls) e cont,
            In (RepReg strA Hgood1 Hgood2 getConstK reg HnoDup) regs ->
            ValidRegsGenAction cont ->
            ValidRegsGenAction (GWriteReg (k:= writeT) (lretT:= retT)
                                          {| isRep:= true; nameRec:= reg |} e cont)
      | GVRIfElse:
          forall {retT1 retT2} ce (ta fa: GenActionT genK type retT1)
                 (cont: type retT1 -> GenActionT genK type retT2),
            ValidRegsGenAction ta ->
            ValidRegsGenAction fa ->
            (forall t, ValidRegsGenAction (cont t)) ->
            ValidRegsGenAction (GIfElse ce ta fa cont)
      | GVRAssert:
          forall {retT} e cont,
            ValidRegsGenAction cont ->
            ValidRegsGenAction (GAssert_ (lretT:= retT) e cont)
      | GVRReturn:
          forall {retT} (e: Expr type (SyntaxKind retT)),
            ValidRegsGenAction (GReturn genK e).

    End Gen.

    Definition ValidRegsMetaRule mr :=
      match mr with
      | OneRule r _ => ValidRegsSinAction (r type)
      | RepRule _ strA _ _ _ _ r _ ls _ => ValidRegsGenAction strA ls (r type)
      end.

    Inductive ValidRegsMetaRules: list MetaRule -> Prop :=
    | ValidRegsMetaRulesNil: ValidRegsMetaRules nil
    | ValidRegsMetaRulesCons:
        forall rule rules,
          ValidRegsMetaRules rules ->
          ValidRegsMetaRule rule ->
          ValidRegsMetaRules (rule :: rules).

    Lemma validRegsMetaRules_app:
      forall r1 r2,
        ValidRegsMetaRules r1 -> ValidRegsMetaRules r2 ->
        ValidRegsMetaRules (r1 ++ r2).
    Proof.
      induction r1; simpl; intros; auto.
      inv H; constructor; auto.
    Qed.

    Definition ValidRegsMetaMeth md :=
      match md with
      | OneMeth d _ => forall v, ValidRegsSinAction (projT2 d type v)
      | RepMeth _ strA _ _ _ _ d _ ls _ => forall v, ValidRegsGenAction strA ls (projT2 d type v)
      end.

    Inductive ValidRegsMetaMeths: list MetaMeth -> Prop :=
    | ValidRegsMetaMethsNil: ValidRegsMetaMeths nil
    | ValidRegsMetaMethsCons:
        forall dm dms,
          ValidRegsMetaMeths dms ->
          ValidRegsMetaMeth dm ->
          ValidRegsMetaMeths (dm :: dms).

    Lemma validRegsMetaMeths_app:
      forall dms1 dms2,
        ValidRegsMetaMeths dms1 -> ValidRegsMetaMeths dms2 ->
        ValidRegsMetaMeths (dms1 ++ dms2).
    Proof.
      induction dms1; simpl; intros; auto.
      inv H; constructor; auto.
    Qed.

  End Regs.

  Fixpoint ValidRegsMetaModule (mm: MetaModule): Prop :=
    ValidRegsMetaRules (metaRegs mm) (metaRules mm) /\
    ValidRegsMetaMeths (metaRegs mm) (metaMeths mm).

End ValidRegs.

Section Facts.

  Lemma oneReg_getListFromMetaReg_In:
    forall c reg regs,
      In (OneReg c reg) regs ->
      In (nameVal reg) (namesOf (Concat.concat (map getListFromMetaReg regs))).
  Proof.
    induction regs; simpl; intros; auto.
    destruct H; subst; rewrite namesOf_app; apply in_or_app; auto.
    left; left; auto.
  Qed.
  
  Lemma getListFromRep_addIndexToStr_In:
    forall {A} (strA: A -> string) {B} (getConstK: A -> B) i name ls,
      In i ls ->
      In (addIndexToStr strA i name)
         (namesOf (getListFromRep strA getConstK name ls)).
  Proof.
    induction ls; simpl; intros; auto.
    destruct H; subst; auto.
  Qed.

  Lemma repReg_getListFromMetaReg_In:
    forall {A} (strA: A -> string) Hgood1 Hgood2 getConstK reg {ls} (HnoDup: NoDup ls) i regs,
      In i ls ->
      In (RepReg strA Hgood1 Hgood2 getConstK reg HnoDup) regs ->
      In (addIndexToStr strA i (nameVal reg))
         (namesOf (Concat.concat (map getListFromMetaReg regs))).
  Proof.
    induction regs; simpl; intros; auto.
    destruct H0; subst; rewrite namesOf_app; apply in_or_app; auto.
    left; apply getListFromRep_addIndexToStr_In; auto.
  Qed.

  Lemma validRegsSinAction_validRegsAction:
    forall {ty} regs {retK} (a: SinActionT ty retK),
      ValidRegsSinAction regs a ->
      ValidRegsAction (namesOf (Concat.concat (map getListFromMetaReg regs))) (getSinAction a).
  Proof.
    induction 1; simpl; intros; try (constructor; auto);
      eapply oneReg_getListFromMetaReg_In; eauto.
  Qed.

  Lemma validRegsGenAction_validRegsAction:
    forall regs ty {A} (strA: A -> string) ls {genK} getConstK i
           {retK} (bgen: GenActionT ty genK retK),
      In i ls ->
      ValidRegsGenAction regs strA ls bgen ->
      ValidRegsAction (namesOf (Concat.concat (map getListFromMetaReg regs)))
                      (getGenAction strA getConstK i bgen).
  Proof.
    induction 2; simpl; intros; try (constructor; auto);
      try (eapply oneReg_getListFromMetaReg_In; eauto; fail);
      try (eapply repReg_getListFromMetaReg_In; eauto; fail).
  Qed.

  Lemma validRegsGenAction_validRegsRules:
    forall regs ty {A} (strA: A -> string) {genK} getConstK (bgen: GenAction genK Void) name
           ls ls',
      ValidRegsGenAction regs strA ls' (bgen ty) ->
      SubList ls ls' ->
      ValidRegsRules ty (namesOf (Concat.concat (map getListFromMetaReg regs)))
                     (repRule strA getConstK bgen name ls).
  Proof.
    induction ls; simpl; intros; [constructor|].
    constructor.
    - eapply IHls; eauto.
      apply SubList_cons_inv in H0; dest; auto.
    - eapply validRegsGenAction_validRegsAction; eauto.
      apply SubList_cons_inv in H0; dest; auto.
  Qed.

  Lemma validRegsGenAction_validRegsDms:
    forall regs ty {A} (strA: A -> string) {genK} getConstK (bgen: sigT (GenMethodT genK)) name
           ls ls',
      (forall v : ty (arg (projT1 bgen)), ValidRegsGenAction regs strA ls' (projT2 bgen ty v)) ->
      SubList ls ls' ->
      ValidRegsDms ty (namesOf (Concat.concat (map getListFromMetaReg regs)))
                   (repMeth strA getConstK bgen name ls).
  Proof.
    induction ls; simpl; intros; [constructor|].
    constructor.
    - eapply IHls; eauto.
      apply SubList_cons_inv in H0; dest; auto.
    - intros; eapply validRegsGenAction_validRegsAction; eauto.
      apply SubList_cons_inv in H0; dest; auto.
  Qed.

  Lemma validRegsMetaRule_validRegsRules:
    forall ty regs a,
      ValidRegsMetaRule ty regs a ->
      ValidRegsRules ty (namesOf (Concat.concat (map getListFromMetaReg regs)))
                     (getListFromMetaRule a).
  Proof.
    destruct a as [a|a]; simpl; intros.
    - repeat constructor; simpl.
      apply validRegsSinAction_validRegsAction; auto.
    - eapply validRegsGenAction_validRegsRules; eauto.
      apply SubList_refl.
  Qed.

  Lemma validRegsMetaMeth_validRegsDms:
    forall ty regs a,
      ValidRegsMetaMeth ty regs a ->
      ValidRegsDms ty (namesOf (Concat.concat (map getListFromMetaReg regs)))
                   (getListFromMetaMeth a).
  Proof.
    destruct a as [a|a]; simpl; intros.
    - repeat constructor; simpl.
      intros; apply validRegsSinAction_validRegsAction; auto.
    - eapply validRegsGenAction_validRegsDms; eauto.
      apply SubList_refl.
  Qed.

  Lemma validRegsMetaModule_validRegsModules:
    forall ty mm,
      ValidRegsMetaModule ty mm ->
      ValidRegsModules ty (modFromMeta mm).
  Proof.
    destruct mm as [regs rules dms]; simpl; intros; dest; split.
    - clear -H; induction rules; [constructor|]; inv H.
      simpl; apply validRegsRules_app; auto.
      apply validRegsMetaRule_validRegsRules; auto.
    - clear -H0; induction dms; [constructor|]; inv H0.
      simpl; apply validRegsDms_app; auto.
      apply validRegsMetaMeth_validRegsDms; auto.
  Qed.

  Lemma validRegsSinAction_regs_weakening:
    forall regs eregs {ty retK} (a: SinActionT ty retK),
      ValidRegsSinAction regs a ->
      SubList regs eregs ->
      ValidRegsSinAction eregs a.
  Proof.
    induction 1; simpl; intros; try (econstructor; eauto).
  Qed.

  Lemma validRegsGenAction_regs_weakening:
    forall {A} (strA: A -> string) ls regs eregs {ty genK retK} (a: GenActionT genK ty retK),
      ValidRegsGenAction regs strA ls a ->
      SubList regs eregs ->
      ValidRegsGenAction eregs strA ls a.
  Proof.
    induction 1; simpl; intros; try (econstructor; eauto).
  Qed.

  Lemma validRegsMetaRules_regs_weakening:
    forall ty regs eregs rules,
      ValidRegsMetaRules ty regs rules ->
      SubList regs eregs ->
      ValidRegsMetaRules ty eregs rules.
  Proof.
    induction rules; simpl; intros; [constructor|].
    inv H; constructor; auto.
    destruct a as [a|a]; unfold ValidRegsMetaRule in *.
    - eapply validRegsSinAction_regs_weakening; eauto.
    - eapply validRegsGenAction_regs_weakening; eauto.
  Qed.

  Lemma validRegsMetaMeths_regs_weakening:
    forall ty regs eregs meths,
      ValidRegsMetaMeths ty regs meths ->
      SubList regs eregs ->
      ValidRegsMetaMeths ty eregs meths.
  Proof.
    induction meths; simpl; intros; [constructor|].
    inv H; constructor; auto.
    destruct a as [a|a]; unfold ValidRegsMetaMeth in *; intros.
    - eapply validRegsSinAction_regs_weakening; eauto.
    - eapply validRegsGenAction_regs_weakening; eauto.
  Qed.
   
  Lemma validRegsMetaModule_modular:
    forall ty mm1 mm2,
      ValidRegsMetaModule ty mm1 ->
      ValidRegsMetaModule ty mm2 ->
      ValidRegsMetaModule ty (mm1 +++ mm2).
  Proof.
    destruct mm1 as [regs1 rules1 dms1], mm2 as [regs2 rules2 dms2].
    simpl; intros; dest; split.
    - apply validRegsMetaRules_app.
      + eapply validRegsMetaRules_regs_weakening; eauto.
        apply SubList_app_1, SubList_refl.
      + eapply validRegsMetaRules_regs_weakening; eauto.
        apply SubList_app_2, SubList_refl.
    - apply validRegsMetaMeths_app.
      + eapply validRegsMetaMeths_regs_weakening; eauto.
        apply SubList_app_1, SubList_refl.
      + eapply validRegsMetaMeths_regs_weakening; eauto.
        apply SubList_app_2, SubList_refl.
  Qed.

End Facts.

