Require Import Bool List String.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.Indexer.
Require Import Lib.ilist Lib.FMap Lib.StringEq.
Require Import Kami.Syntax Kami.Semantics Kami.Wf Kami.ParametricSyntax.
Require Import FunctionalExtensionality Program.Equality Structures.Equalities Eqdep Eqdep_dec.

Set Implicit Arguments.
Set Asymmetric Patterns.

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

    Lemma validRegsMetaRules_app_inv:
      forall r1 r2,
        ValidRegsMetaRules (r1 ++ r2) ->
        ValidRegsMetaRules r1 -> ValidRegsMetaRules r2.
    Proof.
      induction r1; simpl; intros; auto.
      inv H; inv H0.
      firstorder fail.
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

    Lemma validRegsMetaMeths_app_inv:
      forall dms1 dms2,
        ValidRegsMetaMeths (dms1 ++ dms2) ->
        ValidRegsMetaMeths dms1 -> ValidRegsMetaMeths dms2.
    Proof.
      induction dms1; simpl; intros; auto.
      inv H; inv H0.
      firstorder fail.
    Qed.
  End Regs.

  Section Regs2.
    Variable regs: list NameRec.

    Inductive ValidSinRegsSinAction:
      forall {retT}, SinActionT type retT -> Prop :=
    | SSVRMCall:
        forall name sig ar {retT} cont,
          (forall t, ValidSinRegsSinAction (cont t)) ->
          ValidSinRegsSinAction (SMCall (lretT:= retT) name sig ar cont)
    | SSVRLet:
        forall {argT retT} ar cont,
          (forall t, ValidSinRegsSinAction (cont t)) ->
          ValidSinRegsSinAction (SLet_ (lretT':= argT) (lretT:= retT) ar cont)
    | SSVRReadReg:
        forall {retT} reg k cont,
          In reg regs ->
          (forall t, ValidSinRegsSinAction (cont t)) ->
          ValidSinRegsSinAction (SReadReg (lretT:= retT) reg k cont)
    | SSVRWriteReg:
        forall {writeT retT} reg e cont,
          In reg regs ->
          ValidSinRegsSinAction cont ->
          ValidSinRegsSinAction (SWriteReg (k:= writeT) (lretT:= retT)
                                           reg e cont)
    | SSVRIfElse:
        forall {retT1 retT2} ce (ta fa: SinActionT type retT1)
               (cont: type retT1 -> SinActionT type retT2),
          ValidSinRegsSinAction ta ->
          ValidSinRegsSinAction fa ->
          (forall t, ValidSinRegsSinAction (cont t)) ->
          ValidSinRegsSinAction (SIfElse ce ta fa cont)
    | SSVRAssert:
        forall {retT} e cont,
          ValidSinRegsSinAction cont ->
          ValidSinRegsSinAction (SAssert_ (lretT:= retT) e cont)
    | SSVRReturn:
        forall {retT} (e: Expr type (SyntaxKind retT)),
          ValidSinRegsSinAction (SReturn e).

    Definition ValidSinRegsSinRule (rule: SinRule) :=
      ValidSinRegsSinAction (ruleGen rule type).

    Inductive ValidSinRegsSinRules: list SinRule -> Prop :=
    | ValidSinRegsSinRulesNil: ValidSinRegsSinRules nil
    | ValidSinRegsSinRulesCons:
        forall rule rules,
          ValidSinRegsSinRules rules ->
          ValidSinRegsSinRule rule ->
          ValidSinRegsSinRules (rule :: rules).

    Lemma validSinRegsSinRules_app:
      forall r1 r2,
        ValidSinRegsSinRules r1 -> ValidSinRegsSinRules r2 ->
        ValidSinRegsSinRules (r1 ++ r2).
    Proof.
      induction r1; simpl; intros; auto.
      inv H; constructor; auto.
    Qed.

    Lemma validSinRegsSinRules_app_inv:
      forall r1 r2,
        ValidSinRegsSinRules (r1 ++ r2) ->
        ValidSinRegsSinRules r1 -> ValidSinRegsSinRules r2.
    Proof.
      induction r1; simpl; intros; auto.
      inv H; inv H0.
      firstorder fail.
    Qed.

    Definition ValidSinRegsSinMeth md :=
      forall v, ValidSinRegsSinAction (projT2 (methGen md) type v).

    Inductive ValidSinRegsSinMeths: list SinMeth -> Prop :=
    | ValidSinRegsSinMethsNil: ValidSinRegsSinMeths nil
    | ValidSinRegsSinMethsCons:
        forall dm dms,
          ValidSinRegsSinMeths dms ->
          ValidSinRegsSinMeth dm ->
          ValidSinRegsSinMeths (dm :: dms).

    Lemma validSinRegsSinMeths_app:
      forall dms1 dms2,
        ValidSinRegsSinMeths dms1 -> ValidSinRegsSinMeths dms2 ->
        ValidSinRegsSinMeths (dms1 ++ dms2).
    Proof.
      induction dms1; simpl; intros; auto.
      inv H; constructor; auto.
    Qed.

    Lemma validSinRegsSinMeths_app_inv:
      forall dms1 dms2,
        ValidSinRegsSinMeths (dms1 ++ dms2) ->
        ValidSinRegsSinMeths dms1 -> ValidSinRegsSinMeths dms2.
    Proof.
      induction dms1; simpl; intros; auto.
      inv H; inv H0.
      firstorder fail.
    Qed.
  End Regs2.

  Fixpoint ValidRegsMetaModule (mm: MetaModule): Prop :=
    ValidRegsMetaRules (metaRegs mm) (metaRules mm) /\
    ValidRegsMetaMeths (metaRegs mm) (metaMeths mm).


  Fixpoint ValidRegsMetaModules (mm: MetaModules): Prop :=
    match mm with
      | MetaRegFile _ _ _ _ _ _ => ValidRegsMetaRules (metaModulesRegs mm) (metaModulesRules mm) /\
                                   ValidRegsMetaMeths (metaModulesRegs mm) (metaModulesMeths mm)
      | MetaMod (Build_MetaModule regs rules meths) => ValidRegsMetaRules regs rules /\ ValidRegsMetaMeths regs meths
      | ConcatMetaMod m1 m2 => ValidRegsMetaModules m1 /\ ValidRegsMetaModules m2
      | RepeatSinMod A strA goodStrFn GenK getConstK goodStrFn2 ls noDupLs m =>
        ValidSinRegsSinRules (map (@regName _) (sinRegs m)) (sinRules m) /\
        ValidSinRegsSinMeths (map (@regName _) (sinRegs m)) (sinMeths m)
    end.
End ValidRegs.

(* NOTE: Defining "MetaModRegsWf" by Gallina definition affects proof automation by "kvr". *)
Notation "'MetaModRegsWf' m" := (forall ty, ValidRegsMetaModule ty m) (at level 0).

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

  Lemma validSinRegsSinAction_validRegsAction:
    forall regs ty A (strA: A -> string) GenK getConstK i k (a: SinActionT ty k),
      ValidSinRegsSinAction regs a ->
      ValidRegsAction
        (map (fun x => addIndexToStr strA i (nameVal x)) regs)
        (getGenAction strA getConstK i (convSinToGen true GenK a)).
  Proof.
    induction 1; simpl; intros; try (constructor; auto);
    rewrite in_map_iff;
    eexists; eauto.
  Qed.
  
  Lemma validSinRegsSinRules_validRegsRules:
    forall ty A regs rules,
      ValidSinRegsSinRules ty (map (regName (A:=A)) regs) rules ->
      forall (a: A) strA GenK getConstK,
        ValidRegsRules ty
                       (map (fun x : SinReg A => addIndexToStr strA a (nameVal (regName x))) regs)
                       (map
                          (fun sr : SinRule =>
                             (addIndexToStr strA a (nameVal (ruleName sr))
                                            :: (fun ty0 : Kind -> Type =>
                                                  getGenAction strA getConstK a
                                                               (convSinToGen true GenK (ruleGen sr ty0))))%struct)
                          rules).
  Proof.
    induction rules; simpl; auto; intros; [constructor|].
    inv H.
    specialize (IHrules H2 a0 strA GenK getConstK).
    constructor; auto.
    clear - H3.
    destruct a; simpl in *; unfold ValidSinRegsSinRule in *; simpl in *.
    apply (validSinRegsSinAction_validRegsAction strA getConstK a0) in H3; simpl in *; rewrite map_map in H3; auto.
  Qed.

  Lemma validSinRegsSinMeths_validRegsDms:
    forall ty A regs meths,
      ValidSinRegsSinMeths ty (map (regName (A:=A)) regs) meths ->
      forall (a: A) strA GenK getConstK,
        ValidRegsDms
          ty
          (map (fun x : SinReg A => addIndexToStr strA a (nameVal (regName x))) regs)
          (map
             (fun sf : SinMeth =>
                (addIndexToStr strA a (nameVal (methName sf))
                               :: existT
                               (fun sig : SignatureT =>
                                  forall ty0 : Kind -> Type,
                                    ty0 (arg sig) -> ActionT ty0 (ret sig)) 
                               (projT1 (methGen sf))
                               (fun (ty0 : Kind -> Type)
                                    (argv : ty0 (arg (projT1 (methGen sf)))) =>
                                  getGenAction strA getConstK a
                                               (convSinToGen true GenK (projT2 (methGen sf) ty0 argv))))%struct)
             meths).
  Proof.
    induction meths; simpl; auto; intros; [constructor|].
    inv H.
    specialize (IHmeths H2 a0 strA GenK getConstK).
    constructor; auto.
    clear - H3.
    destruct a; simpl in *; unfold ValidSinRegsSinMeth in *; simpl in *.
    intros.
    specialize (H3 argV).
    apply (validSinRegsSinAction_validRegsAction strA getConstK a0) in H3; simpl in *; rewrite map_map in H3; auto.
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


  Lemma validRegsMetaModules_validRegsModules:
    forall ty mm,
      ValidRegsMetaModules ty mm ->
      ValidRegsModules ty (modFromMetaModules mm).
  Proof.
    induction mm.
    - simpl in *; intros; dest; split; simpl in *.
      + constructor.
      + unfold ValidRegsMetaModules in H; simpl in H.
        dest.
        inv H0.
        inv H3.
        clear H H2.
        apply validRegsMetaMeth_validRegsDms in H4.
        apply validRegsMetaMeth_validRegsDms in H5.
        simpl in H4, H5.
        repeat constructor; auto.
    - intros.
      unfold ValidRegsMetaModule in H.
      destruct m as [regs rules dms]; simpl in *.
      dest.
      split.
      + clear -H; induction rules; [constructor|]; inv H.
        simpl in *; apply validRegsRules_app; auto.
        apply validRegsMetaRule_validRegsRules; auto.
      + clear -H0; induction dms; [constructor|]; inv H0.
        simpl; apply validRegsDms_app; auto.
        apply validRegsMetaMeth_validRegsDms; auto.
    - intros; simpl in *; dest.
      tauto.
    - simpl; intros; dest.
      unfold ValidRegsMetaModule in *.
      clear - H H0.
      induction ls; simpl; auto; [split; constructor |].
      repeat split; unfold namesOf; rewrite ?map_map; simpl in *; auto; clear - H H0; unfold getActionFromGen, getMethFromGen; simpl.
      + apply validSinRegsSinRules_validRegsRules; auto.
      + apply validSinRegsSinMeths_validRegsDms; auto.
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
      ValidRegsMetaModule ty (mm1) ->
      ValidRegsMetaModule ty (mm2) ->
      ValidRegsMetaModule ty ((mm1 +++ mm2)).
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

