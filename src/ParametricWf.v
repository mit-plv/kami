Require Import Bool List String Structures.Equalities.
Require Import Lib.Struct Lib.Word Lib.CommonTactics.
Require Import Lib.StringBound Lib.ilist Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.SemanticsExprAction Lts.Semantics Lts.Equiv Lts.Wf.
Require Import Lts.ParametricSyntax.
Require Import FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.

Set Implicit Arguments.

(* Well-formedness w.r.t. valid register uses (read/writes) *)
Section ValidRegs.
  Variable type: Kind -> Type.

  Section Regs.
    Variable regs: list NameRecIdx.

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
        forall {retT} reg k cont,
          In {| isRep:= false; nameRec:= reg |} regs ->
          (forall t, ValidRegsSinAction (cont t)) ->
          ValidRegsSinAction (SReadReg (lretT:= retT) reg k cont)
    | SVRWriteReg:
        forall {writeT retT} reg e cont,
          In {| isRep:= false; nameRec:= reg|} regs ->
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
      Variable genK: Kind.

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
      | GVRReadReg:
          forall {retT} reg k cont,
            In reg regs ->
            (forall t, ValidRegsGenAction (cont t)) ->
            ValidRegsGenAction (GReadReg (lretT:= retT) reg k cont)
      | GVRWriteReg:
          forall {writeT retT} reg e cont,
            In reg regs ->
            ValidRegsGenAction cont ->
            ValidRegsGenAction (GWriteReg (k:= writeT) (lretT:= retT)
                                          reg e cont)
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
      | RepRule _ _ _ _ _ _ r _ _ _ => ValidRegsGenAction (r type)
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
      | RepMeth _ _ _ _ _ _ d _ _ _ => forall v, ValidRegsGenAction (projT2 d type v)
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

  Definition getMetaRegNameIdx m :=
    match m with
    | OneReg b s => {| isRep:= false; nameRec:= s |}
    | RepReg _ _ _ _ _ s _ _ => {| isRep:= true; nameRec:= s |}
    end.

  Fixpoint ValidRegsMetaModule (mm: MetaModule): Prop :=
    ValidRegsMetaRules (map getMetaRegNameIdx (metaRegs mm)) (metaRules mm) /\
    ValidRegsMetaMeths (map getMetaRegNameIdx (metaRegs mm)) (metaMeths mm).

End ValidRegs.

Section Facts.

  Lemma validRegsMetaModule_validRegsModules:
    forall ty mm,
      ValidRegsMetaModule ty mm ->
      ValidRegsModules ty (modFromMeta mm).
  Proof.
    destruct mm as [regs rules dms]; simpl; intros; dest; split.
    - clear -H; induction rules; [constructor|]; inv H.
      simpl; apply validRegsRules_app; auto.
      admit.
    - clear -H0; induction dms; [constructor|]; inv H0.
      simpl; apply validRegsDms_app; auto.
      admit.
  Qed.
  
  Lemma validRegsMetaModule_modular:
    forall ty mm1 mm2,
      ValidRegsMetaModule ty mm1 ->
      ValidRegsMetaModule ty mm2 ->
      ValidRegsMetaModule ty (mm1 +++ mm2).
  Proof.
    destruct mm1 as [regs1 rules1 dms1], mm2 as [regs2 rules2 dms2].
    simpl; intros; dest; split; admit.
  Qed.

End Facts.

