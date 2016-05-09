Require Import Syntax Wf Struct List Inline SimpleInline Coq.Arith.Peano_dec Lib.Indexer
FunctionalExtensionality.

Set Implicit Arguments.

Fixpoint getList A (f: nat -> A) n :=
  match n with
    | 0 => nil
    | S m => f m :: getList f m
  end.

Fixpoint concat A (l: list (list A)) :=
  match l with
    | x :: xs => x ++ concat xs
    | nil => nil
  end.

Inductive MetaRegs :=
| OneReg (_: RegInitT)
| RepeatReg (_: nat -> RegInitT) (_: nat).

Fixpoint getRegsFromMeta (mr: MetaRegs) :=
  match mr with
    | OneReg r => r :: nil
    | RepeatReg fr n => getList fr n
  end.

Inductive MetaRules :=
| OneRule (_: Attribute (Action Void))
| RepeatRule (_: nat -> Attribute (Action Void)) (_: nat).

Fixpoint getRulesFromMeta (mr: MetaRules) :=
  match mr with
    | OneRule r => r :: nil
    | RepeatRule fr n => getList fr n
  end.

Inductive MetaMeths :=
| OneMeth (_: DefMethT)
| RepeatMeth (_: nat -> DefMethT) (_: nat).

Fixpoint getMethsFromMeta (mr: MetaMeths) :=
  match mr with
    | OneMeth r => r :: nil
    | RepeatMeth fr n => getList fr n
  end.

Record MetaModule :=
  { metaRegs: list MetaRegs;
    metaRules: list MetaRules;
    metaMeths: list MetaMeths
  }.

Fixpoint makeModule (mm: MetaModule) :=
  match mm with
    | {| metaRegs := regs; metaRules := rules; metaMeths := meths |} =>
      Mod (concat (map getRegsFromMeta regs)) (concat (map getRulesFromMeta rules))
          (concat (map getMethsFromMeta meths))
  end.

Definition metaInlineDmToRule (inDm: MetaMeths) (r': MetaRules) :=
  match r', inDm with
    | OneRule r, OneMeth dm => OneRule (inlineDmToRule r dm) :: nil
    | RepeatRule fr n, RepeatMeth ff m =>
      match eq_nat_dec n m with
        | left _ => RepeatRule (fun i => inlineDmToRule (fr i) (ff i)) n :: nil
        | right _ => map OneRule (fold_left inlineDmToRules (getMethsFromMeta inDm)
                                            (getRulesFromMeta r'))
      end
    | RepeatRule fr n, OneMeth dm => RepeatRule (fun i => inlineDmToRule (fr i) dm) n :: nil
    | OneRule r, RepeatMeth ff m => OneRule (fold_left inlineDmToRule (getMethsFromMeta inDm) r) :: nil
  end.

Lemma commuteInline:
  forall rules meths,
    fold_left inlineDmToRules meths rules =
    map (fun rule => fold_left inlineDmToRule meths rule) rules.
Proof.
  induction rules; simpl in *; intros.
  - induction meths; simpl in *.
    + reflexivity.
    + assumption.
  - specialize (IHrules meths).
    rewrite <- IHrules.
    clear IHrules.
    generalize a rules; clear.
    induction meths; simpl in *; intros.
    + reflexivity.
    + specialize (IHmeths (inlineDmToRule a0 a) (inlineDmToRules rules a)).
      assumption.
Qed.

Section NoBadCalls.
  Variable noBadCalls:
    forall (fr: nat -> Attribute (Action Void)) i s j,
        In (s __ j) (getCallsA (attrType (fr i) typeUT)) -> i = j.

  Lemma onlyOneInline:
    forall fr n ff,
      (fun i => inlineDmToRule (fr i) (ff i)) =
      fun i => fold_left inlineDmToRule (getList ff n) (fr i).
  Proof.
    intros; extensionality i.
    admit.
  Qed.

  Lemma metaInlineDmToRule_matches inDm r:
    concat (map getRulesFromMeta (metaInlineDmToRule inDm r)) =
    fold_left inlineDmToRules (getMethsFromMeta inDm) (getRulesFromMeta r).
  Proof.
    unfold metaInlineDmToRule.
    destruct inDm, r; subst; auto; simpl in *.
    - clear noBadCalls; rewrite app_nil_r.
      induction n; simpl in *.
      + intuition.
      + f_equal.
        intuition.
    - clear noBadCalls; generalize a; clear a.
      induction (getList d n); simpl in *; intros.
      + reflexivity.
      + apply (IHl (inlineDmToRule a0 a)).
    - destruct (eq_nat_dec n0 n); subst; simpl in *.
      specialize (@noBadCalls a).
      + rewrite app_nil_r.
        rewrite commuteInline.
        rewrite onlyOneInline with (n:=n).
        generalize (getList d n); clear d.
        induction n; intros; simpl in *.
        * reflexivity.
        * f_equal.
          apply IHn.
      + clear.
        induction (fold_left inlineDmToRules (getList d n) (getList a n0)); simpl in *.
        * reflexivity.
        * f_equal; assumption.
  Qed.
End NoBadCalls.

Definition metaInlineDmToDm (inDm: MetaMeths) (g': MetaMeths) :=
  match g', inDm with
    | OneMeth g, OneMeth dm => OneMeth (inlineDmToDm g dm) :: nil
    | RepeatMeth fg n, RepeatMeth ff m =>
      match eq_nat_dec n m with
        | left _ => RepeatMeth (fun i => inlineDmToDm (fg i) (ff i)) n :: nil
        | right _ => map OneMeth (fold_left inlineDmToDms (getMethsFromMeta inDm)
                                            (getMethsFromMeta g'))
      end
    | RepeatMeth fg n, OneMeth dm => RepeatMeth (fun i => inlineDmToDm (fg i) dm) n :: nil
    | OneMeth g, RepeatMeth ff m => OneMeth (fold_left inlineDmToDm (getMethsFromMeta inDm) g) :: nil
  end.

Definition metaInlineDmToMod (inDm: MetaMeths) (mm: MetaModule) :=
  match mm with
    | {| metaRegs := regs; metaRules := rules; metaMeths := meths |} =>
      {| metaRegs := regs; metaRules := concat (map (metaInlineDmToRule inDm) rules);
         metaMeths := concat (map (metaInlineDmToDm inDm) meths) |}
  end.

Fixpoint metaInlineDmsToMod (inDms: list MetaMeths) (mm: MetaModule) :=
  match inDms with
    | x :: xs => metaInlineDmsToMod xs (metaInlineDmToMod x mm)
    | nil => mm
  end.

Definition metaInline (mm: MetaModule) :=
  metaInlineDmsToMod (metaMeths mm) mm.

Fixpoint metaMethNames i dms :=
  match dms with
    | nil => nil
    | x :: xs =>
      match x with
        | OneMeth g => attrName g
        | RepeatMeth fg n => attrName (fg i)
      end :: metaMethNames i xs
  end.

Definition getCallsMetaMeth i dm :=
  match dm with
    | OneMeth g => getCallsA (projT2 (attrType g) typeUT tt)
    | RepeatMeth fg n => getCallsA (projT2 (attrType (fg i)) typeUT tt)
  end.

Fixpoint getCallsMetaMeths i dms :=
  match dms with
    | nil => nil
    | x :: xs => getCallsMetaMeth i x ++ getCallsMetaMeths i xs
  end.

Definition notCalledInMetaDms dms :=
  forall name i dm dmBody, In dm dms -> In name (metaMethNames i dms) ->
                           In name (getCallsMetaMeths i dmBody) -> False.

Section MetaModule.
  Lemma metaInline_matches m:
    makeModule (metaInline m) = simpleInline (makeModule m).
  Proof.
    unfold metaInline.
    admit.
  Qed.
End MetaModule.
