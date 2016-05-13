<<<<<<< HEAD
Require Import Syntax Wf Struct List Inline SimpleInline Coq.Arith.Peano_dec Lib.Indexer
        FunctionalExtensionality String Equiv Program.Equality Lib.FMap CommonTactics StringEq
        InlineFacts_2.
=======
Require Import Coq.Arith.Peano_dec String List.
Require Import Lib.Indexer Lib.Struct.
Require Import Lts.Syntax Lts.Wf Lts.Equiv Lts.Inline Lts.SimpleInline.
Require Import FunctionalExtensionality Program.Equality.
>>>>>>> e91b1e23d67ee94f7e9eaeba1324ba79dee21644

Set Implicit Arguments.

Fixpoint concat A (ls: list (list A)) :=
  match ls with
    | x :: xs => x ++ concat xs
    | nil => nil
  end.

Section MetaDefns.
  Variable A: Type.

  Inductive MetaDefn :=
  | One (_: Attribute A)
  | Rep (_: string) (_: nat -> A) (_: nat).

  Fixpoint getListFromRep s (f: nat -> A) n :=
    {| attrName := s __ n;
       attrType := f n |} :: match n with
                               | 0 => nil
                               | S i => getListFromRep s f i
                             end.

  Definition getListFromMeta m :=
    match m with
      | One a => a :: nil
      | Rep s f n => getListFromRep s f n
    end.
  
  Fixpoint getFullListFromMeta m  :=
    match m with
      | x :: xs => getListFromMeta x ++ getFullListFromMeta xs
      | nil => nil
    end.

  Lemma getFullListFromMeta_app m1: forall m2, getFullListFromMeta (m1 ++ m2) =
                                               getFullListFromMeta m1 ++ getFullListFromMeta m2.
  Proof.
    induction m1; intros.
    - reflexivity.
    - simpl.
      rewrite <- app_assoc.
      f_equal.
      apply IHm1; intuition.
  Qed.
  
  Fixpoint getNamesOfMeta m :=
    match m with
      | One a => attrName a
      | Rep s _ _ => s
    end.
End MetaDefns.

Definition MetaReg := MetaDefn (sigT ConstFullT).

Definition MetaRule := MetaDefn (Action Void).

Definition MetaMeth := MetaDefn (sigT MethodT).

Record MetaModule :=
  { metaRegs: list MetaReg;
    metaRules: list MetaRule;
    metaMeths: list MetaMeth
  }.

Definition makeModule (m: MetaModule) :=
  Mod (getFullListFromMeta (metaRegs m))
      (getFullListFromMeta (metaRules m))
      (getFullListFromMeta (metaMeths m)).

Definition metaInlineDmToRule (inDm: MetaMeth) (r': MetaRule) :=
  match r', inDm with
    | One r, One dm => One (inlineDmToRule r dm) :: nil
    | Rep sr fr n, Rep sf ff m =>
      match eq_nat_dec n m with
        | left _ => Rep sr (fun i ty => inlineDm (fr i ty) {| attrName := sf __ i;
                                                              attrType := ff i |}) n :: nil
        | right _ => map (@One _) (fold_left inlineDmToRules (getListFromMeta inDm)
                                             (getListFromMeta r'))
      end
    | Rep sr fr n, One dm => Rep sr (fun i ty => inlineDm (fr i ty) dm) n :: nil
    | One r, Rep sf ff m => One (fold_left inlineDmToRule (getListFromMeta inDm) r) :: nil
  end.

Definition metaInlineDmToDm (inDm: MetaMeth) (g': MetaMeth) :=
  match g', inDm with
    | One g, One dm => One (inlineDmToDm g dm) :: nil
    | Rep sg fg n, Rep sf ff m =>
      match eq_nat_dec n m with
        | left _ =>
          Rep sg (fun i =>
                    existT MethodT (projT1 (fg i))
                           (fun ty argv =>
                              inlineDm (projT2 (fg i) ty argv)
                                       {| attrName := sf __ i;
                                          attrType := ff i |})) n :: nil
        | right _ => map (@One _) (fold_left inlineDmToDms (getListFromMeta inDm)
                                             (getListFromMeta g'))
      end
    | Rep sg fg n, One dm =>
      Rep sg (fun i =>
                existT MethodT (projT1 (fg i))
                       (fun ty argv =>
                          inlineDm (projT2 (fg i) ty argv) dm)) n :: nil
    | One g, Rep sf ff m => One (fold_left inlineDmToDm (getListFromMeta inDm) g) :: nil
  end.

Lemma commuteInlineDmRules:
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

Lemma commuteInlineDmMeths:
  forall rs meths,
    fold_left inlineDmToDms meths rs =
    map (fun r => fold_left inlineDmToDm meths r) rs.
Proof.
  induction rs; simpl in *; intros.
  - induction meths; simpl in *.
    + reflexivity.
    + assumption.
  - specialize (IHrs meths).
    rewrite <- IHrs.
    clear IHrs.
    generalize a rs; clear.
    induction meths; simpl in *; intros.
    + reflexivity.
    + specialize (IHmeths (inlineDmToDm a0 a) (inlineDmToDms rs a)).
      assumption.
Qed.

Definition metaRuleEquiv (t1 t2: Kind -> Type) (r: MetaRule) : Prop :=
  match r with
    | One r' => forall G,
                  ActionEquiv G (attrType r' t1) (attrType r' t2)
    | Rep s f n => forall i G, ActionEquiv G (f i t1) (f i t2)
  end.

Definition metaMethEquiv (t1 t2: Kind -> Type) (f: MetaMeth) : Prop :=
  match f with
    | One g => forall (argV1: fullType t1 (SyntaxKind (arg (projT1 (attrType g)))))
                      (argV2: fullType t2 (SyntaxKind (arg (projT1 (attrType g))))) G,
                 ActionEquiv (vars argV1 argV2 :: G)
                             (projT2 (attrType g) t1 argV1)
                             (projT2 (attrType g) t2 argV2)
    | Rep s g n => forall i
                          (argV1: fullType t1 (SyntaxKind (arg (projT1 (g i)))))
                          (argV2: fullType t2 (SyntaxKind (arg (projT1 (g i))))) G,
                     ActionEquiv (vars argV1 argV2 :: G)
                                 (projT2 (g i) t1 argV1)
                                 (projT2 (g i) t2 argV2)
  end.

Lemma getFullListFromMetaCommute A (ls: list (Attribute A)):
  getFullListFromMeta (map (@One _) ls) = ls.
Proof.
  induction ls; simpl in *.
  - reflexivity.
  - f_equal; assumption.
Qed.

Definition getCallsMAction (dm: sigT MethodT) :=
  getCallsA (projT2 dm typeUT tt).


Section NoBadCalls.
  Variable inDm: MetaMeth.
  Variable r: MetaRule.
  Variable r': MetaMeth.
  Variable inDmEquiv: forall ty, metaMethEquiv ty typeUT inDm.
  Variable rEquiv: forall ty, metaRuleEquiv ty typeUT r.
  Variable rEquiv': forall ty, metaMethEquiv ty typeUT r'.

  Variable noBadCallsInDm:
    forall sr fr n , inDm = Rep sr fr n ->
                     forall s i j,
                       In (s __ j) (getCallsMAction (fr i)) ->
                       i = j.

  Variable noBadCallsInR:
    forall sr fr n , r = Rep sr fr n  ->
                     forall s i j,
                       In (s __ j) (getCallsA (fr i typeUT)) ->
                       i = j.

  Variable noBadCallsInR':
    forall sr fr n , r' = Rep sr fr n  ->
                     forall s i j,
                       In (s __ j) (getCallsMAction (fr i)) ->
                       i = j.

  Section AboutAttribute.
    Variable A B: Type.
    Variable ls: list B.
    Variable f: A -> B -> A.
    Lemma fold_left_attr:
      forall init,
        {| attrName := attrName init;
           attrType := fold_left f ls (attrType init) |} =
        fold_left (fun a b => {| attrName := attrName a;
                                 attrType := f (attrType a) b |}) ls init.
    Proof.
      clear - A B ls f.
      induction ls; simpl in *; intros.
      - destruct init; reflexivity.
      - specialize (IHl (attrName init :: f (attrType init) a)%struct).
        intuition.
    Qed.
  End AboutAttribute.

  Lemma singleInlineR:
    forall sr fr sg fg n,
      r = Rep sr fr n ->
      inDm = Rep sg fg n ->
      getListFromRep
        sr (fun (i : nat) (ty : Kind -> Type) =>
              inlineDm (fr i ty) (sg __ i :: fg i)%struct) n =
      map
        (fun rule : Attribute (Action Void) =>
           fold_left inlineDmToRule (getListFromRep sg fg n) rule)
        (getListFromRep sr fr n).
  Proof.
    intros.
    unfold metaMethEquiv, metaRuleEquiv in *.
    specialize (noBadCallsInDm H0).
    specialize (noBadCallsInR H).
    subst; simpl in *.
    clear noBadCallsInR' rEquiv' r'.
    induction n; simpl in *; intros.
    - reflexivity.
    - f_equal; simpl in *.
      + simpl in *.
        rewrite inlineNoCallsRule_matches with (dms := getListFromRep sg fg n); simpl in *.
        reflexivity.
        intros.
        apply inlineDm_ActionEquiv; simpl in *; intros.
        apply inDmEquiv.
        apply rEquiv.
        intros.
        pose proof (inlineDm_calls _ _ (in_eq (sg __ (S n) :: fg (S n))%struct nil)
                                   (fr (S n) typeUT) (attrName dm) H0).
        apply in_app_or in H1; simpl in H1.
        rewrite app_nil_r in H1.
        fold (getCallsMAction (fg (S n))) in H1.
        clear H0 IHn inDmEquiv rEquiv.
        assert (sth: exists s i, attrName dm = s __ i /\ i <= n).
        { clear - H.
          induction n; simpl in *; intros; destruct dm; simpl in *.
          - destruct H.
            + inversion H.
              exists sg, 0.
              intuition.
            + intuition.
          - destruct H.
            + inversion H.
              exists sg, (S n).
              intuition.
            + intuition.
              dest.
              exists x, x0; intuition omega.
        }
        destruct sth as [s [i [si ilen]]].
        rewrite si in H1.
        specialize (@noBadCallsInDm s (S n) i).
        specialize (@noBadCallsInR s (S n) i).
        destruct H1; intuition omega.
      + rewrite IHn.
        clear IHn.
        assert (H: forall rule, In rule (getListFromRep sr fr n) ->
                                inlineDmToRule rule (sg __ (S n) :: fg (S n))%struct = rule).
        { intros.
          assert (exists i, i <= n /\ rule = sr __ i :: fr i)%struct.
          { clear - H.
            induction n; simpl in *.
            - destruct H; eexists; eauto; intuition.
            - destruct H.
              + exists (S n); intuition.
              + specialize (IHn H).
                dest.
                exists x; intuition omega.
          }
          destruct rule;
            unfold inlineDmToRule; simpl in *; f_equal.
          destruct H0.
          extensionality ty; intros.
          specialize (rEquiv ty x nil).
          apply inlineNoCallAction_matches with (c := nil) (aUT := fr x typeUT); simpl in *.
          unfold not; intros.
          specialize (@noBadCallsInR sg x (S n) H1).
          dest; omega.
          dest.
          inversion H1.
          subst.
          assumption.
        }
        clear - H.
        { induction (getListFromRep sr fr n); simpl in *.
          - reflexivity.
          - f_equal.
            assert (inlineDmToRule a (sg __ (S n) :: fg (S n))%struct = a)
              by (specialize (H a); intuition).
            rewrite H0.
            reflexivity.
            assert (forall rule, In rule l ->
                                 inlineDmToRule rule (sg __ (S n) :: fg (S n))%struct = rule)
              by (intros; specialize (H rule); intuition).
            apply IHl; auto.
        }
        Grab Existential Variables.
        intuition.
  Qed.

  Lemma singleInlineR':
    forall sr fr sg fg n,
      r' = Rep sr fr n ->
      inDm = Rep sg fg n ->
      getListFromRep
        sr (fun (i : nat) =>
              existT MethodT (projT1 (fr i))
                     (fun ty argv =>
                        inlineDm (projT2 (fr i) ty argv) (sg __ i :: fg i)%struct)) n =
      map
        (fun rule : DefMethT =>
           fold_left inlineDmToDm (getListFromRep sg fg n) rule)
        (getListFromRep sr fr n).
  Proof.
    intros.
    unfold metaMethEquiv, metaRuleEquiv in *.
    specialize (noBadCallsInDm H0).
    specialize (noBadCallsInR' H).
    subst; simpl in *.
    clear noBadCallsInR rEquiv r.
    induction n; simpl in *; intros.
    - reflexivity.
    - f_equal; simpl in *.
      + simpl in *.
        rewrite inlineNoCallsMeth_matches with (dms := getListFromRep sg fg n); simpl in *.
        reflexivity.
        intros.
        apply inlineDm_ActionEquiv; simpl in *; intros.
        apply inDmEquiv.
        apply rEquiv'.
        intros.
        pose proof (inlineDm_calls _ _ (in_eq (sg __ (S n) :: fg (S n))%struct nil)
                                   (projT2 (fr (S n)) typeUT tt) (attrName dm) H0).
        apply in_app_or in H1; simpl in H1.
        rewrite app_nil_r in H1.
        fold (getCallsMAction (fg (S n))) in H1.
        clear H0 IHn inDmEquiv rEquiv'.
        assert (sth: exists s i, attrName dm = s __ i /\ i <= n).
        { clear - H.
          induction n; simpl in *; intros; destruct dm; simpl in *.
          - destruct H.
            + inversion H.
              exists sg, 0.
              intuition.
            + intuition.
          - destruct H.
            + inversion H.
              exists sg, (S n).
              intuition.
            + intuition.
              dest.
              exists x, x0; intuition omega.
        }
        destruct sth as [s [i [si ilen]]].
        rewrite si in H1.
        specialize (@noBadCallsInDm s (S n) i).
        specialize (@noBadCallsInR' s (S n) i).
        destruct H1; intuition omega.
      + rewrite IHn.
        clear IHn.
        assert (H: forall rule, In rule (getListFromRep sr fr n) ->
                                inlineDmToDm rule (sg __ (S n) :: fg (S n))%struct = rule).
        { intros.
          assert (exists i, i <= n /\ rule = sr __ i :: fr i)%struct.
          { clear - H.
            induction n; simpl in *.
            - destruct H; eexists; eauto; intuition.
            - destruct H.
              + exists (S n); intuition.
              + specialize (IHn H).
                dest.
                exists x; intuition omega.
          }
          destruct rule;
            unfold inlineDmToDm; simpl in *; f_equal.
          destruct H0.
          destruct attrType; f_equal.
          extensionality ty; extensionality argv; intros.
          simpl in *.
          pose (tt: fullType typeUT (SyntaxKind (arg x0))) as f.
          pose (argv: fullType ty (SyntaxKind (arg x0))) as f0.
          destruct H0.
          inversion H1.
          assert (x0 = projT1 (fr x)) by (rewrite <- H4; reflexivity).
          specialize (rEquiv' ty x).
          rewrite <- H4 in rEquiv'; simpl in *.
          specialize (rEquiv' argv f nil).
          eapply inlineNoCallAction_matches with
            (aUT := m typeUT tt); simpl in *; eauto.
          unfold not; intros.
          unfold getCallsMAction in noBadCallsInR'.
          specialize (@noBadCallsInR' sg x (S n)).
          simpl in *.
          rewrite <- H4 in noBadCallsInR'; simpl in *.
          specialize (@noBadCallsInR' H5).
          omega.
        }
        clear - H.
        { induction (getListFromRep sr fr n); simpl in *.
          - reflexivity.
          - f_equal.
            assert (inlineDmToDm a (sg __ (S n) :: fg (S n))%struct = a)
              by (specialize (H a); intuition).
            rewrite H0.
            reflexivity.
            assert (forall rule, In rule l ->
                                 inlineDmToDm rule (sg __ (S n) :: fg (S n))%struct = rule)
              by (intros; specialize (H rule); intuition).
            apply IHl; auto.
        }
        Grab Existential Variables.
        intuition.
  Qed.

  Lemma metaInlineDmToRule_matches:
    getFullListFromMeta (metaInlineDmToRule inDm r) =
    fold_left inlineDmToRules (getListFromMeta inDm) (getListFromMeta r).
  Proof.
    intros.
    unfold metaInlineDmToRule.
    case_eq inDm; case_eq r; intros; auto; simpl in *.
    - clear; rewrite app_nil_r.
      induction n; simpl in *.
      + intuition.
      + f_equal.
        intuition.
    - clear; generalize a; clear a.
      induction (getListFromRep s s0 n); simpl in *; intros.
      + reflexivity.
      + apply (IHl (inlineDmToRule a0 a)).
    - destruct (eq_nat_dec n n0); simpl in *.
      rewrite e in *; clear e.
      specialize (@noBadCallsInR s a n0 H).
      + rewrite app_nil_r.
        rewrite commuteInlineDmRules; simpl in *.
        apply singleInlineR; auto.
      + clear.
        induction (fold_left inlineDmToRules (getListFromRep s0 s1 n0)
                             (getListFromRep s a n)); simpl in *.
        * reflexivity.
        * f_equal; assumption.
  Qed.

  Lemma metaInlineDmToDm_matches:
    getFullListFromMeta (metaInlineDmToDm inDm r') =
    fold_left inlineDmToDms (getListFromMeta inDm) (getListFromMeta r').
  Proof.
    intros.
    unfold metaInlineDmToDm.
    case_eq inDm; case_eq r'; intros; auto; simpl in *.
    - clear; rewrite app_nil_r.
      induction n; simpl in *.
      + intuition.
      + f_equal.
        intuition.
    - clear; generalize a; clear a.
      induction (getListFromRep s s0 n); simpl in *; intros.
      + reflexivity.
      + apply (IHl (inlineDmToDm a0 a)).
    - destruct (eq_nat_dec n n0); simpl in *.
      rewrite e in *; clear e.
      specialize (@noBadCallsInR' s s0 n); simpl in *.
      + rewrite app_nil_r.
        rewrite commuteInlineDmMeths; simpl in *.
        apply singleInlineR'; auto.
      + clear.
        induction (fold_left inlineDmToDms (getListFromRep s s0 n)
                             (getListFromRep s1 s2 n)); simpl in *.
        * rewrite commuteInlineDmMeths; simpl in *.
          rewrite getFullListFromMetaCommute.
          reflexivity.
        * assumption.
  Qed.
End NoBadCalls.

Definition metaInlineDmToMod m inDm :=
    {| metaRegs := metaRegs m;
       metaRules := concat (map (metaInlineDmToRule inDm) (metaRules m));
       metaMeths := concat (map (metaInlineDmToDm inDm) (metaMeths m)) |}.

Lemma metaInlineDmToRules_matches (rules: list MetaRule) :
  forall a
         (aEquiv: forall ty, metaMethEquiv ty typeUT a),
    (forall sr fr n , a = Rep sr fr n ->
                      forall s i j,
                        In (s __ j) (getCallsMAction (fr i)) ->
                        i = j) ->
    (forall r, In r rules -> forall ty, metaRuleEquiv ty typeUT r) ->
    (forall sr fr n, In (Rep sr fr n) rules ->
                     forall s i j,
                       In (s __ j) (getCallsA (fr i typeUT)) ->
                       i = j) ->
    getFullListFromMeta (concat (map (metaInlineDmToRule a) rules)) =
    fold_left inlineDmToRules (getListFromMeta a)
              (getFullListFromMeta rules).
Proof.
  dependent induction rules; simpl in *; intros.
  - clear; induction (getListFromMeta a); simpl in *; auto.
  - rewrite commuteInlineDmRules.
    rewrite map_app.
    rewrite <- !commuteInlineDmRules.
    rewrite getFullListFromMeta_app.
    f_equal.
    apply metaInlineDmToRule_matches with (r := a); auto; intros.
    eapply H1; eauto.
    eapply IHrules; eauto.
Qed.

Lemma metaInlineDmToDms_matches (rules: list MetaMeth) :
  forall a
         (aEquiv: forall ty, metaMethEquiv ty typeUT a),
    (forall sr fr n , a = Rep sr fr n ->
                      forall s i j,
                        In (s __ j) (getCallsMAction (fr i)) ->
                        i = j) ->
    (forall r, In r rules -> forall ty, metaMethEquiv ty typeUT r) ->
    (forall sr fr n , In (Rep sr fr n) rules ->
                      forall s i j,
                        In (s __ j) (getCallsMAction (fr i)) ->
                        i = j) ->
    getFullListFromMeta (concat (map (metaInlineDmToDm a) rules)) =
    fold_left inlineDmToDms (getListFromMeta a)
              (getFullListFromMeta rules).
Proof.
  dependent induction rules; simpl in *; intros.
  - clear; induction (getListFromMeta a); simpl in *; auto.
  - rewrite commuteInlineDmMeths.
    rewrite map_app.
    rewrite <- !commuteInlineDmMeths.
    rewrite getFullListFromMeta_app.
    f_equal.
    apply metaInlineDmToDm_matches with (r' := a); auto; intros.
    eapply H1; eauto.
    eapply IHrules; eauto.
Qed.

Fixpoint metaInlineDmsToMod m (inDms: list MetaMeth) :=
  match inDms with
    | x :: xs => metaInlineDmsToMod (metaInlineDmToMod m x) xs
    | nil => m
  end.

Definition metaInline m :=
  metaInlineDmsToMod m (metaMeths m).

Lemma simpleInlineDmsToMod_app dms1:
  forall dms2 regs rules meths,
    simpleInlineDmsToMod (Mod regs rules meths) (dms1 ++ dms2) =
    simpleInlineDmsToMod (simpleInlineDmsToMod (Mod regs rules meths) dms1) dms2.
Proof.
  induction dms1; simpl in *; intros.
  - intuition.
  - specialize (IHdms1 dms2).
    unfold simpleInlineDmToMod at 1.
    simpl in *.
    specialize (@IHdms1 regs (inlineDmToRules rules a) meths).
    assumption.
Qed.

Lemma inlineDmsInMod_app dms1:
  forall dms2 regs rules meths,
    inlineDmsInMod (Mod regs rules meths) (dms1 ++ dms2) =
    inlineDmsInMod (inlineDmsInMod (Mod regs rules meths) dms1) dms2.
Proof.
  induction dms1; simpl in *; intros.
  - intuition.
  - specialize (IHdms1 dms2).
    unfold inlineDmsInMod in *; simpl in *.
    apply IHdms1.
Qed.

(*
Section MetaModule.
  Lemma metaInline_matches dms:
    forall m,
      SubList dms (metaMeths m) ->
      (forall dm ty, In dm (metaMeths m) -> metaMethEquiv ty typeUT dm) ->
      (forall dm1 dm2, In dm1 (metaMeths m) -> In dm2 (metaMeths m) ->
                       In (attrName dm1) (getCallsMAction (attrType dm2))) ->
      (forall sr fr n, In (Rep sr fr n) (metaRules m) ->
                       forall s i j,
                         In (s __ j) (getCallsA (fr i typeUT)) ->
                         i = j) ->
      (forall sr fr n, In (Rep sr fr n) (metaMeths m) ->
                       forall s i j,
                         In (s __ j) (getCallsMAction (fr i)) ->
                         i = j) ->
      (forall r, In r (metaRules m) -> forall ty, metaRuleEquiv ty typeUT r) ->
      (forall dm, In dm (metaMeths m) -> forall ty, metaMethEquiv ty typeUT dm) ->
      makeModule (metaInlineDmsToMod m dms) =
      inlineDmsInMod (makeModule m) (getFullListFromMeta dms).
  Proof.
    unfold makeModule; simpl in *.
    induction dms; simpl in *; intros; auto.
    rewrite inlineDmsInMod_app; simpl in *.
    specialize (IHdms (metaInlineDmToMod m a)); simpl in *.
    rewrite IHdms.
    - f_equal.
      unfold inlineDmsInMod; simpl in *.
      f_equal.           (mEquiv: forall ),

      apply metaInlineDmToRules_matches; auto.
      unfold SubList in H; specialize (H a); simpl in H.
      assert (In a (metaMeths m)) by intuition.
      eapply H3; eauto.
      intros.
      rewrite H4 in H.
      assert (In (Rep sr fr n) (metaMeths m)) by intuition.
      eapply H1; eauto.
      apply metaInlineDmToDms_matches; auto.
      assert (In a (metaMeths m)) by intuition.
      eapply H3; eauto.
      intros.
      rewrite H4 in H.
      assert (In (Rep sr fr n) (metaMeths m)) by intuition.
      eapply H1; eauto.
    - 
    - admit.
    - clear IHdms dms; intros.
      intros.
      destruct a; simpl in *.
      remember (metaRules m) as sth.
      remember (metaMeths m) as nth.
      clear Heqsth Heqnth m.
      induction sth; simpl in *.
      + intuition.
      + assert (sth1:
                  forall sr fr n,
                    In (Rep sr fr n) sth ->
                    forall s i j, In (s __ j) (getCallsA (fr i typeUT)) -> i = j).
        { intros.
          specialize (H sr0 fr0 n0).
          specialize (H (or_intror H3)). admit.
    
          specialize (H s0 i0 j0 H4).
          intuition.
        }
        specialize (IHsth sth1).
        assert (sth2:
                  forall sr fr n,
                    a0 = Rep sr fr n ->
                    forall s i j, In (s __ j) (getCallsA (fr i typeUT)) -> i = j).
        { intros.
          specialize (H sr0 fr0 n0).
          specialize (H (or_introl H3)).
          specialize (H s0 i0 j0 H4).
          intuition.
        }
        apply in_app_or in H1.
        unfold metaInlineDmToRule in H1 at 1; simpl in *.
        destruct H1; [|apply IHsth; assumption].
        destruct a0; simpl in *.
        destruct H1; [discriminate| intuition].
        destruct H1; [| intuition].
        inversion H1; subst; clear H1.
        specialize (H sr fr n).
        specialize (H (or_introl eq_refl)).
        clear sth1 IHsth.
        inversion H0; subst.
        specialize (sth2 sr a0 n).
        apply eq_sym in H0; inversion H0; subst.
        inversion H0; subst.
        
        specialize (sth2 sr fr n).
        destruct H1; [try discriminate; intuition|].
        discriminate.
        apply IHsth; assumption.
        
        unfold metaInlineDmToRule in H0; simpl in *.
        simpl in *.
        specialize (sth1 _ _ _ 
        destruct H1.
        unfold metaInlineDmToRule in H0; simpl in *.
        destruct a0; simpl in *.
        destruct H0; try discriminate; intuition.
        specialize (sth3 _ _ _ eq_refl s i j).
        inversion H0; subst.
        destruct H0.
        inversion H0.
        inversion H0; subst.
        
          try match goal with
                           | [H: False |- _] => apply H
                         end.
        simpl in H0.
        specialize (sth3 sr fr n 
        apply IHsth.
        apply in_app_or in H1.
        specialize (
          (or_intror H0)).
        admit.
    - intros.
      admit.
  Qed.

  Variable m: MetaModule.
  Variable rulesEquiv: forall ty r, In r (metaRules m) -> metaRuleEquiv ty typeUT r.
  Variable methsEquiv: forall ty f, In f (metaMeths m) -> metaMethEquiv ty typeUT f.

  Variable noBadCallsInRules:
    forall sr fr n , In (Rep sr fr n) (metaRules m) ->
                     forall s i j,
                       In (s __ j) (getCallsA (fr i typeUT)) ->
                       i = j.

  Variable noBadCallsInMeths:
    forall sr fr n , In (Rep sr fr n) (metaMeths m) ->
                     forall s i j,
                       In (s __ j) (getCallsMAction (fr i)) ->
                       i = j.

  Variable noOneInteralCallsInRepMeth:
    forall sr fr n, In (Rep sr fr n) (metaMeths m) ->
                    forall s i,
                      In s (getCallsMAction (fr i)) ->
                      In s (map (@getNamesOfMeta _) (metaMeths m)) ->
                      False.

  Variable noRepInteralCallsInRepMeth:
    forall sr fr n, In (Rep sr fr n) (metaMeths m) ->
                    forall s i,
                      In (s __ i) (getCallsMAction (fr i)) ->
                      In s (map (@getNamesOfMeta _) (metaMeths m)) ->
                      False.

  Variable noOneInteralCallsInOneMeth:
    forall r, In (One r) (metaMeths m) ->
              forall s,
                In s (getCallsMAction (attrType r)) ->
                In s (map (@getNamesOfMeta _) (metaMeths m)) ->
                False.

  Variable noRepInteralCallsInOneMeth:
    forall r, In (One r) (metaMeths m) ->
              forall s i,
                In (s __ i) (getCallsMAction (attrType r)) ->
                In s (map (@getNamesOfMeta _) (metaMeths m)) ->
                False.

End MetaModule.
*)