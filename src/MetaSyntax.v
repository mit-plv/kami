Require Import Syntax Wf Struct List Inline SimpleInline Coq.Arith.Peano_dec Lib.Indexer
        FunctionalExtensionality String Equiv Program.Equality Lib.FMap CommonTactics StringEq
        InlineFacts_2 Specialize.

Set Implicit Arguments.

Lemma RulesEquiv_app t1 t2 r1: forall r2, RulesEquiv t1 t2 r1 ->
                                          RulesEquiv t1 t2 r2 ->
                                          RulesEquiv t1 t2 (r1 ++ r2).
Proof.
  induction r1; simpl in *; intros.
  - intuition.
  - dependent destruction H.
    constructor; auto.
Qed.

Lemma RulesEquiv_in t1 t2 (r: list (Attribute (Action Void))):
  (forall i, In i r ->
             forall (G: ctxt (ft1 t1) (ft2 t2)),
               ActionEquiv G (attrType i t1) (attrType i t2)) ->
  RulesEquiv t1 t2 r.
Proof.
  induction r; simpl in *; intros.
  - constructor.
  - assert (sth1: forall i, In i r -> forall G, ActionEquiv G (attrType i t1) (attrType i t2))
      by (intros; apply H; auto).
    assert (sth2: forall G, ActionEquiv G (attrType a t1) (attrType a t2))
      by (intros; apply H; auto).
    specialize (IHr sth1).
    destruct a.
    econstructor; eauto.
Qed.

Lemma MethsEquiv_app t1 t2 r1: forall r2, MethsEquiv t1 t2 r1 ->
                                          MethsEquiv t1 t2 r2 ->
                                          MethsEquiv t1 t2 (r1 ++ r2).
Proof.
  induction r1; simpl in *; intros.
  - intuition.
  - dependent destruction H.
    constructor; auto.
Qed.

Lemma MethsEquiv_in t1 t2 (r: list DefMethT):
  (forall i, In i r ->
             forall (argV1: fullType t1 (SyntaxKind (arg (projT1 (attrType i)))))
                    (argV2: fullType t2 (SyntaxKind (arg (projT1 (attrType i))))) G,
               ActionEquiv ((vars argV1 argV2) :: G)
                           (projT2 (attrType i) t1 argV1) (projT2 (attrType i) t2 argV2)) ->
  MethsEquiv t1 t2 r.
Proof.
  induction r; simpl in *; intros.
  - constructor.
  - assert (sth1: forall i,
                    In i r ->
                    forall(argV1: fullType t1 (SyntaxKind (arg (projT1 (attrType i)))))
                    (argV2: fullType t2 (SyntaxKind (arg (projT1 (attrType i))))) G,
                      ActionEquiv ((vars argV1 argV2) :: G)
                                  (projT2 (attrType i) t1 argV1) (projT2 (attrType i) t2 argV2))
      by (intros; apply H; auto).
    assert (sth2: forall(argV1: fullType t1 (SyntaxKind (arg (projT1 (attrType a)))))
                        (argV2: fullType t2 (SyntaxKind (arg (projT1 (attrType a))))) G,
                    ActionEquiv ((vars argV1 argV2) :: G)
                                (projT2 (attrType a) t1 argV1) (projT2 (attrType a) t2 argV2))
      by (intros; apply H; auto).
    specialize (IHr sth1).
    destruct a.
    destruct attrType.
    econstructor; eauto.
Qed.


Section Concat.
  Fixpoint concat A (ls: list (list A)) :=
    match ls with
      | x :: xs => x ++ concat xs
      | nil => nil
    end.

  Variable A B: Type.
  Variable f: A -> list B.
  Lemma in_concat (ls: list A):
    forall b, In b (concat (map f ls)) <-> exists a, In a ls /\ In b (f a).
  Proof.
    induction ls; intros; simpl in *.
    - intuition.
      dest; intuition.
    - constructor; intros.
      + apply in_app_or in H.
        destruct H; [exists a; intuition auto | ].
        apply IHls in H.
        dest; eexists; eauto.
      + dest.
        apply in_or_app.
        destruct H; subst; intuition auto.
        pose proof (ex_intro (fun x => In x ls /\ In b (f x)) x (conj H H0)).
        apply IHls in H1.
        intuition.
  Qed.
End Concat.

Section NoDup.
  Variable A: Type.
  Lemma noDupApp l1: forall l2, NoDup l1 -> NoDup l2 ->
                                (forall i: A, In i l1 -> ~ In i l2) ->
                                NoDup (l1 ++ l2).
  Proof.
    induction l1; simpl in *; intros.
    - intuition.
    - inv H.
      specialize (IHl1 _ H5 H0).
      assert (forall i, In i l1 -> ~ In i l2) by (intros; apply H1; intuition).
      specialize (IHl1 H).
      assert (~ In a l2) by (intros; apply H1; auto).
      constructor; auto.
      unfold not; intros K; apply in_app_or in K.
      destruct K; intuition auto.
  Qed.
End NoDup.

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

  Lemma in_getListFromRep n:
    forall dm s (f: nat -> A),
      In dm (getListFromRep s f n) ->
      exists i, i <= n /\ dm = (s __ i :: f i)%struct.
  Proof.
    induction n; intros; simpl in *; intuition auto.
    - exists 0; intuition auto.
    - exists (S n); intuition auto.
    - apply IHn in H0; dest.
      repeat (econstructor; eauto).
  Qed.

  Lemma in_getListFromRepNames n:
    forall dmName s (f: nat -> A),
      In dmName (namesOf (getListFromRep s f n)) ->
      exists i, i <= n /\ dmName = s __ i.
  Proof.
    induction n; intros; simpl in *; intuition auto.
    - exists 0; intuition auto.
    - exists (S n); intuition auto.
    - apply IHn in H0; dest.
      exists x.
      constructor; auto.
  Qed.
  
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

  Lemma inFullList ls:
    forall x,
      In x (getFullListFromMeta ls) ->
      exists y, In y ls /\ In x (getListFromMeta y).
  Proof.
    induction ls; simpl in *; intros.
    - intuition auto.
    - apply in_app_or in H.
      destruct H.
      + exists a; intuition.
      + apply IHls in H; dest.
        exists x0; intuition.
  Qed.
  
  Fixpoint getNamesOfMeta m :=
    match m with
      | One a => attrName a
      | Rep s _ _ => s
    end.

  Lemma aboutNoDups ls:
    NoDup (map getNamesOfMeta ls) ->
    (forall s, In s (map getNamesOfMeta ls) -> forall s' i, s <> s' __ i) ->
    NoDup (namesOf (getFullListFromMeta ls)).
  Proof.
    induction ls; simpl in *; intros.
    - intuition.
    - dependent destruction H.
      specialize (IHls H0).
      assert (sth1: forall s, In s (map getNamesOfMeta ls) -> forall s' i, s <> s' __ i) by
          (intros; specialize (H1 s); apply H1; intuition).
      apply IHls in sth1.
      assert (sth2: forall s' i, getNamesOfMeta a <> s' __ i) by
          (specialize (H1 (getNamesOfMeta a)); apply H1; intuition).
      unfold namesOf.
      rewrite map_app.
      fold (namesOf (getListFromMeta a)).
      fold (namesOf (getFullListFromMeta ls)).
      apply noDupApp; auto; intros.
      destruct a; simpl in *.
      intuition.
      assert (sth: forall n i, In (s __ i) (namesOf (getListFromRep s a n)) -> i <= n).
      { clear; induction n; intros; simpl in *; intuition auto.
        apply withIndex_index_eq in H0; dest; subst; auto.
        apply withIndex_index_eq in H0; dest; subst; auto.
      }
      { clear - sth. induction n; simpl in *.
        intuition.
        constructor.
        unfold not; intros.
        specialize (sth n (S n) H).
        omega.
        assumption.
      }
      unfold not; intros.
      assert (sth3: forall s, In s (map getNamesOfMeta ls) -> forall s' i, s <> s' __ i)
        by (intros; apply H1; intuition).
      clear - sth3 sth2 H2 H3 H.
      induction ls; simpl in *.
      + intuition.
      + assert (sth4: ~ In (getNamesOfMeta a) (map getNamesOfMeta ls)) by intuition.
        specialize (IHls sth4); clear sth4.
        assert (sth5: forall s, In s (map getNamesOfMeta ls) -> forall s' i0, s <> s' __ i0)
          by (intros; apply sth3; intuition).
        assert (sth6: getNamesOfMeta a0 <> getNamesOfMeta a) by intuition.
        clear H.
        unfold namesOf in H3.
        rewrite map_app in H3.
        apply in_app_or in H3.
        fold (namesOf (getListFromMeta a0)) in H3.
        fold (namesOf (getFullListFromMeta ls)) in H3.
        destruct H3; [| apply IHls; auto].
        assert (sth7: forall s' i0, getNamesOfMeta a0 <> s' __ i0) by (apply sth3; intuition).
        clear - sth2 H2 H sth6 sth7.
        destruct a, a0; simpl in *; subst; intuition auto; subst; intuition auto.
        pose proof (in_getListFromRepNames n (attrName a) s a0 H); dest.
        eapply sth2; eauto.
        pose proof (in_getListFromRepNames n (attrName a0) s a H2); dest.
        eapply sth7; eauto.
        
        apply in_getListFromRepNames in H2.
        apply in_getListFromRepNames in H.
        dest.
        subst.
        pose proof (withIndex_index_eq _ _ _ _ H0); dest.
        intuition.
  Qed.
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

Definition metaInlineNoFilt m :=
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

Lemma metaInlineDmToRule_equiv dm r:
  (forall ty, metaMethEquiv ty typeUT dm) ->
  (forall ty, metaRuleEquiv ty typeUT r) ->
  forall r', In r' (metaInlineDmToRule dm r) ->
             forall ty, metaRuleEquiv ty typeUT r'.
Proof.
  intros.
  specialize (H ty); specialize (H0 ty).
  unfold metaInlineDmToRule, metaMethEquiv, metaRuleEquiv in *; simpl in *.
  destruct r, dm, r'; simpl in *.
  - destruct H1; intuition auto.
    inv H1.
    unfold inlineDmToRule; simpl in *.
    apply inlineDm_ActionEquiv; auto.
  - destruct H1; intuition auto.
    discriminate.
  - destruct H1; intuition auto.
    inv H1.
    generalize dependent a.
    induction n; simpl in *; intros.
    + apply inlineDm_ActionEquiv; simpl in *; auto.
    + unfold inlineDmToRule at 2; unfold inlineDmToRule at 3; simpl in *.
      match goal with
        | [|- context [fold_left inlineDmToRule _ (attrName a :: ?P)%struct]] =>
          pose P as sth; simpl in sth
      end.
      assert (sth2: forall G, ActionEquiv G (attrType (attrName a :: sth)%struct ty)
                                         (attrType (attrName a :: sth)%struct typeUT)).
      { unfold sth; simpl in *; intros; apply inlineDm_ActionEquiv; auto.
        intuition; simpl in *; auto.
      }
      apply (IHn _ sth2).
  - destruct H1; intuition auto.
    discriminate.
  - destruct H1; intuition auto.
    discriminate.
  - destruct H1; intuition auto.
    inv H1.
    apply inlineDm_ActionEquiv; simpl in *; auto.
  - destruct (eq_nat_dec n n0); simpl in *; subst.
    + destruct H1; intuition auto.
      discriminate.
    + rewrite commuteInlineDmRules in H1.
      apply in_map_iff in H1; dest.
      inv H1.
      clear n1.
      assert (sth: exists i, fold_left inlineDmToRule (getListFromRep s0 s1 n0)
                                       (s __ i :: a i)%struct = a0).
      { clear - H2; induction n; simpl in *; intuition auto.
        - exists 0; auto.
        - exists (S n); auto.
      }
      dest.
      clear H2; subst.
      { specialize (H0 x); generalize dependent a; induction n0; simpl in *; intros.
        - apply inlineDm_ActionEquiv; simpl in *; auto.
        - unfold inlineDmToRule at 2; unfold inlineDmToRule at 3; simpl in *.
          match goal with
            | [|- context [fold_left inlineDmToRule _ (_ :: ?P)%struct]] =>
              pose P as sth; simpl in sth
          end.
          assert (sth2: forall G, ActionEquiv G (attrType (s __ x :: sth)%struct ty)
                                              (attrType (s __ x :: sth)%struct typeUT)).
          { unfold sth; simpl in *; intros; apply inlineDm_ActionEquiv; auto.
            intuition; simpl in *; auto.
          }
          specialize (IHn0 (fun x => sth) sth2 G).
          fold sth.
          assumption.
      }
  - destruct (eq_nat_dec n n0); simpl in *; subst.
    + destruct H1; intuition auto.
      inv H1.
      apply inlineDm_ActionEquiv; simpl in *; auto.
    + rewrite commuteInlineDmRules in H1.
      match goal with
        | [H: In _ (map _ ?P) |- _] => clear -H; induction P; simpl in *; intuition (try discriminate; auto)
      end.
Qed.

Ltac changeType p :=
  match type of p with
    | ?t ?k =>
      change (t k) with (fullType t (SyntaxKind k)) in p
  end.

Lemma metaInlineDmToDm_equiv dm r:
  (forall ty, metaMethEquiv ty typeUT dm) ->
  (forall ty, metaMethEquiv ty typeUT r) ->
  forall r', In r' (metaInlineDmToDm dm r) ->
             forall ty, metaMethEquiv ty typeUT r'.
Proof.
  intros.
  specialize (H ty); specialize (H0 ty).
  unfold metaInlineDmToDm, metaMethEquiv, metaRuleEquiv in *; simpl in *.
  destruct r, dm, r'; simpl in *.
  - destruct H1; intuition auto.
    inv H1.
    unfold inlineDmToDm; simpl in *.
    apply inlineDm_ActionEquiv; auto.
  - destruct H1; intuition auto.
    discriminate.
  - destruct H1; intuition auto.
    inv H1.
    generalize dependent a.
    induction n; simpl in *; intros.
    + apply inlineDm_ActionEquiv; simpl in *; auto.
    + unfold inlineDmToDm at 2; unfold inlineDmToDm at 3; simpl in *.
      match goal with
        | [|- context [fold_left inlineDmToDm _ (attrName a :: ?P)%struct]] =>
          pose P as sth; simpl in sth
      end.
      apply IHn.
      intros.
      unfold sth; simpl in *; apply inlineDm_ActionEquiv; auto.
      intuition; simpl in *; auto.
  - destruct H1; intuition auto.
    discriminate.
  - destruct H1; intuition auto.
    discriminate.
  - destruct H1; intuition auto.
    inv H1.
    apply inlineDm_ActionEquiv; simpl in *; auto.
  - destruct (eq_nat_dec n n0); simpl in *; subst.
    + destruct H1; intuition auto.
      discriminate.
    + rewrite commuteInlineDmMeths in H1.
      apply in_map_iff in H1; dest.
      inv H1.
      clear n1.
      assert (sth: exists i, fold_left inlineDmToDm (getListFromRep s1 s2 n0)
                                       (s __ i :: s0 i)%struct = a).
      { clear - H2; induction n; simpl in *; intuition auto.
        - exists 0; auto.
        - exists (S n); auto.
      }
      dest.
      clear H2; subst.
      { specialize (H0 x).
        generalize dependent s0; induction n0; simpl in *; intros.
        - apply inlineDm_ActionEquiv; simpl in *; auto.
        - unfold inlineDmToDm at 2; unfold inlineDmToDm at 3; simpl in *.
          match goal with
            | [|- context [fold_left inlineDmToDm _ (_ :: ?P)%struct]] =>
              pose P as sth; simpl in sth
          end.
          specialize (IHn0 (fun x => sth)).
          apply IHn0.
          intros.
          unfold sth; simpl in *; intros; apply inlineDm_ActionEquiv; auto.
          intuition; simpl in *; auto.
      }
  - destruct (eq_nat_dec n n0); simpl in *; subst.
    + destruct H1; intuition auto.
      inv H1.
      apply inlineDm_ActionEquiv; simpl in *; auto.
    + rewrite commuteInlineDmMeths in H1.
      match goal with
        | [H: In _ (map _ ?P) |- _] => clear -H; induction P; simpl in *; intuition (try discriminate; auto)
      end.
Qed.


Section MetaModuleEz.
  Variable m: MetaModule.
  Variable rulesEquiv: forall ty r, In r (metaRules m) -> metaRuleEquiv ty typeUT r.
  Variable methsEquiv: forall ty f, In f (metaMeths m) -> metaMethEquiv ty typeUT f.

  Variable noBadCallsInRepRules:
    forall sr fr n , In (Rep sr fr n) (metaRules m) ->
                     forall s i j,
                       In (s __ j) (getCallsA (fr i typeUT)) ->
                       i = j.

  Variable noBadCallsInOneRules:
    forall r, In (One r) (metaRules m) ->
              forall s i,
                In (s __ i) (getCallsA (attrType r typeUT)) ->
                False.

  Variable noCallsInRepMeths:
    forall sr fr n ,
      In (Rep sr fr n) (metaMeths m) ->
      forall i, getCallsMAction (fr i) = nil.

  Variable noCallsInOneMeths:
    forall f ,
      In (One f) (metaMeths m) ->
      getCallsMAction (attrType f) = nil.

  Variable sameN:
    forall sr1 fr1 n1 sr2 fr2 n2,
      In (Rep sr1 fr1 n1) (metaMeths m) ->
      In (Rep sr2 fr2 n2) (metaMeths m) ->
      n1 = n2.

  Variable sameN':
    forall sr1 fr1 n1 sr2 fr2 n2,
      In (Rep sr1 fr1 n1) (metaRules m) ->
      In (Rep sr2 fr2 n2) (metaMeths m) ->
      n1 = n2.


  Lemma metaInline_matches_ez1 dms:
    SubList dms (metaMeths m) ->
    makeModule (metaInlineDmsToMod m dms) =
    inlineDmsInMod (makeModule m) (getFullListFromMeta dms).
  Proof.
    generalize dependent m.
    clear.
    induction dms; simpl in *; intros; auto.
    specialize (IHdms (metaInlineDmToMod m a)); simpl in *.
    assert (In a (metaMeths m)) by intuition.
    rewrite IHdms; simpl in *; clear IHdms; auto.
    - unfold makeModule at 2; rewrite inlineDmsInMod_app.
      fold (makeModule m).
      f_equal.
      unfold makeModule, metaInlineDmToMod, inlineDmsInMod; simpl in *.
      f_equal; [apply metaInlineDmToRules_matches | apply metaInlineDmToDms_matches]; auto;
      intros; subst;
      match goal with
        | [H: In (Rep _ _ _) (metaMeths m) |- _] =>
          specialize (noCallsInRepMeths _ _ _ H i)
      end; rewrite noCallsInRepMeths in *; intuition.
    - intros.
      apply in_concat in H1; dest.
      unfold SubList in H; specialize (H a); simpl in H.
      assert (In a (metaMeths m)) by intuition.
      eapply metaInlineDmToRule_equiv; eauto.
    - intros.
      apply in_concat in H1; dest.
      unfold SubList in H; specialize (H a); simpl in H.
      assert (In a (metaMeths m)) by intuition.
      eapply metaInlineDmToDm_equiv with (r := x); eauto.
    - intros.
      apply in_concat in H1; dest.
      destruct a, x; simpl in *.
      destruct H3; try discriminate; intuition auto.
      destruct H3; intuition auto.
      inv H3.
      apply (inlineDm_calls a (a :: nil)) in H2; intuition.
      apply in_app_or in H2; simpl in *.
      rewrite app_nil_r in H2; simpl in *.
      destruct H2.
      apply (noBadCallsInRepRules _ _ _ H1 s i j H2).
      specialize (noCallsInOneMeths _ H0); subst.
      unfold getCallsMAction in *.
      rewrite noCallsInOneMeths in *.
      intuition.
      destruct H3; try discriminate; intuition auto.
      destruct (eq_nat_dec n1 n0); subst.
      simpl in *.
      destruct H3; intuition auto.
      inv H3.
      apply (inlineDm_calls (s0 __ i :: s1 i)%struct ((s0 __ i :: s1 i)%struct :: nil)) in H2.
      apply in_app_or in H2.
      simpl in *.
      rewrite app_nil_r in H2.
      destruct H2.
      apply (noBadCallsInRepRules _ _ _ H1 s i j H2).
      specialize (noCallsInRepMeths _ _ _ H0 i).
      unfold getCallsMAction in *.
      rewrite noCallsInRepMeths in *.
      intuition.
      intuition.
      apply in_map_iff in H3; dest; discriminate.
    - intros.
      apply in_concat in H1; dest.
      destruct a, x; simpl in *; intuition auto.
      inv H4.
      unfold inlineDmToRule in H2; simpl in *.
      apply (inlineDm_calls a (a :: nil) (@in_eq _ _ _) (attrType a0 typeUT) (s __ i)) in H2.
      apply in_app_or in H2; simpl in *.
      rewrite app_nil_r in H2; simpl in *.
      destruct H2.
      apply noBadCallsInOneRules in H2; auto.
      specialize (noCallsInOneMeths _ H0).
      unfold getCallsMAction in *; rewrite noCallsInOneMeths in H2.
      intuition.
      discriminate.
      inv H4.
      rewrite inlineNoCallsRule_matches in H2.
      apply noBadCallsInOneRules in H2; auto.
      intros.
      specialize (rulesEquiv ty (One a) H1).
      unfold metaRuleEquiv in *; simpl in *.
      apply rulesEquiv; auto.
      intros.
      apply in_getListFromRep in H3; dest.
      subst; simpl in *.
      apply (noBadCallsInOneRules _ H1 s0 x H4).
      destruct (eq_nat_dec n0 n); simpl in *.
      destruct H3; try discriminate; intuition auto.
      specialize (sameN' _ _ _ _ _ _ H1 H0).
      intuition.
    - intros.
      apply in_concat in H1; dest.
      destruct a, x; simpl in *; intuition auto; try discriminate.
      inv H3.
      unfold getCallsMAction in *; simpl in *.
      assert (getCallsA (projT2 (s0 i) typeUT tt) = nil).
      apply noCallsInRepMeths with (i := i) in H1.
      intuition.
      assert (getCallsMAction (attrType a) = nil).
      apply noCallsInOneMeths in H0.
      intuition.
      unfold getCallsMAction in *.
      pose proof (inlineDm_calls a (a :: nil) (@in_eq _ _ _) (projT2 (s0 i) typeUT tt)).
      simpl in *.
      rewrite H2, H3 in H4; simpl in *.
      apply SubList_nil_inv in H4.
      intuition.
      destruct (eq_nat_dec n1 n0); simpl in *; intuition auto.
      inv H3; subst.
      unfold getCallsMAction; simpl in *.
      assert (getCallsA (projT2 (s2 i) typeUT tt) = nil).
      apply noCallsInRepMeths with (i := i) in H1.
      intuition.
      assert (getCallsMAction (s0 i) = nil).
      apply noCallsInRepMeths with (i := i) in H0.
      intuition.
      unfold getCallsMAction in *.
      pose proof (inlineDm_calls (s __ i :: s0 i)%struct ((s __ i :: s0 i)%struct :: nil)
                                 (@in_eq _ _ _) (projT2 (s2 i) typeUT tt)).
      simpl in *.
      rewrite H2, H3 in H4.
      simpl in *.
      apply SubList_nil_inv in H4.
      intuition.
      specialize (sameN _ _ _ _ _ _ H1 H0).
      intuition.
    - intros.
      apply in_concat in H1; dest.
      destruct a, x; simpl in *; intuition auto; unfold getCallsMAction in *.
      inv H3.
      unfold inlineDmToDm; simpl in *; unfold getCallsMAction; simpl in *.
      specialize (noCallsInOneMeths _ H1).
      pose (tt: fullType typeUT (SyntaxKind (arg (projT1 (attrType a0))))) as f.
      rewrite inlineNoCallAction_matches with
      (aUT := projT2 (attrType a0) typeUT tt)
        (c := vars f f :: nil); auto.
      unfold getCallsMAction in *.
      rewrite noCallsInOneMeths.
      intuition.
      specialize (methsEquiv typeUT _ H1).
      intuition.
      discriminate.
      inv H3.
      rewrite inlineNoCallsMeth_matches; auto.
      intros.
      specialize (methsEquiv ty _ H1).
      unfold metaMethEquiv in *.
      apply methsEquiv; auto.
      intros.
      specialize (noCallsInOneMeths _ H1).
      rewrite noCallsInOneMeths in H3.
      intuition.
      destruct (eq_nat_dec n0 n); subst.
      simpl in *; destruct H2; try discriminate; intuition.
      specialize (sameN _ _ _ _ _ _ H1 H0).
      intuition.
    - intros.
      apply in_concat in H1.
      apply in_concat in H2.
      dest.
      destruct x, x0, a; simpl in *; intuition (try discriminate || auto).
      inv H5; inv H4.
      eapply sameN; eauto.
      destruct (eq_nat_dec n n3); simpl in H3; intuition auto.
      destruct (eq_nat_dec n0 n3); simpl in H4; intuition auto.
      inv H5; inv H3.
      intuition.
      inv H5.
      apply in_map_iff in H4; dest.
      discriminate.
      apply in_map_iff in H3; dest.
      discriminate.
    - intros.
      apply in_concat in H1; dest.
      apply in_concat in H2; dest.
      destruct x, x0, a; simpl in *; intuition (try discriminate || auto).
      inv H5; inv H3.
      eapply sameN'; eauto.
      destruct (eq_nat_dec n0 n3); simpl in *; intuition auto.
      destruct (eq_nat_dec n n3); simpl in *; intuition auto.
      inv H5; inv H4.
      intuition.
      apply in_map_iff in H3; dest.
      discriminate.
      apply in_map_iff in H4; dest; discriminate.
    - assert (SubList dms (metaMeths m)) by (unfold SubList in *; intuition).
      unfold SubList; intros.
      specialize (H1 e H2).
      apply in_concat.
      destruct e, a; simpl in *.
      + unfold metaInlineDmToDm; simpl in *; exists (One a0); intuition auto; left; f_equal.
        specialize (noCallsInOneMeths _ H1).
        unfold inlineDmToDm.
        assert (forall ty, metaMethEquiv ty typeUT (One a0)) by
            (intros; specialize (methsEquiv ty); intuition); simpl in *.
        destruct a0; simpl in *.
        f_equal.
        destruct attrType.
        f_equal.
        extensionality ty; extensionality argV; simpl in *.
        pose argV as f0.
        changeType f0.
        pose (tt: fullType typeUT (SyntaxKind (arg x))).
        apply inlineNoCallAction_matches with (aUT := (m0 typeUT tt)) (c := vars f0 f :: nil).
        unfold getCallsMAction in *; simpl in *.
        rewrite noCallsInOneMeths.
        intuition.
        apply H3.
      + unfold metaInlineDmToDm; simpl in *; exists (One a0); intuition auto; left; f_equal.
        apply inlineNoCallsMeth_matches; auto.
        assert (forall ty, metaMethEquiv ty typeUT (One a0)) by
            (intros; specialize (methsEquiv ty); intuition); simpl in *.
        destruct a0; simpl in *.
        assumption.
        intros.
        specialize (noCallsInOneMeths _ H1).
        unfold getCallsMAction in *; rewrite noCallsInOneMeths in *.
        intuition.
      + unfold metaInlineDmToDm; simpl in *; exists (Rep s s0 n); intuition auto; left; f_equal.
        extensionality i.
        case_eq (s0 i); intros; subst; f_equal.
        extensionality ty; extensionality argV; simpl in *.
        pose argV as f0.
        changeType f0.
        pose (tt: fullType typeUT (SyntaxKind (arg x))).
        apply inlineNoCallAction_matches with (aUT := (m0 typeUT tt)) (c := vars f0 f :: nil).
        unfold getCallsMAction in *; simpl in *.
        specialize (noCallsInRepMeths _ _ _ H1 i).
        rewrite H3 in *; simpl in *.
        rewrite noCallsInRepMeths.
        intuition.
        specialize (methsEquiv ty _ H1 i).
        rewrite H3 in methsEquiv; simpl in *.
        apply methsEquiv; auto.
      + exists (Rep s s0 n); simpl in *; intuition auto.
        destruct (eq_nat_dec n n0); subst; simpl in *; intuition auto.
        left.
        f_equal.
        extensionality i.
        case_eq (s0 i); intros.
        f_equal.
        extensionality ty; extensionality argV; simpl in *.
        pose argV as f0.
        changeType f0.
        pose (tt: fullType typeUT (SyntaxKind (arg x))).
        apply inlineNoCallAction_matches with
        (aUT := (m0 typeUT tt)) (c := vars f0 f :: nil).
        specialize (noCallsInRepMeths _ _ _ H1 i).
        rewrite H3 in *.
        unfold getCallsMAction in *; simpl in *; rewrite noCallsInRepMeths.
        intuition.
        specialize (methsEquiv ty _ H1 i).
        rewrite H3 in methsEquiv; simpl in *.
        apply methsEquiv; auto.
        specialize (sameN _ _ _ _ _ _ H1 H0).
        intuition.
  Qed.

  Lemma metaInline_matches_ez2:
    makeModule (metaInlineNoFilt m) =
    inlineDmsInMod (makeModule m) (getFullListFromMeta (metaMeths m)).
  Proof.
    unfold metaInlineNoFilt.
    pose proof (SubList_refl (metaMeths m)) as sth.
    apply metaInline_matches_ez1; intuition.
  Qed.

  Variable noDups: NoDup (map (@getNamesOfMeta _) (metaMeths m)).
  Variable noBadNamesOrig: hasNoIndex (map (@getNamesOfMeta _) (metaMeths m)) = true.

  Variable noBadNames:
    forall s, In s (map (@getNamesOfMeta _) (metaMeths m)) -> forall s' i, s <> s' __ i.    
  
  Lemma metaInline_matches_ez:
    makeModule (metaInlineNoFilt m) =
    fst (inlineDms (makeModule m)).
  Proof.
    rewrite metaInline_matches_ez2.
    apply inlineDmsIn_matches; intros.
    - unfold makeModule in *; simpl in *.
      unfold getCallsDm in H1.
      apply inFullList in H; dest.
      destruct x; simpl in *; intuition auto; subst.
      apply noCallsInOneMeths in H.
      unfold getCallsMAction in H; rewrite H in *.
      intuition.
      apply in_getListFromRep in H2; dest; subst.
      apply noCallsInRepMeths with (i := x) in H.
      unfold getCallsMAction in H; simpl in *.
      rewrite H in *.
      intuition.
    - unfold makeModule, getDefs; simpl.
      clear - noDups noBadNames.
      apply aboutNoDups; auto.
    - unfold ModEquiv; clear - rulesEquiv methsEquiv; unfold makeModule; simpl.
      constructor.
      + induction (metaRules m); simpl in *.
        * constructor.
        * assert (sth1: metaRuleEquiv ty typeUT a) by
              (intros; apply rulesEquiv; intuition).
          assert (sth2: forall ty r, In r l -> metaRuleEquiv ty typeUT r) by
              (intros; apply rulesEquiv; intuition).
          apply IHl in sth2.
          apply RulesEquiv_app; auto.
          clear - sth1.
          destruct a; simpl in *.
          destruct a.
          repeat (econstructor; eauto).
          apply RulesEquiv_in; intros.
          apply in_getListFromRep in H; dest; subst; simpl; auto.
      + induction (metaMeths m); simpl in *.
        * constructor.
        * assert (sth1: metaMethEquiv ty typeUT a) by
              (intros; apply methsEquiv; intuition).
          assert (sth2: forall ty r, In r l -> metaMethEquiv ty typeUT r) by
              (intros; apply methsEquiv; intuition).
          apply IHl in sth2.
          apply MethsEquiv_app; auto.
          clear - sth1.
          destruct a; simpl in *.
          destruct a.
          destruct attrType; simpl in *.
          repeat (econstructor; eauto).
          apply MethsEquiv_in; intros.
          apply in_getListFromRep in H; dest; subst; simpl; auto.
  Qed.
End MetaModuleEz.

