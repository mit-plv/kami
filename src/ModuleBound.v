Require Import Bool String List Arith.Peano_dec.
Require Import Lib.FMap Lib.Struct Lib.CommonTactics Lib.Concat Lib.Indexer Lib.StringEq.
Require Import Syntax ParametricSyntax Semantics SemFacts.
Require Import Specialize Duplicate.

Set Implicit Arguments.

Lemma prefix_refl: forall s, prefix s s = true.
Proof.
  induction s; auto; simpl.
  destruct (Ascii.ascii_dec a a); [auto|elim n; reflexivity].
Qed.

Lemma prefix_empty:
  forall s, prefix ""%string s = true.
Proof. intros; destruct s; auto. Qed.

Lemma prefix_prefix:
  forall p1 p2 s,
    prefix p1 s = true -> prefix p2 s = true ->
    prefix p1 p2 = true \/ prefix p2 p1 = true.
Proof.
  induction p1; intros; [left; apply prefix_empty|].
  destruct s; [inv H|].
  simpl in H; destruct (Ascii.ascii_dec a a0); [subst|inv H].
  destruct p2; [right; apply prefix_empty|].
  simpl in H0; destruct (Ascii.ascii_dec a a0); [subst|inv H0].
  simpl; destruct (Ascii.ascii_dec a0 a0); [|elim n; reflexivity].
  eauto.
Qed.

Lemma prefix_append: forall t s, prefix s (s ++ t) = true.
Proof.
  induction s; simpl; intros; [apply prefix_empty|].
  destruct (Ascii.ascii_dec a a); [|elim n; reflexivity]; auto.
Qed.

Lemma prefix_withIndex: forall i s, prefix s (s __ i) = true.
Proof.
  intros.
  Transparent withIndex.
  unfold withIndex.
  apply prefix_append.
  Opaque withIndex.
Qed.

Lemma prefix_getListFromRep:
  forall s {A} (strA: A -> string) {B} (bgen: A -> B) nameVal ls,
    In s (namesOf (getListFromRep strA bgen nameVal ls)) ->
    prefix nameVal s = true.
Proof.
  induction ls; simpl; intros; [inv H|].
  destruct H; auto.
  subst; apply prefix_append.
Qed.

Section ModuleBound.
  Variable m: Modules.

  Definition Prefixes := list string. (* prefixes *)

  Definition Abstracted (abs: Prefixes) (ls: list string) :=
    forall s, In s ls -> exists abss, In abss abs /\ prefix abss s = true.

  Lemma abstracted_refl: forall l, Abstracted l l.
  Proof.
    unfold Abstracted; intros.
    exists s; split; auto.
    apply prefix_refl.
  Qed.

  Lemma abstracted_app_1:
    forall a1 a2 l1 l2,
      Abstracted a1 l1 -> Abstracted a2 l2 ->
      Abstracted (a1 ++ a2) (l1 ++ l2).
  Proof.
    unfold Abstracted; intros.
    specializeAll s.
    apply in_app_or in H1; destruct H1.
    - specialize (H H1); destruct H as [abss ?]; dest.
      exists abss; split; auto.
      apply in_or_app; auto.
    - specialize (H0 H1); destruct H0 as [abss ?]; dest.
      exists abss; split; auto.
      apply in_or_app; auto.
  Qed.

  Lemma abstracted_app_2:
    forall a1 a2 l,
      Abstracted a1 l -> Abstracted a2 l ->
      Abstracted (a1 ++ a2) l.
  Proof.
    unfold Abstracted; intros.
    specializeAll s.
    specializeAll H1.
    destruct H as [abss [? ?]].
    exists abss; split; auto.
    apply in_or_app; auto.
  Qed.

  Lemma abstracted_app_3:
    forall a l1 l2,
      Abstracted a l1 -> Abstracted a l2 ->
      Abstracted a (l1 ++ l2).
  Proof.
    unfold Abstracted; intros.
    specializeAll s.
    apply in_app_or in H1; destruct H1.
    - specialize (H H1); destruct H as [abss ?]; dest.
      exists abss; split; auto.
    - specialize (H0 H1); destruct H0 as [abss ?]; dest.
      exists abss; split; auto.
  Qed.

  Lemma abstracted_withIndex:
    forall i l, Abstracted l (map (fun s => s __ i) l).
  Proof.
    induction l; unfold Abstracted; intros; [inv H|].
    inv H.
    - exists a; split.
      + left; auto.
      + apply prefix_withIndex.
    - specialize (IHl _ H0).
      destruct IHl as [abss ?]; dest.
      exists abss; split; auto.
      right; auto.
  Qed.

  Definition RegsBound (regss: Prefixes) := Abstracted regss (namesOf (getRegInits m)).
  Definition DmsBound (dmss: Prefixes) := Abstracted dmss (getDefs m).
  Definition CmsBound (cmss: Prefixes) := Abstracted cmss (getCalls m).

  Record ModuleBound := { regss : Prefixes;
                          dmss : Prefixes;
                          cmss : Prefixes }.

  Definition concatModuleBound (mb1 mb2: ModuleBound) :=
    {| regss := regss mb1 ++ regss mb2;
       dmss := dmss mb1 ++ dmss mb2;
       cmss := cmss mb1 ++ cmss mb2 |}.

  Definition BoundedModule (mb: ModuleBound) :=
    RegsBound (regss mb) /\ DmsBound (dmss mb) /\ CmsBound (cmss mb).

  Definition DisjPrefixes (ss1 ss2: Prefixes) :=
    forall p1,
      In p1 ss1 ->
      forall p2,
        In p2 ss2 ->
        prefix p1 p2 = false /\ prefix p2 p1 = false.

  Definition DisjBounds (mb1 mb2: ModuleBound) :=
    DisjPrefixes (regss mb1) (regss mb2) /\
    DisjPrefixes (dmss mb1) (dmss mb2) /\
    DisjPrefixes (cmss mb1) (cmss mb2).

End ModuleBound.

Section Bounds.

  Lemma concatMod_concatModuleBound:
    forall m1 m2 mb1 mb2,
      BoundedModule m1 mb1 ->
      BoundedModule m2 mb2 ->
      BoundedModule (m1 ++ m2)%kami (concatModuleBound mb1 mb2).
  Proof.
    unfold BoundedModule, concatModuleBound; simpl; intros; dest.
    repeat split.
    - unfold RegsBound; simpl.
      unfold RegInitT; rewrite namesOf_app.
      apply abstracted_app_1; auto.
    - unfold DmsBound; simpl.
      rewrite getDefs_app.
      apply abstracted_app_1; auto.
    - clear -H2 H4; unfold CmsBound, Abstracted in *; simpl; intros.
      specializeAll s.
      apply getCalls_in in H; destruct H.
      + specialize (H4 H); destruct H4 as [abss ?]; dest.
        exists abss; split; auto.
        apply in_or_app; auto.
      + specialize (H2 H); destruct H2 as [abss ?]; dest.
        exists abss; split; auto.
        apply in_or_app; auto.
  Qed.

  Definition getModuleBound (m: Modules) :=
    {| regss := namesOf (getRegInits m);
       dmss := getDefs m;
       cmss := getCalls m |}.

  Fixpoint getMetaModuleRegsBound (rs: list MetaReg) :=
    match rs with
    | nil => nil
    | OneReg _ {| nameVal := n |} :: rs' =>
      n :: (getMetaModuleRegsBound rs')
    | RepReg _ _ _ _ _ {| nameVal := n |} _ _ :: rs' =>
      n :: (getMetaModuleRegsBound rs')
    end.

  Fixpoint getMetaModuleDmsBound (ms: list MetaMeth) :=
    match ms with
    | nil => nil
    | OneMeth _ {| nameVal := n |} :: ms' =>
      n :: (getMetaModuleDmsBound ms')
    | RepMeth _ _ _ _ _ _ _ {| nameVal := n |} _ _ :: ms' =>
      n :: (getMetaModuleDmsBound ms')
    end.

  (* TODO: is this the best definition? *)
  Definition getMetaModuleCmsBound (mm: MetaModule) :=
    map (fun n => nameVal (nameRec n))
        ((concat (map getCallsMetaRule (metaRules mm)))
           ++ (concat (map getCallsMetaMeth (metaMeths mm)))).

  Definition getMetaModuleBound (mm: MetaModule) :=
    {| regss := getMetaModuleRegsBound (metaRegs mm);
       dmss := getMetaModuleDmsBound (metaMeths mm);
       cmss := getMetaModuleCmsBound mm |}.

  Lemma getModuleBound_bounded:
    forall m, BoundedModule m (getModuleBound m).
  Proof.
    unfold BoundedModule, getModuleBound; simpl; intros.
    repeat split; apply abstracted_refl.
  Qed.

  Lemma boundedModule_concatMod:
    forall m1 m2 l,
      BoundedModule m1 l ->
      BoundedModule m2 l ->
      BoundedModule (m1 ++ m2)%kami l.
  Proof.
    unfold BoundedModule; simpl; intros; dest.
    repeat split.
    - clear -H H0; unfold RegsBound in *.
      simpl; unfold RegInitT; rewrite namesOf_app.
      apply abstracted_app_3; auto.
    - clear -H1 H3; unfold DmsBound in *.
      simpl; rewrite getDefs_app.
      apply abstracted_app_3; auto.
    - clear -H2 H4; unfold CmsBound in *.
      unfold Abstracted in *; intros.
      specializeAll s.
      apply getCalls_in in H; destruct H.
      + specialize (H4 H); destruct H4 as [abss ?]; dest.
        exists abss; split; auto.
      + specialize (H2 H); destruct H2 as [abss ?]; dest.
        exists abss; split; auto.
  Qed.

  Lemma getModuleBound_modular:
    forall m1 m2,
      BoundedModule m1 (getModuleBound m1) ->
      BoundedModule m2 (getModuleBound m2) ->
      BoundedModule (m1 ++ m2)%kami (getModuleBound (m1 ++ m2)%kami).
  Proof.
    unfold BoundedModule, getModuleBound; simpl; intros; dest.
    repeat split.
    - clear -H H0; unfold RegsBound in *.
      simpl; unfold RegInitT; rewrite namesOf_app.
      apply abstracted_app_1; auto.
    - clear -H1 H3; unfold DmsBound in *.
      simpl; rewrite getDefs_app.
      apply abstracted_app_1; auto.
    - clear -H2 H4; unfold CmsBound in *.
      unfold Abstracted in *; intros.
      specializeAll s.
      apply getCalls_in in H; destruct H.
      + specialize (H4 H); destruct H4 as [abss ?]; dest.
        exists abss; split; auto.
        apply getCalls_in_1; auto.
      + specialize (H2 H); destruct H2 as [abss ?]; dest.
        exists abss; split; auto.
        apply getCalls_in_2; auto.
  Qed.
  
  Lemma getModuleBound_specialize:
    forall m i,
      Specializable m ->
      BoundedModule (specializeMod m i) (getModuleBound m).
  Proof.
    unfold getModuleBound; intros; repeat split; simpl.
    - unfold RegsBound.
      rewrite specializeMod_regs; auto.
      apply abstracted_withIndex.
    - unfold DmsBound.
      rewrite specializeMod_defs; auto.
      apply abstracted_withIndex.
    - unfold CmsBound.
      rewrite specializeMod_calls; auto.
      apply abstracted_withIndex.
  Qed.

  Lemma getModuleBound_duplicate:
    forall m (Hsp: Specializable m) n,
      BoundedModule (duplicate m n) (getModuleBound m).
  Proof.
    induction n; simpl; intros; [apply getModuleBound_specialize; auto|].
    apply boundedModule_concatMod; auto.
    apply getModuleBound_specialize; auto.
  Qed.

  Lemma abstracted_metaRegs:
    forall mregs,
      Abstracted (getMetaModuleRegsBound mregs)
                 (namesOf (concat (map getListFromMetaReg mregs))).
  Proof.
    induction mregs; simpl; [apply abstracted_refl|].
    destruct a.
    - destruct s; simpl.
      unfold Abstracted in *; intros; inv H.
      + exists s; split.
        * left; auto.
        * apply prefix_refl.
      + specialize (IHmregs _ H0).
        destruct IHmregs as [abss ?]; dest.
        exists abss; split; auto.
        right; auto.
    - destruct s; simpl.
      unfold Abstracted in *; intros.
      rewrite namesOf_app in H.
      apply in_app_or in H; inv H.
      + exists nameVal; split; [left; auto|].
        eapply prefix_getListFromRep; eauto.
      + specialize (IHmregs _ H0).
        destruct IHmregs as [abss ?]; dest.
        exists abss; split; auto.
        right; auto.
  Qed.

  Lemma abstracted_metaMeths:
    forall mdms,
      Abstracted (getMetaModuleDmsBound mdms)
                 (namesOf (concat (map getListFromMetaMeth mdms))).
  Proof.
    induction mdms; simpl; [apply abstracted_refl|].
    destruct a.
    - destruct s; simpl.
      unfold Abstracted in *; intros; inv H.
      + exists s; split.
        * left; auto.
        * apply prefix_refl.
      + specialize (IHmdms _ H0).
        destruct IHmdms as [abss ?]; dest.
        exists abss; split; auto.
        right; auto.
    - destruct s; simpl.
      unfold Abstracted in *; intros.
      rewrite namesOf_app in H.
      apply in_app_or in H; inv H.
      + exists nameVal; split; [left; auto|].
        unfold repMeth in H0.
        eapply prefix_getListFromRep; eauto.
      + specialize (IHmdms _ H0).
        destruct IHmdms as [abss ?]; dest.
        exists abss; split; auto.
        right; auto.
  Qed.

  Lemma abstracted_metaCms:
    forall mregs mrules mdms,
      CmsBound
        (makeModule
           {| metaRegs := mregs; metaRules := mrules; metaMeths := mdms |})
        (getMetaModuleCmsBound
           {| metaRegs := mregs; metaRules := mrules; metaMeths := mdms |}).
  Proof.
    unfold CmsBound, makeModule, getMetaModuleCmsBound, getCalls; simpl; intros.
    rewrite map_app.
    admit.
  Qed.

  Lemma getMetaModuleBound_bounded:
    forall mm, BoundedModule (makeModule mm) (getMetaModuleBound mm).
  Proof.
    intros; destruct mm as [mregs mrules mdms].
    repeat split; simpl.
    - apply abstracted_metaRegs.
    - apply abstracted_metaMeths.
    - apply abstracted_metaCms. 
  Qed.

  (* TODO: Check whether it should be proved *)
  (* Lemma getMetaModuleBound_modular: *)
  (*   forall mm1 mm2, *)
  (*     BoundedModule (makeModule mm1) (getMetaModuleBound mm1) -> *)
  (*     BoundedModule (makeModule mm2) (getMetaModuleBound mm2) -> *)
  (*     BoundedModule (makeModule (mm1 +++ mm2)) *)
  (*                   (getMetaModuleBound (mm1 +++ mm2)). *)
  (* Proof. *)
  (* Qed. *)

End Bounds.

Section Correctness.

  Lemma disjPrefixes_DisjList:
    forall ss1 ss2,
      DisjPrefixes ss1 ss2 ->
      forall l1 l2,
        Abstracted ss1 l1 -> Abstracted ss2 l2 ->
        DisjList l1 l2.
  Proof.
    unfold DisjPrefixes, Abstracted, DisjList; intros.
    destruct (in_dec string_dec e l1); [|left; auto].
    destruct (in_dec string_dec e l2); [|right; auto].

    exfalso.
    specialize (H0 _ i); destruct H0 as [abss1 ?]; dest.
    specialize (H1 _ i0); destruct H1 as [abss2 ?]; dest.
    specialize (H _ H0 _ H1); dest.
    destruct (prefix_prefix _ _ _ H2 H3).
    - rewrite H in H5; inv H5.
    - rewrite H4 in H5; inv H5.
  Qed.

  Lemma boundedModule_disj_regs:
    forall mb1 mb2,
      DisjBounds mb1 mb2 ->
      forall m1 m2,
        BoundedModule m1 mb1 -> BoundedModule m2 mb2 ->
        DisjList (namesOf (getRegInits m1)) (namesOf (getRegInits m2)).
  Proof.
    unfold DisjBounds, BoundedModule; intros; dest.
    apply disjPrefixes_DisjList with (ss1:= regss mb1) (ss2:= regss mb2); auto.
  Qed.

  Lemma boundedModule_disj_dms:
    forall mb1 mb2,
      DisjBounds mb1 mb2 ->
      forall m1 m2,
        BoundedModule m1 mb1 -> BoundedModule m2 mb2 ->
        DisjList (getDefs m1) (getDefs m2).
  Proof.
    unfold DisjBounds, BoundedModule; intros; dest.
    apply disjPrefixes_DisjList with (ss1:= dmss mb1) (ss2:= dmss mb2); auto.
  Qed.

  Lemma boundedModule_disj_calls:
    forall mb1 mb2,
      DisjBounds mb1 mb2 ->
      forall m1 m2,
        BoundedModule m1 mb1 -> BoundedModule m2 mb2 ->
        DisjList (getCalls m1) (getCalls m2).
  Proof.
    unfold DisjBounds, BoundedModule; intros; dest.
    apply disjPrefixes_DisjList with (ss1:= cmss mb1) (ss2:= cmss mb2); auto.
  Qed.

End Correctness.

