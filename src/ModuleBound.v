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

  Definition RegsBound (regss: Prefixes) := Abstracted regss (namesOf (getRegInits m)).
  Definition DmsBound (dmss: Prefixes) := Abstracted dmss (getDefs m).
  Definition CmsBound (cmss: Prefixes) := Abstracted cmss (getCalls m).

  Record ModuleBound := { regss : Prefixes;
                          dmss : Prefixes;
                          cmss : Prefixes }.

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

  Lemma getModuleBound_modular:
    forall m1 m2,
      BoundedModule m1 (getModuleBound m1) ->
      BoundedModule m2 (getModuleBound m2) ->
      BoundedModule (m1 ++ m2)%kami (getModuleBound (m1 ++ m2)%kami).
  Proof.
    unfold BoundedModule, getModuleBound; simpl; intros; dest.
    admit.
  Qed.

  Lemma getModuleBound_duplicate:
    forall m n,
      BoundedModule (duplicate m n) (getModuleBound m).
  Proof.
    admit.
  Qed.
  
  Lemma getMetaModuleBound_bounded:
    forall mm, BoundedModule (makeModule mm) (getMetaModuleBound mm).
  Proof.
    admit.
  Qed.

  Lemma getMetaModuleBound_modular:
    forall mm1 mm2,
      BoundedModule (makeModule mm1) (getMetaModuleBound mm1) ->
      BoundedModule (makeModule mm2) (getMetaModuleBound mm2) ->
      BoundedModule (makeModule (mm1 +++ mm2))
                    (getMetaModuleBound (mm1 +++ mm2)).
  Proof.
    admit.
  Qed.

End Bounds.

Section Correctness.

  Lemma prefix_prefix:
    forall p1 p2 s,
      prefix p1 s = true -> prefix p2 s = true ->
      prefix p1 p2 = true \/ prefix p2 p1 = true.
  Proof.
    admit.
  Qed.

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

