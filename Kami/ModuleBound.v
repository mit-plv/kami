Require Import Bool String List Arith.Peano_dec.
Require Import Lib.FMap Lib.Struct Lib.CommonTactics Lib.Concat Lib.Indexer Lib.StringEq.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts.
Require Import Kami.Specialize Kami.Duplicate.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section ModuleBound.
  Variable m: Modules.

  Definition Prefixes := list string. (* prefixes *)

  Definition Abstracted (abs: Prefixes) (ls: list string) :=
    forall s, In s ls -> exists abss, In abss abs /\ prefix abss s = true.

  Lemma abstracted_nil: forall a, Abstracted a nil.
  Proof. unfold Abstracted; intros; inv H. Qed.

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

  (* Record ModuleBound := { regss : Prefixes; *)
  (*                         dmss : Prefixes; *)
  (*                         cmss : Prefixes }. *)

  (* Definition concatModuleBound (mb1 mb2: ModuleBound) := *)
  (*   {| regss := regss mb1 ++ regss mb2; *)
  (*      dmss := dmss mb1 ++ dmss mb2; *)
  (*      cmss := cmss mb1 ++ cmss mb2 |}. *)

  (* Definition BoundedModule (mb: ModuleBound) := *)
  (*   RegsBound (regss mb) /\ DmsBound (dmss mb) /\ CmsBound (cmss mb). *)

  Definition DisjPrefixes (ss1 ss2: Prefixes) :=
    forall p1,
      In p1 ss1 ->
      forall p2,
        In p2 ss2 ->
        prefix p1 p2 = false /\ prefix p2 p1 = false.

  Fixpoint disjPrefix (s: string) (l: list string) :=
    match l with
    | nil => true
    | h :: t =>
      negb (prefix s h) && negb (prefix h s) && disjPrefix s t
    end.

  Fixpoint disjPrefixes (l1 l2: list string) :=
    match l1 with
    | nil => true
    | h1 :: t1 => disjPrefix h1 l2 && disjPrefixes t1 l2
    end.

  Lemma disjPrefix_prefix:
    forall s l,
      disjPrefix s l = true ->
      (forall t, In t l -> prefix s t = false /\ prefix t s = false).
  Proof.
    induction l; simpl; intros; [inv H0|].
    destruct H0; subst.
    - apply andb_true_iff in H; dest.
      apply andb_true_iff in H; dest; auto.
      rewrite negb_true_iff in H, H1; auto.
    - apply andb_true_iff in H; dest; auto.
  Qed.

  Lemma disjPrefixes_DisjPrefixes:
    forall l1 l2,
      disjPrefixes l1 l2 = true -> DisjPrefixes l1 l2.
  Proof.
    induction l1; simpl; unfold DisjPrefixes; intros; [inv H0|].
    apply andb_true_iff in H; dest.
    destruct H0; subst.
    - eapply disjPrefix_prefix; eauto.
    - specialize (IHl1 _ H2); auto.
  Qed.

End ModuleBound.

Section Bounds.

  Lemma concatMod_regsBound_1:
    forall m1 m2 rb1 rb2,
      RegsBound m1 rb1 ->
      RegsBound m2 rb2 ->
      RegsBound (m1 ++ m2)%kami (rb1 ++ rb2).
  Proof.
    unfold RegsBound; simpl; intros.
    unfold RegInitT; rewrite namesOf_app.
    apply abstracted_app_1; auto.
  Qed.

  Lemma concatMod_regsBound_2:
    forall m1 m2 rb,
      RegsBound m1 rb ->
      RegsBound m2 rb ->
      RegsBound (m1 ++ m2)%kami rb.
  Proof.
    unfold RegsBound; simpl; intros.
    unfold RegInitT; rewrite namesOf_app.
    apply abstracted_app_3; auto.
  Qed.

  Lemma concatMod_dmsBound_1:
    forall m1 m2 db1 db2,
      DmsBound m1 db1 ->
      DmsBound m2 db2 ->
      DmsBound (m1 ++ m2)%kami (db1 ++ db2).
  Proof.
    unfold DmsBound; simpl; intros.
    rewrite getDefs_app.
    apply abstracted_app_1; auto.
  Qed.

  Lemma concatMod_dmsBound_2:
    forall m1 m2 db,
      DmsBound m1 db ->
      DmsBound m2 db ->
      DmsBound (m1 ++ m2)%kami db.
  Proof.
    unfold DmsBound; simpl; intros.
    rewrite getDefs_app.
    apply abstracted_app_3; auto.
  Qed.

  Lemma concatMod_cmsBound_1:
    forall m1 m2 cb1 cb2,
      CmsBound m1 cb1 ->
      CmsBound m2 cb2 ->
      CmsBound (m1 ++ m2)%kami (cb1 ++ cb2).
  Proof.
    unfold CmsBound, Abstracted in *; simpl; intros.
    specializeAll s.
    apply getCalls_in in H1; destruct H1.
    - specialize (H H1); destruct H as [abss ?]; dest.
      exists abss; split; auto.
      apply in_or_app; auto.
    - specialize (H0 H1); destruct H0 as [abss ?]; dest.
      exists abss; split; auto.
      apply in_or_app; auto.
  Qed.

  Lemma concatMod_cmsBound_2:
    forall m1 m2 cb,
      CmsBound m1 cb ->
      CmsBound m2 cb ->
      CmsBound (m1 ++ m2)%kami cb.
  Proof.
    unfold CmsBound, Abstracted in *; simpl; intros.
    specializeAll s.
    apply getCalls_in in H1; destruct H1.
    - specialize (H H1); destruct H as [abss ?]; dest.
      exists abss; split; auto.
    - specialize (H0 H1); destruct H0 as [abss ?]; dest.
      exists abss; split; auto.
  Qed.

  (* normal boundaries *)
  Definition getRegsBound (m: Modules) := namesOf (getRegInits m).
  Definition getDmsBound (m: Modules) := getDefs m.
  Definition getCmsBound (m: Modules) := getCalls m.

  Lemma getRegsBound_bounded:
    forall m, RegsBound m (getRegsBound m).
  Proof. intros; apply abstracted_refl. Qed.

  Lemma getDmsBound_bounded:
    forall m, DmsBound m (getDmsBound m).
  Proof. intros; apply abstracted_refl. Qed.
  
  Lemma getCmsBound_bounded:
    forall m, CmsBound m (getCmsBound m).
  Proof. intros; apply abstracted_refl. Qed.

  Lemma getRegsBound_modular:
    forall m1 m2,
      RegsBound m1 (getRegsBound m1) ->
      RegsBound m2 (getRegsBound m2) ->
      RegsBound (m1 ++ m2)%kami (getRegsBound (m1 ++ m2)%kami).
  Proof.
    intros.
    replace (getRegsBound (m1 ++ m2)%kami) with (getRegsBound m1 ++ getRegsBound m2).
    - apply concatMod_regsBound_1; auto.
    - unfold getRegsBound; simpl.
      unfold RegInitT; rewrite namesOf_app; reflexivity.
  Qed.
  
  Lemma getDmsBound_modular:
    forall m1 m2,
      DmsBound m1 (getDmsBound m1) ->
      DmsBound m2 (getDmsBound m2) ->
      DmsBound (m1 ++ m2)%kami (getDmsBound (m1 ++ m2)%kami).
  Proof.
    intros.
    replace (getDmsBound (m1 ++ m2)%kami) with (getDmsBound m1 ++ getDmsBound m2).
    - apply concatMod_dmsBound_1; auto.
    - unfold getDmsBound; simpl.
      rewrite getDefs_app; reflexivity.
  Qed.

  Lemma getCmsBound_modular:
    forall m1 m2,
      CmsBound m1 (getCmsBound m1) ->
      CmsBound m2 (getCmsBound m2) ->
      CmsBound (m1 ++ m2)%kami (getCmsBound (m1 ++ m2)%kami).
  Proof.
    unfold CmsBound, Abstracted in *; intros.
    specializeAll s.
    apply getCalls_in in H1; destruct H1.
    + specialize (H H1); destruct H as [abss ?]; dest.
      exists abss; split; auto.
      apply getCalls_in_1; auto.
    + specialize (H0 H1); destruct H0 as [abss ?]; dest.
      exists abss; split; auto.
      apply getCalls_in_2; auto.
  Qed.

  Lemma getRegsBound_specialize:
    forall m i,
      Specializable m ->
      RegsBound (specializeMod m i) (getRegsBound m).
  Proof.
    unfold RegsBound; intros.
    rewrite specializeMod_regs; auto.
    apply abstracted_withIndex.
  Qed.

  Lemma getDmsBound_specialize:
    forall m i,
      Specializable m ->
      DmsBound (specializeMod m i) (getDmsBound m).
  Proof.
    unfold DmsBound; intros.
    rewrite specializeMod_defs; auto.
    apply abstracted_withIndex.
  Qed.

  Lemma getCmsBound_specialize:
    forall m i,
      Specializable m ->
      CmsBound (specializeMod m i) (getCmsBound m).
  Proof.
    unfold CmsBound; intros.
    rewrite specializeMod_calls; auto.
    apply abstracted_withIndex.
  Qed.

  Lemma getRegsBound_duplicate:
    forall m n,
      (forall i, Specializable (m i)) ->
      (forall i j, getRegsBound (m i) = getRegsBound (m j)) ->
      RegsBound (duplicate m n) (getRegsBound (m 0)).
  Proof.
    induction n; simpl; intros; [apply getRegsBound_specialize; auto|].
    apply concatMod_regsBound_2; auto.
    rewrite H0 with (j:= (S n)).
    apply getRegsBound_specialize; auto.
  Qed.

  Lemma getDmsBound_duplicate:
    forall m n,
      (forall i, Specializable (m i)) ->
      (forall i j, getDmsBound (m i) = getDmsBound (m j)) ->
      DmsBound (duplicate m n) (getDmsBound (m 0)).
  Proof.
    induction n; simpl; intros; [apply getDmsBound_specialize; auto|].
    apply concatMod_dmsBound_2; auto.
    rewrite H0 with (j:= (S n)).
    apply getDmsBound_specialize; auto.
  Qed.

  Lemma getCmsBound_duplicate:
    forall m n,
      (forall i, Specializable (m i)) ->
      (forall i j, getCmsBound (m i) = getCmsBound (m j)) ->
      CmsBound (duplicate m n) (getCmsBound (m 0)).
  Proof.
    induction n; simpl; intros; [apply getCmsBound_specialize; auto|].
    apply concatMod_cmsBound_2; auto.
    rewrite H0 with (j:= (S n)).
    apply getCmsBound_specialize; auto.
  Qed.

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

  Lemma regsBound_disj_regs:
    forall mb1 mb2,
      DisjPrefixes mb1 mb2 ->
      forall m1 m2,
        RegsBound m1 mb1 -> RegsBound m2 mb2 ->
        DisjList (namesOf (getRegInits m1)) (namesOf (getRegInits m2)).
  Proof.
    intros; apply disjPrefixes_DisjList with (ss1:= mb1) (ss2:= mb2); auto.
  Qed.

  Lemma dmsBound_disj_dms:
    forall mb1 mb2,
      DisjPrefixes mb1 mb2 ->
      forall m1 m2,
        DmsBound m1 mb1 -> DmsBound m2 mb2 ->
        DisjList (getDefs m1) (getDefs m2).
  Proof.
    intros; apply disjPrefixes_DisjList with (ss1:= mb1) (ss2:= mb2); auto.
  Qed.

  Lemma cmsBound_disj_calls:
    forall mb1 mb2,
      DisjPrefixes mb1 mb2 ->
      forall m1 m2,
        CmsBound m1 mb1 -> CmsBound m2 mb2 ->
        DisjList (getCalls m1) (getCalls m2).
  Proof.
    intros; apply disjPrefixes_DisjList with (ss1:= mb1) (ss2:= mb2); auto.
  Qed.

  Lemma bound_disj_dms_calls:
    forall mb1 mb2,
      DisjPrefixes mb1 mb2 ->
      forall m1 m2,
        DmsBound m1 mb1 -> CmsBound m2 mb2 ->
        DisjList (getDefs m1) (getCalls m2).
  Proof.
    intros; apply disjPrefixes_DisjList with (ss1:= mb1) (ss2:= mb2); auto.
  Qed.

  Lemma bound_disj_calls_dms:
    forall mb1 mb2,
      DisjPrefixes mb1 mb2 ->
      forall m1 m2,
        CmsBound m1 mb1 -> DmsBound m2 mb2 ->
        DisjList (getCalls m1) (getDefs m2).
  Proof.
    intros; apply disjPrefixes_DisjList with (ss1:= mb1) (ss2:= mb2); auto.
  Qed.

End Correctness.


