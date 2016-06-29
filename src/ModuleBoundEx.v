Require Import Bool String List Arith.Peano_dec.
Require Import Lib.FMap Lib.Struct Lib.CommonTactics Lib.Concat Lib.Indexer Lib.StringEq.
Require Import Syntax ParametricSyntax Semantics SemFacts Refinement.
Require Import Specialize Duplicate Notations.

Set Implicit Arguments.

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

  Record NameBound :=
    { originals : list string;
      prefixes : list (string * nat)
    }.

  Definition appendNameBound (nb1 nb2: NameBound) :=
    Build_NameBound (originals nb1 ++ originals nb2)
                    (prefixes nb1 ++ prefixes nb2).
  Notation "nb1 ++ nb2" := (appendNameBound nb1 nb2) : namebound_scope.
  Delimit Scope namebound_scope with nb.

  Definition unfoldNameBound (nb: NameBound) :=
    (originals nb) ++ (concat (map (fun p => duplicateElt (fst p) (snd p)) (prefixes nb))).

  Definition Abstracted (nb: NameBound) (ls: list string) :=
    EquivList (unfoldNameBound nb) ls.

  Lemma abstracted_nil: Abstracted (Build_NameBound nil nil) nil.
  Proof. compute; auto. Qed.

  Lemma abstracted_originals_refl: forall l, Abstracted (Build_NameBound l nil) l.
  Proof.
    unfold Abstracted, unfoldNameBound; simpl; intros.
    rewrite app_nil_r; apply EquivList_refl.
  Qed.

  Lemma abstracted_EquivList:
    forall nb l1 l2, Abstracted nb l1 -> EquivList l1 l2 -> Abstracted nb l2.
  Proof.
    unfold Abstracted; intros.
    eapply EquivList_trans; eauto.
  Qed.

  Lemma abstracted_app_1:
    forall a1 a2 l1 l2,
      Abstracted a1 l1 -> Abstracted a2 l2 ->
      Abstracted (a1 ++ a2)%nb (l1 ++ l2).
  Proof.
    unfold Abstracted, unfoldNameBound; intros.
    destruct a1 as [o1 p1], a2 as [o2 p2]; simpl in *.
    rewrite map_app, concat_app.
    inv H; inv H0; split.
    - subList_app_tac.
    - repeat apply SubList_app_3.
      + eapply SubList_trans; eauto; subList_app_tac.
      + eapply SubList_trans; eauto; subList_app_tac.
  Qed.

  Lemma abstracted_app_2:
    forall a l1 l2,
      Abstracted a l1 -> Abstracted a l2 ->
      Abstracted a (l1 ++ l2).
  Proof.
    unfold Abstracted, unfoldNameBound; intros.
    destruct a as [o p]; simpl in *.
    inv H; inv H0; split.
    - subList_app_tac.
    - apply SubList_app_3; auto.
  Qed.

  Definition RegsBound (regnb: NameBound) := Abstracted regnb (namesOf (getRegInits m)).
  Definition DmsBound (dmnb: NameBound) := Abstracted dmnb (getDefs m).
  Definition CmsBound (cmnb: NameBound) := Abstracted cmnb (getCalls m).

  Definition DisjPrefixes (ss1 ss2: list string) :=
    forall p1,
      In p1 ss1 ->
      forall p2,
        In p2 ss2 ->
        prefix p1 p2 = false /\ prefix p2 p1 = false.

  Definition DisjNameBound (nb1 nb2: NameBound) :=
    hasNoIndex (originals nb1) = true /\
    hasNoIndex (originals nb2) = true /\
    DisjList (originals nb1) (originals nb2) /\
    DisjPrefixes (map (fun p => fst p) (prefixes nb1)) (map (fun p => fst p) (prefixes nb2)).

  (* TODO: move to Reflection.v *)
  Fixpoint disjListStr (l1 l2: list string) :=
    match l1 with
    | nil => true
    | h1 :: t1 => if string_in h1 l2 then false else disjListStr t1 l2
    end.

  Lemma disjListStr_DisjList:
    forall l1 l2, disjListStr l1 l2 = true -> DisjList l1 l2.
  Proof.
    induction l1; simpl; intros; [apply DisjList_nil_1|].
    remember (string_in a l2) as ain; destruct ain; [inv H|].
    apply DisjList_string_cons; auto.
    apply string_in_dec_not_in in Heqain; auto.
  Qed.

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

  Definition disjNameBound (nb1 nb2: NameBound) :=
    (hasNoIndex (originals nb1))
      && (hasNoIndex (originals nb2))
      && (disjListStr (originals nb1) (originals nb2))
      && (disjPrefixes (map (fun p => fst p) (prefixes nb1))
                       (map (fun p => fst p) (prefixes nb2))).

  Lemma disjNameBound_DisjNameBound:
    forall nb1 nb2, disjNameBound nb1 nb2 = true -> DisjNameBound nb1 nb2.
  Proof.
    unfold disjNameBound, DisjNameBound; intros.
    repeat (apply andb_true_iff in H; dest).
    Opaque DisjPrefixes. repeat split; auto. Transparent DisjPrefixes.
    - apply disjListStr_DisjList; auto.
    - apply disjPrefixes_DisjPrefixes; auto.
  Qed.

End ModuleBound.

Section Bounds.
  Notation "nb1 ++ nb2" := (appendNameBound nb1 nb2) : namebound_scope.
  Delimit Scope namebound_scope with nb.

  Lemma concatMod_regsBound_1:
    forall m1 m2 rb1 rb2,
      RegsBound m1 rb1 ->
      RegsBound m2 rb2 ->
      RegsBound (m1 ++ m2)%kami (rb1 ++ rb2)%nb.
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
    apply abstracted_app_2; auto.
  Qed.

  Lemma concatMod_dmsBound_1:
    forall m1 m2 db1 db2,
      DmsBound m1 db1 ->
      DmsBound m2 db2 ->
      DmsBound (m1 ++ m2)%kami (db1 ++ db2)%nb.
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
    apply abstracted_app_2; auto.
  Qed.

  Lemma concatMod_cmsBound_1:
    forall m1 m2 cb1 cb2,
      CmsBound m1 cb1 ->
      CmsBound m2 cb2 ->
      CmsBound (m1 ++ m2)%kami (cb1 ++ cb2)%nb.
  Proof.
    unfold CmsBound in *; simpl; intros.
    apply EquivList_trans with (l2:= getCalls m1 ++ getCalls m2).
    - apply abstracted_app_1; auto.
    - split; [apply getCalls_subList_1|apply getCalls_subList_2].
  Qed.

  Lemma concatMod_cmsBound_2:
    forall m1 m2 cb,
      CmsBound m1 cb ->
      CmsBound m2 cb ->
      CmsBound (m1 ++ m2)%kami cb.
  Proof.
    unfold CmsBound in *; simpl; intros.
    apply EquivList_trans with (l2:= getCalls m1 ++ getCalls m2).
    - apply abstracted_app_2; auto.
    - split; [apply getCalls_subList_1|apply getCalls_subList_2].
  Qed.

  (** normal boundaries *)
  
  Definition getRegsBound (m: Modules) := Build_NameBound (namesOf (getRegInits m)) nil.
  Definition getDmsBound (m: Modules) := Build_NameBound (getDefs m) nil.
  Definition getCmsBound (m: Modules) := Build_NameBound (getCalls m) nil.

  Lemma getRegsBound_bounded:
    forall m, RegsBound m (getRegsBound m).
  Proof. intros; apply abstracted_originals_refl. Qed.

  Lemma getDmsBound_bounded:
    forall m, DmsBound m (getDmsBound m).
  Proof. intros; apply abstracted_originals_refl. Qed.
  
  Lemma getCmsBound_bounded:
    forall m, CmsBound m (getCmsBound m).
  Proof. intros; apply abstracted_originals_refl. Qed.

  Lemma getRegsBound_modular:
    forall m1 m2,
      RegsBound m1 (getRegsBound m1) ->
      RegsBound m2 (getRegsBound m2) ->
      RegsBound (m1 ++ m2)%kami (getRegsBound (m1 ++ m2)%kami).
  Proof.
    intros.
    replace (getRegsBound (m1 ++ m2)%kami) with (getRegsBound m1 ++ getRegsBound m2)%nb.
    - apply concatMod_regsBound_1; auto.
    - unfold getRegsBound, appendNameBound; simpl.
      unfold RegInitT; rewrite namesOf_app; reflexivity.
  Qed.
  
  Lemma getDmsBound_modular:
    forall m1 m2,
      DmsBound m1 (getDmsBound m1) ->
      DmsBound m2 (getDmsBound m2) ->
      DmsBound (m1 ++ m2)%kami (getDmsBound (m1 ++ m2)%kami).
  Proof.
    intros.
    replace (getDmsBound (m1 ++ m2)%kami) with (getDmsBound m1 ++ getDmsBound m2)%nb.
    - apply concatMod_dmsBound_1; auto.
    - unfold getDmsBound; rewrite getDefs_app; reflexivity.
  Qed.

  Lemma getCmsBound_modular:
    forall m1 m2,
      CmsBound m1 (getCmsBound m1) ->
      CmsBound m2 (getCmsBound m2) ->
      CmsBound (m1 ++ m2)%kami (getCmsBound (m1 ++ m2)%kami).
  Proof.
    intros; pose proof (concatMod_cmsBound_1 H H0); clear H H0.
    eapply EquivList_trans; eauto.
    unfold unfoldNameBound.
    apply EquivList_app; [|apply EquivList_refl].
    split; [apply getCalls_subList_2|apply getCalls_subList_1].
  Qed.

  (** duplicate boundaries *)

  Fixpoint getDupNameBound (names: list string) (n: nat) :=
    match names with
    | nil => nil
    | name :: names' => (name, n) :: (getDupNameBound names' n)
    end.
      
  Definition getDupRegsBound m n :=
    Build_NameBound nil (getDupNameBound (namesOf (getRegInits m)) n).
  Definition getDupDmsBound m n :=
    Build_NameBound nil (getDupNameBound (getDefs m) n).
  Definition getDupCmsBound m n :=
    Build_NameBound nil (getDupNameBound (getCalls m) n).

  Lemma getDupNameBound_concat_vertical:
    forall names n,
      EquivList
        (concat
           (map (fun p => duplicateElt (fst p) (snd p))
                (getDupNameBound names (S n))))
        ((map (spf (S n)) names)
           ++ (concat (map (fun p => duplicateElt (fst p) (snd p))
                           (getDupNameBound names n)))).
  Proof.
    induction names; simpl; intros; [apply EquivList_nil|].
    apply EquivList_cons; auto.
    eapply EquivList_trans.
    - apply EquivList_app.
      + apply EquivList_refl.
      + apply IHnames.
    - clear; equivList_app_tac.
  Qed.

  Lemma getDupRegsBound_bounded:
    forall m n,
      Specializable m ->
      RegsBound (duplicate m n) (getDupRegsBound m n).
  Proof.
    unfold RegsBound, Abstracted, unfoldNameBound; simpl; intros.
    induction n; simpl; intros.
    - rewrite specializeMod_regs by auto.
      generalize (namesOf (getRegInits m)) as regs; clear.
      induction regs; simpl; intros; [apply EquivList_nil|].
      apply EquivList_cons; auto.
    - unfold RegInitT; rewrite namesOf_app.
      rewrite specializeMod_regs by auto.
      match goal with
      | [H: EquivList ?ilhs _ |- EquivList ?lhs (?nl ++ _) ] =>
        apply EquivList_trans with (l2:= (nl ++ ilhs))
      end.
      + apply getDupNameBound_concat_vertical.
      + apply EquivList_app; [apply EquivList_refl|auto].
  Qed.

  Lemma getDupDmsBound_bounded:
    forall m n,
      Specializable m ->
      DmsBound (duplicate m n) (getDupDmsBound m n).
  Proof.
    unfold DmsBound, Abstracted, unfoldNameBound; simpl; intros.
    induction n; simpl; intros.
    - rewrite specializeMod_defs by auto.
      generalize (getDefs m) as dms; clear.
      induction dms; simpl; intros; [apply EquivList_nil|].
      apply EquivList_cons; auto.
    - rewrite getDefs_app.
      rewrite specializeMod_defs by auto.
      match goal with
      | [H: EquivList ?ilhs _ |- EquivList ?lhs (?nl ++ _) ] =>
        apply EquivList_trans with (l2:= (nl ++ ilhs))
      end.
      + apply getDupNameBound_concat_vertical.
      + apply EquivList_app; [apply EquivList_refl|auto].
  Qed.

  Lemma getDupCmsBound_bounded:
    forall m n,
      Specializable m ->
      CmsBound (duplicate m n) (getDupCmsBound m n).
  Proof.
    unfold CmsBound, Abstracted, unfoldNameBound; simpl; intros.
    induction n; simpl; intros.
    - rewrite specializeMod_calls by auto.
      generalize (getCalls m) as cms; clear.
      induction cms; simpl; intros; [apply EquivList_nil|].
      apply EquivList_cons; auto.
    - apply EquivList_trans with
      (l2:= getCalls (specializeMod m (S n)) ++ getCalls (duplicate m n));
        [|split; [apply getCalls_subList_1|apply getCalls_subList_2]].
      rewrite specializeMod_calls by auto.
      match goal with
      | [H: EquivList ?ilhs _ |- EquivList ?lhs (?nl ++ _) ] =>
        apply EquivList_trans with (l2:= (nl ++ ilhs))
      end.
      + apply getDupNameBound_concat_vertical.
      + apply EquivList_app; [apply EquivList_refl|auto].
  Qed.

  (** meta-module boundaries *)

  Definition getOneNameBound (nr: NameRec) :=
    Build_NameBound [nameVal nr] nil.
  Definition getRepNameBound (nr: NameRec) (n: nat) :=
    Build_NameBound nil [(nameVal nr, n)].

  Lemma getOneNameBound_regs_bounded:
    forall mregs mrules mdms rb,
      RegsBound (modFromMeta (Build_MetaModule mregs mrules mdms)) rb ->
      forall c nr,
        RegsBound (modFromMeta (Build_MetaModule (OneReg c nr :: mregs) mrules mdms))
                  (getOneNameBound nr ++ rb)%nb.
  Proof.
    unfold RegsBound, modFromMeta; simpl; intros.
    match goal with
    | [ |- Abstracted _ (?h :: ?t) ] => change (h :: t) with ([h] ++ t)
    end.
    apply abstracted_app_1; auto.
    apply EquivList_refl.
  Qed.

  Lemma getRepNameBound_getListFromRep_abstracted:
    forall {B} (genF: nat -> B) nr n,
      Abstracted (getRepNameBound nr n)
                 (namesOf (getListFromRep string_of_nat genF (nameVal nr) (getNatListToN n))).
  Proof.
    unfold Abstracted, getRepNameBound, unfoldNameBound; simpl; intros.
    rewrite app_nil_r.
    induction n; simpl; [apply EquivList_refl|].
    apply EquivList_cons; auto.
  Qed.

  Lemma getRepNameBound_regs_bounded:
    forall mregs mrules mdms rb,
      RegsBound (modFromMeta (Build_MetaModule mregs mrules mdms)) rb ->
      forall initF nr n,
        RegsBound (modFromMeta (Build_MetaModule
                                  (RepReg string_of_nat
                                          string_of_nat_into
                                          withIndex_index_eq
                                          initF nr (getNatListToN_NoDup n) :: mregs) mrules mdms))
                  (getRepNameBound nr n ++ rb)%nb.
  Proof.
    unfold RegsBound, modFromMeta; simpl; intros.
    rewrite namesOf_app.
    apply abstracted_app_1; auto.
    apply getRepNameBound_getListFromRep_abstracted.
  Qed.

  Lemma getOneNameBound_dms_bounded:
    forall mregs mrules mdms rb,
      DmsBound (modFromMeta (Build_MetaModule mregs mrules mdms)) rb ->
      forall s nr,
        DmsBound (modFromMeta (Build_MetaModule mregs mrules (OneMeth s nr :: mdms)))
                 (getOneNameBound nr ++ rb)%nb.
  Proof.
    unfold DmsBound, modFromMeta, getDefs; simpl; intros.
    match goal with
    | [ |- Abstracted _ (?h :: ?t) ] => change (h :: t) with ([h] ++ t)
    end.
    apply abstracted_app_1; auto.
    apply EquivList_refl.
  Qed.

  Lemma getRepNameBound_dms_bounded:
    forall mregs mrules mdms rb,
      DmsBound (modFromMeta (Build_MetaModule mregs mrules mdms)) rb ->
      forall dm nr n,
        DmsBound (modFromMeta (Build_MetaModule
                                 mregs mrules
                                 (RepMeth string_of_nat
                                          string_of_nat_into
                                          natToVoid
                                          withIndex_index_eq
                                          dm nr (getNatListToN_NoDup n) :: mdms)))
                  (getRepNameBound nr n ++ rb)%nb.
  Proof.
    unfold DmsBound, modFromMeta, getDefs; simpl; intros.
    rewrite namesOf_app.
    apply abstracted_app_1; auto.
    apply getRepNameBound_getListFromRep_abstracted.
  Qed.

  (* Lemma getRegsBoundM_bounded: *)
  (*   forall mm, RegsBound (modFromMeta mm) (getRegsBoundM mm). *)
  (* Proof. intros; apply abstracted_metaRegs. Qed. *)
    
  (* Lemma getDmsBoundM_bounded: *)
  (*   forall mm, DmsBound (modFromMeta mm) (getDmsBoundM mm). *)
  (* Proof. intros; apply abstracted_metaMeths. Qed. *)

  (* Lemma getCmsBoundM_bounded: *)
  (*   forall mm, CmsBound (modFromMeta mm) (getCmsBoundM mm). *)
  (* Proof. intros; apply abstracted_metaCms. Qed. *)

End Bounds.

Section Correctness.

  Lemma disjPrefixes_DisjList:
    forall ss1 ss2,
      DisjNameBound ss1 ss2 ->
      forall l1 l2,
        Abstracted ss1 l1 -> Abstracted ss2 l2 ->
        DisjList l1 l2.
  Proof.
    unfold DisjNameBound, Abstracted, DisjList; intros.
    destruct (in_dec string_dec e l1); [|left; auto].
    destruct (in_dec string_dec e l2); [|right; auto].

    exfalso; dest.
    inv H0; inv H1; clear H0 H5.
    specialize (H6 _ i); specialize (H7 _ i0); clear i i0.
    unfold unfoldNameBound in H6, H7.
    apply in_app_or in H6; apply in_app_or in H7.
    destruct H6, H7.
    - destruct (H3 e); auto.
    - clear -H H0 H1; apply in_concat_iff in H1; destruct H1 as [l ?]; dest.
      apply in_map_iff in H1; destruct H1 as [[s n] ?]; dest; subst; simpl in *.
      admit.
    - admit.
    - admit.
  Qed.

  Lemma regsBound_disj_regs:
    forall mb1 mb2,
      DisjNameBound mb1 mb2 ->
      forall m1 m2,
        RegsBound m1 mb1 -> RegsBound m2 mb2 ->
        DisjList (namesOf (getRegInits m1)) (namesOf (getRegInits m2)).
  Proof.
    intros; apply disjPrefixes_DisjList with (ss1:= mb1) (ss2:= mb2); auto.
  Qed.

  Lemma dmsBound_disj_dms:
    forall mb1 mb2,
      DisjNameBound mb1 mb2 ->
      forall m1 m2,
        DmsBound m1 mb1 -> DmsBound m2 mb2 ->
        DisjList (getDefs m1) (getDefs m2).
  Proof.
    intros; apply disjPrefixes_DisjList with (ss1:= mb1) (ss2:= mb2); auto.
  Qed.

  Lemma cmsBound_disj_calls:
    forall mb1 mb2,
      DisjNameBound mb1 mb2 ->
      forall m1 m2,
        CmsBound m1 mb1 -> CmsBound m2 mb2 ->
        DisjList (getCalls m1) (getCalls m2).
  Proof.
    intros; apply disjPrefixes_DisjList with (ss1:= mb1) (ss2:= mb2); auto.
  Qed.

  Lemma bound_disj_dms_calls:
    forall mb1 mb2,
      DisjNameBound mb1 mb2 ->
      forall m1 m2,
        DmsBound m1 mb1 -> CmsBound m2 mb2 ->
        DisjList (getDefs m1) (getCalls m2).
  Proof.
    intros; apply disjPrefixes_DisjList with (ss1:= mb1) (ss2:= mb2); auto.
  Qed.

  Lemma bound_disj_calls_dms:
    forall mb1 mb2,
      DisjNameBound mb1 mb2 ->
      forall m1 m2,
        CmsBound m1 mb1 -> DmsBound m2 mb2 ->
        DisjList (getCalls m1) (getDefs m2).
  Proof.
    intros; apply disjPrefixes_DisjList with (ss1:= mb1) (ss2:= mb2); auto.
  Qed.

End Correctness.

