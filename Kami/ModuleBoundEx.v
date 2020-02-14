Require Import Bool String List Arith.Peano_dec.
Require Import Lib.FMap Lib.Struct Lib.CommonTactics Lib.Concat Lib.Indexer Lib.StringEq.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.RefinementFacts.
Require Import Kami.Specialize Kami.Duplicate Kami.Notations.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section ModuleBound.
  Variable m: Modules.
  Variable n: nat. (* Assume that all indexed names in "m" is parametrized by "n" *)

  Record NameBound :=
    { originals : list string;
      prefixes : list string
    }.

  Definition emptyNameBound := Build_NameBound nil nil.
  Definition addOriginal s nb := Build_NameBound (s :: originals nb) (prefixes nb).
  Definition addPrefix p nb := Build_NameBound (originals nb) (p :: prefixes nb).

  Definition appendNameBound (nb1 nb2: NameBound) :=
    Build_NameBound (originals nb1 ++ originals nb2)
                    (prefixes nb1 ++ prefixes nb2).

  Declare Scope namebound_scope.
  Notation "nb1 ++ nb2" := (appendNameBound nb1 nb2) : namebound_scope.
  Delimit Scope namebound_scope with nb.

  Definition intersectNameBound (nb1 nb2: NameBound) :=
    Build_NameBound (filter (fun o => string_in o (originals nb2)) (originals nb1))
                    (filter (fun p => string_in p (prefixes nb2)) (prefixes nb1)).
    
  Definition subtractNameBound (nb1 nb2: NameBound) :=
    Build_NameBound (filter (fun o => negb (string_in o (originals nb2))) (originals nb1))
                    (filter (fun p => negb (string_in p (prefixes nb2))) (prefixes nb1)).

  Definition unfoldNameBound (nb: NameBound) :=
    (originals nb) ++ (concat (map (fun p => duplicateElt p n) (prefixes nb))).

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

  Lemma EquivList_filter:
    forall l1 l2 l3 l4,
      EquivList l1 l2 -> EquivList l3 l4 ->
      EquivList (filter (fun d => string_in d l3) l1)
                (filter (fun d => string_in d l4) l2).
  Proof.
    unfold EquivList, SubList; intros; dest; split; intros.
    - specializeAll e.
      apply filter_In; apply filter_In in H3; dest; split; auto.
      apply eq_sym, string_in_dec_in in H4.
      remember (string_in e l4) as ein; destruct ein; auto.
      exfalso; apply string_in_dec_not_in in Heqein; auto.
    - specializeAll e.
      apply filter_In; apply filter_In in H3; dest; split; auto.
      apply eq_sym, string_in_dec_in in H4.
      remember (string_in e l3) as ein; destruct ein; auto.
      exfalso; apply string_in_dec_not_in in Heqein; auto.
  Qed.

  Lemma EquivList_filter_neg:
    forall l1 l2 l3 l4,
      EquivList l1 l2 -> EquivList l3 l4 ->
      EquivList (filter (fun d => negb (string_in d l3)) l1)
                (filter (fun d => negb (string_in d l4)) l2).
  Proof.
    unfold EquivList, SubList; intros; dest; split; intros.
    - specializeAll e.
      apply filter_In; apply filter_In in H3; dest; split; auto.
      rewrite negb_true_iff in *.
      apply eq_sym, string_in_dec_not_in in H4.
      remember (string_in e l4) as ein; destruct ein; auto.
      exfalso; apply string_in_dec_in in Heqein; auto.
    - specializeAll e.
      apply filter_In; apply filter_In in H3; dest; split; auto.
      rewrite negb_true_iff in *.
      apply eq_sym, string_in_dec_not_in in H4.
      remember (string_in e l3) as ein; destruct ein; auto.
      exfalso; apply string_in_dec_in in Heqein; auto.
  Qed.

  Lemma filter_app:
    forall {A} (l1 l2: list A) f,
      filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
  Proof.
    induction l1; simpl; intros; [reflexivity|].
    destruct (f a); auto.
    simpl; f_equal; auto.
  Qed.

  Lemma filter_Forall_true:
    forall {A} (l: list A) f,
      Forall (fun a => f a = true) l ->
      filter f l = l.
  Proof.
    induction l; simpl; intros; [reflexivity|].
    inv H; rewrite H2, IHl; auto.
  Qed.

  Lemma filter_DisjList_app_1:
    forall l1 l2 l3,
      DisjList l1 l3 ->
      filter (fun d => string_in d (l2 ++ l3)) l1 =
      filter (fun d => string_in d l2) l1.
  Proof.
    induction l1; simpl; intros; auto.
    remember (string_in a l2) as ain; destruct ain; simpl.
    - apply string_in_dec_in in Heqain.
      remember (string_in _ _) as aain; destruct aain; simpl.
      + rewrite IHl1; [reflexivity|].
        eapply DisjList_cons; eauto.
      + exfalso; apply string_in_dec_not_in in Heqaain; elim Heqaain.
        apply in_or_app; auto.
    - apply string_in_dec_not_in in Heqain.
      remember (string_in _ _) as aain; destruct aain; simpl.
      + exfalso; apply string_in_dec_in in Heqaain.
        apply in_app_or in Heqaain; destruct Heqaain; auto.
        specialize (H a); destruct H; auto.
        elim H; left; auto.
      + apply IHl1; eapply DisjList_cons; eauto.
  Qed.

  Lemma filter_DisjList_app_2:
    forall l1 l2 l3,
      DisjList l1 l2 ->
      filter (fun d => string_in d (l2 ++ l3)) l1 =
      filter (fun d => string_in d l3) l1.
  Proof.
    induction l1; simpl; intros; auto.
    remember (string_in a l3) as ain; destruct ain; simpl.
    - apply string_in_dec_in in Heqain.
      remember (string_in _ _) as aain; destruct aain; simpl.
      + rewrite IHl1; [reflexivity|].
        eapply DisjList_cons; eauto.
      + exfalso; apply string_in_dec_not_in in Heqaain; elim Heqaain.
        apply in_or_app; auto.
    - apply string_in_dec_not_in in Heqain.
      remember (string_in _ _) as aain; destruct aain; simpl.
      + exfalso; apply string_in_dec_in in Heqaain.
        apply in_app_or in Heqaain; destruct Heqaain; auto.
        specialize (H a); destruct H; auto.
        elim H; left; auto.
      + apply IHl1; eapply DisjList_cons; eauto.
  Qed.

  Lemma filter_DisjList_app_neg_1:
    forall l1 l2 l3,
      DisjList l1 l3 ->
      filter (fun d => negb (string_in d (l2 ++ l3))) l1 =
      filter (fun d => negb (string_in d l2)) l1.
  Proof.
    induction l1; simpl; intros; auto.
    remember (string_in a l2) as ain; destruct ain; simpl.
    - apply string_in_dec_in in Heqain.
      remember (string_in _ _) as aain; destruct aain; simpl.
      + apply IHl1; eapply DisjList_cons; eauto.
      + exfalso; apply string_in_dec_not_in in Heqaain; elim Heqaain.
        apply in_or_app; auto.
    - apply string_in_dec_not_in in Heqain.
      remember (string_in _ _) as aain; destruct aain; simpl.
      + apply string_in_dec_in in Heqaain.
        exfalso; apply in_app_or in Heqaain; destruct Heqaain; auto.
        specialize (H a); destruct H; auto.
        elim H; left; auto.
      + f_equal; apply IHl1; eapply DisjList_cons; eauto.
  Qed.

  Lemma filter_DisjList_app_neg_2:
    forall l1 l2 l3,
      DisjList l1 l2 ->
      filter (fun d => negb (string_in d (l2 ++ l3))) l1 =
      filter (fun d => negb (string_in d l3)) l1.
  Proof.
    induction l1; simpl; intros; auto.
    remember (string_in a l3) as ain; destruct ain; simpl.
    - apply string_in_dec_in in Heqain.
      remember (string_in _ _) as aain; destruct aain; simpl.
      + apply IHl1; eapply DisjList_cons; eauto.
      + exfalso; apply string_in_dec_not_in in Heqaain; elim Heqaain.
        apply in_or_app; auto.
    - apply string_in_dec_not_in in Heqain.
      remember (string_in _ _) as aain; destruct aain; simpl.
      + apply string_in_dec_in in Heqaain.
        exfalso; apply in_app_or in Heqaain; destruct Heqaain; auto.
        specialize (H a); destruct H; auto.
        elim H; left; auto.
      + f_equal; apply IHl1; eapply DisjList_cons; eauto.
  Qed.

  Lemma duplicateElt_in_DisjList:
    forall p n l,
      ~ In p l ->
      DisjList (duplicateElt p n) (concat (map (fun t => duplicateElt t n) l)).
  Proof.
    induction l; simpl; intros; [apply DisjList_nil_2|].
    apply DisjList_comm, DisjList_app_4.
    - apply duplicateElt_DisjList; intuition.
    - apply DisjList_comm; auto.
  Qed.

  Lemma duplicateElt_in_filter:
    forall p n l,
      In p l ->
      duplicateElt p n =
      filter (fun d => string_in d (concat (map (fun p => duplicateElt p n) l)))
             (duplicateElt p n).
  Proof.
    intros.
    rewrite filter_Forall_true; [reflexivity|].
    apply Forall_forall; intros pn ?.
    destruct (string_in _ _) eqn:Hin; [reflexivity|].
    exfalso.
    apply eq_sym, string_in_dec_not_in in Hin; elim Hin; clear Hin.
    induction l; simpl; intros; [dest_in|].
    inv H.
    - apply in_or_app; left; assumption.
    - apply in_or_app; right; auto.
  Qed.

  Lemma duplicateElt_concat_DisjList:
    forall n l1 l2,
      DisjList l1 l2 ->
      DisjList (concat (map (fun t => duplicateElt t n) l1))
               (concat (map (fun t => duplicateElt t n) l2)).
  Proof.
    induction l1; simpl; intros; [apply DisjList_nil_1|].
    apply DisjList_app_4.
    - apply duplicateElt_in_DisjList.
      specialize (H a); destruct H; auto.
      elim H; left; auto.
    - apply IHl1; eapply DisjList_cons; eauto.
  Qed.

  Lemma concat_filter_comm:
    forall p1 p2 n,
      concat
        (map (fun p => duplicateElt p n)
             (filter (fun p => string_in p p2) p1)) =
      filter
        (fun d => string_in d (concat (map (fun p => duplicateElt p n) p2)))
        (concat (map (fun p => duplicateElt p n) p1)).
  Proof.
    induction p1; simpl; intros; auto.
    remember (string_in a p2) as ain; destruct ain; simpl.
    - rewrite IHp1.
      generalize (concat (map (fun p : string => duplicateElt p n0) p1)); intros.
      rewrite filter_app; f_equal.
      apply string_in_dec_in in Heqain.
      apply duplicateElt_in_filter; assumption.
    - rewrite IHp1; clear -Heqain.
      generalize (concat (map (fun p : string => duplicateElt p n0) p1)); intros.
      rewrite filter_app.
      replace (filter (fun d => string_in d (concat (map (fun p => duplicateElt p n0) p2)))
                      (duplicateElt a n0)) with (@nil string); [reflexivity|].
      apply eq_sym.
      apply string_in_dec_not_in in Heqain.
      rewrite <-app_nil_l with (l:= (concat (map (fun p : string => duplicateElt p n0) p2))).
      rewrite filter_DisjList_app_1.
      + induction (duplicateElt a n0); auto.
      + apply duplicateElt_in_DisjList; auto.
  Qed.

  Lemma concat_filter_comm_neg:
    forall p1 p2 n,
      concat
        (map (fun p => duplicateElt p n)
             (filter (fun p => negb (string_in p p2)) p1)) =
      filter
        (fun d => negb (string_in d (concat (map (fun p => duplicateElt p n) p2))))
        (concat (map (fun p => duplicateElt p n) p1)).
  Proof.
    induction p1; simpl; intros; auto.
    remember (string_in a p2) as ain; destruct ain; simpl.
    - rewrite filter_app.
      replace (filter
                (fun d => negb (string_in d (concat (map (fun p => duplicateElt p n0) p2))))
                (duplicateElt a n0)) with (nil (A:= string)).
      + rewrite app_nil_l; auto.
      + apply string_in_dec_in in Heqain; clear -Heqain.
        induction n0; simpl.
        * remember (string_in _ _) as iin; destruct iin; auto.
          exfalso; apply string_in_dec_not_in in Heqiin; elim Heqiin; clear Heqiin.
          induction p2; [inv Heqain|].
          inv Heqain; simpl; auto.
        * remember (string_in _ _) as iin; destruct iin; simpl.
          { clear -IHn0; induction (duplicateElt a n0); simpl in *; auto.
            remember (string_in a0 (concat (map (fun p => duplicateElt p n0) p2)))
              as allin; destruct allin; simpl in IHn0; [|inv IHn0].
            remember (string_in a0 (concat (map (fun p => (p) __ (S n0) :: duplicateElt p n0) p2)))
              as cllin; destruct cllin; simpl; auto.
            exfalso; apply string_in_dec_not_in in Heqcllin; elim Heqcllin.
            apply string_in_dec_in in Heqallin; clear -Heqallin.
            apply in_concat_iff in Heqallin; dest.
            apply in_map_iff in H; dest; subst.
            apply in_concat_iff; eexists; split.
            { apply in_map_iff; eexists; split; eauto. }
            { right; auto. }
          }
          { exfalso; apply string_in_dec_not_in in Heqiin; elim Heqiin; clear Heqiin.
            apply in_concat_iff; eexists; split.
            { apply in_map_iff; eexists; split; eauto. }
            { left; auto. }
          }
    - rewrite IHp1; clear -Heqain.
      generalize (concat (map (fun p : string => duplicateElt p n0) p1)); intros.
      rewrite filter_app; f_equal.
      apply string_in_dec_not_in in Heqain.
      rewrite <-app_nil_l with (l:= (concat (map (fun p : string => duplicateElt p n0) p2))).
      rewrite filter_DisjList_app_neg_1.
      + induction (duplicateElt a n0); auto.
        simpl; f_equal; auto.
      + apply duplicateElt_in_DisjList; auto.
  Qed.

  Lemma hasNoIndex_duplicateElt_DisjList:
    forall l p n,
      hasNoIndex l = true ->
      DisjList l (duplicateElt p n).
  Proof.
    induction n0; simpl; intros.
    - unfold DisjList; intros.
      destruct (in_dec string_dec e [p __ 0]); auto.
      destruct (in_dec string_dec e l); auto.
      exfalso; inv i; [|inv H0].
      pose proof (hasNoIndex_in _ H _ i0).
      clear -H0.
      Transparent withIndex.
      unfold withIndex in H0; generalize H0; apply badIndex.
      Opaque withIndex.
    - apply DisjList_comm, DisjList_string_cons; [|apply DisjList_comm; auto].
      intro Hx; pose proof (hasNoIndex_in _ H _ Hx).
      Transparent withIndex.
      unfold withIndex in H0; generalize H0; apply badIndex.
      Opaque withIndex.
  Qed.

  Lemma subtractNameBound_filter_abstracted:
    forall nb1 nb2 l1 l2,
      hasNoIndex (originals nb1) = true ->
      hasNoIndex (originals nb2) = true ->
      Abstracted nb1 l1 -> Abstracted nb2 l2 ->
      Abstracted (subtractNameBound nb1 nb2) 
                 (filter (fun d => negb (string_in d l2)) l1).
  Proof.
    unfold Abstracted, unfoldNameBound; intros.
    destruct nb1 as [o1 p1], nb2 as [o2 p2]; simpl in *.
    eapply EquivList_trans; [|eapply EquivList_filter_neg; eauto].
    rewrite filter_app; apply EquivList_app.
    - rewrite filter_DisjList_app_neg_1; [apply EquivList_refl|].
      clear -H; induction p2; [apply DisjList_nil_2|].
      simpl; apply DisjList_comm, DisjList_app_4.
      + apply DisjList_comm.
        apply hasNoIndex_duplicateElt_DisjList; auto.
      + apply DisjList_comm; auto.
    - rewrite filter_DisjList_app_neg_2.
      + rewrite concat_filter_comm_neg; apply EquivList_refl.
      + clear -H0; apply DisjList_comm.
        induction p1; [apply DisjList_nil_2|].
        simpl; apply DisjList_comm, DisjList_app_4.
        * apply DisjList_comm, hasNoIndex_duplicateElt_DisjList; auto.
        * apply DisjList_comm; auto.
  Qed.

  Lemma intersectNameBound_filter_abstracted:
    forall nb1 nb2 l1 l2,
      hasNoIndex (originals nb1) = true ->
      hasNoIndex (originals nb2) = true ->
      Abstracted nb1 l1 -> Abstracted nb2 l2 ->
      Abstracted (intersectNameBound nb1 nb2) 
                 (filter (fun d => string_in d l2) l1).
  Proof.
    unfold Abstracted, unfoldNameBound; intros.
    destruct nb1 as [o1 p1], nb2 as [o2 p2]; simpl in *.
    eapply EquivList_trans; [|eapply EquivList_filter; eauto].
    rewrite filter_app; apply EquivList_app.
    - rewrite filter_DisjList_app_1; [apply EquivList_refl|].
      clear -H; induction p2; [apply DisjList_nil_2|].
      simpl; apply DisjList_comm, DisjList_app_4.
      + apply DisjList_comm.
        apply hasNoIndex_duplicateElt_DisjList; auto.
      + apply DisjList_comm; auto.
    - rewrite filter_DisjList_app_2.
      + rewrite concat_filter_comm; apply EquivList_refl.
      + clear -H0; apply DisjList_comm.
        induction p1; [apply DisjList_nil_2|].
        simpl; apply DisjList_comm, DisjList_app_4.
        * apply DisjList_comm, hasNoIndex_duplicateElt_DisjList; auto.
        * apply DisjList_comm; auto.
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
    DisjList (prefixes nb1) (prefixes nb2).

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

  Definition disjNameBound (nb1 nb2: NameBound) :=
    (hasNoIndex (originals nb1))
      && (hasNoIndex (originals nb2))
      && (disjListStr (originals nb1) (originals nb2))
      && (disjListStr (prefixes nb1) (prefixes nb2)).

  Lemma disjNameBound_DisjNameBound:
    forall nb1 nb2, disjNameBound nb1 nb2 = true -> DisjNameBound nb1 nb2.
  Proof.
    unfold disjNameBound, DisjNameBound; intros.
    repeat (apply andb_true_iff in H; dest).
    Opaque DisjPrefixes. repeat split; auto. Transparent DisjPrefixes.
    - apply disjListStr_DisjList; auto.
    - apply disjListStr_DisjList; auto.
  Qed.

End ModuleBound.

Section Bounds.
  Declare Scope namebound_scope.
  Notation "nb1 ++ nb2" := (appendNameBound nb1 nb2) : namebound_scope.
  Delimit Scope namebound_scope with nb.

  Lemma concatMod_regsBound_1:
    forall m1 m2 n rb1 rb2,
      RegsBound m1 n rb1 ->
      RegsBound m2 n rb2 ->
      RegsBound (m1 ++ m2)%kami n (rb1 ++ rb2)%nb.
  Proof.
    unfold RegsBound; simpl; intros.
    unfold RegInitT; rewrite namesOf_app.
    apply abstracted_app_1; auto.
  Qed.

  Lemma concatMod_regsBound_2:
    forall m1 m2 n rb,
      RegsBound m1 n rb ->
      RegsBound m2 n rb ->
      RegsBound (m1 ++ m2)%kami n rb.
  Proof.
    unfold RegsBound; simpl; intros.
    unfold RegInitT; rewrite namesOf_app.
    apply abstracted_app_2; auto.
  Qed.

  Lemma concatMod_dmsBound_1:
    forall m1 m2 n db1 db2,
      DmsBound m1 n db1 ->
      DmsBound m2 n db2 ->
      DmsBound (m1 ++ m2)%kami n (db1 ++ db2)%nb.
  Proof.
    unfold DmsBound; simpl; intros.
    rewrite getDefs_app.
    apply abstracted_app_1; auto.
  Qed.

  Lemma concatMod_dmsBound_2:
    forall m1 m2 n db,
      DmsBound m1 n db ->
      DmsBound m2 n db ->
      DmsBound (m1 ++ m2)%kami n db.
  Proof.
    unfold DmsBound; simpl; intros.
    rewrite getDefs_app.
    apply abstracted_app_2; auto.
  Qed.

  Lemma concatMod_cmsBound_1:
    forall m1 m2 n cb1 cb2,
      CmsBound m1 n cb1 ->
      CmsBound m2 n cb2 ->
      CmsBound (m1 ++ m2)%kami n (cb1 ++ cb2)%nb.
  Proof.
    unfold CmsBound in *; simpl; intros.
    apply EquivList_trans with (l2:= getCalls m1 ++ getCalls m2).
    - apply abstracted_app_1; auto.
    - split; [apply getCalls_subList_1|apply getCalls_subList_2].
  Qed.

  Lemma concatMod_cmsBound_2:
    forall m1 m2 n cb,
      CmsBound m1 n cb ->
      CmsBound m2 n cb ->
      CmsBound (m1 ++ m2)%kami n cb.
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
    forall m n, RegsBound m n (getRegsBound m).
  Proof. intros; apply abstracted_originals_refl. Qed.

  Lemma getDmsBound_bounded:
    forall m n, DmsBound m n (getDmsBound m).
  Proof. intros; apply abstracted_originals_refl. Qed.
  
  Lemma getCmsBound_bounded:
    forall m n, CmsBound m n (getCmsBound m).
  Proof. intros; apply abstracted_originals_refl. Qed.

  Lemma getRegsBound_modular:
    forall m1 m2 n,
      RegsBound m1 n (getRegsBound m1) ->
      RegsBound m2 n (getRegsBound m2) ->
      RegsBound (m1 ++ m2)%kami n (getRegsBound (m1 ++ m2)%kami).
  Proof.
    intros.
    replace (getRegsBound (m1 ++ m2)%kami) with (getRegsBound m1 ++ getRegsBound m2)%nb.
    - apply concatMod_regsBound_1; auto.
    - unfold getRegsBound, appendNameBound; simpl.
      unfold RegInitT; rewrite namesOf_app; reflexivity.
  Qed.
  
  Lemma getDmsBound_modular:
    forall m1 m2 n,
      DmsBound m1 n (getDmsBound m1) ->
      DmsBound m2 n (getDmsBound m2) ->
      DmsBound (m1 ++ m2)%kami n (getDmsBound (m1 ++ m2)%kami).
  Proof.
    intros.
    replace (getDmsBound (m1 ++ m2)%kami) with (getDmsBound m1 ++ getDmsBound m2)%nb.
    - apply concatMod_dmsBound_1; auto.
    - unfold getDmsBound; rewrite getDefs_app; reflexivity.
  Qed.

  Lemma getCmsBound_modular:
    forall m1 m2 n,
      CmsBound m1 n (getCmsBound m1) ->
      CmsBound m2 n (getCmsBound m2) ->
      CmsBound (m1 ++ m2)%kami n (getCmsBound (m1 ++ m2)%kami).
  Proof.
    intros; pose proof (concatMod_cmsBound_1 H H0); clear H H0.
    eapply EquivList_trans; eauto.
    unfold unfoldNameBound.
    apply EquivList_app; [|apply EquivList_refl].
    split; [apply getCalls_subList_2|apply getCalls_subList_1].
  Qed.

  (** duplicate boundaries *)

  Definition getDupRegsBound m :=
    Build_NameBound nil (namesOf (getRegInits m)).
  Definition getDupDmsBound m :=
    Build_NameBound nil (getDefs m).
  Definition getDupCmsBound m :=
    Build_NameBound nil (getCalls m).

  Lemma getDupNameBound_concat_vertical:
    forall names n,
      EquivList
        (concat (map (fun p => (p) __ (S n) :: duplicateElt p n) names))
        ((map (spf (S n)) names)
           ++ (concat (map (fun p : string => duplicateElt p n) names))).
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
      (forall i, Specializable (m i)) ->
      (forall i j, getDupRegsBound (m i) = getDupRegsBound (m j)) ->
      RegsBound (duplicate m n) n (getDupRegsBound (m 0)).
  Proof.
    unfold RegsBound, Abstracted, unfoldNameBound; simpl; intros.
    induction n; simpl; intros.
    - rewrite specializeMod_regs by auto.
      generalize (namesOf (getRegInits (m 0))) as regs; clear.
      induction regs; simpl; intros; [apply EquivList_nil|].
      apply EquivList_cons; auto.
    - unfold RegInitT; rewrite namesOf_app.
      rewrite specializeMod_regs by auto.
      match goal with
      | [H: EquivList ?ilhs _ |- EquivList ?lhs (?nl ++ _) ] =>
        apply EquivList_trans with (l2:= (nl ++ ilhs))
      end.
      + specialize (H0 0 (S n)); inv H0.
        apply getDupNameBound_concat_vertical.
      + apply EquivList_app; [apply EquivList_refl|auto].
  Qed.

  Lemma getDupDmsBound_bounded:
    forall m n,
      (forall i, Specializable (m i)) ->
      (forall i j, getDupDmsBound (m i) = getDupDmsBound (m j)) ->
      DmsBound (duplicate m n) n (getDupDmsBound (m 0)).
  Proof.
    unfold DmsBound, Abstracted, unfoldNameBound; simpl; intros.
    induction n; simpl; intros.
    - rewrite specializeMod_defs by auto.
      generalize (getDefs (m 0)) as dms; clear.
      induction dms; simpl; intros; [apply EquivList_nil|].
      apply EquivList_cons; auto.
    - rewrite getDefs_app.
      rewrite specializeMod_defs by auto.
      match goal with
      | [H: EquivList ?ilhs _ |- EquivList ?lhs (?nl ++ _) ] =>
        apply EquivList_trans with (l2:= (nl ++ ilhs))
      end.
      + specialize (H0 0 (S n)); inv H0.
        apply getDupNameBound_concat_vertical.
      + apply EquivList_app; [apply EquivList_refl|auto].
  Qed.

  Lemma getDupCmsBound_bounded:
    forall m n,
      (forall i, Specializable (m i)) ->
      (forall i j, getDupCmsBound (m i) = getDupCmsBound (m j)) ->
      CmsBound (duplicate m n) n (getDupCmsBound (m 0)).
  Proof.
    unfold CmsBound, Abstracted, unfoldNameBound; simpl; intros.
    induction n; simpl; intros.
    - rewrite specializeMod_calls by auto.
      generalize (getCalls (m 0)) as cms; clear.
      induction cms; simpl; intros; [apply EquivList_nil|].
      apply EquivList_cons; auto.
    - apply EquivList_trans with
      (l2:= getCalls (specializeMod (m (S n)) (S n)) ++ getCalls (duplicate m n));
        [|split; [apply getCalls_subList_1|apply getCalls_subList_2]].
      rewrite specializeMod_calls by auto.
      match goal with
      | [H: EquivList ?ilhs _ |- EquivList ?lhs (?nl ++ _) ] =>
        apply EquivList_trans with (l2:= (nl ++ ilhs))
      end.
      + specialize (H0 0 (S n)); inv H0.
        apply getDupNameBound_concat_vertical.
      + apply EquivList_app; [apply EquivList_refl|auto].
  Qed.

End Bounds.

Section Correctness.

  Lemma disjNameBound_DisjList:
    forall ss1 ss2,
      DisjNameBound ss1 ss2 ->
      forall n l1 l2,
        Abstracted n ss1 l1 -> Abstracted n ss2 l2 ->
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
    - clear -H H0 H1 H2; apply in_concat_iff in H1; destruct H1 as [l ?]; dest.
      apply in_map_iff in H1; destruct H1 as [s ?]; dest; subst; simpl in *.
      pose proof (hasNoIndex_duplicateElt_DisjList _ s n H e) as Hd.
      destruct Hd; auto.
    - clear -H0 H1 H2.
      induction (prefixes ss1); [inv H0|].
      simpl in H0; apply in_app_or in H0; destruct H0; auto.
      pose proof (hasNoIndex_duplicateElt_DisjList _ a n H2 e) as Hd.
      destruct Hd; auto.
    - clear -H0 H1 H4.
      pose proof (duplicateElt_concat_DisjList n H4 e); destruct H; auto.
  Qed.

  Lemma regsBound_disj_regs:
    forall mb1 mb2,
      DisjNameBound mb1 mb2 ->
      forall n m1 m2,
        RegsBound m1 n mb1 -> RegsBound m2 n mb2 ->
        DisjList (namesOf (getRegInits m1)) (namesOf (getRegInits m2)).
  Proof.
    intros; eapply disjNameBound_DisjList; eauto.
  Qed.

  Lemma dmsBound_disj_dms:
    forall mb1 mb2,
      DisjNameBound mb1 mb2 ->
      forall n m1 m2,
        DmsBound m1 n mb1 -> DmsBound m2 n mb2 ->
        DisjList (getDefs m1) (getDefs m2).
  Proof.
    intros; eapply disjNameBound_DisjList; eauto.
  Qed.

  Lemma cmsBound_disj_calls:
    forall mb1 mb2,
      DisjNameBound mb1 mb2 ->
      forall n m1 m2,
        CmsBound m1 n mb1 -> CmsBound m2 n mb2 ->
        DisjList (getCalls m1) (getCalls m2).
  Proof.
    intros; eapply disjNameBound_DisjList; eauto.
  Qed.

  Lemma bound_disj_dms_calls:
    forall mb1 mb2,
      DisjNameBound mb1 mb2 ->
      forall n m1 m2,
        DmsBound m1 n mb1 -> CmsBound m2 n mb2 ->
        DisjList (getDefs m1) (getCalls m2).
  Proof.
    intros; eapply disjNameBound_DisjList; eauto.
  Qed.

  Lemma bound_disj_calls_dms:
    forall mb1 mb2,
      DisjNameBound mb1 mb2 ->
      forall n m1 m2,
        CmsBound m1 n mb1 -> DmsBound m2 n mb2 ->
        DisjList (getCalls m1) (getDefs m2).
  Proof.
    intros; eapply disjNameBound_DisjList; eauto.
  Qed.

  Lemma bound_disj_extDefs_calls:
    forall dnb1 cnb1 cnb2,
      hasNoIndex (originals dnb1) = true ->
      hasNoIndex (originals cnb1) = true ->
      DisjNameBound (subtractNameBound dnb1 cnb1) cnb2 ->
      forall n m1 m2,
        DmsBound m1 n dnb1 -> CmsBound m1 n cnb1 -> CmsBound m2 n cnb2 ->
        DisjList (getExtDefs m1) (getCalls m2).
  Proof.
    intros.
    eapply disjNameBound_DisjList; eauto.
    apply subtractNameBound_filter_abstracted; auto.
  Qed.

  Lemma bound_disj_extCalls_defs:
    forall dnb1 cnb1 dnb2,
      hasNoIndex (originals dnb1) = true ->
      hasNoIndex (originals cnb1) = true ->
      DisjNameBound (subtractNameBound cnb1 dnb1) dnb2 ->
      forall n m1 m2,
        DmsBound m1 n dnb1 -> CmsBound m1 n cnb1 -> DmsBound m2 n dnb2 ->
        DisjList (getExtCalls m1) (getDefs m2).
  Proof.
    intros.
    eapply disjNameBound_DisjList; eauto.
    apply subtractNameBound_filter_abstracted; auto.
  Qed.

  Lemma bound_disj_intCalls_calls:
    forall dnb1 cnb1 cnb2,
      hasNoIndex (originals dnb1) = true ->
      hasNoIndex (originals cnb1) = true ->
      DisjNameBound (intersectNameBound cnb1 dnb1) cnb2 ->
      forall n m1 m2,
        DmsBound m1 n dnb1 -> CmsBound m1 n cnb1 -> CmsBound m2 n cnb2 ->
        DisjList (getIntCalls m1) (getCalls m2).
  Proof.
    intros.
    eapply disjNameBound_DisjList; eauto.
    apply intersectNameBound_filter_abstracted; auto.
  Qed.

  Lemma bound_disj_calls_intCalls:
    forall cnb1 dnb2 cnb2,
      hasNoIndex (originals dnb2) = true ->
      hasNoIndex (originals cnb2) = true ->
      DisjNameBound cnb1 (intersectNameBound cnb2 dnb2) ->
      forall n m1 m2,
        CmsBound m1 n cnb1 -> DmsBound m2 n dnb2 -> CmsBound m2 n cnb2 -> 
        DisjList (getCalls m1) (getIntCalls m2).
  Proof.
    intros.
    eapply disjNameBound_DisjList; eauto.
    apply intersectNameBound_filter_abstracted; auto.
  Qed.

End Correctness.

(** Tactics *)

Ltac get_regs_bound_ex m :=
  lazymatch m with
  | ConcatMod ?m1 ?m2 =>
    let nb1 := get_regs_bound_ex m1 in
    let nb2 := get_regs_bound_ex m2 in
    constr:(appendNameBound nb1 nb2)
  | duplicate ?sm _ => constr:(getDupRegsBound (sm 0))
  | makeModule _ => constr:(getRegsBound m)
  | PrimMod _ => constr:(getRegsBound m)
  | Mod _ _ _ => constr:(getRegsBound m)
  | _ => let m' := eval red in m in get_regs_bound_ex m'
  end.

Ltac get_dms_bound_ex m :=
  lazymatch m with
  | ConcatMod ?m1 ?m2 =>
    let nb1 := get_dms_bound_ex m1 in
    let nb2 := get_dms_bound_ex m2 in
    constr:(appendNameBound nb1 nb2)
  | duplicate ?sm _ => constr:(getDupDmsBound (sm 0))
  | makeModule _ => constr:(getDmsBound m)
  | PrimMod _ => constr:(getDmsBound m)
  | Mod _ _ _ => constr:(getDmsBound m)
  | _ => let m' := eval red in m in get_dms_bound_ex m'
  end.

Ltac get_cms_bound_ex m :=
  lazymatch m with
  | ConcatMod ?m1 ?m2 =>
    let nb1 := get_cms_bound_ex m1 in
    let nb2 := get_cms_bound_ex m2 in
    constr:(appendNameBound nb1 nb2)
  | duplicate ?sm _ => constr:(getDupCmsBound (sm 0))
  | makeModule _ => constr:(getCmsBound m)
  | PrimMod _ => constr:(getCmsBound m)
  | Mod _ _ _ => constr:(getCmsBound m)
  | _ => let m' := eval red in m in get_cms_bound_ex m'
  end.

Ltac red_to_regs_bound_ex rn :=
  match goal with
  | [ |- DisjList (namesOf (getRegInits ?m1))
                  (namesOf (getRegInits ?m2)) ] =>
    let mb1' := get_regs_bound_ex m1 in
    let mb2' := get_regs_bound_ex m2 in
    apply regsBound_disj_regs with (n:= rn) (mb1 := mb1') (mb2 := mb2')
  | [ |- DisjList (map _ (getRegInits ?m1))
                  (map _ (getRegInits ?m2)) ] =>
    let mb1' := get_regs_bound_ex m1 in
    let mb2' := get_regs_bound_ex m2 in
    apply regsBound_disj_regs with (n:= rn) (mb1 := mb1') (mb2 := mb2')
  end.

Ltac red_to_dms_bound_ex dn :=
  match goal with
  | [ |- DisjList (getDefs ?m1) (getDefs ?m2) ] =>
    let mb1' := get_dms_bound_ex m1 in
    let mb2' := get_dms_bound_ex m2 in
    apply dmsBound_disj_dms with (n:= dn) (mb1 := mb1') (mb2 := mb2')
  | [ |- DisjList (namesOf (getDefsBodies ?m1)) (namesOf (getDefsBodies ?m2)) ] =>
    let mb1' := get_dms_bound_ex m1 in
    let mb2' := get_dms_bound_ex m2 in
    apply dmsBound_disj_dms with (n:= dn) (mb1 := mb1') (mb2 := mb2')
  end.

Ltac red_to_cms_bound_ex cn :=
  match goal with
  | [ |- DisjList (getCalls ?m1) (getCalls ?m2) ] =>
    let mb1' := get_cms_bound_ex m1 in
    let mb2' := get_cms_bound_ex m2 in
    apply cmsBound_disj_calls with (n:= cn) (mb1 := mb1') (mb2 := mb2')
  end.

Ltac red_to_dc_bound_ex cn :=
  match goal with
  | [ |- DisjList (getDefs ?m1) (getCalls ?m2) ] =>
    let mb1' := get_dms_bound_ex m1 in
    let mb2' := get_cms_bound_ex m2 in
    apply bound_disj_dms_calls with (n:= cn) (mb1 := mb1') (mb2 := mb2')
  end.

Ltac red_to_cd_bound_ex cn :=
  match goal with
  | [ |- DisjList (getCalls ?m1) (getDefs ?m2) ] =>
    let mb1' := get_cms_bound_ex m1 in
    let mb2' := get_dms_bound_ex m2 in
    apply bound_disj_calls_dms with (n:= cn) (mb1 := mb1') (mb2 := mb2')
  end.

Ltac red_to_edc_bound_ex cn :=
  match goal with
  | [ |- DisjList (getExtDefs ?m1) (getCalls ?m2) ] =>
    let dnb1' := get_dms_bound_ex m1 in
    let cnb1' := get_cms_bound_ex m1 in
    let cnb2' := get_cms_bound_ex m2 in
    apply bound_disj_extDefs_calls with (n:= cn) (dnb1:= dnb1') (cnb1:= cnb1') (cnb2:= cnb2')
  end.

Ltac red_to_ecd_bound_ex cn :=
  match goal with
  | [ |- DisjList (getExtCalls ?m1) (getDefs ?m2) ] =>
    let dnb1' := get_dms_bound_ex m1 in
    let cnb1' := get_cms_bound_ex m1 in
    let dnb2' := get_dms_bound_ex m2 in
    apply bound_disj_extCalls_defs with (n:= cn) (dnb1:= dnb1') (cnb1:= cnb1') (dnb2:= dnb2')
  end.

Ltac red_to_icc_bound_ex cn :=
  match goal with
  | [ |- DisjList (getIntCalls ?m1) (getCalls ?m2) ] =>
    let dnb1' := get_dms_bound_ex m1 in
    let cnb1' := get_cms_bound_ex m1 in
    let cnb2' := get_cms_bound_ex m2 in
    apply bound_disj_intCalls_calls with (n:= cn) (dnb1:= dnb1') (cnb1:= cnb1') (cnb2:= cnb2')
  end.

Ltac red_to_cic_bound_ex cn :=
  match goal with
  | [ |- DisjList (getCalls ?m1) (getIntCalls ?m2) ] =>
    let cnb1' := get_cms_bound_ex m1 in
    let dnb2' := get_dms_bound_ex m2 in
    let cnb2' := get_cms_bound_ex m2 in
    apply bound_disj_calls_intCalls with (n:= cn) (cnb1:= cnb1') (dnb2:= dnb2') (cnb2:= cnb2')
  end.

Ltac regs_bound_tac_unit_ex :=
  match goal with
  | [ |- RegsBound (ConcatMod _ _) _ (appendNameBound _ _) ] =>
    apply concatMod_regsBound_1
  | [ |- RegsBound (ConcatMod _ _) _ _ ] =>
    apply getRegsBound_modular
  | [ |- RegsBound (duplicate _ _) _ _ ] =>
    apply getDupRegsBound_bounded; auto
  | [ |- RegsBound ?m _ _ ] => unfold_head m
  | _ => apply getRegsBound_bounded
  end.
Ltac regs_bound_tac_ex := repeat regs_bound_tac_unit_ex.

Ltac dms_bound_tac_unit_ex :=
  match goal with
  | [ |- DmsBound (ConcatMod _ _) _ (appendNameBound _ _) ] =>
    apply concatMod_dmsBound_1
  | [ |- DmsBound (ConcatMod _ _) _ _ ] =>
    apply getDmsBound_modular
  | [ |- DmsBound (duplicate _ _) _ _ ] =>
    apply getDupDmsBound_bounded; auto
  | [ |- DmsBound ?m _ _ ] => unfold_head m
  | _ => apply getDmsBound_bounded
  end.
Ltac dms_bound_tac_ex := repeat dms_bound_tac_unit_ex.

Ltac cms_bound_tac_unit_ex :=
  match goal with
  | [ |- CmsBound (ConcatMod _ _) _ (appendNameBound _ _) ] =>
    apply concatMod_cmsBound_1
  | [ |- CmsBound (ConcatMod _ _) _ _ ] =>
    apply getCmsBound_modular
  | [ |- CmsBound (duplicate _ _) _ _ ] =>
    apply getDupCmsBound_bounded; auto
  | [ |- CmsBound ?m _ _ ] => unfold_head m
  | _ => apply getCmsBound_bounded
  end.
Ltac cms_bound_tac_ex := repeat cms_bound_tac_unit_ex.

Ltac kdisj_regs_ex n :=
  red_to_regs_bound_ex n;
  [apply disjNameBound_DisjNameBound; reflexivity
  |regs_bound_tac_ex
  |regs_bound_tac_ex].

Ltac kdisj_dms_ex n :=
  red_to_dms_bound_ex n;
  [apply disjNameBound_DisjNameBound; reflexivity
  |dms_bound_tac_ex
  |dms_bound_tac_ex].

Ltac kdisj_cms_ex n :=
  red_to_cms_bound_ex n;
  [apply disjNameBound_DisjNameBound; reflexivity
  |cms_bound_tac_ex
  |cms_bound_tac_ex].

Ltac kdisj_dms_cms_ex n :=
  red_to_dc_bound_ex n;
  [apply disjNameBound_DisjNameBound; reflexivity
  |dms_bound_tac_ex
  |cms_bound_tac_ex].

Ltac kdisj_cms_dms_ex n :=
  red_to_cd_bound_ex n;
  [apply disjNameBound_DisjNameBound; reflexivity
  |cms_bound_tac_ex
  |dms_bound_tac_ex].

Ltac kdisj_edms_cms_ex n :=
  red_to_edc_bound_ex n;
  [reflexivity|reflexivity
   |apply disjNameBound_DisjNameBound; reflexivity
   |dms_bound_tac_ex
   |cms_bound_tac_ex
   |cms_bound_tac_ex].

Ltac kdisj_ecms_dms_ex n :=
  red_to_ecd_bound_ex n;
  [reflexivity|reflexivity
   |apply disjNameBound_DisjNameBound; reflexivity
   |dms_bound_tac_ex
   |cms_bound_tac_ex
   |dms_bound_tac_ex].

Ltac kdisj_icms_cms_ex n :=
  red_to_icc_bound_ex n;
  [reflexivity|reflexivity
   |apply disjNameBound_DisjNameBound; reflexivity
   |dms_bound_tac_ex
   |cms_bound_tac_ex
   |cms_bound_tac_ex].

Ltac kdisj_cms_icms_ex n :=
  red_to_cic_bound_ex n;
  [reflexivity|reflexivity
   |apply disjNameBound_DisjNameBound; reflexivity
   |cms_bound_tac_ex
   |dms_bound_tac_ex
   |cms_bound_tac_ex].

