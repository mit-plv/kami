Require Import Coq.Lists.List Coq.Program.Basics.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

Lemma Forall_app:
  forall {A} (l1 l2: list A) P, Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction l1; simpl; intros; auto.
  inversion H; constructor; auto.
Qed.

Lemma NoDup_app_comm:
  forall {A} (l1 l2: list A), NoDup (l1 ++ l2) -> NoDup (l2 ++ l1).
Proof.
  induction l2; simpl; intros; [rewrite app_nil_r in H; auto|].
  constructor.
  - intro Hx. apply in_app_or, or_comm, in_or_app in Hx.
    apply NoDup_remove_2 in H; elim H; auto.
  - apply IHl2.
    eapply NoDup_remove_1; eauto.
Qed.

Lemma NoDup_app_1:
  forall {A} (l1 l2: list A), NoDup (l1 ++ l2) -> NoDup l1.
Proof.
  induction l1; simpl; intros; auto.
  - constructor.
  - inversion H; constructor; eauto; subst.
    intro Hx; elim H2; apply in_or_app; auto.
Qed.

Lemma NoDup_app_2:
  forall {A} (l1 l2: list A), NoDup (l1 ++ l2) -> NoDup l2.
Proof.
  induction l2; simpl; intros; auto; constructor.
  - apply NoDup_remove_2 in H.
    intro Hx; elim H; apply in_or_app; auto.
  - apply IHl2; eapply NoDup_remove_1; eauto.
Qed.


Lemma NoDup_app_comm_ext:
  forall {A} (l1 l2 l3 l4: list A),
    NoDup (l1 ++ (l2 ++ l3) ++ l4) -> NoDup (l1 ++ (l3 ++ l2) ++ l4).
Proof.
  intros; apply NoDup_app_comm; apply NoDup_app_comm in H.
  rewrite <-app_assoc with (n:= l1).
  rewrite <-app_assoc with (n:= l1) in H.
  apply NoDup_app_comm; apply NoDup_app_comm in H.
  induction (l4 ++ l1).
  - rewrite app_nil_l in *; apply NoDup_app_comm; auto.
  - simpl in *; inversion H; constructor; auto.
    intro Hx; elim H2; clear H2.
    apply in_app_or in Hx; destruct Hx.
    + apply in_or_app; auto.
    + apply in_app_or in H2; destruct H2.
      * apply in_or_app; right; apply in_or_app; auto.
      * apply in_or_app; right; apply in_or_app; auto.
Qed.

Lemma hd_error_revcons_same A ls: forall (a: A), hd_error ls = Some a ->
                                                 forall v, hd_error (ls ++ [v]) = Some a.
Proof.
  induction ls; auto; simpl; intros; discriminate.
Qed.

Lemma hd_error_revcons_holds A (P: A -> Prop) (ls: list A):
  forall a, hd_error ls = Some a ->
            P a ->
            forall b v, hd_error (ls ++ [v]) = Some b ->
                        P b.
Proof.
  intros.
  rewrite hd_error_revcons_same with (a := a) in H1; auto.
  inversion H1; subst; auto.
Qed.

Lemma single_unfold_concat A B a (f: A -> list B) (ls: list A):
  concat (map f (a :: ls)) = (f a ++ concat (map f ls))%list.
Proof.
  reflexivity.
Qed.

Lemma in_single: forall A (a l: A), In a (l :: nil) -> a = l.
Proof.
  intros.
  simpl in *.
  destruct H; intuition auto.
Qed.

Lemma in_pre_suf: forall A l (a: A), In a l -> exists l1 l2, (l = l1 ++ a :: l2)%list.
Proof.
  induction l; simpl.
  - intuition auto.
  - intros.
    destruct H; [| apply IHl in H; intuition auto].
    + subst.
      exists nil, l.
      reflexivity.
    + destruct H as [? [? ?]].
      subst.
      exists (a :: x), x0.
      reflexivity.
Qed.

Lemma list_nil_revcons A: forall (l: list A), l = nil \/ exists l' v, l = (l' ++ [v])%list.
Proof.
  induction l; subst.
  - left; auto.
  - destruct IHl; subst.
    + right.
      exists nil, a.
      reflexivity.
    + destruct H as [? [? ?]];
      subst.
      right; simpl.
      exists (a :: x), x0.
      reflexivity.
Qed.

Lemma list_revcons A (P: Prop): forall l (g: A), (forall l' v, g :: l = l' ++ (v :: nil) -> P) -> P.
Proof.
  intros.
  destruct (list_nil_revcons (g ::l)); firstorder (discriminate || idtac).
Qed.

Lemma app_single_r: forall A (ls1 ls2: list A) v1 v2,
                      (ls1 ++ [v1] = ls2 ++ [v2])%list ->
                      ls1 = ls2 /\ v1 = v2.
Proof.
  induction ls1; simpl; auto; intros.
  - destruct ls2; simpl in *; inversion H; auto.
    apply app_cons_not_nil in H2.
    intuition auto.
  - destruct ls2; simpl in *; inversion H; auto.
    + apply eq_sym in H2; apply app_cons_not_nil in H2.
      intuition auto.
    + specialize (IHls1 _ _ _ H2).
      intuition (try f_equal; auto).
Qed.

Lemma app_cons_in A ls:
  forall (v: A) s1 s2 beg mid last,
    (ls ++ [v] = beg ++ s1 :: mid ++ s2 :: last)%list ->
    In s1 ls.
Proof.
  induction ls; simpl; auto; intros;
  destruct beg; simpl in *; inversion H.
  - apply app_cons_not_nil in H2.
    auto.
  - apply app_cons_not_nil in H2.
    auto.
  - intuition auto.
  - apply IHls in H2; intuition auto.
Qed.

Lemma beg_mid_last_add_eq A ls:
  (forall (v: A) v1 v2 beg mid last,
     ls ++ [v] = beg ++ v1 :: mid ++ v2 :: last ->
     (last = nil /\ v = v2 /\ ls = beg ++ v1 :: mid) \/
     (exists last', last = last' ++ [v] /\ ls = beg ++ v1 :: mid ++ v2 :: last'))%list.
Proof.
  intros.
  pose proof (list_nil_revcons last) as [sth1 | sth2].
  - subst.
    left.
    rewrite app_comm_cons in H.
    rewrite app_assoc in H.
    apply app_single_r in H.
    destruct H as [? ?].
    repeat (constructor; auto).
  - destruct sth2 as [? [? ?]].
    right.
    exists x.
    subst.
    rewrite app_comm_cons in H.
    rewrite app_assoc in H.
    rewrite app_comm_cons in H.
    rewrite app_assoc in H.
    apply app_single_r in H.
    destruct H as [? ?]; subst.
    repeat (constructor; auto).
    rewrite app_comm_cons.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma in_revcons A ls (a v: A):
  In v (ls ++ (a :: nil)) ->
  In v ls \/ v = a.
Proof.
  intros.
  apply in_app_or in H.
  simpl in *.
  intuition.
Qed.

Lemma in_cons A ls (a v: A):
  In v (a :: ls) ->
  In v ls \/ v = a.
Proof.
  simpl.
  intuition.
Qed.

Lemma in_revcons_converse A ls (a v: A):
  In v ls \/ v = a ->
  In v (ls ++ (a :: nil)).
Proof.
  intros.
  apply in_or_app.
  simpl in *.
  intuition.
Qed.

Lemma in_cons_converse A ls (a v: A):
  In v ls \/ v = a ->
  In v (a :: ls).
Proof.
  simpl.
  intuition.
Qed.

Lemma in_revcons_hyp A ls (a v: A) (P: A -> Prop):
  (In v (ls ++ (a :: nil)) -> P v) ->
  (In v ls -> P v) /\ (v = a -> P v).
Proof.
  intros.
  assert ((In v ls \/ v = a) -> P v).
  { intros K.
    apply in_revcons_converse in K.
    tauto.
  } 
  tauto.
Qed.

Lemma in_cons_hyp A ls (a v: A) (P: A -> Prop):
  (In v (a :: ls) -> P v) ->
  (In v ls -> P v) /\ (v = a -> P v).
  intros.
  assert ((In v ls \/ v = a) -> P v).
  { intros K.
    apply in_cons_converse in K.
    tauto.
  } 
  tauto.
Qed.

Lemma app_or A: forall l1 l2 (v: A), iff (In v (l1 ++ l2)) (In v l1 \/ In v l2).
Proof.
  unfold iff.
  split; intros.
  - apply in_app_or; assumption.
  - apply in_or_app; assumption.
Qed.

Lemma cons_or A: forall l (a v: A), iff (In a (v :: l)) (a = v \/ In a l).
Proof.
  unfold iff; simpl.
  intuition auto.
Qed.

Lemma revcons_or A: forall l (a v: A), iff (In a (l ++ [v])) (a = v \/ In a l).
Proof.
  unfold iff; simpl; constructor; intros.
  - apply in_revcons in H.
    intuition auto.
  - apply in_revcons_converse.
    intuition auto.
Qed.

