Require Import String Program.Equality Lia.

Set Asymmetric Patterns.

Open Scope string.

Fixpoint S_In a s :=
  match s with
    | EmptyString => False
    | String a' s' => a' = a \/ S_In a s'
  end.

Theorem S_in_eq : forall a (l:string), S_In a (String a l).
Proof.
  simpl; intuition auto.
Qed.

Theorem S_in_cons : forall a b (l:string), S_In b l -> S_In b (String a l).
Proof.
  induction l; simpl in *; intuition auto.
Qed.

Theorem S_not_in_cons x a (l : string):
  ~ S_In x (String a l) <-> x<>a /\ ~ S_In x l.
Proof.
  induction l; simpl in *; intuition auto.
Qed.

Theorem S_in_nil : forall a, ~ S_In a EmptyString.
Proof.
  intuition auto.
Qed.

Theorem S_in_split : forall x (l: string), S_In x l -> exists l1 l2,
                                                        l = (l1 ++ String x l2).
Proof.
  induction l; simpl in *; intros; subst; intuition auto.
  - subst.
    exists EmptyString, l; reflexivity.
  - destruct H as [l1 [l2 leq]]; subst; simpl.
    exists (String a l1), l2; reflexivity.
Qed.

Lemma S_in_inv : forall a b (l: string), S_In b (String a l) -> a = b \/ S_In b l.
Proof.
  induction l; simpl in *; intuition auto.
Qed.

Theorem S_in_dec :
  forall a (l: string), {S_In a l} + {~ S_In a l}.
Proof.
  induction l; simpl in *; intuition auto.
  destruct (Ascii.ascii_dec a0 a); subst; intuition auto.
Qed.

Theorem S_app_cons_not_nil : forall (x y: string) a, EmptyString <> (x ++ String a y).
Proof.
  induction x; simpl in *; intuition auto; try discriminate.
Qed.

Theorem S_app_nil_l : forall (l: string), (EmptyString ++ l) = l.
Proof.
  reflexivity.
Qed.
  
Theorem S_app_nil_r : forall l: string, (l ++ EmptyString) = l.
Proof.
  induction l; intuition auto.
  rewrite <- IHl at 2; reflexivity.
Qed.

Theorem S_app_assoc : forall l m n:string, (l ++ m ++ n = (l ++ m) ++ n).
Proof.
  induction l; intuition auto; simpl in *.
  f_equal; apply IHl.
Qed.

Theorem S_app_comm_cons : forall (x y: string) a, String a (x ++ y) = (String a x) ++ y.
Proof.
  induction x; intuition auto.
Qed.

Theorem S_app_eq_nil : forall l l':string, l ++ l' = EmptyString ->
                                         l = EmptyString /\ l' = EmptyString.
Proof.
  induction l; intuition auto; try discriminate.
Qed.

Theorem S_app_eq_unit :
  forall (x y: string) a,
    x ++ y = String a EmptyString -> x = EmptyString /\
                                     y = String a EmptyString \/ x = String a EmptyString /\
                                     y = EmptyString.
Proof.
  induction x; intuition auto.
  inversion H; subst; clear H.
  apply S_app_eq_nil in H2; destruct H2; subst; simpl; intuition auto.
Qed.

Lemma S_app_inj_tail :
  forall (x y:string) a b, x ++ String a EmptyString = y ++ String b EmptyString ->
                           x = y /\ a = b.
Proof.
  induction x; simpl in *; destruct y; intuition auto; simpl in *.
  - inversion H; intuition auto.
  - inversion H.
    apply eq_sym in H2.
    apply S_app_eq_nil in H2; destruct H2; discriminate.
  - inversion H.
    apply eq_sym in H2.
    apply S_app_eq_nil in H2; destruct H2; discriminate.
  - inversion H; subst.
    apply S_app_eq_nil in H2. destruct H2; discriminate.
  - inversion H; subst.
    apply S_app_eq_nil in H2. destruct H2; discriminate.
  - f_equal; inversion H; subst; auto.
    apply IHx in H2; destruct H2; auto.
  - inversion H; subst.
    apply IHx in H2; destruct H2; auto.
Qed.

Lemma S_app_length : forall l l' : string, length (l++l') = length l + length l'.
Proof.
  induction l; destruct l'; intuition auto; simpl in *; f_equal; intuition auto; try apply IHl.
Qed.

Lemma S_in_app_or : forall (l m:string) a, S_In a (l ++ m) -> S_In a l \/ S_In a m.
Proof.
  induction l; destruct m; intuition auto; simpl in *.
  - left; rewrite S_app_nil_r in H; intuition auto.
  - intuition auto.
    apply IHl in H0; simpl in *.
    intuition auto.
Qed.


Lemma S_in_or_app : forall (l m: string) a, S_In a l \/ S_In a m -> S_In a (l ++ m).
Proof.
  induction l; destruct m; simpl in *; intuition auto; subst.
  - right; apply IHl; right; simpl in *; left; reflexivity.
  - right; apply IHl; right; simpl in *; right; auto.
Qed.
  
Lemma S_in_app_iff : forall l l' a, S_In a (l++l') <-> S_In a l \/ S_In a l'.
Proof.
  intros; constructor; intros.
  - apply S_in_app_or; auto.
  - apply S_in_or_app; auto.
Qed.

Lemma S_app_inv_head:
  forall l l1 l2 : string, l ++ l1 = l ++ l2 -> l1 = l2.
Proof.
  induction l; simpl in *; intuition auto; inversion H.
  apply IHl; auto.
Qed.

Lemma S_app_inv_tail:
  forall l l1 l2 : string, l1 ++ l = l2 ++ l -> l1 = l2.
Proof.
  intros l l1.
  generalize l; clear l.
  induction l1; destruct l2; simpl in *; intuition auto.
  match goal with
    | H: ?p = ?q |- _ => assert (sth: length p = length q) by (f_equal; auto); simpl in sth
  end.
  simpl in sth; rewrite S_app_length in sth.
  exfalso; lia.
  match goal with
    | H: ?p = ?q |- _ => assert (sth: length p = length q) by (f_equal; auto); simpl in sth
  end.
  rewrite S_app_length in sth; exfalso; lia.
  inversion H; subst; clear H.
  f_equal; eapply IHl1; eauto.
Qed.

#[global] Hint Resolve S_app_assoc: datatypes v62.
#[global] Hint Resolve S_app_comm_cons S_app_cons_not_nil: datatypes v62.
#[global] Hint Immediate S_app_eq_nil: datatypes v62.
#[global] Hint Resolve S_app_eq_unit S_app_inj_tail: datatypes v62.
#[global] Hint Resolve S_in_eq S_in_cons S_in_inv S_in_nil S_in_app_or S_in_or_app: datatypes v62.

Fixpoint S_nth (n:nat) (l:string) default {struct l} :=
  match n, l with
    | O, String x l' => x
    | O, other => default
    | S m, EmptyString => default
    | S m, String x t => S_nth m t default
  end.


Fixpoint S_nth_ok (n:nat) (l: string) (default: Ascii.ascii) {struct l} : bool :=
  match n, l with
    | O, String x l' => true
    | O, other => false
    | S m, EmptyString => false
    | S m, String x t => S_nth_ok m t default
  end.

Lemma S_nth_in_or_default :
  forall (n:nat) (l: string) d, {S_In (S_nth n l d) l} + {S_nth n l d = d}.
Proof.
  induction n, l; simpl in *; auto; intros.
  specialize (IHn l d).
  destruct IHn; intuition auto.
Qed.

Lemma nth_S_cons :
    forall (n:nat) (l: string) d a,
      S_In (S_nth n l d) l -> S_In (S_nth (S n) (String a l) d) (String a l).
Proof.
  induction n, l; simpl in *; auto; intros.
Qed.

Definition S_nth_error l (n: nat) := get n l.

Definition S_nth_default default (l:string) (n:nat) : Ascii.ascii :=
  match get n l with
    | Some x => x
    | None => default
  end.

Lemma S_nth_default_eq :
  forall n l d, S_nth_default d l n = S_nth n l d.
Proof.
  induction n, l; simpl in *; auto; intros.
  apply IHn.
Qed.  

Section RelatingIndex.
  Lemma substring_empty:
    forall s, substring 0 0 s = ""%string.
  Proof. induction s; simpl; intros; auto. Qed.


  Lemma index_not_in a l:
    index 0 (String a EmptyString) l = None <-> ~ S_In a l.
  Proof.
    induction l; simpl in *; intuition auto; subst;
    rewrite (proj2 (prefix_correct "" l) (substring_empty l)) in *.
    - destruct (Ascii.ascii_dec a a); intuition auto; try discriminate.
    - destruct (Ascii.ascii_dec a a0); intuition auto; try discriminate.
      case_eq (index 0 (String a "") l); intros.
      + rewrite H2 in H1.
        discriminate.
      + apply H; auto.
    - destruct (Ascii.ascii_dec a a0); intuition auto; try discriminate; subst; intuition auto.
      rewrite H1; reflexivity.
  Qed.
End RelatingIndex.      

Lemma S_nth_In :
  forall (n:nat) l d, n < length l -> S_In (S_nth n l d) l.
Proof.
  induction n, l; simpl in *; intuition auto; try lia.
  assert (sth: n < length l) by lia.
  apply IHn with (d := d) in sth; auto.
Qed.

Lemma S_In_nth l x d : S_In x l ->
                       exists n, n < length l /\ S_nth n l d = x.
Proof.
  induction l; simpl in *; subst; intuition auto; intros.
  - exists 0; constructor; try lia; auto.
  - destruct H as [n [nlt eq]].
    exists (S n); constructor; try lia; auto.
Qed.

Lemma S_nth_overflow : forall l n d, length l <= n -> S_nth n l d = d.
Proof.
  induction l, n; intuition auto; simpl in *.
  - exfalso; lia.
  - assert (sth: length l <= n) by lia.
    apply IHl; auto.
Qed.

Lemma S_nth_indep :
  forall l n d d', n < length l -> S_nth n l d = S_nth n l d'.
Proof.
  induction l, n; intuition auto; simpl in *.
  - exfalso; lia.
  - exfalso; lia.
  - assert (sth: n < length l) by lia; apply IHl; auto.
Qed.

Lemma S_app_nth1 :
  forall l l' d n, n < length l -> S_nth n (l++l') d = S_nth n l d.
Proof.
  induction l, n; intuition auto; simpl in *.
  - exfalso; lia.
  - exfalso; lia.
  - assert (sth: n < length l) by lia; apply IHl; auto.
Qed.
    
Lemma S_app_nth2 :
  forall l l' d n, n >= length l -> S_nth n (l++l') d = S_nth (n-length l) l' d.
Proof.
  induction l, n; intuition auto; simpl in *.
  - exfalso; lia.
  - assert (sth: n >= length l) by lia; apply IHl; auto.
Qed.

Lemma S_nth_split l :
  forall n d,
    n < length l ->
    exists l1, exists l2, l = l1 ++ String (S_nth n l d) l2 /\ length l1 = n.
Proof.
  induction l; destruct n; simpl in *; intuition auto; subst; try discriminate; try lia.
  - exists "", l; constructor; auto.
  - assert (sth: n < length l) by lia.
    specialize (IHl _ d sth).
    destruct IHl as [l1 [l2 [? ?]]].
    exists (String a l1), l2; constructor; f_equal; simpl in *; f_equal; auto.
Qed.
  
Lemma S_nth_error_In l n x : S_nth_error l n = Some x -> S_In x l.
Proof.
  generalize n x; clear n x.
  induction l; destruct n; intuition auto; simpl in *; try discriminate.
  - inversion H; intuition auto.
  - right; apply IHl with (n := n); auto.
Qed.

Lemma S_In_nth_error l : forall x, S_In x l -> exists n, S_nth_error l n = Some x.
Proof.
  induction l; simpl in *; intuition auto; subst.
  - exists 0; reflexivity.
  - destruct (IHl x H0) as [n rest].
    exists (S n); auto.
Qed.

Lemma S_nth_error_None l : forall n, S_nth_error l n = None <-> length l <= n.
Proof.
  induction l; destruct n; simpl in *; intuition auto; subst; try lia; try discriminate.
  apply IHl in H; lia.
  apply IHl; lia.
Qed.
  
Lemma S_nth_error_Some l : forall n, S_nth_error l n <> None <-> n < length l.
Proof.
  induction l; destruct n; simpl in *; intuition auto; subst; try lia; try discriminate.
  apply IHl in H; lia.
  generalize H0; clear H0.
  apply IHl; lia.
Qed.

Lemma S_nth_error_split l : forall n a,
                            S_nth_error l n = Some a ->
                            exists l1, exists l2, l = l1 ++ String a l2 /\ length l1 = n.
Proof.
  induction l; destruct n; simpl in *; intuition auto; subst; try discriminate; try lia.
  - inversion H; clear H; subst.
    exists ""; simpl.
    repeat econstructor; eauto.
  - apply IHl in H.
    destruct H as [l1 [l2 [? ?]]].
    exists (String a l1), l2; simpl in *.
    constructor; f_equal; auto.
Qed.

Lemma S_nth_error_app1 l : forall l' n, n < length l ->
                                        S_nth_error (l++l') n = S_nth_error l n.
Proof.
  induction l; destruct l', n; simpl in *; intuition auto; subst; try discriminate; try lia;
  apply IHl; lia.
Qed.
  

Lemma S_nth_error_app2 l : forall l' n, length l <= n ->
                                        S_nth_error (l++l') n = S_nth_error l' (n-length l).
Proof.
  induction l; destruct l', n; simpl in *; intuition auto; subst; try discriminate; try lia;
  apply IHl; lia.
Qed.

Close Scope string.

