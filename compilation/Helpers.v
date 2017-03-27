Require Import String Lib.StringEq List Compare_dec Omega.

Set Implicit Arguments.
Set Asymmetric Patterns.


Section intersect.
  Variable A: Type.
  Variable decA: forall a1 a2: A, {a1 = a2} + {a1 <> a2}.
  Fixpoint intersect (s1 s2: list A) :=
    match s1 with
      | nil => nil
      | v :: s1' =>
        if in_dec decA v s2
        then v :: intersect s1' s2
        else intersect s1' s2
    end.

  Definition not_nil (a: list A) := match a with
                                     | x :: xs => true
                                     | _ => false
                                    end.

  Definition is_nil (a: list A) := match a with
                                     | x :: xs => false
                                     | _ => true
                                   end.

  Fixpoint find_pos' s (ls: list A) n :=
    match ls with
      | nil => None
      | x :: xs => if decA x s
                   then Some n
                   else find_pos' s xs (S n)
    end.

  Definition find_pos s ls := find_pos' s ls 0.

  Local Fixpoint sameList' s (ls: list A) :=
    match ls with
      | nil => true
      | x :: xs => if decA s x
                   then sameList' s xs
                   else false
    end.

  Definition sameList (ls: list A) :=
    match ls with
      | nil => true
      | x :: xs => sameList' x xs
    end.
End intersect.

Section CallChain.
  Variable A: Type.
  Variable decA: forall a1 a2: A, {a1 = a2} + {a1 <> a2}.
  Variable graph: list (A * list A).

  Definition lengthOrder (l1 l2: (A * list A)) := length (snd l1) < length (snd l2).
  Lemma lengthOrder_wf': forall len ls, length (snd ls) <= len -> Acc lengthOrder ls.
  Proof.
    unfold lengthOrder; induction len; simpl; intros; auto.
    - constructor; intros.
      assert (sth: length (snd ls) = 0) by abstract (Omega.omega).
      abstract (Omega.omega).
    - apply PeanoNat.Nat.le_succ_r in H.
      destruct H; [eapply IHlen; eauto|].
      constructor; intros.
      apply IHlen.
      abstract (Omega.omega).
  Defined.

  Theorem lengthOrder_wf: well_founded lengthOrder.
  Proof.
    red; intro;
    eapply lengthOrder_wf'; eauto.
  Defined.

  Theorem remove_length_le ls: forall v: A, length (remove decA v ls) <= length ls.
  Proof.
    induction ls; simpl; auto; intros.
    destruct (decA v a); [subst|]; simpl; auto.
    apply Le.le_n_S; eapply IHls; eauto.
  Qed.

  Theorem remove_length_in_lt ls: forall v: A, In v ls -> length (remove decA v ls) < length ls.
  Proof.
    induction ls; simpl; auto; intros.
    - contradiction.
    - destruct (decA v a); [subst|].
      + apply Lt.le_lt_n_Sm.
        eapply remove_length_le.
      + simpl.
        apply Lt.lt_n_S; eapply IHls; eauto.
        destruct H; [subst; tauto|auto].
  Qed.

  Definition getConnectedChain': (A * list A) -> list A :=
    Fix lengthOrder_wf (fun _ => list A)
        (fun (ls: A * list A)
             (getConnectedChain: forall ls': A * list A, lengthOrder ls' ls -> list A) =>
           match find (fun v => if decA (fst ls) (fst v) then true else false) graph with
             | None => nil
             | Some (_, vs) =>
               match vs with
                 | nil => nil
                 | v :: vs' =>
                   (if in_dec decA v (snd ls)
                    then v :: getConnectedChain (v, remove decA v (snd ls))
                           (ltac:(eapply remove_length_in_lt; eauto))
                    else nil)
                     ++
                     (fix help vs' :=
                        match vs' with
                          | nil => nil
                          | y :: ys =>
                            if in_dec decA y (snd ls)
                            then y :: getConnectedChain (y, remove decA y (snd ls))
                                   (ltac:(eapply remove_length_in_lt; eauto))
                                   ++ help ys
                            else help ys
                        end) vs'
               end
           end).

  Definition getConnectedChain v :=
    getConnectedChain' (v, map fst graph).
End CallChain.

