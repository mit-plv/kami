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

  Lemma fold_left_remove_nil ls:
    fold_left (fun rest x => remove decA x rest) ls nil = nil.
  Proof.
    induction ls;simpl; auto; intros.
  Qed.

  Lemma fold_left_remove_le ls1:
    forall a ls2,
      length (fold_left (fun rest x => remove decA x rest) ls1 (a :: ls2)) <=
      S (length (fold_left (fun rest x => remove decA x rest) ls1 ls2)).
  Proof.
    induction ls1;simpl; auto; intros.
    destruct (decA a a0); [subst | ].
    - Omega.omega.
    - apply IHls1.
  Qed.


  Lemma remove_length_in_fold_lt' init ls:
    length (fold_left (fun rest x => remove decA x rest) init ls) <= length ls.
  Proof.
    induction ls; simpl; auto; intros.
    - rewrite fold_left_remove_nil; simpl; Omega.omega.
    - pose proof (fold_left_remove_le init a ls).
      Omega.omega.
  Qed.  

  Theorem remove_length_in_fold_lt ls:
    forall a init,
      In a ls ->
      length (fold_left (fun rest x => remove decA x rest) (a :: init) ls) < length ls.
  Proof.
    simpl; intros.
    pose proof (remove_length_in_fold_lt' init (remove decA a ls)).
    pose proof (remove_length_in_lt ls a H).
    Omega.omega.
  Qed.

  (*
  lengthOrder
    (y,
    fold_left (fun (rest : list A) (x : A) => remove decA x rest) visited
      (remove decA y (snd vRemaining))) vRemaining
   *)

  Definition getConnectedChain': (A * list A) -> list A.
    refine
      (Fix lengthOrder_wf (fun _ => list A)
           (fun (vRemaining: A * list A)
                (getConnectedChain: forall ls': A * list A, lengthOrder ls' vRemaining -> list A) =>
              match find (fun v => if decA (fst vRemaining) (fst v) then true else false) graph with
                | None => nil
                | Some (_, nghs) =>
                  match nghs with
                    | nil => nil
                    | n :: ns =>
                      (if in_dec decA n (snd vRemaining)
                       then n :: getConnectedChain (n, fold_left (fun rest x => remove decA x rest) (n :: ns) (snd vRemaining))
                              (ltac:(eapply remove_length_in_fold_lt; eauto))
                       else
                         match find (fun v => if decA n (fst v) then true else false) graph with
                           | None => n :: nil
                           | Some _ => nil
                         end)
                        ++
                        (fix help ns :=
                           match ns with
                             | nil => nil
                             | y :: ys =>
                               if in_dec decA y (snd vRemaining)
                               then y :: getConnectedChain (y, fold_left (fun rest x => remove decA x rest) (y :: n :: ys)
                                                                         (snd vRemaining))
                                      (ltac:(eapply remove_length_in_fold_lt; eauto))
                                      ++ help ys
                               else
                                 match find (fun v => if decA y (fst v) then true else false) graph with
                                   | None => y :: help ys
                                   | Some _ => help ys
                                 end
                           end) ns
                  end
              end)).
  Defined.

  Definition getConnectedChain v :=
    getConnectedChain' (v, remove decA v (map fst graph)).
End CallChain.

