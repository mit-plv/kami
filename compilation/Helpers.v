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

  Fixpoint find_pos' s (ls: list A) n :=
    match ls with
      | nil => None
      | x :: xs => if decA x s
                   then Some n
                   else find_pos' s xs (S n)
    end.

  Definition find_pos s ls := find_pos' s ls 0.

End intersect.

Section GenerateRegIndicies.
  Variable regs: list string.
  Variable regReads: string -> list string.
  Variable regWrites: string -> list string.
  Variable totalOrder: list string.
  Variable ignoreLess: list (string * string).

  Local Fixpoint find_all_prev' s (ignoreLess': list (string * string)) :=
    match ignoreLess' with
      | nil => nil
      | (l, g) :: xs => if string_eq l s
                        then g :: find_all_prev' s xs
                        else find_all_prev' s xs
    end.

  Local Definition find_all_prev s := find_all_prev' s ignoreLess.

  Section FindWritePrevPos.
    Variable reg: string.
    Variable pos: nat.

    Local Fixpoint find_write_prev_pos' currPos (ls: list string) :=
      match ls with
        | nil => None
        | x :: xs => match find_write_prev_pos' (S currPos) xs with
                       | None =>
                         if in_dec string_dec reg (regWrites x)
                         then if lt_dec currPos pos
                              then Some (currPos, x)
                              else None
                         else None
                       | Some y => Some y
                     end
      end.

    Local Lemma find_write_prev_pos'_correct:
      forall ls currPos i x, Some (i, x) = find_write_prev_pos' currPos ls  -> i < pos.
    Proof.
      induction ls; simpl; intros; try congruence.
      specialize (IHls (S currPos) i x).
      repeat match goal with
               | H: context [match ?P with _ => _ end] |- _ => destruct P
             end; try solve [congruence || eapply IHls; eauto].
    Qed.

    Local Definition find_write_prev_pos := find_write_prev_pos' 0 totalOrder.
    
    Local Lemma find_write_prev_pos_correct:
      forall i x, Some (i, x) = find_write_prev_pos  -> i < pos.
    Proof.
      eapply find_write_prev_pos'_correct.
    Qed.
  End FindWritePrevPos.

  Variable cheat: forall t, t.

  Section Reg.
    Variable reg: string.

    Local Definition find_reg_index: nat -> nat :=
      Fix
        Wf_nat.lt_wf (fun _ => nat)
        (fun (pos: nat)
             (find_reg_index: forall pos', pos' < pos -> nat) =>
           match pos return (forall pos', pos' < pos -> nat) -> nat with
             | 0 => fun _ => 0
             | S m =>
               fun find_reg_index =>
                 match nth_error totalOrder (S m) with
                   | Some a =>
                     if in_dec string_dec reg (regReads a ++ regWrites a)%list
                     then
                       match
                         find_write_prev_pos reg (S m) as val
                         return (forall i x, Some (i, x) = val -> i < S m) -> nat with
                         | None => fun _ => find_reg_index m (ltac:(Omega.omega))
                         | Some (prev_pos, a') =>
                           if in_dec string_dec reg (regWrites a')
                           then fun pf => max (S (find_reg_index  prev_pos (pf _ _ eq_refl)))
                                              (find_reg_index m (ltac:(Omega.omega)))
                           else fun _ => find_reg_index m (ltac:(Omega.omega))
                       end (find_write_prev_pos_correct reg (S m))
                     else find_reg_index m (ltac:(Omega.omega))
                   | None => 0
                 end
           end find_reg_index).

    Local Definition find_max_reg_index :=
      match length totalOrder with
        | 0 => 0
        | S m => find_reg_index m
      end.
      
  End Reg.
End GenerateRegIndicies.

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

  Definition getConnectedChain: (A * list A) -> list A :=
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
                    then getConnectedChain (v, remove decA v (snd ls))
                                           (ltac:(eapply remove_length_in_lt; eauto))
                    else nil)
                     ++
                     (fix help vs' :=
                        match vs' with
                          | nil => nil
                          | y :: ys =>
                            if in_dec decA y (snd ls)
                            then getConnectedChain (y, remove decA y (snd ls))
                                                   (ltac:(eapply remove_length_in_lt; eauto))
                                                   ++ help ys
                            else help ys
                        end) vs'
               end
           end).
End CallChain.

