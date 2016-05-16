Require Import MetaSyntax Specialize.
Require Import Bool String List.
Require Import Lib.FMap Lib.Struct Lib.CommonTactics Lib.Indexer Lib.StringEq.
Require Import Syntax Semantics SemFacts Refinement Renaming Equiv Wf.

Require Import FunctionalExtensionality.
Require Import Compare_dec.

Set Implicit Arguments.


Lemma duplicate_meta_disj_regs_one:
  forall m s r,
    (forall i, DisjList (namesOf (getRegInits (specializeMod m i))) [s]) ->
    forall mrules mmeths n,
      DisjList (namesOf (getRegInits (duplicate m n)))
               (namesOf (getRegInits (makeModule (Build_MetaModule [One (s :: r)%struct]
                                                                   mrules mmeths)))).
Proof.
  induction n; simpl; [auto|].
  unfold namesOf in *; simpl in *.
  rewrite map_app.
  apply DisjList_app_4; auto.
Qed.

Lemma duplicate_meta_disj_defs_rep:
  forall m s,
    (forall i j, DisjList (getDefs (specializeMod m i)) [s __ j]) ->
    forall mregs mrules mf n,
      DisjList (getDefs (duplicate m n))
               (getDefs (makeModule (Build_MetaModule mregs mrules [Rep s mf n]))).
Proof.
  induction n; [unfold getDefs in *; simpl in *; auto|].

  unfold getDefs in *; simpl in *.
  apply DisjList_comm, SemFacts.DisjList_string_cons.

  - clear IHn.
    unfold namesOf in *; simpl in *.
    rewrite map_app; intro Hx; apply in_app_or in Hx; destruct Hx.
    + specialize (H (S n) (S n) (s __ (S n))); destruct H; auto.
      elim H; simpl; tauto.
    + remember (S n); clear Heqn0.
      induction n.
      * specialize (H 0 n0 (s __ n0)); destruct H; auto.
        elim H; simpl; tauto.
      * simpl in H0; rewrite map_app in H0.
        apply in_app_or in H0; destruct H0; auto.
        specialize (H (S n) n0 (s __ n0)); destruct H; auto.
        elim H; simpl; tauto.

  - rewrite app_nil_r in *.
    match goal with
    | [ |- context[namesOf (?l ++ ?r)] ] =>
      replace (namesOf (l ++ r)) with (namesOf l ++ namesOf r)
        by (unfold namesOf; rewrite map_app; reflexivity)
    end.
    apply DisjList_comm, DisjList_app_4; [|auto].
    clear IHn; generalize (S n); intros.
    induction n; simpl; [auto|].
    apply DisjList_comm, SemFacts.DisjList_string_cons.
    + specialize (H n0 (S n) (s __ (S n))); destruct H; auto.
      elim H; simpl; tauto.
    + apply DisjList_comm; auto.
Qed.

Lemma duplicate_meta_disj_meth_calls_rep:
  forall m mregso mregs mn mf,
    (forall i j, DisjList (getCalls (specializeMod m i))
                          (getCalls (makeModule (Build_MetaModule
                                                   mregso
                                                   nil
                                                   [One (mn __ j :: (mf j))%struct])))) ->
    forall n,
      DisjList (getCalls (duplicate m n))
               (getCalls (makeModule (Build_MetaModule mregs nil [Rep mn mf n]))).
Proof.
  induction n; [unfold getCalls in *; simpl in *; auto|].
  unfold getCalls in *; simpl in *.
  apply DisjList_comm, DisjList_app_4; apply DisjList_comm.

  - apply DisjList_app_4.
    + rewrite getCallsR_app; apply DisjList_app_4.
      * specialize (H (S n) (S n)); rewrite app_nil_r in *.
        apply DisjList_comm, DisjList_app_1, DisjList_comm in H; auto.
      * generalize (S n); intros; clear -H; induction n.
        { specialize (H 0 n0); rewrite app_nil_r in *.
          apply DisjList_comm, DisjList_app_1, DisjList_comm in H; auto.
        }
        { simpl; rewrite getCallsR_app.
          apply DisjList_app_4; [|auto].
          specialize (H (S n) n0); rewrite app_nil_r in *.
          apply DisjList_comm, DisjList_app_1, DisjList_comm in H; auto.
        }
    + rewrite getCallsM_app; apply DisjList_app_4.
      * specialize (H (S n) (S n)); rewrite app_nil_r in *.
        apply DisjList_comm, DisjList_app_2, DisjList_comm in H; auto.
      * generalize (S n); intros; clear -H; induction n.
        { specialize (H 0 n0); rewrite app_nil_r in *.
          apply DisjList_comm, DisjList_app_2, DisjList_comm in H; auto.
        }
        { simpl; rewrite getCallsM_app.
          apply DisjList_app_4; [|auto].
          specialize (H (S n) n0); rewrite app_nil_r in *.
          apply DisjList_comm, DisjList_app_2, DisjList_comm in H; auto.
        }

  - assert (DisjList (getCallsR (getRules (specializeMod m (S n)))
                                ++ getCallsM (getDefsBodies (specializeMod m (S n))))
                     (getCallsM (getListFromRep mn mf n ++ nil))).
    { clear -H; generalize (S n); intros; induction n; [simpl; auto|].
      simpl; apply DisjList_comm, DisjList_app_4; apply DisjList_comm; [|auto].
      specialize (H n0 (S n)); rewrite app_nil_r in *; auto.
    }

    apply DisjList_app_3 in IHn; apply DisjList_app_3 in H0; dest.
    apply DisjList_app_4.
    + rewrite getCallsR_app; apply DisjList_app_4; auto.
    + rewrite getCallsM_app; apply DisjList_app_4; auto.
Qed.

Section DupRep.
  Variable m: Modules.
  Hypothesis (Hmregs: NoDup (namesOf (getRegInits m))).
  Variable n: nat.

  Fixpoint regsToRep (regs: list RegInitT) :=
    match regs with
    | nil => nil
    | r :: rs =>
      (Rep (attrName r) (fun _ => (attrType r)) n)
        :: (regsToRep rs)
    end.

  Fixpoint rulesToRep (rules: list (Attribute (Action Void))) :=
    match rules with
    | nil => nil
    | r :: rs =>
      (Rep (attrName r) (fun i => (fun ty => renameAction (specializer m i) (attrType r ty))) n)
        :: (rulesToRep rs)
    end.

  Fixpoint methsToRep (meths: list DefMethT): list MetaMeth :=
    match meths with
    | nil => nil
    | dm :: dms =>
      (Rep (attrName dm) (fun i : nat =>
                            existT MethodT _ (fun ty arg =>
                                                renameAction (specializer m i)
                                                             (projT2 (attrType dm) ty arg))) n)
        :: (methsToRep dms)
    end.

  Lemma regsToRep_regs_equiv:
    SubList (getRegInits (duplicate m n)) (getFullListFromMeta (regsToRep (getRegInits m))) /\
    SubList (getFullListFromMeta (regsToRep (getRegInits m))) (getRegInits (duplicate m n)).
  Proof.
    admit.
  Qed.

  Definition duplicateByRep := 
    makeModule {| metaRegs := regsToRep (getRegInits m);
                  metaRules := rulesToRep (getRules m);
                  metaMeths := methsToRep (getDefsBodies m) |}.
  
  Lemma duplicate_refines_repeat:
    duplicate m n <<== duplicateByRep.
  Proof.
    unfold makeModule; simpl.
    rewrite idElementwiseId.
    apply traceRefines_same_module_structure; simpl; auto; admit.
    (* - apply duplicate_NoDup_regs; auto. *)
    (* - apply regsToRep_regs_equiv. *)
    (* - apply regsToRep_regs_equiv. *)
  Qed.

End DupRep.

Hint Unfold specializeMod duplicate: ModuleDefs.
Hint Unfold regsToRep rulesToRep methsToRep duplicateByRep: ModuleDefs.

