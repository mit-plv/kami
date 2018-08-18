Require Import Bool List String Omega.
Require Import Structures.Equalities Program.Equality Eqdep Eqdep_dec.
Require Import FunctionalExtensionality.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct.
Require Import Kami.Syntax Kami.Semantics.

Ltac shatter := repeat match goal with
                       | [ H : exists _, _ |- _ ] => destruct H
                       | [ H : _ /\ _ |- _ ] => destruct H
                       end.


Module Type Assumptions.
  
  Parameter m: Modules.
  
  Parameter Prule : MethsT -> Prop.
  Parameter Pmeth : MethsT -> Prop.  
  
  Axiom Pmeth_empty : Pmeth ([])%fmap.

  Axiom Prule_empty : Prule ([])%fmap.
  
  Axiom Prules : forall k a, List.In {| attrName := k; attrType := a |} (getRules m) ->
                        forall o u cs retVal, SemAction o (a type) u cs retVal ->
                                       Prule cs.

  Axiom Pmeths :  forall f, In f (getDefsBodies m) ->
                       forall o (u : UpdatesT) (cs : MethsT) (argV : type (arg (projT1 (attrType f)))) (retV : type (ret (projT1 (attrType f)))),
                         SemAction o (projT2 (attrType f) type argV) u cs retV ->
                         Pmeth cs.
  
  Axiom Prume : forall rcs, Prule rcs ->
                       forall mcs, Pmeth mcs ->
                              Prule (M.union rcs mcs).  
  
  Axiom Pmeru : forall mcs, Pmeth mcs ->
                       forall rcs, Prule rcs ->
                              Prule (M.union mcs rcs).  

  Axiom Pmeme : forall mcs, Pmeth mcs ->
                       forall mcs', Pmeth mcs' ->
                               Pmeth (M.union mcs mcs').

  Axiom Prsub : forall rcs rcs', Prule rcs' -> M.Sub rcs rcs' -> Prule rcs.

End Assumptions.

Module Conclusions (A : Assumptions).
  Import A.

  Lemma Pmeth_rule : forall cs, Pmeth cs -> Prule cs.
  Proof.
    intros. replace cs with (M.union [] cs)%fmap by (apply M.union_empty_L).
    apply Prume. apply Prule_empty. assumption.
  Qed.
  
  Fixpoint union_all_calls {o} (ss : Substeps m o) : MethsT :=
    match ss with
    | nil => []%fmap
    | s :: ss' => M.union (cms s) (union_all_calls ss')
    end.
  
  Definition PSubstepRec {o} (s : SubstepRec m o) : Prop :=
    match (unitAnnot s) with
    | Rle _ => Prule (cms s)
    | Meth _  => Pmeth (cms s)
    end.  
  
  Lemma base_cases : forall {o}, forall s : SubstepRec m o, PSubstepRec s.
  Proof.
    intros o s. destruct s. inversion substep; subst; unfold PSubstepRec; simpl.
    - apply Prule_empty.
    - apply Pmeth_empty.
    - eapply Prules; try eassumption.
    - eapply Pmeths; try eassumption.
  Qed.
  
  Lemma PSubsteps : forall {o} (ss : Substeps m o), substepsComb ss -> (Prule (union_all_calls ss) /\ exists s k, In s ss /\ (unitAnnot s) = Rle k) \/ Pmeth (union_all_calls ss).
  Proof. induction 1; simpl.
         right. apply Pmeth_empty.           
         destruct IHsubstepsComb.
         - left. shatter. specialize (H0 _ H2). inv H0. shatter.
           destruct H5.
           + pose proof (base_cases s) as X.  unfold PSubstepRec in X; rewrite H5 in X.
             split. apply Pmeru; assumption.
             eauto.
           + congruence.
         - pose proof (base_cases s) as X. unfold PSubstepRec in X. destruct (unitAnnot s) eqn:Hua.
           + left. split. apply Prume; assumption. eauto.
           + right. apply Pmeme; assumption.
  Qed.

    
  Lemma combine_compat:
    forall {o}, forall ss : Substeps m o, union_all_calls ss = calls (foldSSLabel ss).
  Proof.
    induction ss; auto. 
    simpl. 
    unfold addLabelLeft. unfold getSLabel.
    destruct a; destruct unitAnnot; simpl; destruct (foldSSLabel ss) eqn:H; simpl; simpl in IHss; congruence.
  Qed.
         
  Theorem Prule_Step :  forall o u l, Step m o u l -> Prule (calls l).
    induction 1.
    pose proof (PSubsteps ss HSubsteps) as H.
    unfold hide; simpl. destruct H; shatter;
                          eapply Prsub; try apply M.subtractKV_sub.
    rewrite <- combine_compat; assumption.
    rewrite <- combine_compat; apply Pmeth_rule; assumption.
  Qed.

End Conclusions.