From Coq Require Import Peano_dec Bool String List PeanoNat.
Require Import Lib.CommonTactics Lib.ilist Lib.NatLib Lib.Word Lib.Struct.
Require Import Lib.FMap Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.RefinementFacts.
Require Import Kami.Wf Kami.Notations Kami.Tactics.
Require Import Kami.Decomposition.
Require Import Ex.Fifo Ex.NativeFifo Lia.

Import ListNotations.

Set Implicit Arguments.

Local Hint Unfold listIsEmpty listEnq listDeq listFirstElt: MethDefs.

Section Facts.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.
  Variable default: ConstT dType.

  Definition rsz := S sz.
  #[local] Hint Unfold rsz: MethDefs.

  Definition sfifo := simpleFifo fifoName rsz dType.
  Definition nsfifo := @nativeSimpleFifo fifoName dType default.
  #[local] Hint Unfold sfifo nsfifo: ModuleDefs.

  Notation "^ s" := (fifoName -- s) (at level 0).

  Fixpoint sfifo_nsfifo_elt_not_full
           (eltv : word rsz -> type dType)
           (enqPv : word rsz)
           (edSub : nat): list (type dType) :=
    match edSub with
    | O => nil
    | S ed =>
      (eltv (enqPv ^- (natToWord rsz edSub)))
        :: (sfifo_nsfifo_elt_not_full eltv enqPv ed)
    end.

  Lemma sfifo_nsfifo_elt_not_full_prop_1:
    forall eltv x, sfifo_nsfifo_elt_not_full eltv (x ^+ $1) 1 = [eltv x].
  Proof.
    intros; simpl; repeat f_equal.
    unfold rsz in *; word_lia_Z.
  Qed.

  Lemma sfifo_nsfifo_elt_not_full_prop_2:
    forall eltv enqPv edSub,
      edSub <> O ->
      exists tfifo,
        sfifo_nsfifo_elt_not_full eltv enqPv edSub = (eltv (enqPv ^- $ edSub)) :: tfifo.
  Proof.
    intros; destruct edSub; [elim H; auto|].
    eexists; reflexivity.
  Qed.

  Lemma sfifo_nsfifo_elt_not_full_enq:
    forall eltv enqPv elt edSub,
      (edSub <= wordToNat (wones rsz))%nat -> 
      sfifo_nsfifo_elt_not_full eltv enqPv edSub ++ [elt] =
      sfifo_nsfifo_elt_not_full (fun w => if weq w enqPv then elt else eltv w)
                              (enqPv ^+ $1) (S edSub).
  Proof.
    induction edSub; intros.
    - simpl; f_equal.
      destruct (weq _ _); auto.
      elim n; clear n.
      unfold rsz in *; word_lia_Z.
    - unfold sfifo_nsfifo_elt_not_full in *.
      fold sfifo_nsfifo_elt_not_full in *.
      rewrite <-IHedSub by lia; clear IHedSub.
      unfold app; f_equal.
      destruct (weq _ _).
      + exfalso; unfold rsz in *; word_lia_Z.
      + f_equal; unfold rsz in *; word_lia_Z.
  Qed.

  Lemma sfifo_nsfifo_elt_not_full_deq:
    forall eltv enqPv edSub,
      match sfifo_nsfifo_elt_not_full eltv enqPv edSub with
      | nil => nil
      | _ :: t => t
      end = 
      sfifo_nsfifo_elt_not_full eltv enqPv (pred edSub).
  Proof.
    induction edSub; reflexivity.
  Qed.

  Definition sfifo_nsfifo_eta (r: RegsT): option (sigT (fullType type)).
  Proof.
    kgetv ^"elt" eltv r (Vector dType rsz) (None (A:= sigT (fullType type))).
    kgetv ^"empty" emptyv r Bool (None (A:= sigT (fullType type))).
    kgetv ^"full" fullv r Bool (None (A:= sigT (fullType type))).
    kgetv ^"enqP" enqPv r (Bit rsz) (None (A:= sigT (fullType type))).
    kgetv ^"deqP" deqPv r (Bit rsz) (None (A:= sigT (fullType type))).

    refine (Some (existT _ (listEltK dType type) _)).
    destruct (weq enqPv deqPv).
    - refine (if fullv then _ else _).
      + exact ((eltv deqPv) :: (sfifo_nsfifo_elt_not_full eltv enqPv (wordToNat (wones rsz)))).
      + exact nil.
    - exact (sfifo_nsfifo_elt_not_full eltv enqPv (wordToNat (enqPv ^- deqPv))).
  Defined.
  #[local] Hint Unfold sfifo_nsfifo_eta: MethDefs.

  Definition sfifo_nsfifo_theta (r: RegsT): RegsT :=
    match sfifo_nsfifo_eta r with
    | Some er => M.add ^"elt" er (M.empty _)
    | None => M.empty _
    end.
  #[local] Hint Unfold sfifo_nsfifo_theta: MethDefs.
  
  Definition sfifo_nsfifo_ruleMap (_: RegsT) (r: string): option string := Some r.
  #[local] Hint Unfold sfifo_nsfifo_ruleMap: MethDefs.

  Lemma sfifo_substeps_updates:
    forall (o : RegsT) (u1 u2 : UpdatesT) (ul1 ul2 : UnitLabel)
           (cs1 cs2 : MethsT),
      Substep sfifo o u1 ul1 cs1 ->
      Substep sfifo o u2 ul2 cs2 ->
      CanCombineUL u1 u2 (getLabel ul1 cs1) (getLabel ul2 cs2) ->
      u1 = M.empty (sigT (fullType type)) \/
      u2 = M.empty (sigT (fullType type)).
  Proof.
    intros.
    inv H; inv H0; auto; try inv HInRules.
    CommonTactics.dest_in; simpl in *; invertActionRep.
    - exfalso.
      inv H1; inv H19; simpl in *.
      clear -H1; findeq.
    - exfalso.
      inv H1; simpl in *.
      clear -H17; findeq.
    - exfalso.
      inv H1; simpl in *.
      clear -H17; findeq.
    - exfalso.
      inv H1; inv H17; simpl in *.
      clear -H1; findeq.
  Qed.

  Definition sfifo_inv_0 (o: RegsT): Prop.
  Proof.
    kexistv ^"elt" eltv o (Vector dType rsz).
    kexistv ^"empty" emptyv o Bool.
    kexistv ^"full" fullv o Bool.
    kexistv ^"enqP" enqPv o (Bit rsz).
    kexistv ^"deqP" deqPv o (Bit rsz).
    exact True.
  Defined.
  #[local] Hint Unfold sfifo_inv_0: InvDefs.

  Lemma sfifo_inv_0_ok:
    forall o, reachable o sfifo -> sfifo_inv_0 o.
  Proof.
    apply decompositionInv.
    - simpl; kinv_action_dest.
      unfold initRegs, rawInitRegs, getRegInits; simpl.
      kinv_regmap_red; kinv_constr; kinv_eq.
    - intros; inv H0; inv HInRules.
    - intros; inv H0; CommonTactics.dest_in.
      + kinv_magic.
      + kinv_magic.
    - apply sfifo_substeps_updates.
  Qed.

  Definition sfifo_inv_1 (o: RegsT): Prop.
  Proof.
    kexistv ^"empty" emptyv o Bool.
    kexistv ^"full" fullv o Bool.
    kexistv ^"enqP" enqPv o (Bit rsz).
    kexistv ^"deqP" deqPv o (Bit rsz).
    refine (or3 _ _ _).
    - exact (emptyv = true /\ fullv = false /\ (if weq enqPv deqPv then true else false) = true).
    - exact (emptyv = false /\ fullv = true /\ (if weq enqPv deqPv then true else false) = true).
    - exact (emptyv = false /\ fullv = false /\ (if weq enqPv deqPv then true else false) = false).
  Defined.
  #[local] Hint Unfold sfifo_inv_1: InvDefs.

  Lemma sfifo_inv_1_ok:
    forall o,
      reachable o sfifo ->
      sfifo_inv_1 o.
  Proof.
    apply decompositionInv.
    - simpl; kinv_action_dest.
      unfold initRegs, rawInitRegs, getRegInits; simpl.
      kinv_regmap_red; kinv_constr; kinv_eq.
      or3_fst; repeat split; destruct (weq _ _); congruence.
    - intros; inv H0; inv HInRules.
    - intros; inv H0; CommonTactics.dest_in.
      + simpl in *; kinv_magic_light_with kinv_or3.
        * or3_thd; repeat split.
          { destruct (weq _ _); auto.
            wplus_one_contra.
          }
          { destruct (weq _ _); auto.
            wplus_one_contra.
          }
        * destruct (weq x6 (x5 ^+ $1)).
          { or3_snd; repeat split.
            destruct (weq _ _); auto.
          }
          { or3_thd; repeat split.
            destruct (weq _ _); auto.
            elim n0; auto.
          }
      + simpl in *; kinv_magic_light_with kinv_or3.
        * or3_thd; repeat split.
          { destruct (weq _ _); auto.
            wplus_one_contra.
          }
          { destruct (weq _ _); auto.
            wplus_one_contra.
          }
        * destruct (weq x5 (x6 ^+ $1)).
          { or3_fst; auto. }
          { or3_thd; auto. }
    - apply sfifo_substeps_updates.
  Qed.

  Lemma sfifo_refines_nsfifo: sfifo <<== nsfifo.
  Proof.
    apply decompositionOne with (eta:= sfifo_nsfifo_eta)
                                  (ruleMap:= sfifo_nsfifo_ruleMap)
                                  (specRegName:= ^"elt").

    - kequiv.
    - unfold theta; kdecompose_regmap_init; kinv_finish.
    - auto.
    - auto.
    - intros; inv H0; inv HInRules.
    - intros; inv H0.

      pose proof (sfifo_inv_0_ok H).
      pose proof (sfifo_inv_1_ok H).
      CommonTactics.dest_in; simpl in *; invertActionRep.

      + kinv_red.
        eexists; split.
        * eapply SingleMeth.
          { left; reflexivity. }
          { instantiate (3:= argV).
            simpl; repeat econstructor.
            kregmap_red; kregmap_clear; reflexivity.
            findeq.
          }
          { reflexivity. }

        * kinv_red.
          repeat split.
          { intros; inv H0. }
          { intros; inv H0. }
          { kregmap_red; kregmap_clear; meq.
            { wplus_one_contra. }
            { wplus_one_contra. }
            { repeat f_equal.
              simpl; replace (wordToNat _) with 1.
              { rewrite sfifo_nsfifo_elt_not_full_prop_1.
                destruct (weq x6 x6); intuition idtac.
              }
              { unfold rsz in *; word_lia_Z. }
            }
            { wplus_one_contra. }
            { repeat f_equal.
              unfold evalExpr.
              rewrite sfifo_nsfifo_elt_not_full_enq.
              { unfold sfifo_nsfifo_elt_not_full.
                fold sfifo_nsfifo_elt_not_full.
                repeat f_equal.
                { unfold rsz in *; clear n e n0.
                  destruct (weq _ _); [|clear n].
                  { exfalso; unfold rsz in *; word_lia_Z. }
                  { f_equal; unfold rsz in *; word_lia_Z. }
                }
                { unfold rsz in *; word_lia_Z. }
              }
              { unfold rsz in *; word_lia_Z. }
            }
            { repeat f_equal; simpl.
              rewrite sfifo_nsfifo_elt_not_full_enq.
              { repeat f_equal.
                unfold rsz in *; word_lia_Z.
              }
              { unfold rsz in *; word_lia_Z. }
            }
          }

      + kinv_red.
        destruct H13 as [|[|]]; dest; subst; [discriminate| |].
        * eexists; split.
          { unfold rsz in *.
            destruct (weq x5 x6); [|discriminate]; subst.
            eapply SingleMeth.
            { right; left; reflexivity. }
            { instantiate (3:= argV).
              repeat econstructor.
              { kregmap_red; kregmap_clear; reflexivity. }
              { destruct (weq x6 x6); [|elim n; reflexivity].
                reflexivity.
              }
              { findeq. }
            }
            { destruct (weq x6 x6); [|elim n; reflexivity].
              reflexivity.
            }
          }
          { repeat split.
            { intros; inv H1. }
            { intros; inv H1. }
            { kregmap_red; kregmap_clear; meq.
              { wplus_one_contra. }
              { replace (x6 ^- (x6 ^+ $1)) with (wones (S sz)); auto.
                unfold rsz in *; word_lia_Z.
              }
            }
          }
          
        * eexists; split.
          { unfold rsz in *.
            destruct (weq x5 x6); [discriminate|].
            eapply SingleMeth.
            { right; left; reflexivity. }
            { instantiate (3:= argV).
              repeat econstructor.
              { kregmap_red; kregmap_clear; reflexivity. }
              { destruct (weq x5 x6); [elim n; auto|].
                pose proof (@sfifo_nsfifo_elt_not_full_prop_2 x7 x5 (wordToNat (x5 ^- x6))).
                assert (wordToNat (x5 ^- x6) <> 0) by (unfold rsz in *; word_lia_Z).
                specialize (H1 H10); clear H10; dest.
                rewrite H1; reflexivity.
              }
              { findeq. }
            }
            { destruct (weq x5 x6); [elim n; auto|].
              simpl; repeat f_equal.
              pose proof (@sfifo_nsfifo_elt_not_full_prop_2 x7 x5 (wordToNat (x5 ^- x6))).
              assert (wordToNat (x5 ^- x6) <> 0) by (unfold rsz in *; word_lia_Z).
              specialize (H1 H10); clear H10; dest.
              rewrite H1; unfold listFirstElt, evalExpr; f_equal.

              rewrite natToWord_wordToNat.
              unfold rsz in *; word_lia_Z.
            }
          }
          { repeat split.
            { intros; inv H1. }
            { intros; inv H1. }
            { kregmap_red; kregmap_clear; meq.
              { simpl; repeat f_equal.
                replace (wordToNat _) with 1.
                { rewrite sfifo_nsfifo_elt_not_full_prop_1; reflexivity. }
                { unfold rsz in *; word_lia_Z. }
              }
              { simpl; repeat f_equal.
                rewrite sfifo_nsfifo_elt_not_full_deq.
                f_equal; unfold rsz in *; word_lia_Z.
              }
            }
          }

    - intros; subst.
      inv H0; inv H1; inv H3; inv H4.
      + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto.
      + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto.
      + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto.
      + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto.
      + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto.
      + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto.
      + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto.
      + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto.
      + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto.
      + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto.
      + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto.
      + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto.
      + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto.
      + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto.
      + simpl in *; inv H2; inv H1; dest; repeat split; unfold getLabel; simpl; auto.
      + CommonTactics.dest_in; try discriminate; simpl in *.

        * exfalso; inv H2; inv H1; dest; simpl in *; findeq.
        * exfalso; clear HAction1 HAction2 Hsig Hsig0.
          invertActionRep; inv H2; findeq.
        * exfalso; clear HAction1 HAction2 Hsig Hsig0.
          invertActionRep; inv H2; findeq.
        * exfalso; inv H2; inv H1; dest; simpl in *; findeq.
  Qed.

End Facts.
