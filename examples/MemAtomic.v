Require Import Bool String List.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct Lib.Reflection Lib.ilist Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate Kami.RefinementFacts.
Require Import Kami.SemFacts Kami.Wf Kami.ParametricSyntax Kami.ParametricEquiv Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo.

Set Implicit Arguments.

Section Middleman.
  Variable inName outName: string.
  Variable addrSize lgDataBytes: nat.

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  Definition getReq := MethodSig (inName -- "deq")() : Struct RqFromProc.
  Definition setRep := MethodSig (outName -- "enq")(Struct RsToProc) : Void.
  Definition exec := MethodSig "exec"(Struct RqFromProc) : Struct RsToProc.

  Definition processLd {ty} : ActionT ty Void :=
    (Call req <- getReq();
     Assert !#req!RqFromProc@."op";
     Call rep <- exec(#req);
     Call setRep(#rep);
     Retv)%kami_action.

  Definition processSt {ty} : ActionT ty Void :=
    (Call req <- getReq();
     Assert #req!RqFromProc@."op";
     Call rep <- exec(#req);
     Call setRep(#rep);
     Retv)%kami_action.

  Definition mid := MODULE {
    Rule "processLd" := processLd
    with Rule "processSt" := processSt
  }.

  Section MemAtomicWoQInl.
    Variable n: nat.

    Hypothesis HinName: index 0 indexSymbol (inName -- "deq") = None.
    Hypothesis HoutName: index 0 indexSymbol (outName -- "enq") = None.

    Definition getReqI (i: nat) := MethodSig (inName -- "deq" __ i)() : Struct RqFromProc.
    Definition setRepI (i: nat) := MethodSig (outName -- "enq" __ i)(Struct RsToProc) : Void.

    Definition processLdInlGen: GenAction Void Void :=
      fun ty =>
        (Calli req <- { getReq | HinName } ();
           Assert !#req!RqFromProc@."op";
           Read memv <- "mem";
           LET ldval <- #memv@[#req!RqFromProc@."addr"];
           LET rep <- STRUCT { "data" ::= #ldval } :: Struct RsToProc;
           Calli { setRep | HoutName } (#rep);
           Retv)%kami_gen.

    Definition processStInlGen: GenAction Void Void :=
      fun ty =>
        (Calli req <- { getReq | HinName } ();
           Assert #req!RqFromProc@."op";
           Read memv <- "mem";
           Write "mem" <- #memv@[ #req!RqFromProc@."addr" <- #req!RqFromProc@."data" ];
           LET rep <- STRUCT { "data" ::= $$Default } :: Struct RsToProc;
           Calli { setRep | HoutName } (#rep);
           Retv)%kami_gen.

    Definition memAtomicWoQInlM := META {
      Register "mem" : Vector (Data lgDataBytes) addrSize <- Default
      with Repeat Rule till n by "processLd" := (processLdInlGen _)
      with Repeat Rule till n by "processSt" := (processStInlGen _)
    }.
    
  End MemAtomicWoQInl.
  
End Middleman.

Hint Unfold mid memAtomicWoQInlM : ModuleDefs.
Hint Unfold RqFromProc RsToProc getReq setRep exec
     getReqI setRepI processLdInlGen processStInlGen
     processLd processSt : MethDefs.

Section MemAtomic.
  Variables (addrSize fifoSize lgDataBytes: nat).

  Variable n: nat.

  Definition minst := memInst n addrSize lgDataBytes.

  Definition inQ := @simpleFifo "rqFromProc" fifoSize (Struct (RqFromProc addrSize lgDataBytes)).
  Definition outQ := @simpleFifo "rsToProc" fifoSize (Struct (RsToProc lgDataBytes)).
  Definition ioQ := ConcatMod inQ outQ.

  Definition ios (i: nat) := duplicate ioQ i.

  Definition midQ := mid "rqFromProc" "rsToProc" addrSize lgDataBytes.
  Definition mids (i: nat) := duplicate midQ i.
  
  Definition iom := ConcatMod ioQ midQ.
  Definition ioms (i: nat) := duplicate iom i.

  Definition memAtomicWoQ := ConcatMod (mids n) minst.
  Definition memAtomicWoQInl :=
    modFromMeta (memAtomicWoQInlM "rqFromProc" "rsToProc" addrSize lgDataBytes n
                                  eq_refl eq_refl).
  Definition memAtomic := ConcatMod (ioms n) minst.

End MemAtomic.

Hint Unfold minst inQ outQ ioQ midQ mids iom ioms
     memAtomicWoQInl memAtomicWoQ memAtomic : ModuleDefs.

Section Facts.
  Variables (addrSize fifoSize lgDataBytes: nat).

  Lemma midQ_ModEquiv:
    ModPhoasWf (midQ addrSize lgDataBytes).
  Proof.
    kequiv.
  Qed.
  Hint Resolve midQ_ModEquiv.

  Lemma iom_ModEquiv:
    ModPhoasWf (iom addrSize fifoSize lgDataBytes).
  Proof.
    kequiv.
  Qed.
  Hint Resolve iom_ModEquiv.

  Variable n: nat.

  Lemma mids_ModEquiv:
    ModPhoasWf (mids addrSize lgDataBytes n).
  Proof.
    kequiv.
  Qed.
  Hint Resolve mids_ModEquiv.

  Lemma ioms_ModEquiv:
    ModPhoasWf (ioms addrSize fifoSize lgDataBytes n).
  Proof.
    kequiv.
  Qed.
  Hint Resolve ioms_ModEquiv.

  Lemma memAtomicWoQInl_ModEquiv:
    ModPhoasWf (memAtomicWoQInl addrSize lgDataBytes n).
  Proof.
    kequiv.
  Qed.

  Lemma memAtomicWoQ_ModEquiv:
    ModPhoasWf (memAtomicWoQ addrSize lgDataBytes n).
  Proof.
    kequiv.
  Qed.

  Lemma memAtomic_ModEquiv:
    ModPhoasWf (memAtomic addrSize fifoSize lgDataBytes n).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Immediate midQ_ModEquiv iom_ModEquiv
     mids_ModEquiv ioms_ModEquiv
     memAtomicWoQ_ModEquiv memAtomicWoQInl_ModEquiv memAtomic_ModEquiv.

Section MemAtomicWoQ.
  Variables (addrSize fifoSize lgDataBytes: nat).
  Variable n: nat.

  Lemma ios_memAtomicWoQ_memAtomic:
    ((ios addrSize fifoSize lgDataBytes n ++ memAtomicWoQ addrSize lgDataBytes n)%kami)
      <<== (memAtomic addrSize fifoSize lgDataBytes n).
  Proof.
    unfold memAtomic, memAtomicWoQ.
    krewrite assoc left.
    kmodular_sim_l.
    - apply duplicate_regs_ConcatMod; [kequiv|kequiv|kvr|kvr| |]; auto.
    - apply duplicate_rules_ConcatMod; [kequiv|kequiv|kvr|kvr| |]; auto.
    - apply duplicate_defs_ConcatMod; [kequiv|kequiv|kvr|kvr| |]; auto.
  Qed.

End MemAtomicWoQ.

Section MemAtomicWoQInl.
  Variables addrSize lgDataBytes: nat.
  Variable n: nat.

  Definition memAtomicWoQ_regMap (r: RegsT) := r.
  Definition memAtomicWoQ_ruleMap (o: RegsT) (rn: string) := Some rn.

  Lemma memAtomicWoQInl_refines_memAtomicWoQ_ld:
    forall o u cs i
           (H: (i <= n)%nat)
           (HAction:
              SemAction
                o (getActionFromGen string_of_nat natToVoid
                                    (processLdInlGen "rqFromProc" "rsToProc"
                                                     addrSize lgDataBytes eq_refl eq_refl) i
                                    type) u cs WO),
      Step (memAtomicWoQ addrSize lgDataBytes n) o u
           {| annot := Some (Some ("processLd") __ (i)); defs := []%fmap; calls := cs |}.
  Proof.
    intros; apply step_consistent.
    invertActionRep; clear H0 H3 H4.

    evar (execLabel: {x : SignatureT & SignT x}).
    match goal with
    | [ |- StepInd _ _ _ {| annot := ?ann; defs := _; calls := ?cs |} ] =>
      assert ({| annot := ann; defs := []%fmap; calls := cs |}
              = hide {| annot := ann;
                        defs := ["exec" __ i <- execLabel]%fmap;
                        calls := cs +["exec" __ i <- execLabel]%fmap |}) as Hl
          by (unfold hide; simpl; f_equal; meq)
    end.
    rewrite Hl; constructor.

    - clear Hl.
      eapply SubstepsCons.
      + eapply SubstepsCons.
        * apply SubstepsNil.
        * (* processLd *)
          eapply SingleRule.
          { instantiate
              (1:= fun ty =>
                     Renaming.renameAction
                       (specializer (midQ addrSize lgDataBytes) i)
                       (@processLd "rqFromProc" "rsToProc" addrSize lgDataBytes ty)).
            instantiate (1:= "processLd"%string __ i).

            replace (getRules (memAtomicWoQ addrSize lgDataBytes n))
            with (getRules (mids addrSize lgDataBytes n))
              by (simpl; rewrite app_nil_r; reflexivity).
            apply getRules_duplicate_in; auto.
            simpl; tauto.
          }
          { kinv_constr.
            instantiate (1:= x); simpl.
            rewrite H2; reflexivity.
          }
        * repeat split; auto.
        * reflexivity.
        * reflexivity.
      + (* exec *)
        eapply SingleMeth.
        * instantiate
            (1:= {| attrName := "exec"%string __ i;
                    attrType :=
                      (getMethFromGen
                         string_of_nat
                         natToVoid
                         (existT _ {| arg := Struct (RqFromProc addrSize lgDataBytes);
                                      ret := Struct (RsToProc lgDataBytes) |}
                                 (@memInstExec addrSize lgDataBytes))
                         i) |}).

          replace (getDefsBodies (memAtomicWoQ addrSize lgDataBytes n))
          with (getDefsBodies (minst addrSize lgDataBytes n))
            by (simpl; unfold mids; rewrite getDefsBodies_duplicate_nil by reflexivity;
                rewrite app_nil_l; reflexivity).
          simpl; rewrite app_nil_r.
          apply repMeth_in.
          apply getNatListToN_le; auto.
        * kinv_constr; auto; try eassumption.
          instantiate (1:= x); simpl.
          rewrite H2; reflexivity.
        * reflexivity.
      + repeat split; auto.
        simpl; findeq.
      + reflexivity.
      + repeat (rewrite specializer_dom;
                [|apply specializable_disj_dom_img; reflexivity|cbn; tauto]).
        unfold mergeLabel, getLabel; f_equal.
        * unfold execLabel; meq.
        * meq.

    - rewrite <-Hl; clear Hl; split.
      + apply M.KeysDisj_empty.
      + simpl; unfold memAtomicWoQ.
        rewrite getDefs_app.
        unfold mids; rewrite getDefs_duplicate_nil by reflexivity.
        rewrite app_nil_l.

        match goal with
        | [ |- M.KeysDisj (M.add _ _ (M.add _ ?v _)) _ ] =>
          remember v as val eqn:Heqv; clear
        end.
        induction n.
        * cbn; unfold M.KeysDisj; intros.
          findeq; try (inv H; [discriminate|inv H0]).
        * cbn; rewrite app_nil_r; unfold M.KeysDisj; intros.
          inv H.
          { findeq; try (inv H; [discriminate|inv H0]). }
          { apply IHn0; cbn; rewrite app_nil_r; auto. }
  Qed.

  Lemma memAtomicWoQInl_refines_memAtomicWoQ_st:
    forall o u cs i
           (H: (i <= n)%nat)
           (HAction:
              SemAction
                o (getActionFromGen string_of_nat natToVoid
                                    (processStInlGen "rqFromProc" "rsToProc"
                                                     addrSize lgDataBytes eq_refl eq_refl) i
                                    type) u cs WO),
      Step (memAtomicWoQ addrSize lgDataBytes n) o u
           {| annot := Some (Some ("processSt") __ (i)); defs := []%fmap; calls := cs |}.
  Proof.
    intros; apply step_consistent.
    invertActionRep; clear H0 H4 H5.

    evar (execLabel: {x : SignatureT & SignT x}).
    match goal with
    | [ |- StepInd _ _ _ {| annot := ?ann; defs := _; calls := ?cs |} ] =>
      assert ({| annot := ann; defs := []%fmap; calls := cs |}
              = hide {| annot := ann;
                        defs := ["exec" __ i <- execLabel]%fmap;
                        calls := cs +["exec" __ i <- execLabel]%fmap |}) as Hl
          by (unfold hide; simpl; f_equal; meq)
    end.
    rewrite Hl; constructor.

    - clear Hl.
      eapply SubstepsCons.
      + eapply SubstepsCons.
        * apply SubstepsNil.
        * (* processSt *)
          eapply SingleRule.
          { instantiate
              (1:= fun ty =>
                     Renaming.renameAction
                       (specializer (midQ addrSize lgDataBytes) i)
                       (@processSt "rqFromProc" "rsToProc" addrSize lgDataBytes ty)).
            instantiate (1:= "processSt"%string __ i).

            replace (getRules (memAtomicWoQ addrSize lgDataBytes n))
            with (getRules (mids addrSize lgDataBytes n))
              by (simpl; rewrite app_nil_r; reflexivity).
            apply getRules_duplicate_in; auto.
            simpl; tauto.
          }
          { kinv_constr.
            instantiate (1:= x); simpl; auto.
          }
        * repeat split; auto.
        * reflexivity.
        * reflexivity.
      + (* exec *)
        eapply SingleMeth.
        * instantiate
            (1:= {| attrName := "exec"%string __ i;
                    attrType :=
                      (getMethFromGen
                         string_of_nat
                         natToVoid
                         (existT _ {| arg := Struct (RqFromProc addrSize lgDataBytes);
                                      ret := Struct (RsToProc lgDataBytes) |}
                                 (@memInstExec addrSize lgDataBytes))
                         i) |}).

          replace (getDefsBodies (memAtomicWoQ addrSize lgDataBytes n))
          with (getDefsBodies (minst addrSize lgDataBytes n))
            by (simpl; unfold mids; rewrite getDefsBodies_duplicate_nil by reflexivity;
                rewrite app_nil_l; reflexivity).
          simpl; rewrite app_nil_r.
          apply repMeth_in.
          apply getNatListToN_le; auto.
        * eapply SemIfElseFalse; kinv_constr; auto; try eassumption.
          instantiate (1:= x); simpl.
          rewrite H2; reflexivity.
        * reflexivity.
      + repeat split; auto.
        simpl; findeq.
      + reflexivity.
      + repeat (rewrite specializer_dom;
                [|apply specializable_disj_dom_img; reflexivity|cbn; tauto]).
        unfold mergeLabel, getLabel; f_equal.
        * unfold execLabel; meq.
        * meq.

    - rewrite <-Hl; clear Hl; split.
      + apply M.KeysDisj_empty.
      + simpl; unfold memAtomicWoQ.
        rewrite getDefs_app.
        unfold mids; rewrite getDefs_duplicate_nil by reflexivity.
        rewrite app_nil_l.

        match goal with
        | [ |- M.KeysDisj (M.add _ _ (M.add _ ?v _)) _ ] =>
          remember v as val eqn:Heqv; clear
        end.
        induction n.
        * cbn; unfold M.KeysDisj; intros.
          findeq; try (inv H; [discriminate|inv H0]).
        * cbn; rewrite app_nil_r; unfold M.KeysDisj; intros.
          inv H.
          { findeq; try (inv H; [discriminate|inv H0]). }
          { apply IHn0; cbn; rewrite app_nil_r; auto. }
  Qed.

  Lemma memAtomicWoQInl_refines_memAtomicWoQ:
    memAtomicWoQInl addrSize lgDataBytes n <<== memAtomicWoQ addrSize lgDataBytes n.
  Proof.
    apply stepRefinement with (ruleMap:= memAtomicWoQ_ruleMap) (theta:= memAtomicWoQ_regMap).

    - unfold memAtomicWoQ_regMap.
      f_equal; simpl.
      unfold mids; rewrite getRegInits_duplicate_nil by reflexivity.
      rewrite app_nil_l; reflexivity.

    - intros; clear H.
      apply step_zero in H0; [|reflexivity]; dest.
      destruct l as [ann ds cs]; simpl in *; subst; cbn.
      destruct ann as [r|];
        [|inv H0; exists (M.empty _); cbn; split; auto; apply step_empty; auto].
      inv H0; [exists (M.empty _); cbn; split; auto; apply step_empty; auto|].
      rewrite idElementwiseId.
      unfold Datatypes.id, memAtomicWoQ_regMap, memAtomicWoQ_ruleMap.
      
      exists u; split; auto.

      assert (exists i,
                 le i n /\
                 (k = "processLd"%string __ i /\
                  a = getActionFromGen
                        string_of_nat
                        natToVoid
                        (processLdInlGen "rqFromProc" "rsToProc" addrSize lgDataBytes
                                         eq_refl eq_refl) i \/
                  k = "processSt"%string __ i /\
                  a = getActionFromGen
                        string_of_nat
                        natToVoid
                        (processStInlGen "rqFromProc" "rsToProc" addrSize lgDataBytes
                                         eq_refl eq_refl) i)) as Ha.
      { clear -HInRules; cbn in HInRules.
        rewrite app_nil_r in HInRules.
        apply in_app_or in HInRules; destruct HInRules.
        { apply repRule_in_exists in H; destruct H as [i ?]; dest; subst.
          exists i; split.
          { apply getNatListToN_le; auto. }
          { left; repeat split. }
        }
        { apply repRule_in_exists in H; destruct H as [i ?]; dest; subst.
          exists i; split.
          { apply getNatListToN_le; auto. }
          { right; repeat split. }
        }
      }
      clear HInRules; destruct Ha as [i ?]; dest.
      destruct H0; dest; subst.
      + apply memAtomicWoQInl_refines_memAtomicWoQ_ld; auto.
      + apply memAtomicWoQInl_refines_memAtomicWoQ_st; auto.
  Qed.
    
End MemAtomicWoQInl.

