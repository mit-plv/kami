Require Import List.
Require Import Notations.
Require Import Coq.Numbers.BinNums.
Require Import Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.SymEvalTac Kami.Tactics Kami.ModularFacts Kami.SemFacts.
Require Import Ex.SC Ex.IsaRv32 Ex.ProcThreeStage Ex.OneEltFifo.
Require Import Lib.CommonTactics.
Require Import Compile.Rtl Compile.CompileToRtlTryOpt.
Require Import Logic.FunctionalExtensionality.
Require Import Renaming.

Open Scope string_scope.

Ltac shatter := repeat match goal with
                       | [ H : exists _, _ |- _ ] => destruct H
                       | [ H : _ /\ _ |- _ ] => destruct H
                       end.

Section Specification.
  Variable fhMeth : String.string.
  Variable thMeth : String.string.

  Section AbstractTrace.
    Definition address := type (Bit rv32iAddrSize).
    Definition iaddress := type (Bit rv32iIAddrSize).

    Definition data := type (MemTypes.Data rv32iDataBytes).

    Definition register := type (Bit rv32iRfIdx).

    Definition regfile := StateT rv32iDataBytes rv32iRfIdx type.

    Definition rset (rf : regfile) (r : register) (v : data) : regfile :=
      if weq r (wzero _)
      then rf
      else evalExpr (UpdateVector #rf #r #v)%kami_expr.

    Definition progMem := iaddress -> data.

    Definition memory := type (Vector (MemTypes.Data rv32iDataBytes) rv32iAddrSize).

    Inductive TraceEvent : Type :=
    | Nop (pc : address)
    | Nm (pc : address)
    | Rd (pc : address) (addr : address) (val : data)
    | RdZ (pc : address) (addr : address)
    | Wr (pc : address) (addr : address) (val : data)
    | Branch (pc : address) (taken : bool)
    | ToHost (pc : address) (val : data)
    | FromHost (pc : address) (val : data).

    Inductive hasTrace : regfile -> progMem -> address -> memory -> list TraceEvent -> Prop :=
    | htNil : forall rf pm pc mem,
        hasTrace rf pm pc mem nil
    | htNop : forall rf pm pc mem trace',
        hasTrace rf pm pc mem trace' ->
        hasTrace rf pm pc mem (Nop pc :: trace')
    | htLd : forall inst val rf pm pc mem trace',
        pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
        evalExpr (rv32iGetOptype type inst) = opLd ->
        let addr := evalExpr (rv32iGetLdAddr type inst) in
        let dstIdx := evalExpr (rv32iGetLdDst type inst) in
        dstIdx <> wzero _ ->
        let srcIdx := evalExpr (rv32iGetLdSrc type inst) in
        let srcVal := rf srcIdx in
        let laddr := evalExpr (rv32iCalcLdAddr type addr srcVal) in
        let laddr_aligned := evalExpr (rv32iAlignAddr type laddr) in
        val = mem laddr_aligned ->
        hasTrace (rset rf dstIdx val) pm (evalExpr (rv32iNextPc type rf pc inst)) mem trace' ->
        hasTrace rf pm pc mem (Rd pc laddr_aligned val :: trace')
    | htLdZ : forall inst rf pm pc mem trace',
        pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
        evalExpr (rv32iGetOptype type inst) = opLd ->
        evalExpr (rv32iGetLdDst type inst) = wzero _ ->
        let addr := evalExpr (rv32iGetLdAddr type inst) in
        let srcIdx := evalExpr (rv32iGetLdSrc type inst) in
        let srcVal := rf srcIdx in
        let laddr := evalExpr (rv32iCalcLdAddr type addr srcVal) in
        let laddr_aligned := evalExpr (rv32iAlignAddr type laddr) in
        hasTrace rf pm (evalExpr (rv32iNextPc type rf pc inst)) mem trace' ->
        hasTrace rf pm pc mem (RdZ pc laddr_aligned :: trace')
    | htSt : forall inst rf pm pc mem trace',
        pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
        evalExpr (rv32iGetOptype type inst) = opSt ->
        let addr := evalExpr (rv32iGetStAddr type inst) in
        let srcIdx := evalExpr (rv32iGetStSrc type inst) in
        let srcVal := rf srcIdx in
        let vsrcIdx := evalExpr (rv32iGetStVSrc type inst) in
        let stVal := rf vsrcIdx in
        let saddr := evalExpr (rv32iCalcStAddr type addr srcVal) in
        let saddr_aligned := evalExpr (rv32iAlignAddr type saddr) in
        hasTrace rf pm (evalExpr (rv32iNextPc type rf pc inst)) (fun a => if weq a saddr_aligned then stVal else mem a) trace' ->
        hasTrace rf pm pc mem (Wr pc saddr_aligned stVal :: trace')
    | htTh : forall inst rf pm pc mem trace',
        pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
        evalExpr (rv32iGetOptype type inst) = opTh ->
        let srcIdx := evalExpr (rv32iGetSrc1 type inst) in
        let srcVal := rf srcIdx in
        hasTrace rf pm (evalExpr (rv32iNextPc type rf pc inst)) mem trace' ->
        hasTrace rf pm pc mem (ToHost pc srcVal :: trace')
    | htFh : forall inst rf val pm pc mem trace',
        pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
        evalExpr (rv32iGetOptype type inst) = opFh ->
        let dst := evalExpr (rv32iGetDst type inst) in
        hasTrace (rset rf dst val) pm (evalExpr (rv32iNextPc type rf pc inst)) mem trace' ->
        hasTrace rf pm pc mem (FromHost pc val :: trace')
    | htNmBranch : forall inst rf pm pc mem trace',
        pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
        evalExpr (rv32iGetOptype type inst) = opNm ->
        evalExpr (getOpcodeE #inst)%kami_expr = rv32iOpBRANCH ->
        hasTrace rf pm (evalExpr (rv32iNextPc type rf pc inst)) mem trace' ->
        hasTrace rf pm pc mem (Branch pc (evalExpr (rv32iBranchTaken type rf inst)) :: trace')
    | htNm : forall inst rf pm pc mem trace',
        pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
        evalExpr (rv32iGetOptype type inst) = opNm ->
        evalExpr (getOpcodeE #inst)%kami_expr <> rv32iOpBRANCH ->
        let src1 := evalExpr (rv32iGetSrc1 type inst) in
        let val1 := rf src1 in
        let src2 := evalExpr (rv32iGetSrc2 type inst) in
        let val2 := rf src2 in
        let dst := evalExpr (rv32iGetDst type inst) in
        let execVal := evalExpr (rv32iExec type val1 val2 pc inst) in
        hasTrace (rset rf dst execVal) pm (evalExpr (rv32iNextPc type rf pc inst)) mem trace' ->
        hasTrace rf pm pc mem (Nm pc :: trace').


    Definition censorTrace : list TraceEvent -> list TraceEvent :=
      map (fun te => match te with
                  | Nop _ => te
                  | Nm _ => te
                  | Branch _ _ => te
                  | RdZ _ _ => te
                  | Rd pc addr val => Rd pc addr $0
                  | Wr pc addr val => Wr pc addr $0
                  | ToHost pc val => ToHost pc $0
                  | FromHost pc val => FromHost pc $0
                  end).

    Lemma censorEq_same_pc :
      forall rf1 rf2 pm1 pm2 pc1 pc2 mem1 mem2 tr1 tr2,
        hasTrace rf1 pm1 pc1 mem1 tr1
        -> hasTrace rf2 pm2 pc2 mem2 tr2
        -> censorTrace tr1 = censorTrace tr2
        -> (tr1 = nil /\ tr2 = nil)
           \/ pc1 = pc2.
    Proof.
      intros ? ? ? ? ? ? ? ? ? ? Hht1 Hht2 Hct.
      inversion Hht1; inversion Hht2;
        intros; subst; try tauto; right;
          unfold censorTrace in Hct;
          unfold map in Hct;
          try match goal with
              | [ H : _ :: ?x1 = _ :: ?x2 |- _ ] =>
                let v1 := fresh in
                let v2 := fresh in
                let Heq1 := fresh in
                let Heq2 := fresh in
                remember x1 as v1 eqn:Heq1;
                  remember x2 as v2 eqn:Heq2;
                  clear - Hct;
                  match goal with
                  | [ H : Branch _ ?b1 :: _ = Branch _ ?b2 :: _ |- _ ] =>
                    let b1' := fresh in
                    let Heq1 := fresh in
                    let b2' := fresh in
                    let Heq2 := fresh in
                    remember b1 as b1' eqn:Heq1;
                      remember b2 as b2' eqn:Heq2;
                      clear - Hct
                  end;
                  repeat match goal with
                         | [ x := _ : _ |- _ ] =>
                           let x' := fresh in
                           let Heq := fresh in
                           remember x as x' eqn:Heq; clear - Hct
                         end
              end; inversion Hct; congruence.
    Qed.

    Definition extractFhTrace : list TraceEvent -> list data :=
      flat_map (fun te => match te with
                       | FromHost _ val => cons val nil
                       | _ => nil
                       end).

    Definition abstractHiding rf pm pc mem : Prop :=
      forall trace fhTrace,
        hasTrace rf pm pc mem trace ->
        extractFhTrace trace = fhTrace ->
        forall fhTrace',
          length fhTrace = length fhTrace' ->
          exists trace',
            hasTrace rf pm pc mem trace' /\
            censorTrace trace = censorTrace trace' /\
            extractFhTrace trace' = fhTrace'.

  End AbstractTrace.

  Section KamiTrace.
    Inductive ForwardMultistep (m : Modules) : RegsT -> RegsT -> list LabelT -> Prop :=
      NilFMultistep : forall o1 o2 : RegsT,
        o1 = o2 -> ForwardMultistep m o1 o2 nil
    | FMulti : forall (o : RegsT) (a : list LabelT) (n : RegsT) (u : UpdatesT) (l : LabelT),
        Step m o u l ->
        ForwardMultistep m (FMap.M.union u o) n a ->
        ForwardMultistep m o n (l :: a).

    Lemma FMulti_Multi : forall m o n a,
        ForwardMultistep m o n a ->
        Multistep m o n (List.rev a).
    Proof.
      intros m o n a.
      move a at top.
      generalize m o n.
      clear - a.
      induction a; intros;
        match goal with
        | [ H : ForwardMultistep _ _ _ _ |- _ ] => inversion H; clear H
        end.
      - constructor.
        assumption.
      - simpl.
        subst.
        match goal with
        | [ H : ForwardMultistep _ _ _ _, IH : forall _ _ _, ForwardMultistep _ _ _ _ -> _ |- _ ] => specialize (IH _ _ _ H)
        end.
        match goal with
        | [ HM : Multistep ?m (FMap.M.union ?u ?o) ?n (List.rev ?a), HS : Step ?m ?o ?u ?l |- _ ] =>
          let a' := fresh in
          remember (List.rev a) as a'; clear - HM HS; move a' at top; generalize m u o n l HM HS; clear - a'; induction a'
        end;
          simpl;
          intros;
          match goal with
          | [ HM : Multistep _ _ _ _ |- _ ] => inversion HM
          end;
          subst;
          repeat constructor; 
          try assumption.
        eapply IHlist; eassumption.
    Qed.
    
    Lemma Multi_FMulti : forall m o n a,
        Multistep m o n a ->
        ForwardMultistep m o n (List.rev a).
    Proof.
      intros m o n a.
      move a at top.
      generalize m o n.
      clear - a.
      induction a; intros;
        match goal with
        | [ H : Multistep _ _ _ _ |- _ ] => inversion H; clear H
        end.
      - constructor.
        assumption.
      - simpl.
        subst.
        match goal with
        | [ H : Multistep _ _ _ _, IH : forall _ _ _, Multistep _ _ _ _ -> _ |- _ ] => specialize (IH _ _ _ H)
        end.
        match goal with
        | [ HM : ForwardMultistep ?m ?o ?n (List.rev ?a), HS : Step ?m ?n ?u ?l |- _ ] =>
          let a' := fresh in
          remember (List.rev a) as a'; clear - HM HS; move a' at top; generalize m u o n l HM HS; clear - a'; induction a'
        end;
          simpl;
          intros;
          match goal with
          | [ HM : ForwardMultistep _ _ _ _ |- _ ] => inversion HM
          end;
          subst;
          repeat econstructor;
          try eassumption.
        eapply IHlist; eassumption.
    Qed.

    Section TwoModules.
      Variables (ma mb: Modules).

      Hypotheses (HmaEquiv: Wf.ModEquiv type typeUT ma)
                 (HmbEquiv: Wf.ModEquiv type typeUT mb).

      Hypotheses (Hinit: FMap.DisjList (Struct.namesOf (getRegInits ma)) (Struct.namesOf (getRegInits mb)))
                 (defsDisj: FMap.DisjList (getDefs ma) (getDefs mb))
                 (callsDisj: FMap.DisjList (getCalls ma) (getCalls mb))
                 (Hvr: Wf.ValidRegsModules type (ConcatMod ma mb)).

      Definition regsA (r: RegsT) := FMap.M.restrict r (Struct.namesOf (getRegInits ma)).
      Definition regsB (r: RegsT) := FMap.M.restrict r (Struct.namesOf (getRegInits mb)).

      Lemma union_restrict : forall A (m : FMap.M.t A) d1 d2,
          FMap.M.union (FMap.M.restrict m d1) (FMap.M.restrict m d2) = FMap.M.restrict m (d1 ++ d2).
      Proof.
        intros.
        FMap.M.ext k.
        FMap.findeq.
        repeat rewrite FMap.M.restrict_find.
        repeat match goal with
               | [ |- context[if ?b then _ else _] ] => destruct b
               end;
          rewrite in_app_iff in *;
          destruct (FMap.M.find k m);
          intuition idtac.
      Qed.

      Lemma validRegsModules_forward_multistep_newregs_subset:
        forall m,
          Wf.ValidRegsModules type m ->
          forall or u ll,
            ForwardMultistep m or u ll ->
            FMap.M.KeysSubset or (Struct.namesOf (getRegInits m)) ->
            FMap.M.KeysSubset u (Struct.namesOf (getRegInits m)).
      Proof.
        induction 2; simpl; intros.
        - subst; assumption.
        - apply IHForwardMultistep.
          apply FMap.M.KeysSubset_union; auto.
          apply step_consistent in H0.
          eapply Wf.validRegsModules_stepInd_newregs_subset; eauto.
      Qed.

      Lemma forward_multistep_split:
        forall s ls ir,
          ForwardMultistep (ConcatMod ma mb) ir s ls ->
          ir = FMap.M.union (regsA ir) (regsB ir) ->
          exists sa lsa sb lsb,
            ForwardMultistep ma (regsA ir) sa lsa /\
            ForwardMultistep mb (regsB ir) sb lsb /\
            FMap.M.Disj sa sb /\ s = FMap.M.union sa sb /\ 
            CanCombineLabelSeq lsa lsb /\ WellHiddenConcatSeq ma mb lsa lsb /\
            ls = composeLabels lsa lsb.
      Proof.
        induction 1; simpl; intros; subst.
        - do 2 (eexists; exists nil); repeat split; try (econstructor; eauto; fail).
          + unfold regsA, regsB;
              eapply FMap.M.DisjList_KeysSubset_Disj with (d1:= Struct.namesOf (getRegInits ma));
              try apply FMap.M.KeysSubset_restrict;
              eauto.
          + assumption.

        - intros; subst.
          match goal with
          | [ H : ?x = ?y -> _ |- _ ] =>
            let Heq := fresh in
            assert (x = y) as Heq;
              [| specialize (H Heq)]
          end.
          + unfold regsA, regsB.
            rewrite union_restrict.
            rewrite FMap.M.restrict_KeysSubset; try reflexivity.
            apply FMap.M.KeysSubset_union.
            * match goal with
              | [ H : Step (_ ++ _)%kami _ _ _ |- _ ] =>
                let Hsubset := fresh in
                pose (Wf.validRegsModules_step_newregs_subset Hvr H) as Hsubset;
                  simpl in Hsubset;
                  unfold Struct.namesOf in *;
                  rewrite map_app in Hsubset
              end.
              assumption.
            * match goal with
              | [ H : ?r = _ |- FMap.M.KeysSubset ?r _ ] =>
                rewrite H
              end.
              unfold regsA, regsB.
              apply FMap.M.KeysSubset_union;
                eapply FMap.M.KeysSubset_SubList;
                try apply FMap.M.KeysSubset_restrict.
              -- eapply FMap.SubList_app_1.
                 apply FMap.SubList_refl.
              -- eapply FMap.SubList_app_2.
                 apply FMap.SubList_refl.
          + destruct IHForwardMultistep as [sa [lsa [sb [lsb ?]]]]; dest; subst.

            match goal with
            | [ H : Step (_ ++ _)%kami _ _ _ |- _ ] =>
              apply step_split in H
            end; try assumption.
            destruct H as [sua [sub [sla [slb ?]]]]; dest; subst.

            inv Hvr.
            unfold regsA, regsB, ModularFacts.regsA, ModularFacts.regsB in *.
            match goal with
            | [ Hvra : Wf.ValidRegsModules _ ma,
                       Hfma : ForwardMultistep ma _ _ _,
                              Hsa : Step ma _ _ _ |- _ ] =>
              pose proof (validRegsModules_forward_multistep_newregs_subset _ Hvra _ _ _ Hfma (FMap.M.KeysSubset_restrict (A := _) (m := _) (d := _)));
                pose proof (Wf.validRegsModules_step_newregs_subset Hvra Hsa)
            end.
            match goal with
            | [ Hvrb : Wf.ValidRegsModules _ mb,
                       Hfmb : ForwardMultistep mb _ _ _,
                              Hsb : Step mb _ _ _ |- _ ] =>
              pose proof (validRegsModules_forward_multistep_newregs_subset _ Hvrb _ _ _ Hfmb (FMap.M.KeysSubset_restrict (A := _) (m := _) (d := _)));
                pose proof (Wf.validRegsModules_step_newregs_subset Hvrb Hsb)
            end.

            match goal with
            | [ H : CanCombineLabel _ _ |- _ ] => inv H; dest
            end.
            exists sa, (sla :: lsa).
            exists sb, (slb :: lsb).
            repeat split; auto;

              try match goal with
                  | [ H : ForwardMultistep ?m _ _ _,
                          Hwf : Wf.ValidRegsModules _ ?m,
                                Hwf' : Wf.ValidRegsModules _ ?m'
                      |- ForwardMultistep ?m _ _ _ ] =>
                    econstructor; eauto;
                      p_equal H;
                      repeat rewrite FMap.M.restrict_union;
                      repeat (
                          (rewrite FMap.M.restrict_KeysSubset;
                           [|assumption])
                          ||
                          (rewrite FMap.M.restrict_DisjList with (d1:= Struct.namesOf (getRegInits m'));
                           [
                           | assumption
                           | try assumption;
                             apply FMap.DisjList_comm;
                             assumption]));
                      auto
                  end.
            constructor; assumption.
      Qed.

      Lemma forward_multistep_modular:
        forall lsa oa sa,
          ForwardMultistep ma oa sa lsa ->
          FMap.M.KeysSubset oa (Struct.namesOf (getRegInits ma)) ->
          forall ob sb lsb,
            ForwardMultistep mb ob sb lsb ->
            FMap.M.KeysSubset ob (Struct.namesOf (getRegInits mb)) ->
            CanCombineLabelSeq lsa lsb ->
            WellHiddenModularSeq ma mb lsa lsb ->
            ForwardMultistep (ConcatMod ma mb) (FMap.M.union oa ob)
                             (FMap.M.union sa sb) (composeLabels lsa lsb).
      Proof.
        induction lsa; simpl; intros; subst.

        - destruct lsb; [|intuition idtac].
          match goal with
          | [ Ha : ForwardMultistep ma _ _ nil,
                   Hb : ForwardMultistep mb _ _ nil |- _ ] =>
            inv Ha; inv Hb
          end; constructor; reflexivity.

        - destruct lsb as [|]; [intuition idtac|].
          shatter.
          match goal with
          | [ H : WellHiddenModularSeq _ _ _ _ |- _ ] => inv H
          end.
          pose proof Hvr as Hvr'.
          inv Hvr'.
          match goal with
          | [ Hvra : Wf.ValidRegsModules _ ma,
                     Hfma : ForwardMultistep ma _ _ _,
                            Hksa : FMap.M.KeysSubset oa _ |- _ ] =>
            pose proof (validRegsModules_forward_multistep_newregs_subset _ Hvra _ _ _ Hfma Hksa)
          end.
          match goal with
          | [ Hvrb : Wf.ValidRegsModules _ mb,
                     Hfmb : ForwardMultistep mb _ _ _,
                            Hksb : FMap.M.KeysSubset ob _ |- _ ] =>
            pose proof (validRegsModules_forward_multistep_newregs_subset _ Hvrb _ _ _ Hfmb Hksb)
          end.
          match goal with
          | [ Ha : ForwardMultistep ma _ _ _,
                   Hb : ForwardMultistep mb _ _ _ |- _ ] =>
            inv Ha; inv Hb
          end.
          match goal with
          | [ Hvra : Wf.ValidRegsModules _ ma,
                     Hsa : Step ma _ _ _ |- _ ] =>
            pose proof (Wf.validRegsModules_step_newregs_subset Hvra Hsa)
          end.
          match goal with
          | [ Hvrb : Wf.ValidRegsModules _ mb,
                     Hsb : Step mb _ _ _ |- _ ] =>
            pose proof (Wf.validRegsModules_step_newregs_subset Hvrb Hsb)
          end.

          econstructor; eauto.
          + apply step_modular; eauto.
            * eapply FMap.M.DisjList_KeysSubset_Disj; [|eassumption|eassumption]; assumption.
            * split; auto.
              eapply FMap.M.DisjList_KeysSubset_Disj; [|eassumption|eassumption]; assumption.
          + replace (FMap.M.union (FMap.M.union u u0) (FMap.M.union oa ob))
              with (FMap.M.union (FMap.M.union u oa) (FMap.M.union u0 ob))
              by (assert (FMap.M.Disj oa u0);
                  [eapply FMap.M.DisjList_KeysSubset_Disj;
                   [|eassumption|eassumption]; assumption
                  |FMap.meq]).
            * apply IHlsa; auto; apply FMap.M.KeysSubset_union; auto.
      Qed.

    End TwoModules.

    Definition censorLabel censorMeth (l : LabelT) : LabelT :=
      match l with
      | {| annot := a;
           defs := d;
           calls := c; |} =>
        {| annot := a;
           defs := FMap.M.mapi censorMeth d;
           calls := FMap.M.mapi censorMeth c; |}
      end.

    Definition censorLabelSeq censorMeth : LabelSeqT -> LabelSeqT :=
      map (censorLabel censorMeth).

    Definition extractFhMeths (cs : MethsT) : list (word 32) :=
      match FMap.M.find fhMeth cs with
      | Some (existT _
                     {| arg := Bit 0;
                        ret := Bit 32 |}
                     (argV, retV)) =>
        [retV]
      | _ => nil
      end.

    Definition extractFhLabel (l : LabelT) : list (word 32) :=
      match l with
      | {| annot := _;
           defs := _;
           calls := c; |} => extractFhMeths c
      end.

    Definition extractFhLabelSeq : LabelSeqT -> list (word 32) :=
      flat_map extractFhLabel.

    Definition censorHostMeth (n : String.string) (t : {x : SignatureT & SignT x}) : {x : SignatureT & SignT x} :=
      if String.string_dec n thMeth
      then match t with
           | existT _
                    {| arg := Bit 32;
                       ret := Bit 0 |}
                    (argV, retV) =>
             existT _
                    {| arg := Bit 32;
                       ret := Bit 0 |}
                    ($0, retV)
           | _ => t
           end
      else if String.string_dec n fhMeth
           then match t with
                | existT _
                         {| arg := Bit 0;
                            ret := Bit 32 |}
                         (argV, retV) =>
                  existT _
                         {| arg := Bit 0;
                            ret := Bit 32 |}
                         (argV, $0)
                | _ => t
                end
           else t.

    (* Security property to be applied to a complete processor++memory
       module, where the only external method calls are
       toHost/fromHost *)
    Definition kamiHiding m regs : Prop :=
      forall labels newRegs fhs,
        ForwardMultistep m regs newRegs labels ->
        extractFhLabelSeq labels = fhs ->
        forall fhs',
          length fhs = length fhs' ->
          exists labels' newRegs',
            ForwardMultistep m regs newRegs' labels' /\
            censorLabelSeq censorHostMeth labels = censorLabelSeq censorHostMeth  labels' /\
            extractFhLabelSeq labels' = fhs'.

  End KamiTrace.

  Section RtlTrace.

    Definition RtlTrace := list MethsT.

    Variable RtlSem : RtlModule -> RtlTrace -> Prop.

    Definition rtlHiding (censorMeth : String.string -> {x : SignatureT & SignT x} -> {x : SignatureT & SignT x}) m : Prop :=
      forall rt fhs,
        RtlSem m rt ->
        flat_map extractFhMeths rt = fhs ->
        forall fhs',
          length fhs = length fhs' ->
          exists rt',
            RtlSem m rt' ->
            map (FMap.M.mapi censorMeth) rt = map (FMap.M.mapi censorMeth) rt' /\
            flat_map extractFhMeths rt' = fhs'.

  End RtlTrace.
End Specification.


Section SCSimpleDefs.
  Definition rv32iRq := RqFromProc rv32iAddrSize rv32iDataBytes.
  Definition rv32iRs := RsToProc rv32iDataBytes.

  Lemma inv_rq :
    forall r : type (Struct rv32iRq),
    exists a o d,
      r = evalExpr (STRUCT { "addr" ::= #a;
                             "op" ::= #o;
                             "data" ::= #d })%kami_expr.
  Proof.
    intros.
    exists (r Fin.F1), (r (Fin.FS Fin.F1)), (r (Fin.FS (Fin.FS Fin.F1))).
    simpl.
    fin_func_tac; reflexivity.
  Qed.

  Lemma inv_rs :
    forall r : type (Struct rv32iRs),
    exists d,
      r = evalExpr (STRUCT { "data" ::= #d })%kami_expr.
  Proof.
    intros.
    exists (r Fin.F1).
    simpl.
    fin_func_tac; reflexivity.
  Qed.
End SCSimpleDefs.

Module Type SCInterface.
  Parameter p : Modules.
  Parameter m : Modules.

  Axiom pequiv : Wf.ModEquiv type typeUT p.
  Axiom mequiv : Wf.ModEquiv type typeUT m.
  Axiom reginits : FMap.DisjList (Struct.namesOf (getRegInits p))
                                 (Struct.namesOf (getRegInits m)).

  Axiom validRegs : Wf.ValidRegsModules type (p ++ m)%kami.

  Axiom defsDisj : FMap.DisjList (getDefs p) (getDefs m).
  Axiom callsDisj : FMap.DisjList (getCalls p) (getCalls m).

  Parameter SCProcRegs : regfile -> progMem -> address -> RegsT.
  Parameter SCMemRegs : memory -> RegsT.

  Parameter fhMeth : String.string.
  Parameter thMeth : String.string.
  Parameter execMeth : String.string.

  Axiom methsDistinct : fhMeth <> thMeth /\ thMeth <> execMeth /\ execMeth <> fhMeth.
  Axiom mdexec : In execMeth (getDefs m).
  Axiom pcexec : In execMeth (getCalls p).
  Axiom pcfh : In fhMeth (getCalls p).
  Axiom pndfh : ~ In fhMeth (getDefs p).
  Axiom mndfh : ~ In fhMeth (getDefs m).

  Axiom pRegs : forall rf pm pc, FMap.M.KeysSubset (SCProcRegs rf pm pc) (Struct.namesOf (getRegInits p)).
  Axiom mRegs : forall mem, FMap.M.KeysSubset (SCMemRegs mem) (Struct.namesOf (getRegInits m)).
End SCInterface.


Module SCDefs (SC : SCInterface).
  Import SC.

  Definition censorSCMeth (n : String.string) (t : {x : SignatureT & SignT x}) : {x : SignatureT & SignT x} :=
    if String.string_dec n execMeth
    then match t with
         | existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (argV, retV) =>
           let op := evalExpr (#argV!rv32iRq@."op")%kami_expr in
           existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (evalExpr (STRUCT { "addr" ::= #argV!rv32iRq@."addr";
                                      "op" ::= #argV!rv32iRq@."op";
                                      "data" ::= if op then $0 else #argV!rv32iRq@."data" })%kami_expr,
                   evalExpr (STRUCT { "data" ::= if op then #retV!rv32iRs@."data" else $0 })%kami_expr)
         | _ => t
         end
    else if String.string_dec n thMeth
         then match t with
              | existT _
                       {| arg := Bit 32;
                          ret := Bit 0 |}
                       (argV, retV) =>
                existT _
                       {| arg := Bit 32;
                          ret := Bit 0 |}
                       ($0, retV)
              | _ => t
              end
         else if String.string_dec n fhMeth
              then match t with
                   | existT _
                            {| arg := Bit 0;
                               ret := Bit 32 |}
                            (argV, retV) =>
                     existT _
                            {| arg := Bit 0;
                               ret := Bit 32 |}
                            (argV, $0)
                   | _ => t
                   end
              else t.

  Inductive SCProcMemConsistent : LabelSeqT -> memory -> Prop :=
  | SPMCnil : forall mem, SCProcMemConsistent nil mem
  | SPMCcons : forall mem l mem' ls,
      match FMap.M.find execMeth (calls l) with
      | Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (argV, retV)) =>
        let addr := evalExpr (#argV!rv32iRq@."addr")%kami_expr in
        let argval := evalExpr (#argV!rv32iRq@."data")%kami_expr in
        let retval := evalExpr (#retV!rv32iRs@."data")%kami_expr in
        if evalExpr (#argV!rv32iRq@."op")%kami_expr
        then mem' = (fun a => if weq a addr then argval else mem a)
        else mem addr = retval /\ mem' = mem
      | _ => mem' = mem
      end ->
      SCProcMemConsistent ls mem' ->
      SCProcMemConsistent (l :: ls) mem.

  Definition SCProcHiding m regs mem : Prop := 
    forall labels newRegs fhs,
      ForwardMultistep m regs newRegs labels ->
      SCProcMemConsistent labels mem ->
      extractFhLabelSeq fhMeth labels = fhs ->
      forall fhs',
        length fhs = length fhs' ->
        exists labels' newRegs',
          ForwardMultistep m regs newRegs' labels' /\
          SCProcMemConsistent labels' mem /\
          censorLabelSeq censorSCMeth labels = censorLabelSeq censorSCMeth labels' /\
          extractFhLabelSeq fhMeth labels' = fhs'.

  Definition censorSCMemDefs (n : String.string) (t : {x : SignatureT & SignT x}) : {x : SignatureT & SignT x} :=
    if String.string_dec n execMeth
    then match t with
         | existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (argV, retV) =>
           let op := evalExpr (#argV!rv32iRq@."op")%kami_expr in
           existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (evalExpr (STRUCT { "addr" ::= #argV!rv32iRq@."addr";
                                      "op" ::= #argV!rv32iRq@."op";
                                      "data" ::= if op then $0 else #argV!rv32iRq@."data" })%kami_expr,
                   evalExpr (STRUCT { "data" ::= if op then #retV!rv32iRs@."data" else $0 })%kami_expr)
         | _ => t
         end
    else t.

  Definition extractMethsWrVals (ms : MethsT) : list (word 32) :=
    match FMap.M.find execMeth ms with
    | Some (existT _
                   {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                             "op" :: Bool;
                                             "data" :: Bit 32});
                      ret := Struct (STRUCT {"data" :: Bit 32}) |}
                   (argV, retV)) =>
      if evalExpr (#argV!rv32iRq@."op")%kami_expr
      then [evalExpr (#argV!rv32iRq@."data")%kami_expr]
      else nil
    | _ => nil
    end.

  Definition extractProcWrValSeq : LabelSeqT -> list (word 32) :=
    flat_map (fun l => extractMethsWrVals (calls l)).
  
  Definition extractMemWrValSeq : LabelSeqT -> list (word 32) :=
    flat_map (fun l => extractMethsWrVals (defs l)).
  
  Inductive SCMemMemConsistent : LabelSeqT -> memory -> Prop :=
  | SMMCnil : forall mem, SCMemMemConsistent nil mem
  | SMMCcons : forall mem l mem' ls,
      match FMap.M.find execMeth (defs l) with
      | Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (argV, retV)) =>
        let addr := evalExpr (#argV!rv32iRq@."addr")%kami_expr in
        let argval := evalExpr (#argV!rv32iRq@."data")%kami_expr in
        let retval := evalExpr (#retV!rv32iRs@."data")%kami_expr in
        if evalExpr (#argV!rv32iRq@."op")%kami_expr
        then mem' = (fun a => if weq a addr then argval else mem a)
        else mem addr = retval /\ mem' = mem
      | _ => mem' = mem
      end ->
      SCMemMemConsistent ls mem' ->
      SCMemMemConsistent (l :: ls) mem.

  Definition SCMemHiding m : Prop :=
    forall mem labels newRegs,
      SCMemMemConsistent labels mem ->
      ForwardMultistep m (SCMemRegs mem) newRegs labels ->
      forall wrs,
        extractMemWrValSeq labels = wrs ->
        forall mem' wrs',
          length wrs = length wrs' ->
          exists labels' newRegs',
            ForwardMultistep m (SCMemRegs mem') newRegs' labels' /\
            SCMemMemConsistent labels' mem' /\
            censorLabelSeq censorSCMemDefs labels = censorLabelSeq censorSCMemDefs labels' /\
            extractMemWrValSeq labels' = wrs'.

  Definition SCMemSpec m : Prop :=
    forall oldRegs newRegs labels,
      ForwardMultistep m oldRegs newRegs labels ->
      forall mem,
        oldRegs = SCMemRegs mem ->
        SCMemMemConsistent labels mem.

End SCDefs.

Module Type SCModularHiding (SC : SCInterface).
  Module Defs := SCDefs SC.
  Import SC Defs.

  Axiom abstractToProcHiding :
    forall rf pm pc mem,
      abstractHiding rf pm pc mem ->
      SCProcHiding p (SCProcRegs rf pm pc) mem.

  Axiom MemHiding : SCMemHiding m.

  Axiom MemSpec : SCMemSpec m.
End SCModularHiding.

Module SCHiding (SC : SCInterface) (Hiding : SCModularHiding SC).
  Module Defs := SCDefs SC.
  Import SC Defs Hiding.

  Lemma mncfh : ~ In fhMeth (getCalls m).
    pose (callsDisj fhMeth).
    pose pcfh.
    tauto.
  Qed.

  Lemma pndex : ~ In execMeth (getDefs p).
    pose (defsDisj execMeth).
    pose mdexec.
    tauto.
  Qed.

  Lemma whc : forall lp lm rp up rm um,
      WellHiddenConcat p m lp lm ->
      Step p rp up lp ->
      Step m rm um lm ->
      FMap.M.find execMeth (Semantics.calls lp) = FMap.M.find execMeth (Semantics.defs lm).
  Proof.
    intros.
    unfold WellHiddenConcat, wellHidden in *.
    shatter.
    destruct lp as [ap dp cp]. destruct lm as [am dm cm].
    unfold mergeLabel, hide, Semantics.defs, Semantics.calls in *.
    repeat match goal with
           | [ H : FMap.M.KeysDisj _ ?x |- _ ] =>
             let Hin := fresh in
             unfold FMap.M.KeysDisj in H;
               assert (In execMeth x) as Hin by ((apply getCalls_in_1; apply pcexec) || (apply getDefs_in_2; apply mdexec));
               specialize (H execMeth Hin);
               clear Hin;
               pose proof (fun v => FMap.M.subtractKV_not_In_find (v := v) H)
           end.
    replace (FMap.M.find execMeth (FMap.M.union dp dm)) with (FMap.M.find execMeth dm) in *;
      [replace (FMap.M.find execMeth (FMap.M.union cp cm)) with (FMap.M.find execMeth cp) in *|].
    - match goal with
      | [ |- ?x = ?y ] => case_eq x; case_eq y; intros
      end;
        repeat match goal with
               | [ H : forall _, ?x = _ -> _, H' : ?x = _ |- _ ] => specialize (H _ H')
               end;
        congruence.
    - rewrite FMap.M.find_union.
      replace (FMap.M.find execMeth cm) with (None (A:={x : SignatureT & SignT x})).
      + destruct (FMap.M.find execMeth cp); reflexivity.
      + apply eq_sym.
        rewrite <- FMap.M.F.P.F.not_find_in_iff.
        assert (FMap.M.KeysDisj cm (getCalls p)); [|pose proof pcexec; auto].
        eapply RefinementFacts.DisjList_KeysSubset_KeysDisj.
        * apply FMap.DisjList_comm.
          apply callsDisj.
        * match goal with
          | [ H : Step m _ _ _ |- _ ] =>
            let Hsci := fresh in
            pose (step_calls_in mequiv H) as Hsci;
              simpl in Hsci
          end.
          assumption.
    - rewrite FMap.M.find_union.
      replace (FMap.M.find execMeth dp) with (None (A:={x : SignatureT & SignT x})); auto.
      apply eq_sym.
      rewrite <- FMap.M.F.P.F.not_find_in_iff.
      assert (FMap.M.KeysDisj dp (getDefs m)); [|pose proof mdexec; auto].
      eapply RefinementFacts.DisjList_KeysSubset_KeysDisj; try apply defsDisj.
      match goal with
      | [ H : Step p _ _ _ |- _ ] =>
        let Hsdi := fresh in
        pose (step_defs_in H) as Hsdi;
          simpl in Hsdi
      end.
      assumption.
  Qed.

  Lemma ConcatMemoryConsistent :
    forall lsm mem,
      Defs.SCMemMemConsistent lsm mem ->
      forall om nm,
        ForwardMultistep m om nm lsm ->
        forall lsp op np,
          ForwardMultistep p op np lsp ->
          WellHiddenConcatSeq p m lsp lsm ->
          Defs.SCProcMemConsistent lsp mem.
  Proof.
    induction 1; intros;
      match goal with
      | [ H : WellHiddenConcatSeq _ _ _ _ |- _ ] => inv H
      end.
    - constructor.
    - repeat match goal with
             | [ H : ForwardMultistep _ _ _ (_ :: _) |- _ ] => inv H
             end.
      econstructor; try (eapply IHSCMemMemConsistent; eauto).
      match goal with
      | [ H : match ?x with | _ => _ end |- match ?y with | _ => _ end ] => replace y with x; try eassumption
      end.
      apply eq_sym.
      eapply whc; eauto.
  Qed.

  Lemma fhCombine : forall rm um lsm,
      ForwardMultistep m rm um lsm ->
      forall rp up lsp lspm,
        ForwardMultistep p rp up lsp ->
        CanCombineLabelSeq lsp lsm ->
        lspm = composeLabels lsp lsm ->
        extractFhLabelSeq fhMeth lspm = extractFhLabelSeq fhMeth lsp.
  Proof.
    induction 1; intros; destruct lsp; subst; intuition.
    simpl.
    match goal with
    | [ H : ForwardMultistep _ _ _ (_ :: _) |- _ ] => inv H
    end.
    f_equal.
    - destruct l0.
      destruct l.
      unfold extractFhLabel, extractFhMeths.
      match goal with
      | [ |- match ?x with | _ => _ end = match ?y with | _ => _ end ] => replace x with y; auto
      end.
      unfold Semantics.calls, Semantics.defs, mergeLabel.
      rewrite FMap.M.subtractKV_find.
      repeat rewrite FMap.M.find_union.
      match goal with
      | [ H : Step p _ _ _ |- _ ] => pose (step_defs_in H); pose (step_calls_in pequiv H)
      end.
      match goal with
      | [ H : Step m _ _ _ |- _ ] => pose (step_defs_in H); pose (step_calls_in mequiv H)
      end.
      pose pndfh.
      pose mndfh.
      pose mncfh.
      unfold Semantics.calls, Semantics.defs in *.
      repeat multimatch goal with
             | [ |- context[FMap.M.find fhMeth ?mths] ] =>
               replace (FMap.M.find fhMeth mths) with (None (A := {x : SignatureT & SignT x})) by (apply eq_sym; eapply FMap.M.find_KeysSubset; eassumption)
             end.
      destruct (FMap.M.find fhMeth calls); reflexivity.
    - match goal with
      | [ H : CanCombineLabelSeq (_ :: _) (_ :: _) |- _ ] => destruct H
      end.
      eapply IHForwardMultistep; eauto.
  Qed.

  Lemma concatWrLen : forall lsp lsm,
      WellHiddenConcatSeq p m lsp lsm ->
      forall rp rp' rm rm',
        ForwardMultistep p rp rp' lsp ->
        ForwardMultistep m rm rm' lsm ->
        length (Defs.extractProcWrValSeq lsp) = length (Defs.extractMemWrValSeq lsm).
  Proof.
    induction 1; auto; intros.
    simpl.
    repeat match goal with
           | [ H : ForwardMultistep _ _ _ (_ :: _) |- _ ] => inv H
           end.
    match goal with
    | [ IH : forall _ _ _ _, ForwardMultistep p _ _ _ -> ForwardMultistep m _ _ _ -> _, Hp : ForwardMultistep p _ _ _, Hm : ForwardMultistep m _ _ _ |- _ ] => specialize (IHWellHiddenConcatSeq _ _ _ _ Hp Hm)
    end.
    repeat rewrite app_length.
    match goal with
    | [ |- ?x + _ = ?y + _ ] => replace x with y; auto
    end.
    unfold Defs.extractMethsWrVals.
    match goal with
    | [ |- length match ?x with | _ => _ end = length match ?y with | _ => _ end ] => replace x with y; auto
    end.
    eapply whc; eauto.
  Qed.

  Lemma inv_label : forall a a' c c' d d',
      {| annot := a; calls := c; defs := d |} = {| annot := a'; calls := c'; defs := d' |} -> a = a' /\ c = c' /\ d = d'.
  Proof.
    intros.
    match goal with
    | [ H : _ = _ |- _ ] => inv H
    end.
    tauto.
  Qed.

  Ltac inv_label :=
    match goal with
    | [ H : {| annot := _; calls := _; defs := _ |} = {| annot := _; calls := _; defs := _ |} |- _ ] =>
      apply inv_label in H; destruct H as [? [? ?]]
    end.

  Lemma inv_some : forall A (x y : A), Some x = Some y -> x = y.
  Proof.
    intros; congruence.
  Qed.

  Ltac inv_some :=
    match goal with
    | [ H : Some _ = Some _ |- _ ] => apply inv_some in H
    end.

  Lemma inv_pair : forall A B (x1 x2 : A) (y1 y2 : B), (x1, y1) = (x2, y2) -> x1 = x2 /\ y1 = y2.
  Proof.
    intros.
    inv H.
    tauto.
  Qed.

  Lemma inv_censor_exec_calls : forall l l',
      censorLabel Defs.censorSCMeth l = l' ->
      FMap.M.find execMeth (calls l) = FMap.M.find execMeth (calls l') \/
      exists adr op arg val,
        FMap.M.find execMeth (calls l) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr (STRUCT { "data" ::= #val })%kami_expr)) /\
        FMap.M.find execMeth (calls l') = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= if op then $0 else #arg })%kami_expr,
                      evalExpr (STRUCT { "data" ::= if op then #val else $0 })%kami_expr)).
  Proof.
    intros l l' H.
    destruct l. destruct l'.
    pose methsDistinct. shatter.
    unfold censorLabel, Defs.censorSCMeth in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f calls = calls0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find execMeth (FMap.M.mapi f calls) = FMap.M.find execMeth calls0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind
    end.
    unfold Semantics.calls, Semantics.defs in *.
    remember (FMap.M.find execMeth calls0) as e' eqn:He'.
    clear He'.
    match goal with
    | [ H : match ?x with | _ => _ end = _ |- _ ] => destruct x
    end; try solve [ left; assumption ].
    match goal with
    | [ H : Some _ = ?e |- _ ] => destruct e; [inv_some | discriminate]
    end.
    match goal with
    | [ H : (if ?x then _ else _) = _ |- _ ] => destruct x
    end; try solve [ congruence ].
    repeat match goal with
    | [ s : {_ : _ & _} |- _ ] => destruct s
    end.
    repeat (match goal with
            | [ H : match ?x with | _ => _ end _ = _ |- _ ] => destruct x
            end; try solve [ left; f_equal; assumption ]).
    match goal with
    | [ x : SignT _ |- _ ] => destruct s
    end.
    unfold arg, ret in *.
    right.
    subst.
    pose (Hrq := inv_rq t).
    pose (Hrs := inv_rs t0).
    destruct Hrq as [adr [op [dat Heqq]]].
    destruct Hrs as [val Heqs].
    exists adr, op, dat, val.
    subst.
    destruct op; tauto.
  Qed.

  Lemma inv_censor_exec_memdefs : forall l l',
      censorLabel Defs.censorSCMemDefs l = l' ->
      FMap.M.find execMeth (defs l) = FMap.M.find execMeth (defs l') \/
      exists adr op arg val,
        FMap.M.find execMeth (defs l) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr (STRUCT { "data" ::= #val })%kami_expr)) /\
        FMap.M.find execMeth (defs l') = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= if op then $0 else #arg })%kami_expr,
                      evalExpr (STRUCT { "data" ::= if op then #val else $0 })%kami_expr)).
  Proof.
    intros l l' H.
    destruct l. destruct l'.
    pose methsDistinct. shatter.
    unfold censorLabel, Defs.censorSCMemDefs in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f defs = defs0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find execMeth (FMap.M.mapi f defs) = FMap.M.find execMeth defs0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind
    end.
    unfold Semantics.calls, Semantics.defs in *.
    remember (FMap.M.find execMeth defs0) as e' eqn:He'.
    clear He'.
    match goal with
    | [ H : match ?x with | _ => _ end = _ |- _ ] => destruct x
    end; try solve [ left; assumption ].
    match goal with
    | [ H : Some _ = ?e |- _ ] => destruct e; [inv_some | discriminate]
    end.
    match goal with
    | [ H : (if ?x then _ else _) = _ |- _ ] => destruct x
    end; try solve [ congruence ].
    repeat match goal with
    | [ s : {_ : _ & _} |- _ ] => destruct s
    end.
    repeat (match goal with
            | [ H : match ?x with | _ => _ end _ = _ |- _ ] => destruct x
            end; try solve [ left; f_equal; assumption ]).
    match goal with
    | [ x : SignT _ |- _ ] => destruct s
    end.
    unfold arg, ret in *.
    right.
    subst.
    pose (Hrq := inv_rq t).
    pose (Hrs := inv_rs t0).
    destruct Hrq as [adr [op [dat Heqq]]].
    destruct Hrs as [val Heqs].
    exists adr, op, dat, val.
    subst.
    destruct op; tauto.
  Qed.

  Lemma inv_censoreq_exec_calls : forall la lb,
      censorLabel Defs.censorSCMeth la = censorLabel Defs.censorSCMeth lb ->
      FMap.M.find execMeth (calls la) = FMap.M.find execMeth (calls lb) \/
      exists adr op arg arg' val val',
        FMap.M.find execMeth (calls la) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr (STRUCT { "data" ::= #val })%kami_expr)) /\
        FMap.M.find execMeth (calls lb) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg' })%kami_expr,
                      evalExpr (STRUCT { "data" ::= #val' })%kami_expr)) /\ if op then val = val' else arg = arg'.
  Proof.
    intros la lb H.
    destruct (inv_censor_exec_calls la _ eq_refl) as [Haeq | [? [? [? [? [? [? [Ha Hac]]]]]]]];
      destruct (inv_censor_exec_calls lb _ eq_refl) as [Hbeq | [? [? [? [? [? [? [Hb Hbc]]]]]]]].
    - left.
      congruence.
    - right.
      rewrite H in Haeq.
      rewrite Hbc in Haeq.
      repeat eexists; eauto.
    - right.
      rewrite <- H in Hbeq.
      rewrite Hac in Hbeq.
      repeat eexists; eauto.
    - right.
      rewrite H in Hac.
      rewrite Hbc in Hac.
      inv_some.
      apply Semantics.sigT_eq in Hac.
      match goal with
      | [ H : (?x1, _) = (?x2, _) |- _ ] =>
        let Heqa := fresh in
        let Heqo := fresh in
        let Hdiscard := fresh in
        assert (evalExpr (#(x1)!rv32iRq@."addr")%kami_expr = evalExpr (#(x2)!rv32iRq@."addr")%kami_expr) as Heqa by (apply inv_pair in H; destruct H as [Hdiscard _]; rewrite Hdiscard; reflexivity);
          assert (evalExpr (#(x1)!rv32iRq@."op")%kami_expr = evalExpr (#(x2)!rv32iRq@."op")%kami_expr) as Heqo by (apply inv_pair in H; destruct H as [Hdiscard _]; rewrite Hdiscard; reflexivity);
          simpl in Heqa;
          simpl in Heqo
      end; subst.
      repeat eexists; eauto.
  Qed.

  Lemma censor_length_extract : forall la lb,
      censorLabel Defs.censorSCMeth la = censorLabel Defs.censorSCMeth lb ->
      length (Defs.extractMethsWrVals (calls la)) = length (Defs.extractMethsWrVals (calls lb)).
  Proof.
    intros la lb H.
    unfold Defs.extractMethsWrVals.
    destruct (inv_censoreq_exec_calls _ _ H) as [Heq | [? [? [? [? [? [? [Ha Hb]]]]]]]].
    - rewrite Heq; reflexivity.
    - rewrite Ha; rewrite Hb; simpl.
      destruct x0; reflexivity.
  Qed.

  Lemma inv_censoreq_exec_memdefs : forall la lb,
      censorLabel Defs.censorSCMemDefs la = censorLabel Defs.censorSCMemDefs lb ->
      FMap.M.find execMeth (defs la) = FMap.M.find execMeth (defs lb) \/
      exists adr op arg arg' val val',
        FMap.M.find execMeth (defs la) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr (STRUCT { "data" ::= #val })%kami_expr)) /\
        FMap.M.find execMeth (defs lb) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg' })%kami_expr,
                      evalExpr (STRUCT { "data" ::= #val' })%kami_expr)).
  Proof.
    intros la lb H.
    destruct (inv_censor_exec_memdefs la _ eq_refl) as [Haeq | [? [? [? [? [? [? [Ha Hac]]]]]]]];
      destruct (inv_censor_exec_memdefs lb _ eq_refl) as [Hbeq | [? [? [? [? [? [? [Hb Hbc]]]]]]]].
    - left.
      congruence.
    - right.
      rewrite H in Haeq.
      rewrite Hbc in Haeq.
      repeat eexists; eauto.
    - right.
      rewrite <- H in Hbeq.
      rewrite Hac in Hbeq.
      repeat eexists; eauto.
    - right.
      rewrite H in Hac.
      rewrite Hbc in Hac.
      inv_some.
      apply Semantics.sigT_eq in Hac.
      match goal with
      | [ H : (?x1, _) = (?x2, _) |- _ ] =>
        let Heqa := fresh in
        let Heqo := fresh in
        let Hdiscard := fresh in
        assert (evalExpr (#(x1)!rv32iRq@."addr")%kami_expr = evalExpr (#(x2)!rv32iRq@."addr")%kami_expr) as Heqa by (apply inv_pair in H; destruct H as [Hdiscard _]; rewrite Hdiscard; reflexivity);
          assert (evalExpr (#(x1)!rv32iRq@."op")%kami_expr = evalExpr (#(x2)!rv32iRq@."op")%kami_expr) as Heqo by (apply inv_pair in H; destruct H as [Hdiscard _]; rewrite Hdiscard; reflexivity);
          simpl in Heqa;
          simpl in Heqo
      end; subst.
      repeat eexists; eauto.
  Qed.

  Lemma censor_mem_length_extract : forall la lb,
      censorLabel Defs.censorSCMemDefs la = censorLabel Defs.censorSCMemDefs lb ->
      length (Defs.extractMethsWrVals (defs la)) = length (Defs.extractMethsWrVals (defs lb)).
  Proof.
    intros la lb H.
    unfold Defs.extractMethsWrVals.
    destruct (inv_censoreq_exec_memdefs _ _ H) as [Heq | [? [? [? [? [? [? [Ha Hb]]]]]]]].
    - rewrite Heq; reflexivity.
    - rewrite Ha; rewrite Hb; simpl.
      destruct x0; reflexivity.
  Qed.

  Lemma censorWrLen : forall lsp lsp',
      censorLabelSeq Defs.censorSCMeth lsp =
      censorLabelSeq Defs.censorSCMeth lsp' ->
      length (Defs.extractProcWrValSeq lsp) = length (Defs.extractProcWrValSeq lsp').
  Proof.
    induction lsp; intros; destruct lsp'; simpl in *; try congruence.
    match goal with
    | [ H : _ :: _ = _ :: _ |- _ ] => inv H
    end.
    repeat rewrite app_length.
    match goal with
    | [ |- ?x + _ = ?y + _ ] => replace x with y; eauto
    end.
    apply censor_length_extract; auto.
  Qed.

  Lemma combineCensor : forall lsp lsm lsp' lsm',
      CanCombineLabelSeq lsp lsm ->
      censorLabelSeq Defs.censorSCMeth lsp = censorLabelSeq Defs.censorSCMeth lsp' ->
      censorLabelSeq Defs.censorSCMemDefs lsm = censorLabelSeq Defs.censorSCMemDefs lsm' ->
      CanCombineLabelSeq lsp' lsm'.
  Proof.
    induction lsp; intros;
      destruct lsm; destruct lsp'; destruct lsm';
        simpl in *; try tauto; try congruence.
    repeat match goal with
           | [ H : _ :: _ = _ :: _ |- _ ] => inv H
           end.
    intuition idtac.
    - repeat match goal with
             | [ H : context[censorLabelSeq] |- _ ] => clear H
             | [ H : context[CanCombineLabelSeq] |- _ ] => clear H
             | [ x : list _ |- _ ] => clear x
             | [ x : LabelT |- _ ] => destruct x
             end.
      unfold CanCombineLabel, censorLabel, Semantics.annot, Semantics.calls, Semantics.defs in *.
      repeat inv_label.
      subst.
      intuition idtac;
        match goal with
        | [ Hx : _ = FMap.M.mapi _ ?x, Hy : _ = FMap.M.mapi _ ?y |- FMap.M.Disj ?x ?y ] =>
          unfold FMap.M.Disj in *;
            intros;
            erewrite <- (FMap.M.F.P.F.mapi_in_iff x);
            erewrite <- (FMap.M.F.P.F.mapi_in_iff y);
            rewrite <- Hx;
            rewrite <- Hy;
            repeat rewrite FMap.M.F.P.F.mapi_in_iff;
            auto
        end.
    - eapply IHlsp; eauto.
  Qed.

  Lemma app_inv : forall A (lh1 lt1 lh2 lt2 : list A),
      lh1 ++ lt1 = lh2 ++ lt2 ->
      length lh1 = length lh2 ->
      lh1 = lh2 /\ lt1 = lt2.
  Proof.
    induction lh1; intros; destruct lh2; simpl in *; try congruence; auto.
    inv H.
    inv H0.
    split.
    - f_equal.
      eapply proj1; apply IHlh1; eauto.
    - eapply proj2; apply IHlh1; eauto.
  Qed.

  Lemma In_subtractKV : forall A k (m1 m2 : FMap.M.t A) dec,
      FMap.M.In k (FMap.M.subtractKV dec m1 m2) <-> (FMap.M.In k m1 /\ (~ FMap.M.In k m2 \/ FMap.M.find k m1 <> FMap.M.find k m2)).
  Proof.
    intros.
    intuition idtac;
      rewrite FMap.M.F.P.F.in_find_iff in *;
      match goal with
      | [ H : context[FMap.M.subtractKV] |- _ ] => rewrite FMap.M.subtractKV_find in H
      | [ |- context[FMap.M.subtractKV] ] => rewrite FMap.M.subtractKV_find
      end;
      destruct (FMap.M.Map.find k m1);
      destruct (FMap.M.Map.find k m2);
      try congruence;
      try tauto.
    - destruct (dec a a0); try congruence.
      right.
      congruence.
    - exfalso; apply H; congruence.
    - destruct (dec a a0); congruence.
  Qed.

  Lemma In_union : forall A k (m1 m2 : FMap.M.t A),
      FMap.M.In k (FMap.M.union m1 m2) <-> (FMap.M.In k m1 \/ FMap.M.In k m2).
  Proof.
    intros; 
      intuition idtac;
      repeat rewrite FMap.M.F.P.F.in_find_iff in *;
      match goal with
      | [ H : context[FMap.M.union] |- _ ] => rewrite FMap.M.find_union in H
      | [ |- context[FMap.M.union] ] => rewrite FMap.M.find_union
      end;
      destruct (FMap.M.find k m1);
      destruct (FMap.M.find k m2);
      try congruence;
      tauto.
  Qed.

  Lemma inv_censor_exec_calls_with_mem : forall l l' mem mem',
      censorLabel Defs.censorSCMeth l = l' ->
      match FMap.M.find execMeth (calls l) with
      | Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (argV, retV)) =>
        let addr := evalExpr (#argV!rv32iRq@."addr")%kami_expr in
        let argval := evalExpr (#argV!rv32iRq@."data")%kami_expr in
        let retval := evalExpr (#retV!rv32iRs@."data")%kami_expr in
        if evalExpr (#argV!rv32iRq@."op")%kami_expr
        then mem' = (fun a => if weq a addr then argval else mem a)
        else mem addr = retval /\ mem' = mem
      | _ => mem' = mem
      end ->
      (FMap.M.find execMeth (calls l) = FMap.M.find execMeth (calls l') /\ mem' = mem) \/
      exists adr op arg arg' val val',
        FMap.M.find execMeth (calls l) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr (STRUCT { "data" ::= #val })%kami_expr)) /\
        FMap.M.find execMeth (calls l') = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg' })%kami_expr,
                      evalExpr (STRUCT { "data" ::= #val' })%kami_expr)).
  Proof.
    intros l l' mem mem' H Hmem.
    destruct l. destruct l'.
    pose methsDistinct. shatter.
    unfold censorLabel, Defs.censorSCMeth in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f calls = calls0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find execMeth (FMap.M.mapi f calls) = FMap.M.find execMeth calls0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind Hmem
    end.
    unfold Semantics.calls, Semantics.defs in *.
    remember (FMap.M.find execMeth calls0) as e' eqn:He'.
    clear He'.
    match goal with
    | [ H : match ?x with | _ => _ end = _ |- _ ] => destruct x
    end; try solve [ left; auto ].
    match goal with
    | [ H : Some _ = ?e |- _ ] => destruct e; [inv_some | discriminate]
    end.
    match goal with
    | [ H : (if ?x then _ else _) = _ |- _ ] => destruct x
    end; try solve [ congruence ].
    repeat match goal with
    | [ s : {_ : _ & _} |- _ ] => destruct s
    end.
    repeat (match goal with
            | [ H : match ?x with | _ => _ end _ = _ |- _ ] => destruct x
            end; try solve [ left; split; try f_equal; assumption ]).
    match goal with
    | [ x : SignT _ |- _ ] => destruct s
    end.
    unfold arg, ret in *.
    right.
    subst.
    pose (Hrq := inv_rq t).
    pose (Hrs := inv_rs t0).
    destruct Hrq as [adr [op [dat Heqq]]].
    destruct Hrs as [val Heqs].
    exists adr, op, dat, $0, val, $0.
    subst.
    tauto.
  Qed.

  Lemma inv_censor_exec_memdefs_with_mem : forall l l' mem mem',
      censorLabel Defs.censorSCMemDefs l = l' ->
      match FMap.M.find execMeth (defs l) with
      | Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (argV, retV)) =>
        let addr := evalExpr (#argV!rv32iRq@."addr")%kami_expr in
        let argval := evalExpr (#argV!rv32iRq@."data")%kami_expr in
        let retval := evalExpr (#retV!rv32iRs@."data")%kami_expr in
        if evalExpr (#argV!rv32iRq@."op")%kami_expr
        then mem' = (fun a => if weq a addr then argval else mem a)
        else mem addr = retval /\ mem' = mem
      | _ => mem' = mem
      end ->
      (FMap.M.find execMeth (defs l) = FMap.M.find execMeth (defs l') /\ mem' = mem) \/
      exists adr op arg arg' val val',
        FMap.M.find execMeth (defs l) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr (STRUCT { "data" ::= #val })%kami_expr)) /\
        FMap.M.find execMeth (defs l') = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg' })%kami_expr,
                      evalExpr (STRUCT { "data" ::= #val' })%kami_expr)).
  Proof.
    intros l l' mem mem' H Hmem.
    destruct l. destruct l'.
    pose methsDistinct. shatter.
    unfold censorLabel, Defs.censorSCMemDefs in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f defs = defs0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find execMeth (FMap.M.mapi f defs) = FMap.M.find execMeth defs0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind Hmem
    end.
    unfold Semantics.calls, Semantics.defs in *.
    remember (FMap.M.find execMeth defs0) as e' eqn:He'.
    clear He'.
    match goal with
    | [ H : match ?x with | _ => _ end = _ |- _ ] => destruct x
    end; try solve [ left; auto ].
    match goal with
    | [ H : Some _ = ?e |- _ ] => destruct e; [inv_some | discriminate]
    end.
    match goal with
    | [ H : (if ?x then _ else _) = _ |- _ ] => destruct x
    end; try solve [ congruence ].
    repeat match goal with
    | [ s : {_ : _ & _} |- _ ] => destruct s
    end.
    repeat (match goal with
            | [ H : match ?x with | _ => _ end _ = _ |- _ ] => destruct x
            end; try solve [ left; split; try f_equal; assumption ]).
    match goal with
    | [ x : SignT _ |- _ ] => destruct s
    end.
    unfold arg, ret in *.
    right.
    subst.
    pose (Hrq := inv_rq t).
    pose (Hrs := inv_rs t0).
    destruct Hrq as [adr [op [dat Heqq]]].
    destruct Hrs as [val Heqs].
    exists adr, op, dat, $0, val, $0.
    subst.
    tauto.
  Qed.

  Ltac conceal x :=
    let x' := fresh in
    let H := fresh in
    remember x as x' eqn:H;
    clear H.

  Ltac subst_finds :=
    repeat match goal with
           | [ H : context[FMap.M.find execMeth ?x] |- _ ] => conceal (FMap.M.find execMeth x)
           end;
    subst.

  Ltac exhibit_finds :=
    repeat match goal with
           | [ H : censorLabel ?c ?l = censorLabel ?c ?l' |- _ ] =>
             assert (FMap.M.find execMeth (calls (censorLabel c l)) = FMap.M.find execMeth (calls (censorLabel c l'))) by (rewrite H; reflexivity);
             assert (FMap.M.find execMeth (defs (censorLabel c l)) = FMap.M.find execMeth (defs (censorLabel c l'))) by (rewrite H; reflexivity);
             clear H
           end.

  Ltac inv_meth_eq :=
    match goal with
    | [ H : Some (existT _ _ (?q1, ?s1)) = Some (existT _ _ (?q2, ?s2)) |- _ ] =>
      apply inv_some in H;
      apply Semantics.sigT_eq in H;
      let Heqa := fresh in
      let Heqo := fresh in
      let Heqd := fresh in
      let Heqv := fresh in
      let Hdiscard := fresh in
      assert (evalExpr (#(q1)!rv32iRq@."addr")%kami_expr = evalExpr (#(q2)!rv32iRq@."addr")%kami_expr) as Heqa by (apply inv_pair in H; destruct H as [Hdiscard _]; rewrite Hdiscard; reflexivity);
      assert (evalExpr (#(q1)!rv32iRq@."op")%kami_expr = evalExpr (#(q2)!rv32iRq@."op")%kami_expr) as Heqo by (apply inv_pair in H; destruct H as [Hdiscard _]; rewrite Hdiscard; reflexivity);
      assert (evalExpr (#(q1)!rv32iRq@."data")%kami_expr = evalExpr (#(q2)!rv32iRq@."data")%kami_expr) as Heqd by (apply inv_pair in H; destruct H as [Hdiscard _]; rewrite Hdiscard; reflexivity);
      assert (evalExpr (#(s1)!rv32iRs@."data")%kami_expr = evalExpr (#(s2)!rv32iRs@."data")%kami_expr) as Heqv by (apply inv_pair in H; destruct H as [_ Hdiscard]; rewrite Hdiscard; reflexivity);
      simpl in Heqa;
      simpl in Heqo;
      simpl in Heqd;
      simpl in Heqv;
      subst;
      clear H
    end.

  Inductive SCProcMemCanonical : LabelSeqT -> memory -> Prop :=
  | SPMCnil : forall mem, SCProcMemCanonical nil mem
  | SPMCcons : forall mem l mem' ls,
      match FMap.M.find execMeth (calls l) with
      | Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (argV, retV)) =>
        let op := evalExpr (#argV!rv32iRq@."op")%kami_expr in
        let argval := evalExpr (#argV!rv32iRq@."data")%kami_expr in
        let retval := evalExpr (#retV!rv32iRs@."data")%kami_expr in
        if op then retval = $0 else argval = $0
      | _ => mem' = mem
      end ->
      SCProcMemCanonical ls mem' ->
      SCProcMemCanonical (l :: ls) mem.



  Lemma concatCensor : forall lsp lsm,
      WellHiddenConcatSeq p m lsp lsm ->
      forall rp up rm um lsp' lsm' mem,
        ForwardMultistep p rp up lsp ->
        ForwardMultistep m rm um lsm ->
        censorLabelSeq Defs.censorSCMeth lsp = censorLabelSeq Defs.censorSCMeth lsp' ->
        censorLabelSeq Defs.censorSCMemDefs lsm = censorLabelSeq Defs.censorSCMemDefs lsm' ->
        Defs.extractProcWrValSeq lsp' = Defs.extractMemWrValSeq lsm' ->
        Defs.SCProcMemConsistent lsp' mem ->
        Defs.SCMemMemConsistent lsm' mem ->
        WellHiddenConcatSeq p m lsp' lsm'.
  Proof.
    induction 1;
      intros;
      destruct lsp';
      destruct lsm';
      simpl in *;
      try congruence;
      try solve [ constructor ].
    repeat match goal with
           | [ H : context[_ :: _] |- _ ] => inv H
           end.
    match goal with
    | [ H : WellHiddenConcat _ _ _ _ |- _ ] =>
      let H' := fresh in
      let H'' := fresh in
      remember H as H' eqn:H'';
        clear H'';
        eapply whc in H;
        eauto
    end.
    match goal with
    | [ H : ?x ++ ?xs = ?y ++ ?ys |- _ ] => apply app_inv in H; intuition idtac
    end.
    - constructor.
      + eapply IHWellHiddenConcatSeq; eauto.
        match goal with
        | [ H : Defs.SCMemMemConsistent lsm' ?mem |- Defs.SCMemMemConsistent lsm' ?mem' ] => replace mem' with mem; auto
        end.
        exhibit_finds;
          unfold Defs.extractMethsWrVals in *;
          destruct (inv_censor_exec_calls_with_mem _ _ _ _ eq_refl H9);
          destruct (inv_censor_exec_memdefs_with_mem _ _ _ _ eq_refl H10);
          destruct (inv_censor_exec_calls la _ eq_refl);
          destruct (inv_censor_exec_memdefs lb _ eq_refl);
          shatter;
          subst_finds;
          repeat inv_meth_eq;
          simpl in *;
          try match goal with
          | [ H : (if ?x then _ else _) = (if ?x then _ else _) |- _ ] => destruct x; try inv H; subst
          end;
          shatter;
          try congruence.
(*        match goal with
        | [ H : _ |- _ ] => destruct (inv_censoreq_exec_calls _ _ H) as [Hceq | [? [? [? [? [? [? [Hca Hcb]]]]]]]]
        end;
          match goal with
          | [ H : _ |- _ ] => destruct (inv_censoreq_exec_memdefs _ _ H) as [Hdeq | [? [? [? [? [? [? [Hda Hdb]]]]]]]]
          end.
        * *)
        
      + unfold WellHiddenConcat, wellHidden in *.
        shatter.
        split; eapply RefinementFacts.DomainSubset_KeysDisj; eauto.
        * unfold FMap.M.DomainSubset.
          intros.
          destruct la. destruct lb. destruct l. destruct l0.
          unfold hide, mergeLabel, Semantics.calls, Semantics.defs in *.
          rewrite In_subtractKV in *; shatter; split.
          -- match goal with
             | [ H : FMap.M.In k (FMap.M.union _ _) |- _ ] => rewrite In_union in *; destruct H
             end;
               match goal with
               | [ Hin : FMap.M.In k ?d, Hcen : _ = censorLabel _ {| annot := _; defs := ?d; calls := _ |} |- _ ] =>
                 unfold censorLabel in Hcen;
                   inv_label;
                   erewrite <- FMap.M.F.P.F.mapi_in_iff in Hin;
                   match goal with
                   | [ Heq : _ |- _ ] => rewrite <- Heq in Hin
                   end;
                   rewrite FMap.M.F.P.F.mapi_in_iff in Hin;
                   tauto
               end.
          -- intuition idtac.
             ++ left; intros;
                  match goal with
                  | [ H : _ -> False |- _ ] => apply H
                  end.
                match goal with
                | [ H : FMap.M.In k (FMap.M.union _ _) |- _ ] => rewrite In_union in *; destruct H
                end;
                  match goal with
                  | [ Hin : FMap.M.In k ?c, Hcen : censorLabel _ {| annot := _; defs := _; calls := ?c |} = _ |- _ ] =>
                    unfold censorLabel in Hcen;
                      inv_label;
                      erewrite <- FMap.M.F.P.F.mapi_in_iff in Hin;
                      match goal with
                      | [ Heq : _ |- _ ] => rewrite -> Heq in Hin
                      end;
                      rewrite FMap.M.F.P.F.mapi_in_iff in Hin;
                      tauto
                  end.
             ++ right; intros;
                  match goal with
                  | [ H : _ -> False |- _ ] => apply H; clear H
                  end.
                destruct (String.string_dec k execMeth).
                ** subst.
                   repeat rewrite FMap.M.find_union.
                   replace (FMap.M.find execMeth defs1) with (None (A := {x : SignatureT & SignT x}));
                     [replace (FMap.M.find execMeth calls2) with (None (A := {x : SignatureT & SignT x}));
                      [replace (FMap.M.find execMeth calls1) with (FMap.M.find execMeth defs2); [destruct (FMap.M.find execMeth defs2); auto|]|]|].
                           Ltac meth_equal :=
                             match goal with
                             | [ |- Some (existT _ _ (evalExpr STRUCT {"addr" ::= #(?a); "op" ::= #(?o); "data" ::= #(?d)}%kami_expr, evalExpr STRUCT {"data" ::= #(?v)}%kami_expr)) = Some (existT _ _ (evalExpr STRUCT {"addr" ::= #(?a'); "op" ::= #(?o'); "data" ::= #(?d')}%kami_expr, evalExpr STRUCT {"data" ::= #(?v')}%kami_expr)) ] => replace a with a'; [replace o with o'; [replace d with d'; [replace v with v'; [reflexivity|]|]|]|]
                             end; try reflexivity.
                   --- unfold Defs.extractMethsWrVals in *;
                         destruct (inv_censoreq_exec_calls _ _ H6) as [Hceq | [? [? [? [? [? [? [Hca Hcb]]]]]]]];
                         destruct (inv_censoreq_exec_memdefs _ _ H7) as [Hdeq | [? [? [? [? [? [? [Hda Hdb]]]]]]]];
                         unfold Semantics.calls, Semantics.defs in *;
                         shatter;
                         exhibit_finds;
                         subst_finds;
                         try meth_equal.
                       +++ congruence.
                       +++ simpl in *.

                         repeat inv_meth_eq;
                         simpl in *;
                         try match goal with
                             | [ H : (if ?x then _ else _) = (if ?x then _ else _) |- _ ] => destruct x; try inv H; subst
                             end;
                         shatter;
                         try congruence.
                       +++ 
                       +++ congruence.
                       +++ rewrite Hceq in H0.
                           rewrite Hda in H0.
                           unfold Defs.extractMethsWrVals in H2.
                           rewrite Hdb in H2.
                           rewrite H0 in H2.
                           simpl in H2.
                           destruct x0; subst.
(*                       clear - H
                     unfold Defs.extract
                     rewrite Hdb
                   match goal with
                   | [ H : censorLabel Defs.censorSCMeth 
                   destruct (inv_censor_exec_calls {| annot : _ eq_refl) as [Haeq | [? [? [? [? [? [? [Ha Hac]]]]]]]];
      destruct (inv_censor_exec_calls lb _ eq_refl) as [Hbeq | [? [? [? [? [? [? [Hb Hbc]]]]]]]].

                   
                repeat rewrite FMap.M.find_union in H10.
                pose (FMap.M.find_KeysSubset _ (step_defs_in H11) pndex) as Hnfind.
                unfold Semantics.defs in *.
                rewrite Hnfind in H10.
                
          -- clear - H6 H5.
             unfold censorLabel in H6.
             inv_label.
             erewrite <- FMap.M.F.P.F.mapi_in_iff in H5.
             rewrite <- H1 in H5.
             rewrite FMap.M.F.P.F.mapi_in_iff in H5.
             tauto.
          -- clear - H7 H5.
             unfold censorLabel in H5.
             inv_label
        
            
    - replace (length (Defs.extractMethsWrVals (calls l))) with (length (Defs.extractMethsWrVals (calls la))) by (apply censor_length_extract; auto).
      replace (length (Defs.extractMethsWrVals (defs l0))) with (length (Defs.extractMethsWrVals (defs lb))) by (apply censor_mem_length_extract; auto).
      match goal with
      | [ H : FMap.M.find _ _ = FMap.M.find _ _ |- _ ] =>
        unfold Defs.extractMethsWrVals; rewrite H; reflexivity
      end.*)
  Admitted.

  Lemma composeCensor : forall lsp lsm lsp' lsm',
      censorLabelSeq Defs.censorSCMeth lsp = censorLabelSeq Defs.censorSCMeth lsp' ->
      censorLabelSeq Defs.censorSCMemDefs lsm = censorLabelSeq Defs.censorSCMemDefs lsm' ->
      censorLabelSeq (censorHostMeth fhMeth thMeth) (composeLabels lsp lsm) =
      censorLabelSeq (censorHostMeth fhMeth thMeth) (composeLabels lsp' lsm').
  Proof.
  Admitted.

  Theorem abstractToSCHiding : forall rf pm pc mem,
      abstractHiding rf pm pc mem ->
      kamiHiding fhMeth thMeth (p ++ m)%kami (FMap.M.union (SCProcRegs rf pm pc) (SCMemRegs mem)).
  Proof.
    unfold kamiHiding.
    intros.
    assert (regsA p (FMap.M.union (SCProcRegs rf pm pc) (SCMemRegs mem)) = SCProcRegs rf pm pc) as Hrp by
        (unfold regsA;
         rewrite FMap.M.restrict_union;
         rewrite FMap.M.restrict_KeysSubset; [|apply pRegs];
         erewrite FMap.M.restrict_DisjList; [FMap.findeq|apply mRegs|];
         apply FMap.DisjList_comm;
         apply reginits).
    assert (regsB m (FMap.M.union (SCProcRegs rf pm pc) (SCMemRegs mem)) = SCMemRegs mem) as Hrm by
        (unfold regsB;
         rewrite FMap.M.restrict_union;
         erewrite FMap.M.restrict_DisjList; [|apply pRegs|apply reginits];
         rewrite FMap.M.restrict_KeysSubset; [FMap.findeq|apply mRegs]).
    match goal with
    | [ H : ForwardMultistep (p ++ m)%kami _ _ _ |- _ ] =>
      apply (forward_multistep_split p m pequiv mequiv reginits defsDisj callsDisj validRegs) in H;
        try congruence;
        destruct H as [sp [lsp [sm [lsm [Hfmp [Hfmm [Hdisj [Hnr [Hcomb [Hconc Hcomp]]]]]]]]]]
    end.
    rewrite Hrp, Hrm in *.
    assert (Defs.SCProcMemConsistent lsp mem) as Hpmc by (eapply ConcatMemoryConsistent; eauto; eapply MemSpec; eauto).
    assert (extractFhLabelSeq fhMeth lsp = fhs) as Hfh by (erewrite <- fhCombine; eauto).
    match goal with
    | [ Hah : abstractHiding _ _ _ _,
              Hlen : length _ = length _ |- _ ] =>
      let Hph := fresh in
      pose (abstractToProcHiding _ _ _ _ Hah) as Hph;
        unfold Defs.SCProcHiding in Hph;
        specialize (Hph _ _ fhs Hfmp Hpmc Hfh _ Hlen);
        destruct Hph as [lsp' [sp' [Hfmp' [Hpmc' [Hpcensor Hfh']]]]]
    end.
    assert (length (Defs.extractMemWrValSeq lsm) = length (Defs.extractProcWrValSeq lsp')) as Hlen by (erewrite <- censorWrLen by eassumption; apply eq_sym; eapply concatWrLen; eassumption).
    pose (MemHiding _ _ _ (MemSpec _ _ _ Hfmm _ eq_refl) Hfmm _ eq_refl mem (Defs.extractProcWrValSeq lsp') Hlen) as Hmh.
    destruct Hmh as [lsm' [sm' [Hfmm' [Hmmc' [Hmcensor Hwrval]]]]].
    exists (composeLabels lsp' lsm'), (FMap.M.union sp' sm').
    intuition idtac.
    - apply (forward_multistep_modular p m pequiv mequiv reginits defsDisj callsDisj validRegs); auto.
      + apply pRegs.
      + apply mRegs.
      + eapply combineCensor; eauto.
      + apply wellHidden_concat_modular_seq.
        eapply concatCensor; eauto.
    - subst.
      apply composeCensor; auto.
    - erewrite fhCombine; eauto.
      eapply combineCensor; eauto.
  Qed.

End SCHiding.

Module SCSingle <: SCInterface.
  Definition p :=
    procInst rv32iGetOptype
             rv32iGetLdDst rv32iGetLdAddr rv32iGetLdSrc rv32iCalcLdAddr
             rv32iGetStAddr rv32iGetStSrc rv32iCalcStAddr rv32iGetStVSrc
             rv32iGetSrc1 rv32iGetSrc2 rv32iGetDst
             rv32iExec rv32iNextPc rv32iAlignPc rv32iAlignAddr
             (procInitDefault  _ _ _ _).

  Definition rv32iMemInstExec {ty} : ty (Struct rv32iRq) -> ActionT ty (Struct rv32iRs) :=
    fun (a: ty (Struct rv32iRq)) =>
      (If !#a!rv32iRq@."op" then (* load *)
         Read memv <- "mem";
         LET ldval <- #memv@[#a!rv32iRq@."addr"];
         Ret (STRUCT { "data" ::= #ldval } :: Struct rv32iRs)
       else (* store *)
         Read memv <- "mem";
         Write "mem" <- #memv@[ #a!rv32iRq@."addr" <- #a!rv32iRq@."data" ];
         Ret (STRUCT { "data" ::= $$Default } :: Struct rv32iRs)
       as na;
       Ret #na)%kami_action.

  Definition m := MODULE {
    Register "mem" : Vector (MemTypes.Data rv32iDataBytes) rv32iAddrSize <- Default

    with Method "exec" (a : Struct rv32iRq) : Struct rv32iRs := (rv32iMemInstExec a)
  }.

  Theorem pequiv : Wf.ModEquiv type typeUT p.
  Proof.
    kequiv.
  Qed.

  Theorem mequiv : Wf.ModEquiv type typeUT m.
  Proof.
    kequiv.
  Qed.

  Theorem reginits : FMap.DisjList (Struct.namesOf (getRegInits p))
                                   (Struct.namesOf (getRegInits m)).
  Proof.
    kdisj_regs.
  Qed.    

  Theorem validRegs : Wf.ValidRegsModules type (p ++ m)%kami.
  Proof.
    kvr.
  Qed.

  Theorem defsDisj : FMap.DisjList (getDefs p) (getDefs m).
  Proof.
    kdisj_dms.
  Qed.

  Theorem callsDisj : FMap.DisjList (getCalls p) (getCalls m).
  Proof.
    kdisj_cms.
  Qed.

  Definition SCProcRegs rf pm pc : RegsT :=
    FMap.M.add "rf" (existT _ (SyntaxKind (Vector (Bit 32) 5)) rf)
               (FMap.M.add "pgm" (existT _ (SyntaxKind (Vector (Bit 32) 8)) pm)
                           (FMap.M.add "pc" (existT _ (SyntaxKind (Bit 16)) pc)
                                                   (FMap.M.empty _))).

  Definition SCMemRegs mem : RegsT :=
    FMap.M.add "mem" (existT _ (SyntaxKind (Vector (Bit 32) 16)) mem)
               (FMap.M.empty _).

  Definition fhMeth := "fromHost".
  Definition thMeth := "toHost".
  Definition execMeth := "exec".

  Theorem mdexec : In execMeth (getDefs m).
  Proof.
    simpl; auto.
  Qed.

  Theorem pcexec : In execMeth (getCalls p).
  Proof.
    simpl; auto.
  Qed.

  Theorem pfh : In fhMeth (getCalls p).
  Proof.
    simpl; auto.
  Qed.

  Theorem pcfh : In fhMeth (getCalls p).
  Proof.
    simpl; auto.
  Qed.

  Theorem pndfh : ~ In fhMeth (getDefs p).
  Proof.
    tauto.
  Qed.

  Theorem mndfh : ~ In fhMeth (getDefs m).
  Proof.
    simpl.
    intuition idtac.
    discriminate.
  Qed.

  Theorem pRegs : forall rf pm pc, FMap.M.KeysSubset (SCProcRegs rf pm pc) (Struct.namesOf (getRegInits p)).
  Proof.
    intros; simpl.
    unfold SCProcRegs, FMap.M.KeysSubset.
    intro.
    repeat rewrite FMap.M.F.P.F.add_in_iff.
    rewrite FMap.M.F.P.F.empty_in_iff.
    intuition idtac; subst; simpl; tauto.
  Qed.
    
  Theorem mRegs : forall mem, FMap.M.KeysSubset (SCMemRegs mem) (Struct.namesOf (getRegInits m)).
  Proof.
    intros; simpl.
    unfold SCMemRegs, FMap.M.KeysSubset.
    intro.
    repeat rewrite FMap.M.F.P.F.add_in_iff.
    rewrite FMap.M.F.P.F.empty_in_iff.
    intuition idtac; subst; simpl; tauto.
  Qed.

End SCSingle.

Module SCSingleModularHiding <: (SCModularHiding SCSingle).
  Module Defs := SCDefs SCSingle.
  Import SCSingle Defs.

  Lemma SCProcRegs_find_rf : forall rf pm pc rf',
      FMap.M.find (elt:={x : FullKind & fullType type x}) "rf"
                  (SCProcRegs rf pm pc) =
      Some
        (existT (fullType type) (SyntaxKind (Vector (Bit 32) 5)) rf') -> rf = rf'.
  Proof.
    intros.
    unfold SCProcRegs in *.
    FMap.findeq.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1).
  Qed.

  Lemma SCProcRegs_find_pm : forall rf pm pc pm',
      FMap.M.find (elt:={x : FullKind & fullType type x}) "pgm"
                  (SCProcRegs rf pm pc) =
      Some
        (existT (fullType type) (SyntaxKind (Vector (Bit 32) 8)) pm') -> pm = pm'.
  Proof.
    intros.
    unfold SCProcRegs in *.
    FMap.findeq.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1).
  Qed.

  Lemma SCProcRegs_find_pc : forall rf pm pc pc',
      FMap.M.find (elt:={x : FullKind & fullType type x}) "pc"
                  (SCProcRegs rf pm pc) =
      Some
        (existT (fullType type) (SyntaxKind (Bit 16)) pc') -> pc = pc'.
  Proof.
    intros.
    unfold SCProcRegs in *.
    FMap.findeq.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1).
  Qed.

  Ltac SCProcRegs_find :=
    repeat match goal with
           | [ H : FMap.M.find "rf" (SCProcRegs ?rf _ _) = Some (existT _ _ ?rf') |- _ ] => assert (rf = rf') by (eapply SCProcRegs_find_rf; eassumption); subst; clear H
           | [ H : FMap.M.find "pgm" (SCProcRegs _ ?pm _) = Some (existT _ _ ?pm') |- _ ] => assert (pm = pm') by (eapply SCProcRegs_find_pm; eassumption); subst; clear H
           | [ H : FMap.M.find "pc" (SCProcRegs _ _ ?pc) = Some (existT _ _ ?pc') |- _ ] => assert (pc = pc') by (eapply SCProcRegs_find_pc; eassumption); subst; clear H
           end.

  Definition callsToTraceEvent (c : MethsT) : option TraceEvent :=
    match FMap.M.find fhMeth c with
    | Some (existT _
                   {| arg := Bit 0;
                      ret := Bit 32 |}
                   (argV, retV)) =>
      Some (FromHost $0 retV)
    | None =>
      match FMap.M.find thMeth c with
      | Some (existT _
                     {| arg := Bit 32;
                        ret := Bit 0 |}
                     (argV, retV)) =>
        Some (ToHost $0 argV)
      | None =>
        match FMap.M.find execMeth c with
        | Some (existT _
                       {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                                 "op" :: Bool;
                                                 "data" :: Bit 32});
                          ret := Struct (STRUCT {"data" :: Bit 32}) |}
                       (argV, retV)) =>
          let addr := evalExpr (#argV!rv32iRq@."addr")%kami_expr in
          let argval := evalExpr (#argV!rv32iRq@."data")%kami_expr in
          let retval := evalExpr (#retV!rv32iRs@."data")%kami_expr in
          if evalExpr (#argV!rv32iRq@."op")%kami_expr
          then Some (Wr $0 addr argval)
          else Some (Rd $0 addr retval)
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end.

  Definition labelToTraceEvent (l : LabelT) : option TraceEvent :=
    match l with
    | {| annot := _;
         defs := _;
         calls := c; |} => callsToTraceEvent c
    end.

  Inductive relatedTrace : list TraceEvent -> LabelSeqT -> Prop :=
  | RtNil : relatedTrace nil nil
  | RtNop : forall pc lbl trace' ls',
      annot lbl = None \/ annot lbl = Some None ->
      calls lbl = FMap.M.empty _ ->
      relatedTrace trace' ls' ->
      relatedTrace (Nop pc :: trace') (lbl :: ls')
  | RtRd : forall pc addr val lbl trace' ls',
      labelToTraceEvent lbl = Some (Rd $0 addr val) ->
      relatedTrace trace' ls' ->
      relatedTrace (Rd pc addr val :: trace') (lbl :: ls')
  | RtWr : forall pc addr val lbl trace' ls',
      labelToTraceEvent lbl = Some (Wr $0 addr val) ->
      relatedTrace trace' ls' ->
      relatedTrace (Wr pc addr val :: trace') (lbl :: ls')
  | RtTh : forall pc val lbl trace' ls',
      labelToTraceEvent lbl = Some (ToHost $0 val) ->
      relatedTrace trace' ls' ->
      relatedTrace (ToHost pc val :: trace') (lbl :: ls')
  | RtFh : forall pc val lbl trace' ls',
      labelToTraceEvent lbl = Some (FromHost $0 val) ->
      relatedTrace trace' ls' ->
      relatedTrace (FromHost pc val :: trace') (lbl :: ls')
  | RtBranch : forall pc taken lbl trace' ls',
      annot lbl <> None ->
      annot lbl <> Some None ->
      labelToTraceEvent lbl = None ->
      relatedTrace trace' ls' ->
      relatedTrace (Branch pc taken :: trace') (lbl :: ls')
  | RtNm : forall pc lbl trace' ls',
      annot lbl <> None ->
      annot lbl <> Some None ->
      labelToTraceEvent lbl = None ->
      relatedTrace trace' ls' ->
      relatedTrace (Nm pc :: trace') (lbl :: ls')
  | RtRdZ : forall pc addr lbl trace' ls',
      annot lbl <> None ->
      annot lbl <> Some None ->
      labelToTraceEvent lbl = None ->
      relatedTrace trace' ls' ->
      relatedTrace (RdZ pc addr :: trace') (lbl :: ls').

  Lemma relatedFhTrace :
    forall trace ls,
      relatedTrace trace ls -> extractFhTrace trace = extractFhLabelSeq fhMeth ls.
  Proof.
    induction 1; try eauto;
      simpl;
      match goal with
      | [ H : ?a = ?b |- ?a = ?c ++ ?b ] => assert (Hnil : c = nil); [ idtac | rewrite Hnil; simpl; assumption ]
      | [ H : ?a = ?b |- ?v :: ?a = ?c ++ ?b ] => assert (Hval : c = cons v nil); [ idtac | rewrite Hval; simpl; rewrite H; reflexivity ]
      end;
      match goal with
      | [ |- extractFhLabel fhMeth ?l = _ ] => destruct l
      end;
      unfold labelToTraceEvent, callsToTraceEvent in *;
      unfold extractFhLabel, extractFhMeths;
      repeat (match goal with
              | [ H : match ?x with | _ => _ end = _ |- _ ] => destruct x
              | [ H : match ?x with | _ => _ end _ = _ |- _ ] => destruct x
              | [ s : {_ : _ & _} |- _ ] => destruct s
              | [ x : SignatureT |- _ ] => destruct x
              end; try congruence; try discriminate).
    - simpl in *.
      subst.
      FMap.findeq.
    - match goal with
      | [ H : Some _ = Some _ |- _ ] => inversion H
      end.
      reflexivity.
  Qed.

  (* A [subst] tactic that doesn't unfold definitions *)
  Ltac opaque_subst :=
    repeat match goal with
           | [ Heq : ?x = ?y |- _ ] => ((tryif unfold x then fail else subst x) || (tryif unfold y then fail else subst y))
           end.

  Lemma SCProcSubsteps :
    forall o (ss : Substeps p o),
      SubstepsInd p o (foldSSUpds ss) (foldSSLabel ss) ->
      (((foldSSLabel ss) = {| annot := None; defs := FMap.M.empty _; calls := FMap.M.empty _ |}
        \/ (foldSSLabel ss) = {| annot := Some None; defs := FMap.M.empty _; calls := FMap.M.empty _ |})
       /\ (foldSSUpds ss) = FMap.M.empty _)
      \/ (exists k a u cs,
            In (k :: a)%struct (getRules p)
            /\ SemAction o (a type) u cs WO
            /\ (foldSSLabel ss) = {| annot := Some (Some k); defs := FMap.M.empty _; calls := cs |}
            /\ (foldSSUpds ss) = u).
  Proof.
    intros.
    match goal with
    | [ H : SubstepsInd _ _ _ _ |- _ ] => induction H
    end.
    - tauto.
    - intuition idtac;
        simpl;
        shatter;
        intuition idtac;
        subst;
        match goal with
        | [ H : Substep _ _ _ _ _ |- _ ] => destruct H
        end;
        try tauto;
        match goal with
        | [ HCCU : CanCombineUUL _ {| annot := Some _; defs := FMap.M.empty _; calls := _ |} _ _ (Rle _) |- _ ] =>
          unfold CanCombineUUL in HCCU;
            simpl in HCCU;
            tauto
        | [ HIn : In _ (getDefsBodies p) |- _ ] =>
          simpl in HIn;
            tauto
        | [ HIR : In (?k :: ?a)%struct _, HA : SemAction _ _ ?u ?cs _ |- _ ] =>
          right;
            exists k, a, u, cs;
            simpl in HIR;
            intuition idtac;
            simpl;
            FMap.findeq
        end.
  Qed.

  Definition canonicalizeLabel (l : LabelT) : LabelT :=
    match l with
    | {| annot := None;
        defs := d;
        calls := c |} => {| annot := Some None; defs := d; calls := c |}
    | _ => l
    end.

  Definition canonicalize := map canonicalizeLabel.

  Lemma decanon : forall m o n mem f l0 l1,
      ForwardMultistep m o n l1 ->
      SCProcMemConsistent l1 mem ->
      censorLabelSeq censorSCMeth (canonicalize l0) = censorLabelSeq censorSCMeth (canonicalize l1) ->
      extractFhLabelSeq fhMeth l1 = f ->
      exists l1',
        ForwardMultistep m o n l1' /\
        SCProcMemConsistent l1' mem /\
        censorLabelSeq censorSCMeth l0 = censorLabelSeq censorSCMeth l1' /\
        extractFhLabelSeq fhMeth l1' = f.
  Proof.
    intros m o n mem f l0 l1 Hfm.
    move Hfm at top.
    generalize mem, f, l0.
    clear mem f l0.
    induction Hfm; intros; simpl in *; subst.
    - exists nil; intuition idtac.
      + constructor; congruence.
      + destruct l0; simpl in *; try congruence.
    - destruct l0; simpl in *; try congruence.
      match goal with
      | [ H : _ :: _ = _ :: _ |- _ ] => inv H
      end.
      match goal with
      | [ H : SCProcMemConsistent _ _ |- _ ] => inv H
      end.
      match goal with
      | [ Hc : censorLabelSeq censorSCMeth _ = censorLabelSeq censorSCMeth _,
               Hm : SCProcMemConsistent _ _,
                    IHHfm : forall _ _ _, SCProcMemConsistent _ _ -> _ = _ -> _ |- _ ] =>
        specialize (IHHfm _ _ _ Hm Hc eq_refl)
      end.
      shatter.
      match goal with
      | [ H : censorLabel censorSCMeth (canonicalizeLabel ?label) = censorLabel censorSCMeth (canonicalizeLabel ?label') |- _ ] =>
        destruct label as [[[|]|] ? ?];
          destruct label' as [[[|]|] ? ?];
          simpl in H;
          inversion H;
          subst
      end;
        match goal with
        | [ |- exists _, _ /\ _ /\ _ {| annot := ?a; defs := _; calls := _ |} :: _ = _ /\ _ = _ {| annot := _; defs := ?d; calls := ?c |} ++ _ ] =>
          exists ({| annot := a; defs := d; calls := c |} :: x);
            intuition idtac;
            try solve [ simpl; f_equal; congruence ];
            econstructor;
            try eassumption;
            (apply step_rule_annot_1 || eapply step_rule_annot_2);
            assumption
        end.
  Qed.


  Ltac evex H := unfold evalExpr in H; fold evalExpr in H.
  Ltac evexg := unfold evalExpr; fold evalExpr.

  Ltac boolex :=
    try match goal with
        | [ H : evalUniBool Neg _ = _ |- _ ] =>
          unfold evalUniBool in H;
          rewrite Bool.negb_true_iff in H
        end;
    match goal with
    | [ H : (if ?x then true else false) = _ |- _ ] =>
      destruct x; try discriminate
    end.

  Ltac evbool_auto :=
    match goal with
    | [ H : _ = true |- _ ] => evex H; boolex
    end.

  Ltac evbool_auto_rep :=
    repeat match goal with
           | [ H : _ = true |- _ ] => evex H; boolex; clear H
           end.

  Ltac simplify_match :=
    repeat match goal with
           | [ |- context[match ?x with _ => _ end] ] =>
             let x' := eval hnf in x in change x with x'; cbv beta iota
           end.

  Ltac simplify_match_hyp :=
    repeat multimatch goal with
           | [ H : context[match ?x with _ => _ end] |- _ ] =>
             let x' := eval hnf in x in change x with x' in H; cbv beta iota
           end.

  Lemma expr_bool_equality : forall n (x : (Bit n) @ (type)) (y : word n),
      evalExpr (x == $$ (y))%kami_expr = true -> evalExpr x = y.
  Proof.
    intros.
    simpl in *.
    destruct (weq (evalExpr x) y); (assumption || discriminate).
  Qed.

  Lemma expr_bool_unequality : forall n (x : (Bit n) @ (type)) (y : word n),
      evalExpr (!%kami_expr (x == $$ (y))%kami_expr) = true -> evalExpr x <> y.
  Proof.
    intros.
    simpl in *.
    destruct (weq (evalExpr x) y); (assumption || discriminate).
  Qed.

  Ltac expr_equalities :=
    repeat match goal with
           | [ H : evalExpr (_ == $$(_))%kami_expr = true |- _ ] => apply expr_bool_equality in H
           | [ H : evalExpr (!%kami_expr (_ == $$ (_))%kami_expr) = true |- _ ] => apply expr_bool_unequality in H
           end.

  Lemma relatedCensor :
    forall rf1 rf2 pm pc mem1 mem2 trace1 trace2 newRegs1 newRegs2 ls1 ls2,
      hasTrace rf1 pm pc mem1 trace1 ->
      hasTrace rf2 pm pc mem2 trace2 ->
      ForwardMultistep p (SCProcRegs rf1 pm pc) newRegs1 ls1 ->
      SCProcMemConsistent ls1 mem1 ->
      ForwardMultistep p (SCProcRegs rf2 pm pc) newRegs2 ls2 ->
      SCProcMemConsistent ls2 mem2 ->
      relatedTrace trace1 ls1 ->
      relatedTrace trace2 ls2 ->
      censorTrace trace1 = censorTrace trace2 ->
      censorLabelSeq censorSCMeth (canonicalize ls1) = censorLabelSeq censorSCMeth (canonicalize ls2).
  Proof.
    intros rf1 rf2 pm pc mem1 mem2 trace1 trace2 newRegs1 newRegs2 ls1 ls2 Hht1.
    move Hht1 at top.
    generalize rf2 mem2 trace2 newRegs1 newRegs2 ls1 ls2.
    clear rf2 mem2 trace2 newRegs1 newRegs2 ls1 ls2.
    induction Hht1; intros.
    - match goal with
      | [ H : censorTrace nil = censorTrace ?l |- _ ] => destruct l; simpl in H; try congruence
      end.
      match goal with
      | [ H1 : relatedTrace nil _, H2 : relatedTrace nil _ |- _ ] => inversion H1; inversion H2
      end.
      reflexivity.
    - match goal with
      | [ Hct : censorTrace (Nop _ :: _) = censorTrace ?tr |- _ ] =>
        let t := fresh in
        destruct tr as [|t tr];
          simpl in Hct;
          try destruct t;
          try congruence;
          inversion Hct;
          clear Hct;
          opaque_subst
      end.
      match goal with
      | [ Hrt1 : relatedTrace (_ :: _) ?l1, Hrt2 : relatedTrace (_ :: _) ?l2 |- _ ] => destruct l1; destruct l2; inversion Hrt1; inversion Hrt2; clear Hrt1; clear Hrt2
      end.
      opaque_subst.
      simpl.
      repeat match goal with
             | [ Hbm : ForwardMultistep _ _ _ (?lbl :: _) |- _ ] =>
               inversion Hbm;
                 clear Hbm;
                 match goal with
                 | [ Hst : Step _ _ _ lbl |- _ ] =>
                   inversion Hst;
                     clear Hst
                 end
             end.
      opaque_subst.
      apply substepsComb_substepsInd in HSubsteps.
      apply SCProcSubsteps in HSubsteps.
      apply substepsComb_substepsInd in HSubsteps0.
      apply SCProcSubsteps in HSubsteps0.
      intuition idtac; shatter;
        match goal with
        | [ H : foldSSLabel ss = _, H0 : foldSSLabel ss0 = _ |- _ ] => rewrite H in *; rewrite H0 in *; simpl
        end;
        try discriminate;
        f_equal;
        match goal with
        | [ H : foldSSUpds ss = _, H0 : foldSSUpds ss0 = _ |- _ ] => rewrite H in *; rewrite H0 in *; simpl
        end;
        match goal with
        | [ H : hasTrace _ _ _ _ (Nop _ :: _) |- _ ] => inversion H
        end;
        subst;
        eapply IHHht1;
        try eassumption;
        match goal with
        | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => inversion H; simpl in *; subst; assumption
        end.
    - match goal with
      | [ Hct : censorTrace (Rd _ _ _ :: _) = censorTrace ?tr |- _ ] =>
        let t := fresh in
        destruct tr as [|t tr];
          simpl in Hct;
          try destruct t;
          try congruence;
          inversion Hct;
          clear Hct;
          opaque_subst
      end.
      match goal with
      | [ Hrt1 : relatedTrace (_ :: _) ?l1, Hrt2 : relatedTrace (_ :: _) ?l2 |- _ ] => destruct l1; destruct l2; inversion Hrt1; inversion Hrt2; clear Hrt1; clear Hrt2
      end.
      opaque_subst.
      simpl.
      repeat match goal with
             | [ Hbm : ForwardMultistep _ _ _ (?lbl :: _) |- _ ] =>
               inversion Hbm;
                 clear Hbm;
                 match goal with
                 | [ Hst : Step _ _ _ lbl |- _ ] =>
                   inversion Hst;
                     clear Hst
                 end
             end.
      opaque_subst.
      apply substepsComb_substepsInd in HSubsteps.
      apply SCProcSubsteps in HSubsteps.
      intuition idtac; shatter;
        match goal with
        | [ H : foldSSLabel ss = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
        end.
      match goal with
      | [ H : In _ _ |- _ ] => simpl in H
      end.
      Opaque evalExpr.
      intuition idtac; kinv_action_dest; SCProcRegs_find; expr_equalities; try tauto; try discriminate.
      Transparent evalExpr.
      apply substepsComb_substepsInd in HSubsteps0.
      apply SCProcSubsteps in HSubsteps0.
      intuition idtac; shatter;
        match goal with
        | [ H : foldSSLabel ss0 = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss0)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
        end.
      match goal with
      | [ H : In _ _ |- _ ] => simpl in H
      end.
      Opaque evalExpr.
      intuition idtac; kinv_action_dest; SCProcRegs_find;
        expr_equalities;
        try tauto;
        try match goal with
            | [ H : ?x = ?y, H' : ?x = ?z |- _ ] => rewrite H' in H; discriminate H
            end.
      Transparent evalExpr.
      f_equal.
      + do 2 match goal with
             | [ |- context[@evalExpr ?t (STRUCT {"addr" ::= rv32iAlignAddr ?ty ?adr; "op" ::= ?o; "data" ::= ?d})%kami_expr] ] => replace (@evalExpr t (STRUCT {"addr" ::= rv32iAlignAddr ty adr; "op" ::= _; "data" ::= _})%kami_expr) with (@evalExpr t (STRUCT {"addr" ::= #(evalExpr (rv32iAlignAddr ty adr)); "op" ::= o; "data" ::= d})%kami_expr) by eauto
             end.
        unfold censorLabel, censorSCMeth, canonicalizeLabel, hide, annot, calls, defs.
        f_equal.
        match goal with
        | [ H1 : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add "exec" (existT _ _ (evalExpr STRUCT {"addr" ::= ?addr1; "op" ::= _; "data" ::= _}%kami_expr, _)) _ |}) = _,
                 H2 : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add "exec" (existT _ _ (evalExpr STRUCT {"addr" ::= ?addr2; "op" ::= _; "data" ::= _}%kami_expr, _)) _ |}) = _
            |- _ ] => replace (evalExpr addr1) with (evalExpr addr2)
        end.
        * clear; eauto.
        * match goal with
          | [ H : labelToTraceEvent ?l = _,
                  x : forall _ : Fin.t 1, _
                                     |- _ = evalExpr ?adr ] =>
            replace (labelToTraceEvent l) with (Some (Rd $ (0) (evalExpr adr) (evalExpr (#x!rv32iRs@."data")%kami_expr))) in H by eauto
          end.
          Opaque evalExpr.
          match goal with
          | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
          end.
          Transparent evalExpr.
          match goal with
          | [ H : ?x = _ |- _ = ?x ] => rewrite H
          end.
          unfold laddr_aligned, laddr, addr, srcVal, srcIdx.
          clear.
          reflexivity.
      + match goal with
        | [ rf : word rv32iRfIdx -> word 32,
                 rf' : word rv32iRfIdx -> word 32,
                       pm : word rv32iIAddrSize -> word 32,
                            pc : word rv32iAddrSize |- _ ] =>
          assert (evalExpr
                    (rv32iNextPc type rf pc (pm (evalExpr (rv32iAlignPc type pc)))) =
                  evalExpr
                    (rv32iNextPc type rf' pc (pm (evalExpr (rv32iAlignPc type pc))))) by
              (unfold rv32iNextPc;
               evexg;
               match goal with
               | [ H : context[rv32iGetOptype] |- _ ] =>
                 unfold rv32iGetOptype in H;
                 evex H;
                 repeat match goal with
                        | [ H : context[isEq _ _ (evalConstT ?o)] |- _ ] => destruct (isEq _ _ (evalConstT o))
                        | [ |- context[isEq _ _ (evalConstT ?o) ] ] => destruct (isEq _ _ (evalConstT o))
                        end;
                 unfold evalConstT in *;
                 try congruence;
                 try match goal with
                     | [ H1 : evalExpr (getOpcodeE _) = ?o1, H2 : evalExpr (getOpcodeE _) = ?o2 |- _ ] => rewrite H1 in H2; discriminate H2
                     end;
                 discriminate H
               end)
        end.
        match goal with
        | [ IH : context[censorLabelSeq _ _ = censorLabelSeq _ _] |- _ ] => eapply IH
        end;
          try match goal with
              | [ HBFM : ForwardMultistep _ ?r1 _ ?l |- ForwardMultistep _ ?r2 _ ?l ] =>
                replace r2 with r1; try eassumption
              | [ |- censorTrace _ = censorTrace _ ] => eassumption
              | [ |- relatedTrace _ _ ] => eassumption
              end.
        * match goal with
          | [ Hht : hasTrace _ _ _ _ (_ :: ?t) |- hasTrace _ _ _ _ ?t ] => inversion Hht
          end.
          subst.
          match goal with
          | [ Hht : hasTrace _ _ ?pc1 _ ?t |- hasTrace _ _ ?pc2 _ ?t ] => replace pc2 with pc1 by congruence; eassumption
          end.
        * match goal with
          | [ H : foldSSUpds ss0 = _ |- _ ] => rewrite H
          end.
          match goal with
          | [ |- FMap.M.union (FMap.M.add "rf" (existT _ _ ?r1) (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _))) _ = SCProcRegs ?r2 _ ?p2 ] => unfold SCProcRegs; replace r1 with r2
          end.
          -- clear; eauto.
          -- unfold rset.
             destruct (weq dstIdx (wzero _)); try tauto.
             evexg.
             apply functional_extensionality.
             intros.
             unfold dstIdx.
             match goal with
             | [ |- (if _ then ?x else _) = (if _ then ?y else _) ] => replace x with y; [ reflexivity | idtac ]
             end.
             simpl.
             match goal with
             | [ H : labelToTraceEvent ?l = Some (Rd $ (0) laddr_aligned (mem laddr_aligned)),
                     x : forall _ : Fin.t 1, _
                                        |- _ ] =>
               match goal with
               | [ H : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add _ (existT _ _ (evalExpr STRUCT {"addr" ::= ?adr; "op" ::= _; "data" ::= _}%kami_expr, x)) _|}) = Some (Rd $ (0) _ (mem laddr_aligned)) |- _ ] =>
                 replace (labelToTraceEvent l) with (Some (Rd $ (0) (evalExpr adr) (evalExpr (#x!rv32iRs@."data")%kami_expr))) in H by eauto; inversion H
               end
             end.
             reflexivity.
        * Opaque evalExpr.
          match goal with
          | [ H : SCProcMemConsistent (_ :: ?l) _ |- SCProcMemConsistent ?l _ ] => clear - H; inversion H; clear H
          end.
          subst.
          simpl in *.
          Transparent evalExpr.
          match goal with
          | [ H : if ?x then _ else _ |- _ ] =>
            replace x with false in H by reflexivity
          end.
          intuition idtac.
          subst.
          assumption.
        * match goal with
          | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
          end.
          match goal with
          | [ |- FMap.M.union (FMap.M.add "rf" (existT _ _ ?r1) (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _))) _ = SCProcRegs ?r2 _ ?p2 ] => unfold SCProcRegs; replace r1 with r2; [ replace p1 with p2 by congruence | idtac ]
          end.
          -- clear; eauto.
          -- unfold rset.
             fold dstIdx.
             destruct (weq dstIdx (wzero _)); try tauto.
             evexg.
             apply functional_extensionality.
             intros.
             unfold dstIdx.
             match goal with
             | [ |- (if _ then ?x else _) = (if _ then ?y else _) ] => replace x with y; [ reflexivity | idtac ]
             end.
             simpl.
             match goal with
             | [ H : labelToTraceEvent ?l = Some (Rd $ (0) laddr_aligned val0),
                     x : forall _ : Fin.t 1, _
                                        |- _ ] =>
               match goal with
               | [ H : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add _ (existT _ _ (evalExpr STRUCT {"addr" ::= ?adr; "op" ::= _; "data" ::= _}%kami_expr, x)) _|}) = Some (Rd $ (0) _ val0) |- _ ] =>
                 replace (labelToTraceEvent l) with (Some (Rd $ (0) (evalExpr adr) (evalExpr (#x!rv32iRs@."data")%kami_expr))) in H
               end
             end.
             ++ Opaque evalExpr.
                match goal with
                | [ H : Some _ = Some _ |- _ ] => inversion H
                end.
                match goal with
                | [ H : ?x = _ |- _ = _ ?x ] => rewrite H
                end.
                match goal with
                | [ H : SCProcMemConsistent _ ?m |- _ = ?m _ ] =>
                  inversion H;
                    clear H
                end.
                subst.
                simpl in *.
                Transparent evalExpr.
                match goal with
                | [ H : if ?x then _ else _ |- _ ] =>
                  replace x with false in H by reflexivity
                end.
                intuition idtac; subst.
                match goal with
                | [ H : ?m ?a = ?v |- ?x = ?y ] => replace (m a) with y in H; [replace v with x in H|]
                end.
                ** congruence.
                ** reflexivity.
                ** match goal with
                   | [ |- context[(evalExpr STRUCT {"addr" ::= ?a; "op" ::= _; "data" ::= _ })%kami_expr] ] => replace laddr_aligned with (evalExpr a)
                   end.
                   reflexivity.
             ++ eauto.
        * Opaque evalExpr.
          match goal with
          | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => inversion H; clear H
          end.
          subst.
          simpl in *.
          Transparent evalExpr.
          match goal with
          | [ H : if ?x then _ else _ |- _ ] =>
            replace x with false in H by reflexivity
          end.
          intuition idtac.
          subst.
          assumption.
    - match goal with
      | [ Hct : censorTrace (RdZ _ _ :: _) = censorTrace ?tr |- _ ] =>
        let t := fresh in
        destruct tr as [|t tr];
          simpl in Hct;
          try destruct t;
          try congruence;
          inversion Hct;
          clear Hct;
          opaque_subst
      end.
      match goal with
      | [ Hrt1 : relatedTrace (_ :: _) ?l1, Hrt2 : relatedTrace (_ :: _) ?l2 |- _ ] => destruct l1; destruct l2; inversion Hrt1; inversion Hrt2; clear Hrt1; clear Hrt2
      end.
      opaque_subst.
      simpl.
      repeat match goal with
             | [ Hbm : ForwardMultistep _ _ _ (?lbl :: _) |- _ ] =>
               inversion Hbm;
                 clear Hbm;
                 match goal with
                 | [ Hst : Step _ _ _ lbl |- _ ] =>
                   inversion Hst;
                     clear Hst
                 end
             end.
      opaque_subst.
      apply substepsComb_substepsInd in HSubsteps.
      apply SCProcSubsteps in HSubsteps.
      intuition idtac; shatter;
        match goal with
        | [ H : foldSSLabel ss = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
        | [ H : foldSSLabel ss = _, H1 : annot (hide (foldSSLabel ss)) = None -> False, H2 : annot (hide (foldSSLabel ss)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
        end.
      match goal with
      | [ H : In _ _ |- _ ] => simpl in H
      end.
      Opaque evalExpr.
      intuition idtac; kinv_action_dest; SCProcRegs_find; expr_equalities; try tauto; try discriminate.
      Transparent evalExpr.
      + apply substepsComb_substepsInd in HSubsteps0.
        apply SCProcSubsteps in HSubsteps0.
        intuition idtac; shatter;
          match goal with
          | [ H : foldSSLabel ss0 = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss0)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
          | [ H : foldSSLabel ss0 = _, H1 : annot (hide (foldSSLabel ss0)) = None -> False, H2 : annot (hide (foldSSLabel ss0)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
          end.
        match goal with
        | [ H : In _ _ |- _ ] => simpl in H
        end.
        Opaque evalExpr.
        intuition idtac; kinv_action_dest; SCProcRegs_find;
        expr_equalities;
        try tauto;
        try match goal with
            | [ H : ?x = ?y, H' : ?x = ?z |- _ ] => rewrite H' in H; discriminate H
            end.
        Transparent evalExpr.
        f_equal.
        * match goal with
          | [ rf : word rv32iRfIdx -> word 32,
                   rf' : word rv32iRfIdx -> word 32,
                         pm : word rv32iIAddrSize -> word 32,
                              pc : word rv32iAddrSize |- _ ] =>
            assert (evalExpr
                      (rv32iNextPc type rf pc (pm (evalExpr (rv32iAlignPc type pc)))) =
                    evalExpr
                      (rv32iNextPc type rf' pc (pm (evalExpr (rv32iAlignPc type pc))))) by
                (unfold rv32iNextPc;
                 evexg;
                 match goal with
                 | [ H : context[rv32iGetOptype] |- _ ] =>
                   unfold rv32iGetOptype in H;
                   evex H;
                   repeat match goal with
                          | [ H : context[isEq _ _ (evalConstT ?o)] |- _ ] => destruct (isEq _ _ (evalConstT o))
                          | [ |- context[isEq _ _ (evalConstT ?o) ] ] => destruct (isEq _ _ (evalConstT o))
                          end;
                   unfold evalConstT in *;
                   try congruence;
                   try match goal with
                       | [ H1 : evalExpr (getOpcodeE _) = ?o1, H2 : evalExpr (getOpcodeE _) = ?o2 |- _ ] => rewrite H1 in H2; discriminate H2
                       end;
                   discriminate H
                 end)
          end.
          match goal with
          | [ IH : context[censorLabelSeq _ _ = censorLabelSeq _ _] |- _ ] => eapply IH
          end;
            try match goal with
                | [ HBFM : ForwardMultistep _ ?r1 _ ?l |- ForwardMultistep _ ?r2 _ ?l ] =>
                  replace r2 with r1; try eassumption
                | [ |- censorTrace _ = censorTrace _ ] => eassumption
                | [ |- relatedTrace _ _ ] => eassumption
                end.
          -- match goal with
             | [ Hht : hasTrace _ _ _ _ (_ :: ?t) |- hasTrace _ _ _ _ ?t ] => inversion Hht
             end.
             subst.
             match goal with
             | [ Hht : hasTrace _ _ ?pc1 _ ?t |- hasTrace _ _ ?pc2 _ ?t ] => replace pc2 with pc1 by congruence; try eassumption
             end.
          -- match goal with
             | [ H : foldSSUpds ss0 = _ |- _ ] => rewrite H
             end.
             unfold SCProcRegs; clear; eauto.
          -- match goal with
             | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => clear - H; inversion H
             end.
             simpl in *.
             subst.
             assumption.
          -- match goal with
             | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
             end.
             match goal with
             | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) _ = SCProcRegs _ _ ?p2 ] => unfold SCProcRegs; replace p1 with p2 by congruence
             end.
             clear; eauto.
          -- match goal with
             | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => clear - H; inversion H
             end.
             simpl in *.
             subst.
             assumption.
      + match goal with
        | [ H : ?x = opLd, H' : ?y = opNm |- _ ] => replace x with y in H by reflexivity; rewrite H' in H
        end.
        discriminate.
      + match goal with
        | [ H : ?x = opLd, H' : ?y = opNm |- _ ] => replace x with y in H by reflexivity; rewrite H' in H
        end.
        discriminate.
    - match goal with
      | [ Hct : censorTrace (Wr _ _ _ :: _) = censorTrace ?tr |- _ ] =>
        let t := fresh in
        destruct tr as [|t tr];
          simpl in Hct;
          try destruct t;
          try congruence;
          inversion Hct;
          clear Hct;
          opaque_subst
      end.
      match goal with
      | [ Hrt1 : relatedTrace (_ :: _) ?l1, Hrt2 : relatedTrace (_ :: _) ?l2 |- _ ] => destruct l1; destruct l2; inversion Hrt1; inversion Hrt2; clear Hrt1; clear Hrt2
      end.
      opaque_subst.
      simpl.
      repeat match goal with
             | [ Hbm : ForwardMultistep _ _ _ (?lbl :: _) |- _ ] =>
               inversion Hbm;
                 clear Hbm;
                 match goal with
                 | [ Hst : Step _ _ _ lbl |- _ ] =>
                   inversion Hst;
                     clear Hst
                 end
             end.
      opaque_subst.
      apply substepsComb_substepsInd in HSubsteps.
      apply SCProcSubsteps in HSubsteps.
      intuition idtac; shatter;
        match goal with
        | [ H : foldSSLabel ss = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
        | [ H : foldSSLabel ss = _, H1 : annot (hide (foldSSLabel ss)) = None -> False, H2 : annot (hide (foldSSLabel ss)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
        end.
      match goal with
      | [ H : In _ _ |- _ ] => simpl in H
      end.
      Opaque evalExpr.
      intuition idtac; kinv_action_dest; SCProcRegs_find; expr_equalities; try tauto; try discriminate.
      Transparent evalExpr.
      apply substepsComb_substepsInd in HSubsteps0.
      apply SCProcSubsteps in HSubsteps0.
      intuition idtac; shatter;
        match goal with
        | [ H : foldSSLabel ss0 = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss0)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
        | [ H : foldSSLabel ss0 = _, H1 : annot (hide (foldSSLabel ss0)) = None -> False, H2 : annot (hide (foldSSLabel ss0)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
        end.
      match goal with
      | [ H : In _ _ |- _ ] => simpl in H
      end.
      Opaque evalExpr.
      intuition idtac; kinv_action_dest; SCProcRegs_find;
        expr_equalities;
        try tauto;
        try match goal with
            | [ H : ?x = ?y, H' : ?x = ?z |- _ ] => rewrite H' in H; discriminate H
            end.
      Transparent evalExpr.
      f_equal.
      + do 2 match goal with
             | [ |- context[@evalExpr ?t (STRUCT {"addr" ::= rv32iAlignAddr ?ty ?adr; "op" ::= ?o; "data" ::= ?d})%kami_expr] ] => replace (@evalExpr t (STRUCT {"addr" ::= rv32iAlignAddr ty adr; "op" ::= _; "data" ::= _})%kami_expr) with (@evalExpr t (STRUCT {"addr" ::= #(evalExpr (rv32iAlignAddr ty adr)); "op" ::= o; "data" ::= d})%kami_expr) by eauto
             end.
        unfold censorLabel, censorSCMeth, canonicalizeLabel, hide, annot, calls, defs.
        f_equal.
        match goal with
        | [ H1 : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add "exec" (existT _ _ (evalExpr STRUCT {"addr" ::= ?addr1; "op" ::= _; "data" ::= _}%kami_expr, _)) _ |}) = _,
                 H2 : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add "exec" (existT _ _ (evalExpr STRUCT {"addr" ::= ?addr2; "op" ::= _; "data" ::= _}%kami_expr, _)) _ |}) = _
            |- _ ] => replace (evalExpr addr1) with (evalExpr addr2)
        end.
        * clear; eauto.
        * match goal with
          | [ H : labelToTraceEvent ?l = _,
                  x : forall _ : Fin.t 1, _,
                Hignore : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add "exec" (existT _ _ (evalExpr STRUCT {"addr" ::= ?adr'; "op" ::= _; "data" ::= _}%kami_expr, _)) _ |}) = _
                |- evalExpr ?adr' = evalExpr ?adr ] =>
            match goal with
            | [ H : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add "exec" (existT _ _ (evalExpr STRUCT {"addr" ::= adr; "op" ::= _; "data" ::= ?dat}%kami_expr, _)) _ |}) = _ |- _ ] =>
              replace (labelToTraceEvent l) with (Some (Wr $ (0) (evalExpr adr) (evalExpr dat))) in H by eauto
            end
          end.
          Opaque evalExpr.
          match goal with
          | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
          end.
          Transparent evalExpr.
          match goal with
          | [ H : ?x = _ |- _ = ?x ] => rewrite H
          end.
          unfold saddr_aligned, saddr, addr, srcVal, srcIdx.
          reflexivity.
      + match goal with
        | [ rf : word rv32iRfIdx -> word 32,
                 rf' : word rv32iRfIdx -> word 32,
                       pm : word rv32iIAddrSize -> word 32,
                            pc : word rv32iAddrSize |- _ ] =>
          assert (evalExpr
                    (rv32iNextPc type rf pc (pm (evalExpr (rv32iAlignPc type pc)))) =
                  evalExpr
                    (rv32iNextPc type rf' pc (pm (evalExpr (rv32iAlignPc type pc))))) by
              (unfold rv32iNextPc;
               evexg;
               match goal with
               | [ H : context[rv32iGetOptype] |- _ ] =>
                 unfold rv32iGetOptype in H;
                 evex H;
                 repeat match goal with
                        | [ H : context[isEq _ _ (evalConstT ?o)] |- _ ] => destruct (isEq _ _ (evalConstT o))
                        | [ |- context[isEq _ _ (evalConstT ?o) ] ] => destruct (isEq _ _ (evalConstT o))
                        end;
                 unfold evalConstT in *;
                 try congruence;
                 try match goal with
                     | [ H1 : evalExpr (getOpcodeE _) = ?o1, H2 : evalExpr (getOpcodeE _) = ?o2 |- _ ] => rewrite H1 in H2; discriminate H2
                     end;
                 discriminate H
               end)
        end.
        match goal with
        | [ IH : context[censorLabelSeq _ _ = censorLabelSeq _ _] |- _ ] => eapply IH
        end;
          try match goal with
              | [ HFM : ForwardMultistep _ ?r1 _ ?l |- ForwardMultistep _ ?r2 _ ?l ] =>
                replace r2 with r1; try eassumption
              | [ |- censorTrace _ = censorTrace _ ] => eassumption
              | [ |- relatedTrace _ _ ] => eassumption
              end.
        * match goal with
          | [ Hht : hasTrace _ _ _ _ (_ :: ?t) |- hasTrace _ _ _ _ ?t ] => inversion Hht
          end.
          subst.
          match goal with
          | [ Hht : hasTrace _ _ ?pc1 _ ?t |- hasTrace _ _ ?pc2 _ ?t ] => replace pc2 with pc1 by congruence; eassumption
          end.
        * match goal with
          | [ H : foldSSUpds ss0 = _ |- _ ] => rewrite H
          end.
          unfold SCProcRegs; clear; eauto.
        * Opaque evalExpr.
          match goal with
          | [ H : SCProcMemConsistent (_ :: ?l) _ |- SCProcMemConsistent ?l _ ] => inversion H; clear H
          end.
          subst.
          simpl in *.
          Transparent evalExpr.
          match goal with
          | [ H : if ?x then _ else _ |- _ ] =>
            replace x with true in H by reflexivity
          end.
          subst.
          match goal with
          | [ H : SCProcMemConsistent ?l ?mem |- SCProcMemConsistent ?l ?mem' ] => replace mem' with mem; [assumption|]
          end.
          match goal with
          | [ |- (fun a => if weq a ?x then ?y else _) = (fun a => if weq a ?x' then ?y' else _) ] => replace x with x' by reflexivity; replace y with y' by reflexivity; reflexivity
          end.
        * match goal with
          | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
          end.
          match goal with
          | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) _ = SCProcRegs _ _ ?p2 ] => unfold SCProcRegs; replace p1 with p2 by congruence
          end.
          clear; eauto.
        * Opaque evalExpr labelToTraceEvent.
          match goal with
          | [ H : SCProcMemConsistent (_ :: ?l) _ |- SCProcMemConsistent ?l _ ] => inversion H; clear H
          end.
          subst.
          simpl in *.
          Transparent evalExpr labelToTraceEvent.
          match goal with
          | [ H : if ?x then _ else _ |- _ ] =>
            replace x with true in H by reflexivity
          end.
          subst.
          match goal with
          | [ H : SCProcMemConsistent ?l ?mem |- SCProcMemConsistent ?l ?mem' ] => replace mem' with mem; [assumption|]
          end.
          match goal with
          | [ |- context[if _ then ?ex else _] ] =>
            match goal with
            | [ |- context[if _ then (evalExpr (ReadField _ # (evalExpr STRUCT {"addr" ::= _; "op" ::= _; "data" ::= # (?d)})%kami_expr)) else _] ] => replace ex with d by reflexivity
            end
          end.
          match goal with
          | [ |- context[weq _ ?ex] ] =>
            match goal with
            | [ |- context[weq _ (evalExpr (ReadField _ # (evalExpr STRUCT {"addr" ::= ?a; "op" ::= _; "data" ::= _})%kami_expr))] ] => replace ex with (evalExpr a) by reflexivity
            end
          end.
          match goal with
          | [ H : labelToTraceEvent ?l = Some (Wr _ _ val) |- _ ] =>
            match goal with
            | [ H : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add _ (existT _ _ (evalExpr STRUCT {"addr" ::= ?adr; "op" ::= _; "data" ::= # (?d)}%kami_expr, _)) _|}) = Some (Wr _ _ val) |- _ ] => replace (labelToTraceEvent l) with (Some (Wr $ (0) (evalExpr adr) d)) in H by reflexivity
            end
          end.
          Opaque evalExpr.
          match goal with
          | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
          end.
          Transparent evalExpr.
          reflexivity.
    - match goal with
      | [ Hct : censorTrace (ToHost _ _ :: _) = censorTrace ?tr |- _ ] =>
        let t := fresh in
        destruct tr as [|t tr];
          simpl in Hct;
          try destruct t;
          try congruence;
          inversion Hct;
          clear Hct;
          opaque_subst
      end.
      match goal with
      | [ Hrt1 : relatedTrace (_ :: _) ?l1, Hrt2 : relatedTrace (_ :: _) ?l2 |- _ ] => destruct l1; destruct l2; inversion Hrt1; inversion Hrt2; clear Hrt1; clear Hrt2
      end.
      opaque_subst.
      simpl.
      repeat match goal with
             | [ Hbm : ForwardMultistep _ _ _ (?lbl :: _) |- _ ] =>
               inversion Hbm;
                 clear Hbm;
                 match goal with
                 | [ Hst : Step _ _ _ lbl |- _ ] =>
                   inversion Hst;
                     clear Hst
                 end
             end.
      opaque_subst.
      apply substepsComb_substepsInd in HSubsteps.
      apply SCProcSubsteps in HSubsteps.
      intuition idtac; shatter;
        match goal with
        | [ H : foldSSLabel ss = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
        | [ H : foldSSLabel ss = _, H1 : annot (hide (foldSSLabel ss)) = None -> False, H2 : annot (hide (foldSSLabel ss)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
        end.
      match goal with
      | [ H : In _ _ |- _ ] => simpl in H
      end.
      Opaque evalExpr.
      intuition idtac; kinv_action_dest; SCProcRegs_find; expr_equalities; try tauto; try discriminate.
      Transparent evalExpr.
      apply substepsComb_substepsInd in HSubsteps0.
      apply SCProcSubsteps in HSubsteps0.
      intuition idtac; shatter;
        match goal with
        | [ H : foldSSLabel ss0 = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss0)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
        | [ H : foldSSLabel ss0 = _, H1 : annot (hide (foldSSLabel ss0)) = None -> False, H2 : annot (hide (foldSSLabel ss0)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
        end.
      match goal with
      | [ H : In _ _ |- _ ] => simpl in H
      end.
      Opaque evalExpr.
      intuition idtac; kinv_action_dest; SCProcRegs_find;
        expr_equalities;
        try tauto;
        try match goal with
            | [ H : ?x = ?y, H' : ?x = ?z |- _ ] => rewrite H' in H; discriminate H
            end.
      Transparent evalExpr.
      f_equal.
      + repeat match goal with
               | [ x : word 0 |- _ ] => shatter_word x; clear x
               end.
        repeat match goal with
               | [ |- context[hide ?l] ] => change (hide l) with l 
               end.
        unfold censorLabel, canonicalizeLabel; f_equal.
        FMap.M.ext k.
        do 2 rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
        FMap.mred.
      + match goal with
        | [ rf : word rv32iRfIdx -> word 32,
                 rf' : word rv32iRfIdx -> word 32,
                       pm : word rv32iIAddrSize -> word 32,
                            pc : word rv32iAddrSize |- _ ] =>
          assert (evalExpr
                    (rv32iNextPc type rf pc (pm (evalExpr (rv32iAlignPc type pc)))) =
                  evalExpr
                    (rv32iNextPc type rf' pc (pm (evalExpr (rv32iAlignPc type pc))))) by
              (unfold rv32iNextPc;
               evexg;
               match goal with
               | [ H : context[rv32iGetOptype] |- _ ] =>
                 unfold rv32iGetOptype in H;
                 evex H;
                 repeat match goal with
                        | [ H : context[isEq _ _ (evalConstT ?o)] |- _ ] => destruct (isEq _ _ (evalConstT o))
                        | [ |- context[isEq _ _ (evalConstT ?o) ] ] => destruct (isEq _ _ (evalConstT o))
                        end;
                 unfold evalConstT in *;
                 try congruence;
                 try match goal with
                     | [ H1 : evalExpr (getOpcodeE _) = ?o1, H2 : evalExpr (getOpcodeE _) = ?o2 |- _ ] => rewrite H1 in H2; discriminate H2
                     end;
                 discriminate H
               end)
        end.
        match goal with
        | [ IH : context[censorLabelSeq _ _ = censorLabelSeq _ _] |- _ ] => eapply IH
        end;
          try match goal with
              | [ HBFM : ForwardMultistep _ ?r1 _ ?l |- ForwardMultistep _ ?r2 _ ?l ] =>
                replace r2 with r1; try eassumption
              | [ |- censorTrace _ = censorTrace _ ] => eassumption
              | [ |- relatedTrace _ _ ] => eassumption
              end.
        * match goal with
          | [ Hht : hasTrace _ _ _ _ (_ :: ?t) |- hasTrace _ _ _ _ ?t ] => inversion Hht
          end.
          subst.
          match goal with
          | [ Hht : hasTrace _ _ ?pc1 _ ?t |- hasTrace _ _ ?pc2 _ ?t ] => replace pc2 with pc1 by congruence; eassumption
          end.
        * match goal with
          | [ H : foldSSUpds ss0 = _ |- _ ] => rewrite H
          end.
          clear; unfold SCProcRegs; eauto.
        * Opaque evalExpr.
          match goal with
          | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => clear - H; inversion H
          end.
          simpl in *.
          Transparent evalExpr.
          subst.
          assumption.
        * match goal with
          | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
          end.
          match goal with
          | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) _ = SCProcRegs _ _ ?p2 ] => unfold SCProcRegs; replace p1 with p2 by congruence
          end.
          clear; eauto.
        * Opaque evalExpr.
          match goal with
          | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => clear - H; inversion H
          end.
          simpl in *.
          Transparent evalExpr.
          subst.
          assumption.
    - match goal with
      | [ Hct : censorTrace (FromHost _ _ :: _) = censorTrace ?tr |- _ ] =>
        let t := fresh in
        destruct tr as [|t tr];
          simpl in Hct;
          try destruct t;
          try congruence;
          inversion Hct;
          clear Hct;
          opaque_subst
      end.
      match goal with
      | [ Hrt1 : relatedTrace (_ :: _) ?l1, Hrt2 : relatedTrace (_ :: _) ?l2 |- _ ] => destruct l1; destruct l2; inversion Hrt1; inversion Hrt2; clear Hrt1; clear Hrt2
      end.
      opaque_subst.
      simpl.
      repeat match goal with
             | [ Hbm : ForwardMultistep _ _ _ (?lbl :: _) |- _ ] =>
               inversion Hbm;
                 clear Hbm;
                 match goal with
                 | [ Hst : Step _ _ _ lbl |- _ ] =>
                   inversion Hst;
                     clear Hst
                 end
             end.
      opaque_subst.
      apply substepsComb_substepsInd in HSubsteps.
      apply SCProcSubsteps in HSubsteps.
      intuition idtac; shatter;
        match goal with
        | [ H : foldSSLabel ss = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
        | [ H : foldSSLabel ss = _, H1 : annot (hide (foldSSLabel ss)) = None -> False, H2 : annot (hide (foldSSLabel ss)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
        end.
      match goal with
      | [ H : In _ _ |- _ ] => simpl in H
      end.
      Opaque evalExpr.
      intuition idtac; kinv_action_dest; SCProcRegs_find; expr_equalities; try tauto; try discriminate.
      Transparent evalExpr.
      + apply substepsComb_substepsInd in HSubsteps0.
        apply SCProcSubsteps in HSubsteps0.
        intuition idtac; shatter;
          match goal with
          | [ H : foldSSLabel ss0 = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss0)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
          | [ H : foldSSLabel ss0 = _, H1 : annot (hide (foldSSLabel ss0)) = None -> False, H2 : annot (hide (foldSSLabel ss0)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
          end.
        match goal with
        | [ H : In _ _ |- _ ] => simpl in H
        end.
        Opaque evalExpr.
        intuition idtac; kinv_action_dest; SCProcRegs_find;
          expr_equalities;
          try tauto;
          try match goal with
              | [ H : ?x = ?y, H' : ?x = ?z |- _ ] => rewrite H' in H; discriminate H
              end.
        Transparent evalExpr.
        f_equal.
        * repeat match goal with
                 | [ |- context[hide ?l] ] => change (hide l) with l 
                 end.
          unfold censorLabel, canonicalizeLabel; f_equal.
          FMap.M.ext k.
          do 2 rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
          FMap.mred.
        * match goal with
          | [ rf : word rv32iRfIdx -> word 32,
                   rf' : word rv32iRfIdx -> word 32,
                         pm : word rv32iIAddrSize -> word 32,
                              pc : word rv32iAddrSize |- _ ] =>
            assert (evalExpr
                      (rv32iNextPc type rf pc (pm (evalExpr (rv32iAlignPc type pc)))) =
                    evalExpr
                      (rv32iNextPc type rf' pc (pm (evalExpr (rv32iAlignPc type pc))))) by
                (unfold rv32iNextPc;
                 evexg;
                 match goal with
                 | [ H : context[rv32iGetOptype] |- _ ] =>
                   unfold rv32iGetOptype in H;
                   evex H;
                   repeat match goal with
                          | [ H : context[isEq _ _ (evalConstT ?o)] |- _ ] => destruct (isEq _ _ (evalConstT o))
                          | [ |- context[isEq _ _ (evalConstT ?o) ] ] => destruct (isEq _ _ (evalConstT o))
                          end;
                   unfold evalConstT in *;
                   try congruence;
                   try match goal with
                       | [ H1 : evalExpr (getOpcodeE _) = ?o1, H2 : evalExpr (getOpcodeE _) = ?o2 |- _ ] => rewrite H1 in H2; discriminate H2
                       end;
                   discriminate H
                 end)
          end.
          match goal with
          | [ IH : context[censorLabelSeq _ _ = censorLabelSeq _ _] |- _ ] => eapply IH
          end;
            try match goal with
                | [ HBFM : ForwardMultistep _ ?r1 _ ?l |- ForwardMultistep _ ?r2 _ ?l ] =>
                  replace r2 with r1; try eassumption
                | [ |- censorTrace _ = censorTrace _ ] => eassumption
                | [ |- relatedTrace _ _ ] => eassumption
                end.
          -- match goal with
             | [ Hht : hasTrace _ _ _ _ (_ :: ?t) |- hasTrace _ _ _ _ ?t ] => inversion Hht
             end.
             subst.
             match goal with
             | [ Hht : hasTrace _ _ ?pc1 _ ?t |- hasTrace _ _ ?pc2 _ ?t ] => replace pc2 with pc1 by congruence; eassumption
             end.
          -- match goal with
             | [ H : foldSSUpds ss0 = _ |- _ ] => rewrite H
             end.
             match goal with
             | [ |- FMap.M.union (FMap.M.add "rf" (existT _ _ ?r1) (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _))) _ = SCProcRegs ?r2 _ ?p2 ] => unfold SCProcRegs; replace r1 with r2
             end.
             ++ clear; eauto.
             ++ unfold rset.
                destruct (weq dst (wzero _)); try tauto.
                evexg.
                apply functional_extensionality.
                intros.
                unfold dst.
                match goal with
                | [ |- (if _ then ?x else _) = (if _ then ?y else _) ] => replace x with y; [ reflexivity | idtac ]
                end.
                match goal with
                | [ H : labelToTraceEvent ?l = Some (FromHost $ (0) ?val),
                        x : word 32
                    |- _ = ?val ] =>
                  replace (labelToTraceEvent l) with (Some (FromHost $ (0) x)) by eauto; inversion H
                end.
                reflexivity.
          -- Opaque evalExpr.
             match goal with
             | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => clear - H; inversion H
             end.
             simpl in *.
             Transparent evalExpr.
             subst.
             assumption.
          -- match goal with
             | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
             end.
             match goal with
             | [ |- FMap.M.union (FMap.M.add "rf" (existT _ _ ?r1) (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _))) _ = SCProcRegs ?r2 _ ?p2 ] => unfold SCProcRegs; replace r1 with r2; [ replace p1 with p2 by congruence | idtac ]
             end.
             ++ clear; eauto.
             ++ unfold rset.
                match goal with
                | [ |- (if ?b then _ else _) = _ ] => destruct b; try tauto
                end.
                evexg.
                match goal with
                | [ |- (fun _ => if _ then ?v else _) = (fun _ => if _ then ?v' else _) ] => replace v with v'; try reflexivity
                end.
                match goal with
                | [ H : labelToTraceEvent ?l = Some (FromHost $ (0) ?v) |- ?v' = ?v ] =>
                  replace (labelToTraceEvent l) with (Some (FromHost $ (0) v')) in H by eauto; inversion H
                end.
                reflexivity.
          -- Opaque evalExpr.
             match goal with
             | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => clear - H; inversion H
             end.
             simpl in *.
             Transparent evalExpr.
             subst.
             assumption.
      + apply substepsComb_substepsInd in HSubsteps0.
        apply SCProcSubsteps in HSubsteps0.
        intuition idtac; shatter;
          match goal with
          | [ H : foldSSLabel ss0 = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss0)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
          | [ H : foldSSLabel ss0 = _, H1 : annot (hide (foldSSLabel ss0)) = None -> False, H2 : annot (hide (foldSSLabel ss0)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
          end.
        match goal with
        | [ H : In _ _ |- _ ] => simpl in H
        end.
        Opaque evalExpr.
        intuition idtac; kinv_action_dest; SCProcRegs_find;
          expr_equalities;
          try tauto;
          try match goal with
              | [ H : ?x = ?y, H' : ?x = ?z |- _ ] => rewrite H' in H; discriminate H
              end.
        Transparent evalExpr.
        f_equal.
        * repeat match goal with
                 | [ |- context[hide ?l] ] => change (hide l) with l 
                 end.
          unfold censorLabel, canonicalizeLabel; f_equal.
          FMap.M.ext k.
          do 2 rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
          FMap.mred.
        * match goal with
          | [ rf : word rv32iRfIdx -> word 32,
                   rf' : word rv32iRfIdx -> word 32,
                         pm : word rv32iIAddrSize -> word 32,
                              pc : word rv32iAddrSize |- _ ] =>
            assert (evalExpr
                      (rv32iNextPc type rf pc (pm (evalExpr (rv32iAlignPc type pc)))) =
                    evalExpr
                      (rv32iNextPc type rf' pc (pm (evalExpr (rv32iAlignPc type pc))))) by
                (unfold rv32iNextPc;
                 evexg;
                 match goal with
                 | [ H : context[rv32iGetOptype] |- _ ] =>
                   unfold rv32iGetOptype in H;
                   evex H;
                   repeat match goal with
                          | [ H : context[isEq _ _ (evalConstT ?o)] |- _ ] => destruct (isEq _ _ (evalConstT o))
                          | [ |- context[isEq _ _ (evalConstT ?o) ] ] => destruct (isEq _ _ (evalConstT o))
                          end;
                   unfold evalConstT in *;
                   try congruence;
                   try match goal with
                       | [ H1 : evalExpr (getOpcodeE _) = ?o1, H2 : evalExpr (getOpcodeE _) = ?o2 |- _ ] => rewrite H1 in H2; discriminate H2
                       end;
                   discriminate H
                 end)
          end.
          match goal with
          | [ IH : context[censorLabelSeq _ _ = censorLabelSeq _ _] |- _ ] => eapply IH
          end;
            try match goal with
                | [ HBFM : ForwardMultistep _ ?r1 _ ?l |- ForwardMultistep _ ?r2 _ ?l ] =>
                  replace r2 with r1; try eassumption
                | [ |- censorTrace _ = censorTrace _ ] => eassumption
                | [ |- relatedTrace _ _ ] => eassumption
                end.
          -- match goal with
             | [ Hht : hasTrace _ _ _ _ (_ :: ?t) |- hasTrace _ _ _ _ ?t ] => inversion Hht
             end.
             subst.
             match goal with
             | [ Hht : hasTrace _ _ ?pc1 _ ?t |- hasTrace _ _ ?pc2 _ ?t ] => replace pc2 with pc1 by congruence; eassumption
             end.
          -- match goal with
             | [ H : foldSSUpds ss0 = _ |- _ ] => rewrite H
             end.
             match goal with
             | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) (SCProcRegs ?r1 _ _) = SCProcRegs ?r2 _ ?p2 ] => unfold SCProcRegs; replace r2 with r1
             end.
             ++ clear; eauto.
             ++ unfold rset.
                destruct (weq dst (wzero _)); try tauto.
          -- Opaque evalExpr.
             match goal with
             | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => clear - H; inversion H
             end.
             simpl in *.
             Transparent evalExpr.
             subst.
             assumption.
          -- match goal with
             | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
                end.
             match goal with
             | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) (SCProcRegs ?r1 _ _) = SCProcRegs ?r2 _ ?p2 ] => unfold SCProcRegs; replace r2 with r1; [ replace p1 with p2 by congruence | idtac ]
             end.
             ++ clear; eauto.
             ++ unfold rset.
                match goal with
                | [ |- _ = (if ?b then _ else _) ] => destruct b; tauto
                end.
          -- Opaque evalExpr.
             match goal with
             | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => clear - H; inversion H
             end.
             simpl in *.
             Transparent evalExpr.
             subst.
             assumption.
    - case_eq (evalExpr (rv32iBranchTaken type rf inst)); intro Hbr; rewrite Hbr in *.
      + match goal with
        | [ Hct : censorTrace (Branch _ _ :: _) = censorTrace ?tr |- _ ] =>
          let t := fresh in
          destruct tr as [|t tr];
            simpl in Hct;
            try destruct t;
            try congruence;
            inversion Hct;
            clear Hct;
            opaque_subst
        end.
        match goal with
        | [ Hrt1 : relatedTrace (_ :: _) ?l1, Hrt2 : relatedTrace (_ :: _) ?l2 |- _ ] => destruct l1; destruct l2; inversion Hrt1; inversion Hrt2; clear Hrt1; clear Hrt2
        end.
        opaque_subst.
        simpl.
        repeat match goal with
               | [ Hbm : ForwardMultistep _ _ _ (?lbl :: _) |- _ ] =>
                 inversion Hbm;
                   clear Hbm;
                   match goal with
                   | [ Hst : Step _ _ _ lbl |- _ ] =>
                     inversion Hst;
                       clear Hst
                   end
               end.
        opaque_subst.
        apply substepsComb_substepsInd in HSubsteps.
        apply SCProcSubsteps in HSubsteps.
        intuition idtac; shatter;
          match goal with
          | [ H : foldSSLabel ss = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
          | [ H : foldSSLabel ss = _, H1 : annot (hide (foldSSLabel ss)) = None -> False, H2 : annot (hide (foldSSLabel ss)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
          end.
        match goal with
        | [ H : In _ _ |- _ ] => simpl in H
        end.
        Opaque evalExpr.
        intuition idtac; kinv_action_dest; SCProcRegs_find; expr_equalities; try tauto; try discriminate.
        Transparent evalExpr.
        * match goal with
          | [ H : ?x = opLd, H' : ?y = opNm |- _ ] => replace x with y in H by reflexivity; rewrite H' in H
          end.
          discriminate.
        * match goal with
          | [ Hdst : evalExpr #(evalExpr (rv32iGetDst _ _))%kami_expr <> _, Hopty : _ = rv32iOpBRANCH |- _ ] => unfold rv32iGetDst in Hdst; evex Hdst; rewrite Hopty in Hdst
          end.
          tauto.
        * apply substepsComb_substepsInd in HSubsteps0.
          apply SCProcSubsteps in HSubsteps0.
          intuition idtac; shatter;
            match goal with
            | [ H : foldSSLabel ss0 = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss0)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
            | [ H : foldSSLabel ss0 = _, H1 : annot (hide (foldSSLabel ss0)) = None -> False, H2 : annot (hide (foldSSLabel ss0)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
            end.
          match goal with
          | [ H : In _ _ |- _ ] => simpl in H
          end.
          Opaque evalExpr.
          intuition idtac; kinv_action_dest; SCProcRegs_find;
            expr_equalities;
            try tauto;
            try match goal with
                | [ H : ?x = ?y, H' : ?x = ?z |- _ ] => rewrite H' in H; discriminate H
                end.
          Transparent evalExpr.
          f_equal.
          Opaque evalExpr.
          match goal with
          | [ H : hasTrace _ _ _ _ (_ :: _) |- _ ] => inversion H; clear H
          end.
          Transparent evalExpr.
          subst.
          match goal with
          | [ Hht1 : hasTrace _ _ ?pc1 _ ?tr1, Hht2 : hasTrace _ _ ?pc2 _ ?tr2, Hct : censorTrace ?tr1 = censorTrace ?tr2 |- _ ] => assert (tr1 = nil /\ tr2 = nil \/ pc1 = pc2) by (eapply censorEq_same_pc; eassumption)
          end.
          intuition idtac; subst;
            try (repeat match goal with
                        | [ H : relatedTrace nil _ |- _ ] => inversion H; clear H
                        end; reflexivity).
          match goal with
          | [ IH : context[censorLabelSeq _ _ = censorLabelSeq _ _] |- _ ] => eapply IH
          end;
            try match goal with
                | [ HBFM : ForwardMultistep _ ?r1 _ ?l |- ForwardMultistep _ ?r2 _ ?l ] =>
                  replace r2 with r1; try eassumption
                | [ |- censorTrace _ = censorTrace _ ] => eassumption
                | [ |- relatedTrace _ _ ] => eassumption
                end.
          -- match goal with
             | [ Hht : hasTrace _ _ ?pc1 _ ?t |- hasTrace _ _ ?pc2 _ ?t ] => replace pc2 with pc1 by congruence; eassumption
             end.
          -- match goal with
             | [ H : foldSSUpds ss0 = _ |- _ ] => rewrite H
             end.
             unfold SCProcRegs; clear; eauto.
          -- Opaque evalExpr.
             match goal with
             | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => clear - H; inversion H
             end.
             simpl in *.
             Transparent evalExpr.
             subst.
             assumption.
          -- match goal with
             | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
             end.
             match goal with
             | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) _ = SCProcRegs _ _ ?p2 ] => unfold SCProcRegs; replace p1 with p2 by congruence
             end.
             clear; eauto.
          -- Opaque evalExpr.
             match goal with
             | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => clear - H; inversion H
             end.
             simpl in *.
             Transparent evalExpr.
             subst.
             assumption.
      + match goal with
        | [ Hct : censorTrace (Branch _ _ :: _) = censorTrace ?tr |- _ ] =>
          let t := fresh in
          destruct tr as [|t tr];
            simpl in Hct;
            try destruct t;
            try congruence;
            inversion Hct;
            clear Hct;
            opaque_subst
        end.
        match goal with
        | [ Hrt1 : relatedTrace (_ :: _) ?l1, Hrt2 : relatedTrace (_ :: _) ?l2 |- _ ] => destruct l1; destruct l2; inversion Hrt1; inversion Hrt2; clear Hrt1; clear Hrt2
        end.
        opaque_subst.
        simpl.
        repeat match goal with
               | [ Hbm : ForwardMultistep _ _ _ (?lbl :: _) |- _ ] =>
                 inversion Hbm;
                   clear Hbm;
                   match goal with
                   | [ Hst : Step _ _ _ lbl |- _ ] =>
                     inversion Hst;
                       clear Hst
                   end
               end.
        opaque_subst.
        apply substepsComb_substepsInd in HSubsteps.
        apply SCProcSubsteps in HSubsteps.
        intuition idtac; shatter;
          match goal with
          | [ H : foldSSLabel ss = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
          | [ H : foldSSLabel ss = _, H1 : annot (hide (foldSSLabel ss)) = None -> False, H2 : annot (hide (foldSSLabel ss)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
          end.
        match goal with
        | [ H : In _ _ |- _ ] => simpl in H
        end.
        Opaque evalExpr.
        intuition idtac; kinv_action_dest; SCProcRegs_find; expr_equalities; try tauto; try discriminate.
        Transparent evalExpr.
        * match goal with
          | [ H : ?x = opLd, H' : ?y = opNm |- _ ] => replace x with y in H by reflexivity; rewrite H' in H
          end.
          discriminate.
        * match goal with
          | [ Hdst : evalExpr #(evalExpr (rv32iGetDst _ _))%kami_expr <> _, Hopty : _ = rv32iOpBRANCH |- _ ] => unfold rv32iGetDst in Hdst; evex Hdst; rewrite Hopty in Hdst
          end.
          tauto.
        * apply substepsComb_substepsInd in HSubsteps0.
          apply SCProcSubsteps in HSubsteps0.
          intuition idtac; shatter;
            match goal with
            | [ H : foldSSLabel ss0 = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss0)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
            | [ H : foldSSLabel ss0 = _, H1 : annot (hide (foldSSLabel ss0)) = None -> False, H2 : annot (hide (foldSSLabel ss0)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
            end.
          match goal with
          | [ H : In _ _ |- _ ] => simpl in H
          end.
          Opaque evalExpr.
          intuition idtac; kinv_action_dest; SCProcRegs_find;
            expr_equalities;
            try tauto;
            try match goal with
                | [ H : ?x = ?y, H' : ?x = ?z |- _ ] => rewrite H' in H; discriminate H
                end.
          Transparent evalExpr.
          f_equal.
          Opaque evalExpr.
          match goal with
          | [ H : hasTrace _ _ _ _ (_ :: _) |- _ ] => inversion H; clear H
          end.
          Transparent evalExpr.
          subst.
          match goal with
          | [ Hht1 : hasTrace _ _ ?pc1 _ ?tr1, Hht2 : hasTrace _ _ ?pc2 _ ?tr2, Hct : censorTrace ?tr1 = censorTrace ?tr2 |- _ ] => assert (tr1 = nil /\ tr2 = nil \/ pc1 = pc2) by (eapply censorEq_same_pc; eassumption)
          end.
          intuition idtac; subst;
            try (repeat match goal with
                        | [ H : relatedTrace nil _ |- _ ] => inversion H; clear H
                        end; reflexivity).
          match goal with
          | [ IH : context[censorLabelSeq _ _ = censorLabelSeq _ _] |- _ ] => eapply IH
          end;
            try match goal with
                | [ HBFM : ForwardMultistep _ ?r1 _ ?l |- ForwardMultistep _ ?r2 _ ?l ] =>
                  replace r2 with r1; try eassumption
                | [ |- censorTrace _ = censorTrace _ ] => eassumption
                | [ |- relatedTrace _ _ ] => eassumption
                end.
          -- match goal with
             | [ Hht : hasTrace _ _ ?pc1 _ ?t |- hasTrace _ _ ?pc2 _ ?t ] => replace pc2 with pc1 by congruence; eassumption
             end.
          -- match goal with
             | [ H : foldSSUpds ss0 = _ |- _ ] => rewrite H
             end.
             unfold SCProcRegs; clear; eauto.
          -- Opaque evalExpr.
             match goal with
             | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => clear - H; inversion H
             end.
             simpl in *.
             Transparent evalExpr.
             subst.
             assumption.
          -- match goal with
             | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
             end.
             match goal with
             | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) _ = SCProcRegs _ _ ?p2 ] => unfold SCProcRegs; replace p1 with p2 by congruence
             end.
             clear; eauto.
          -- Opaque evalExpr.
             match goal with
             | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => clear - H; inversion H
             end.
             simpl in *.
             Transparent evalExpr.
             subst.
             assumption.
    - match goal with
      | [ Hct : censorTrace (Nm _ :: _) = censorTrace ?tr |- _ ] =>
        let t := fresh in
        destruct tr as [|t tr];
          simpl in Hct;
          try destruct t;
          try congruence;
          inversion Hct;
          clear Hct;
          opaque_subst
      end.
      match goal with
      | [ Hrt1 : relatedTrace (_ :: _) ?l1, Hrt2 : relatedTrace (_ :: _) ?l2 |- _ ] => destruct l1; destruct l2; inversion Hrt1; inversion Hrt2; clear Hrt1; clear Hrt2
      end.
      opaque_subst.
      simpl.
      repeat match goal with
             | [ Hbm : ForwardMultistep _ _ _ (?lbl :: _) |- _ ] =>
               inversion Hbm;
                 clear Hbm;
                 match goal with
                 | [ Hst : Step _ _ _ lbl |- _ ] =>
                   inversion Hst;
                     clear Hst
                 end
             end.
      opaque_subst.
      apply substepsComb_substepsInd in HSubsteps.
      apply SCProcSubsteps in HSubsteps.
      intuition idtac; shatter;
        match goal with
        | [ H : foldSSLabel ss = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
        | [ H : foldSSLabel ss = _, H1 : annot (hide (foldSSLabel ss)) = None -> False, H2 : annot (hide (foldSSLabel ss)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
        end.
      match goal with
      | [ H : In _ _ |- _ ] => simpl in H
      end.
      Opaque evalExpr.
      intuition idtac; kinv_action_dest; SCProcRegs_find; expr_equalities; try tauto; try discriminate.
      Transparent evalExpr.
      + match goal with
        | [ H : ?x = opLd, H' : ?y = opNm |- _ ] => replace x with y in H by reflexivity; rewrite H' in H
        end.
        discriminate.
      + apply substepsComb_substepsInd in HSubsteps0.
        apply SCProcSubsteps in HSubsteps0.
        intuition idtac; shatter;
          match goal with
          | [ H : foldSSLabel ss0 = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss0)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
          | [ H : foldSSLabel ss0 = _, H1 : annot (hide (foldSSLabel ss0)) = None -> False, H2 : annot (hide (foldSSLabel ss0)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
          end.
        match goal with
        | [ H : In _ _ |- _ ] => simpl in H
        end.
        Opaque evalExpr.
        intuition idtac; kinv_action_dest; SCProcRegs_find;
          expr_equalities;
          try tauto;
          try match goal with
              | [ H : ?x = ?y, H' : ?x = ?z |- _ ] => rewrite H' in H; discriminate H
              end.
        Transparent evalExpr.
        f_equal.
        Opaque evalExpr.
        match goal with
        | [ H : hasTrace _ _ _ _ (_ :: _) |- _ ] => inversion H; clear H
        end.
        Transparent evalExpr.
        subst.
        match goal with
        | [ Hht1 : hasTrace _ _ ?pc1 _ ?tr1, Hht2 : hasTrace _ _ ?pc2 _ ?tr2, Hct : censorTrace ?tr1 = censorTrace ?tr2 |- _ ] => assert (tr1 = nil /\ tr2 = nil \/ pc1 = pc2) by (eapply censorEq_same_pc; eassumption)
        end.
        intuition idtac; subst;
          try (repeat match goal with
                      | [ H : relatedTrace nil _ |- _ ] => inversion H; clear H
                      end; reflexivity).
        match goal with
        | [ IH : context[censorLabelSeq _ _ = censorLabelSeq _ _] |- _ ] => eapply IH
        end;
          try match goal with
              | [ HBFM : ForwardMultistep _ ?r1 _ ?l |- ForwardMultistep _ ?r2 _ ?l ] =>
                replace r2 with r1; try eassumption
              | [ |- censorTrace _ = censorTrace _ ] => eassumption
              | [ |- relatedTrace _ _ ] => eassumption
              end.
        * match goal with
          | [ Hht : hasTrace _ _ ?pc1 _ ?t |- hasTrace _ _ ?pc2 _ ?t ] => replace pc2 with pc1 by congruence; eassumption
          end.
        * match goal with
          | [ H : foldSSUpds ss0 = _ |- _ ] => rewrite H
          end.
          match goal with
          | [ |- FMap.M.union (FMap.M.add "rf" (existT _ _ ?r1) (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _))) _ = SCProcRegs ?r2 _ ?p2 ] => unfold SCProcRegs; replace r1 with r2
          end.
          -- clear; eauto.
          -- unfold rset.
             destruct (weq dst (wzero _)); tauto.
        * Opaque evalExpr.
          match goal with
          | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => clear - H; inversion H
          end.
          simpl in *.
          Transparent evalExpr.
          subst.
          assumption.
        * match goal with
          | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
          end.
          match goal with
          | [ |- FMap.M.union (FMap.M.add "rf" (existT _ _ ?r1) (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _))) _ = SCProcRegs ?r2 _ ?p2 ] => unfold SCProcRegs; replace r1 with r2; [ replace p1 with p2 by congruence | idtac ]
          end.
          -- clear; eauto.
          -- unfold rset.
             destruct (weq dst0 (wzero _)); try tauto.
        * Opaque evalExpr.
          match goal with
          | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => clear - H; inversion H
          end.
          simpl in *.
          Transparent evalExpr.
          subst.
          assumption.
      + apply substepsComb_substepsInd in HSubsteps0.
        apply SCProcSubsteps in HSubsteps0.
        intuition idtac; shatter;
          match goal with
          | [ H : foldSSLabel ss0 = _, Hltt : labelToTraceEvent (hide (foldSSLabel ss0)) = Some _ |- _ ] => rewrite H in *; try solve [simpl in Hltt; discriminate]
          | [ H : foldSSLabel ss0 = _, H1 : annot (hide (foldSSLabel ss0)) = None -> False, H2 : annot (hide (foldSSLabel ss0)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
          end.
        match goal with
        | [ H : In _ _ |- _ ] => simpl in H
        end.
        Opaque evalExpr.
        intuition idtac; kinv_action_dest; SCProcRegs_find;
          expr_equalities;
          try tauto;
          try match goal with
              | [ H : ?x = ?y, H' : ?x = ?z |- _ ] => rewrite H' in H; discriminate H
              end.
        Transparent evalExpr.
        f_equal.
        Opaque evalExpr.
        match goal with
        | [ H : hasTrace _ _ _ _ (_ :: _) |- _ ] => inversion H; clear H
        end.
        Transparent evalExpr.
        subst.
        match goal with
        | [ Hht1 : hasTrace _ _ ?pc1 _ ?tr1, Hht2 : hasTrace _ _ ?pc2 _ ?tr2, Hct : censorTrace ?tr1 = censorTrace ?tr2 |- _ ] => assert (tr1 = nil /\ tr2 = nil \/ pc1 = pc2) by (eapply censorEq_same_pc; eassumption)
        end.
        intuition idtac; subst;
          try (repeat match goal with
                      | [ H : relatedTrace nil _ |- _ ] => inversion H; clear H
                      end; reflexivity).
        match goal with
        | [ IH : context[censorLabelSeq _ _ = censorLabelSeq _ _] |- _ ] => eapply IH
        end;
          try match goal with
              | [ HBFM : ForwardMultistep _ ?r1 _ ?l |- ForwardMultistep _ ?r2 _ ?l ] =>
                replace r2 with r1; try eassumption
              | [ |- censorTrace _ = censorTrace _ ] => eassumption
              | [ |- relatedTrace _ _ ] => eassumption
              end.
        * match goal with
          | [ Hht : hasTrace _ _ ?pc1 _ ?t |- hasTrace _ _ ?pc2 _ ?t ] => replace pc2 with pc1 by congruence; eassumption
          end.
        * match goal with
          | [ H : foldSSUpds ss0 = _ |- _ ] => rewrite H
          end.
          match goal with
          | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) (SCProcRegs ?r1 _ _) = SCProcRegs ?r2 _ ?p2 ] => unfold SCProcRegs; replace r2 with r1
          end.
          -- clear; eauto.
          -- unfold rset.
             destruct (weq dst (wzero _)); tauto.
        * Opaque evalExpr.
          match goal with
          | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => clear - H; inversion H
          end.
          simpl in *.
          Transparent evalExpr.
          subst.
          assumption.
        * match goal with
          | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
          end.
          match goal with
          | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) (SCProcRegs ?r1 _ _) = SCProcRegs ?r2 _ ?p2 ] => unfold SCProcRegs; replace r2 with r1; [ replace p1 with p2 by congruence | idtac ]
          end.
          -- clear; eauto.
          -- unfold rset.
             destruct (weq dst0 (wzero _)); try tauto.
        * Opaque evalExpr.
          match goal with
          | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => clear - H; inversion H
          end.
          simpl in *.
          Transparent evalExpr.
          subst.
          assumption.
  Qed.

  Lemma eval_const : forall n (t : Expr type (SyntaxKind (Bit n))) c, evalExpr t = c -> evalExpr (t == (Const _ (ConstBit c)))%kami_expr = true.
    simpl.
    intros.
    rewrite H.
    destruct (weq c c); tauto.
  Qed.

  Lemma abstractToSCRelated :
    forall rf pm pc mem trace,
      hasTrace rf pm pc mem trace ->
      exists newRegs ls,
        ForwardMultistep p (SCProcRegs rf pm pc) newRegs ls /\
        SCProcMemConsistent ls mem /\
        relatedTrace trace ls.
  Proof.
    induction 1.
    - repeat eexists; repeat econstructor.
    - shatter.
      repeat eexists.
      + eapply FMulti.
        * apply SemFacts.substepZero_imp_step.
          -- reflexivity.
          -- eapply EmptyRule.
        * match goal with
          | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
          end.
          eauto.
      + econstructor; try eassumption.
        simplify_match.
        reflexivity.
      + constructor; eauto.
    - shatter.
      repeat eexists.
      + eapply FMulti.
        * apply SemFacts.substepZero_imp_step.
          -- reflexivity.
          -- eapply SingleRule.
             ++ instantiate (2 := "execLd").
                simpl.
                tauto.
             ++ repeat match goal with
                       | [ |- SemAction _ (MCall _ _ _ _) _ _ _ ] => fail 1
                       | _ => econstructor
                       end; try FMap.findeq.
                ** match goal with
                   | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                     replace x with (pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                       subst;
                       rewrite eval_const;
                       tauto
                   end.
                ** unfold evalExpr; fold evalExpr.
                   unfold evalUniBool.
                   rewrite Bool.negb_true_iff.
                   unfold isEq.
                   match goal with
                   | |- (if ?b then _ else _) = _ => destruct b
                   end.
                   --- subst. tauto.
                   --- reflexivity.
                ** eapply SemMCall.
                   --- instantiate (1 := FMap.M.empty _).
                       FMap.findeq.
                   --- instantiate (1 := evalExpr (STRUCT { "data" ::= #val })%kami_expr).
                       reflexivity.
                   --- repeat econstructor; try FMap.findeq.
        * match goal with
          | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
          end.
          unfold SCProcRegs, rset.
          eauto.
      + econstructor; try eassumption.
        simplify_match.
        split; try reflexivity.
        match goal with
        | [ |- mem ?a = ?v ] => replace v with val by reflexivity;
                                replace a with laddr_aligned
        end; try congruence.
        unfold laddr_aligned, laddr, addr, srcVal, srcIdx.
        subst.
        reflexivity.
      + constructor; try assumption.
        unfold labelToTraceEvent, getLabel.
        unfold callsToTraceEvent.
        simplify_match.
        unfold evalExpr.
        match goal with
        | [ |- Some (Rd $ (0) ?x1 ?y1) = Some (Rd $ (0) ?x2 ?y2) ] => replace x1 with x2; [ reflexivity | idtac ]
        end.
        match goal with
        | [ |- context[icons' ("addr" ::= ?x)%init _] ] => replace laddr_aligned with (evalExpr x)%kami_expr; [ reflexivity | idtac ] 
        end.
        subst.
        repeat match goal with
               | [ x : fullType type _ |- _ ] =>
                 progress unfold x
               | [ x : word _ |- _ ] =>
                 progress unfold x
               end.
        unfold evalExpr.
        reflexivity.
    - shatter.
      repeat eexists.
      + eapply FMulti.
        * apply SemFacts.substepZero_imp_step.
          -- reflexivity.
          -- eapply SingleRule.
             ++ instantiate (2 := "execLdZ").
                simpl.
                tauto.
             ++ repeat econstructor; try FMap.findeq.
                ** match goal with
                   | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                     replace x with (pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                       subst;
                       rewrite eval_const;
                       tauto
                   end.
                ** unfold evalExpr; fold evalExpr.
                   unfold evalUniBool.
                   unfold isEq.
                   match goal with
                   | |- (if ?b then _ else _) = _ => destruct b
                   end.
                   --- reflexivity.
                   --- subst. tauto.
        * match goal with
          | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
          end.
          unfold SCProcRegs, rset.
          eauto.
      + econstructor; try eassumption.
        simplify_match.
        reflexivity.
      + constructor; (eauto || discriminate).
    - shatter.
      repeat eexists.
      + eapply FMulti.
        * apply SemFacts.substepZero_imp_step.
          -- reflexivity.
          -- eapply SingleRule.
             ++ instantiate (2 := "execSt").
                simpl.
                tauto.
             ++ repeat econstructor; try FMap.findeq. 
                ** match goal with
                   | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                     replace x with (pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                       subst;
                       rewrite eval_const;
                       tauto
                   end.
        * match goal with
          | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
          end.
          unfold SCProcRegs.
          eauto.
      + econstructor; try eassumption.
        simplify_match.
        intuition idtac.
        match goal with
        | [ |- (fun _ => if weq _ ?a then ?v else _) = (fun _ => if weq _ ?a' then ?v' else _) ] => replace a' with a; [replace v' with v; [reflexivity|]|]
        end.
        * unfold stVal, vsrcIdx.
          subst.
          reflexivity.
        * unfold saddr_aligned, saddr, addr, srcVal, srcIdx.
          subst.
          reflexivity.
      + constructor; try assumption.
        unfold labelToTraceEvent, getLabel.
        unfold callsToTraceEvent.
        simplify_match.
        unfold evalExpr.
        match goal with
        | [ |- Some (Wr $ (0) ?x1 ?y1) = Some (Wr $ (0) ?x2 ?y2) ] => replace x1 with x2; [ replace y1 with y2; [ reflexivity | idtac ] | idtac ]
        end.
        * match goal with
          | [ |- context[icons' ("data" ::= ?x)%init _] ] => replace stVal with (evalExpr x)%kami_expr; [ reflexivity | idtac ] 
          end.
          subst.
          unfold evalExpr.
          repeat match goal with
                 | [ x : fullType type _ |- _ ] =>
                   progress unfold x
                 | [ x : word _ |- _ ] =>
                   progress unfold x
                 end.
          reflexivity.
        * match goal with
          | [ |- context[icons' ("addr" ::= ?x)%init _] ] => replace saddr_aligned with (evalExpr x)%kami_expr; [ reflexivity | idtac ] 
          end.
          subst.
          repeat match goal with
                 | [ x : fullType type _ |- _ ] =>
                   progress unfold x
                 | [ x : word _ |- _ ] =>
                   progress unfold x
                 end.
          unfold evalExpr.
          reflexivity.
    - shatter.
      repeat eexists.
      + eapply FMulti.
        * apply SemFacts.substepZero_imp_step.
          -- reflexivity.
          -- eapply SingleRule.
             ++ instantiate (2 := "execToHost").
                simpl.
                tauto.
             ++ repeat econstructor; try FMap.findeq.
                ** match goal with
                   | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                     replace x with (pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                       subst;
                       rewrite eval_const;
                       tauto
                   end.
        * match goal with
          | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
          end.
          unfold SCProcRegs.
          eauto.
      + econstructor; try eassumption.
        simplify_match.
        reflexivity.
      + constructor; try assumption.
        unfold labelToTraceEvent, getLabel.
        unfold callsToTraceEvent.
        simplify_match.
        unfold evalExpr; fold evalExpr.
        match goal with
        | [ |- Some (ToHost $ (0) ?x1) = Some (ToHost $ (0) ?x2) ] => replace x1 with x2; [ reflexivity | idtac ]
        end.
        subst.
        repeat match goal with
               | [ x : fullType type _ |- _ ] =>
                 progress unfold x
               | [ x : word _ |- _ ] =>
                 progress unfold x
               end.
          reflexivity.
    - shatter.
      destruct (isEq (Bit rv32iRfIdx)
                     dst
                     (wzero _)).
      + repeat eexists.
        * eapply FMulti.
          -- apply SemFacts.substepZero_imp_step.
             ++ reflexivity.
             ++ eapply SingleRule.
                ** instantiate (2 := "execFromHostZ").
                   simpl.
                   tauto.
                ** repeat econstructor; try FMap.findeq.
                   --- match goal with
                       | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                         replace x with (pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                           subst;
                           rewrite eval_const;
                           tauto
                       end.
                   --- unfold evalExpr; fold evalExpr.
                       unfold isEq.
                       match goal with
                       | |- (if ?b then _ else _) = _ => destruct b
                       end.
                       +++ reflexivity.
                       +++ unfold dst in e.
                           subst.
                           tauto.
          -- match goal with
             | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
             end.
             unfold SCProcRegs, rset.
             eauto.
        * econstructor; try eassumption.
          simplify_match.
          reflexivity.
        * constructor; try assumption.
          reflexivity.
      + repeat eexists.
        * eapply FMulti.
          -- apply SemFacts.substepZero_imp_step.
             ++ reflexivity.
             ++ eapply SingleRule.
                ** instantiate (2 := "execFromHost").
                   simpl.
                   tauto.
                ** repeat match goal with
                          | [ |- SemAction _ (MCall _ _ _ _) _ _ _ ] => fail 1
                          | _ => econstructor
                          end; try FMap.findeq.
                   --- match goal with
                       | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                         replace x with (pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                           subst;
                           rewrite eval_const;
                           tauto
                       end.
                   --- unfold evalExpr; fold evalExpr.
                       unfold evalUniBool.
                       unfold isEq.
                       rewrite Bool.negb_true_iff.
                       match goal with
                       | |- (if ?b then _ else _) = _ => destruct b
                       end.
                       +++ unfold dst in n.
                           subst.
                           tauto.
                       +++ reflexivity.
                   --- eapply SemMCall.
                       +++ instantiate (1 := FMap.M.empty _).
                           FMap.findeq.
                       +++ instantiate (1 := val).
                           reflexivity.
                       +++ repeat econstructor; FMap.findeq.
          -- match goal with
             | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
             end.
             unfold SCProcRegs, rset.
             eauto.
        * econstructor; try eassumption.
          simplify_match.
          reflexivity.
        * constructor; try assumption.
          reflexivity.
    - shatter.
      repeat eexists.
      + eapply FMulti.
        * apply SemFacts.substepZero_imp_step.
          -- reflexivity.
          -- eapply SingleRule.
             ++ instantiate (2 := "execNmZ").
                simpl.
                tauto.
             ++ repeat econstructor; try FMap.findeq.
                ** match goal with
                   | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                     let Heq := fresh in
                     replace x with (pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                       subst;
                       rewrite eval_const;
                       tauto
                   end.
                ** unfold rv32iGetDst.
                   unfold evalExpr; fold evalExpr.
                   subst.
                   match goal with
                   | [ H : evalExpr (getOpcodeE _) = _ |- context[evalExpr (getOpcodeE _)] ] => rewrite H
                   end.
                   simpl.
                   reflexivity.
        * match goal with
          | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
          end.
          unfold SCProcRegs, rset.
          eauto.
      + econstructor; try eassumption.
        simplify_match.
        reflexivity.
      + constructor; (eauto || discriminate).
    - shatter.
      destruct (isEq (Bit rv32iRfIdx)
                     dst
                     (wzero _)).
      + repeat eexists.
        * eapply FMulti.
          -- apply SemFacts.substepZero_imp_step.
             ++ reflexivity.
             ++ eapply SingleRule.
                ** instantiate (2 := "execNmZ").
                   simpl.
                   tauto.
                ** repeat econstructor; try FMap.findeq.
                   --- match goal with
                       | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                         replace x with (pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                           subst;
                           rewrite eval_const;
                           tauto
                       end.
                   --- unfold evalExpr; fold evalExpr.
                       unfold isEq.
                       match goal with
                       | |- (if ?b then _ else _) = _ => destruct b
                       end.
                       +++ reflexivity.
                       +++ unfold dst in e.
                           subst.
                           tauto.
          -- match goal with
             | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
             end.
             unfold SCProcRegs, rset.
             eauto.
        * econstructor; try eassumption.
          simplify_match.
          reflexivity.
        * constructor; (eauto || discriminate).
      + repeat eexists.
        * eapply FMulti.
          -- apply SemFacts.substepZero_imp_step.
             ++ reflexivity.
             ++ eapply SingleRule.
                ** instantiate (2 := "execNm").
                   simpl.
                   tauto.
                ** repeat econstructor; try FMap.findeq.
                   --- match goal with
                       | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                         replace x with (pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                           subst;
                           rewrite eval_const;
                           tauto
                       end.
                   --- unfold evalExpr; fold evalExpr.
                       unfold evalUniBool.
                       unfold isEq.
                       rewrite Bool.negb_true_iff.
                       match goal with
                       | |- (if ?b then _ else _) = _ => destruct b
                       end.
                       +++ unfold dst in n.
                           subst.
                           tauto.
                       +++ reflexivity.
          -- match goal with
             | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
             end.
             unfold SCProcRegs, rset.
             eauto.
        * econstructor; try eassumption.
          simplify_match.
          reflexivity.
        * constructor; (eauto || discriminate).
          Unshelve.
          -- exact (evalExpr (STRUCT { "data" ::= $0 }))%kami_expr.
          -- exact (wzero _).
  Qed.

  Definition getrf (regs : RegsT) : regfile :=
    match FMap.M.find "rf" regs with
    | Some (existT _
                   (SyntaxKind (Vector (Bit 32) 5))
                   rf) => rf
    | _ => (fun _ => wzero _)
    end.

  Definition getpm (regs : RegsT) : progMem :=
    match FMap.M.find "pgm" regs with
    | Some (existT _
                   (SyntaxKind (Vector (Bit 32) 8))
                   pm) => pm
    | _ => (fun _ => wzero _)
    end.

  Definition getpc (regs : RegsT) : word 16 :=
    match FMap.M.find "pc" regs with
    | Some (existT _
                   (SyntaxKind (Bit 16))
                   pc) => pc
    | _ => (wzero _)
    end.

  Lemma SCToAbstractRelated :
    forall rf pm pc mem newRegs ls,
      ForwardMultistep p (SCProcRegs rf pm pc) newRegs ls ->
      SCProcMemConsistent ls mem ->
      exists trace,
        hasTrace rf pm pc mem trace /\
        relatedTrace trace ls.
  Proof.
    intros rf pm pc mem newRegs ls Hfm Hmem.
    let Heq := fresh in
    remember (SCProcRegs rf pm pc) as regs eqn:Heq; unfold SCProcRegs in Heq;
      replace rf with (getrf regs) by (subst; FMap.findeq);
      replace pm with (getpm regs) by (subst; FMap.findeq);
      replace pc with (getpc regs) by (subst; FMap.findeq);
      clear rf pm pc Heq.
    generalize mem Hmem.
    clear mem Hmem.
    induction Hfm.
    - eexists; repeat econstructor.
    - intros.
      match goal with
      | [ H : Step _ _ _ _ |- _ ] => destruct H
      end.
      apply substepsComb_substepsInd in HSubsteps.
      apply SCProcSubsteps in HSubsteps.
      intuition idtac; shatter;
        match goal with
        | [ Hle : foldSSLabel ss = _, Hue : foldSSUpds ss = _ |- _ ] => rewrite Hle in *; rewrite Hue in *
        end; try tauto.
      + match goal with
        | [ H : SCProcMemConsistent (_ :: _) _ |- _ ] => inversion H
        end.
        simpl in *.
        subst.
        match goal with
        | [ H : SCProcMemConsistent ?a ?m,
                IH : forall _, SCProcMemConsistent ?a _ -> _
                          |- _ ] => specialize (IH m H)
        end.
        shatter.
        match goal with
        | [ H : relatedTrace ?t ?ls |- exists _, hasTrace _ _ ?p _ _ /\ relatedTrace _ (_ :: ?ls) ] => exists (Nop p :: t)
        end.
        split.
        * constructor.
          match goal with
          | [ H : hasTrace ?r ?m ?p _ _ |- hasTrace ?r' ?m' ?p' _ _ ] => replace r' with r by reflexivity; replace m' with m by reflexivity; replace p' with p by reflexivity; assumption
          end.
        * constructor; eauto.
      + match goal with
        | [ H : SCProcMemConsistent (_ :: _) _ |- _ ] => inversion H
        end.
        simpl in *.
        subst.
        match goal with
        | [ H : SCProcMemConsistent ?a ?m,
                IH : forall _, SCProcMemConsistent ?a _ -> _
                          |- _ ] => specialize (IH m H)
        end.
        shatter.
        match goal with
        | [ H : relatedTrace ?t ?ls |- exists _, hasTrace _ _ ?p _ _ /\ relatedTrace _ (_ :: ?ls) ] => exists (Nop p :: t)
        end.
        split.
        * constructor.
          match goal with
          | [ H : hasTrace ?r ?m ?p _ _ |- hasTrace ?r' ?m' ?p' _ _ ] => replace r' with r by reflexivity; replace m' with m by reflexivity; replace p' with p by reflexivity; assumption
          end.
        * constructor; eauto.
      + Opaque evalExpr.
        match goal with
        | [ HIn : In (_ :: _)%struct (getRules _) |- _ ] => simpl in HIn; intuition idtac
        end;
          match goal with
          | [ Heq : _ = (_ :: _)%struct |- _ ] =>
            inversion Heq; clear Heq
          end; subst;
            kinv_action_dest;
            match goal with
            | [ Hpc : FMap.M.find "pc" o = Some (existT _ _ ?pc),
                      Hrf : FMap.M.find "rf" o = Some (existT _ _ ?rf),
                            Hpm : FMap.M.find "pgm" o = Some (existT _ _ ?pm)
                |- _ ] =>
              replace (getpc o) with pc by (unfold getpc; FMap.findeq);
                replace (getrf o) with rf by (unfold getrf; FMap.findeq);
                replace (getpm o) with pm by (unfold getpm; FMap.findeq)
            end.
        Transparent evalExpr.
        * Opaque evalExpr.
          match goal with
          | [ H : SCProcMemConsistent (_ :: _) _ |- _ ] => inversion H
          end.
          subst.
          simpl in *.
          Transparent evalExpr.
          match goal with
          | [ H : if ?x then _ else _ |- _ ] =>
            replace x with false in H by reflexivity
          end.
          shatter.
          subst.
          match goal with
          | [ H : SCProcMemConsistent ?a ?m,
                  IH : forall _, SCProcMemConsistent ?a _ -> _
                            |- _ ] => specialize (IH m H)
          end.
          shatter.
          eexists.
          split.
          -- apply htLd.
             ++ reflexivity.
             ++ match goal with
                | [ H : context[rv32iGetOptype] |- _ ] =>
                  evex H
                end.
                boolex.
                assumption.
             ++ match goal with
                | [ H : context[rv32iGetLdDst] |- _ ] =>
                  evex H
                end.
                boolex.
                assumption.
             ++ reflexivity.
             ++ match goal with
                | [ Hht : hasTrace ?x1 ?x2 ?x3 _ _ |- hasTrace ?y1 ?y2 ?y3 _ _ ] =>
                  let Heq := fresh in
                  assert (x1 = y1) as Heq;
                    [ idtac |
                      rewrite Heq in Hht;
                      clear Heq;
                      assert (x2 = y2) as Heq;
                      [ idtac |
                        rewrite Heq in Hht;
                        clear Heq;
                        assert (x3 = y3) as Heq;
                        [ idtac |
                          rewrite Heq in Hht;
                          clear Heq;
                          eassumption
                        ]
                      ]
                    ]
                end.
                ** match goal with
                   | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
                   end.
                   unfold getrf.
                   FMap.findeq.
                   simplify_match.
                   match goal with
                   | [ H : mem _ = ?x' |- evalExpr ?v @[ ?i <- ?x ]%kami_expr = _ ] => replace (evalExpr v @[ i <- x]%kami_expr) with (evalExpr v @[ i <- #(x')]%kami_expr) by reflexivity; rewrite <- H
                   end.
                   match goal with
                   | [ |- evalExpr (# (x0)) @[ #(?i) <- #(?v)]%kami_expr = rset x0 ?i' ?v' ] => replace i with i' by reflexivity; replace v with v' by reflexivity
                   end.
                   apply functional_extensionality.
                   intros.
                   unfold rset.
                   match goal  with
                   | [ H : context[(#(evalExpr (rv32iGetLdDst _ _)) == _)%kami_expr] |- _ ] => evex H
                   end.
                   boolex.
                   match goal with
                   | [ |- _ = (if ?eq then _ else _) _ ] => destruct eq; tauto
                   end.
                ** match goal with
                   | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
                   end.
                   unfold getpm.
                   FMap.findeq.
                ** match goal with
                   | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
                   end.
                   unfold getpc.
                   FMap.findeq.
          -- constructor; try assumption.
             unfold labelToTraceEvent, callsToTraceEvent.
             simplify_match.
             match goal with
             | [ H : mem _ = ?x |- Some (Rd _ ?a ?v) = Some (Rd _ ?a' ?v') ] => replace v with x by reflexivity; rewrite <- H
             end.
             reflexivity.
        * Opaque evalExpr.
          match goal with
          | [ H : SCProcMemConsistent (_ :: _) _ |- _ ] => inversion H
          end.
          subst.
          simpl in *.
          Transparent evalExpr.
          subst.
          match goal with
          | [ H : SCProcMemConsistent ?a ?m,
                  IH : forall _, SCProcMemConsistent ?a _ -> _
                            |- _ ] => specialize (IH m H)
          end.
          shatter.
          eexists.
          split.
          -- eapply htLdZ.
             ++ reflexivity.
             ++ match goal with
                | [ H : context[rv32iGetOptype] |- _ ] =>
                  evex H
                end.
                boolex.
                assumption.
             ++ match goal with
                | [ H : context[rv32iGetLdDst] |- _ ] =>
                  evex H
                end.
                boolex.
                assumption.
             ++ match goal with
                | [ Hfu : foldSSUpds ss = _,
                          Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
                  replace (getrf o') with x1 in Hht by (rewrite Hfu; unfold getrf; FMap.findeq);
                    replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                    replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                    eassumption
                end.
          -- constructor; (eauto || discriminate).
        * Opaque evalExpr.
          match goal with
          | [ H : SCProcMemConsistent (_ :: _) _ |- _ ] => inversion H
          end.
          subst.
          simpl in *.
          Transparent evalExpr.
          match goal with
          | [ H : if ?x then _ else _ |- _ ] =>
            replace x with true in H by reflexivity
          end.
          subst.
          match goal with
          | [ H : SCProcMemConsistent ?a ?m,
                  IH : forall _, SCProcMemConsistent ?a _ -> _
                            |- _ ] => specialize (IH m H)
          end.
          shatter.
          eexists.
          split.
          -- eapply htSt.
             ++ reflexivity.
             ++ match goal with
                | [ H : context[rv32iGetOptype] |- _ ] =>
                  evex H
                end.
                boolex.
                assumption.
             ++ match goal with
                | [ Hfu : foldSSUpds ss = _,
                          Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
                  replace (getrf o') with x1 in Hht by (rewrite Hfu; unfold getrf; FMap.findeq);
                    replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                    replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                    eassumption
                end.
          -- constructor; try assumption.
             FMap.findeq.
        * Opaque evalExpr.
          match goal with
          | [ H : SCProcMemConsistent (_ :: _) _ |- _ ] => inversion H
          end.
          subst.
          simpl in *.
          Transparent evalExpr.
          subst.
          match goal with
          | [ H : SCProcMemConsistent ?a ?m,
                  IH : forall _, SCProcMemConsistent ?a _ -> _
                            |- _ ] => specialize (IH m H)
          end.
          shatter.
          eexists.
          split.
          -- eapply htTh.
             ++ reflexivity.
             ++ match goal with
                | [ H : context[rv32iGetOptype] |- _ ] =>
                  evex H
                end.
                boolex.
                assumption.
             ++ match goal with
                | [ Hfu : foldSSUpds ss = _,
                          Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
                  replace (getrf o') with x1 in Hht by (rewrite Hfu; unfold getrf; FMap.findeq);
                    replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                    replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                    eassumption
                end.
          -- constructor; try assumption.
             FMap.findeq.
        * Opaque evalExpr.
          match goal with
          | [ H : SCProcMemConsistent (_ :: _) _ |- _ ] => inversion H
          end.
          subst.
          simpl in *.
          Transparent evalExpr.
          subst.
          match goal with
          | [ H : SCProcMemConsistent ?a ?m,
                  IH : forall _, SCProcMemConsistent ?a _ -> _
                            |- _ ] => specialize (IH m H)
          end.
          shatter.
          eexists.
          split.
          -- eapply htFh.
             ++ reflexivity.
             ++ match goal with
                | [ H : context[rv32iGetOptype] |- _ ] =>
                  evex H
                end.
                boolex.
                assumption.
             ++ match goal with
                | [ Hfu : foldSSUpds ss = _,
                          Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
                  replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                    replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                    replace (getrf o') with x1 in Hht;
                    try eassumption
                end.
                match goal with
                | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
                end.
                unfold getrf.
                FMap.findeq.
                simplify_match.
                evexg.
                apply functional_extensionality.
                intros.
                unfold rset.
                match goal with
                | [ H : context[(#(evalExpr (rv32iGetDst _ _)) == _)%kami_expr] |- _ ] => evex H
                end.
                boolex.
                match goal with
                | [ |- (if ?eq then _ else _) _ = _ ] => destruct eq; tauto
                end.
          -- constructor; try assumption.
             FMap.findeq.
        * Opaque evalExpr.
          match goal with
          | [ H : SCProcMemConsistent (_ :: _) _ |- _ ] => inversion H
          end.
          subst.
          simpl in *.
          Transparent evalExpr.
          subst.
          match goal with
          | [ H : SCProcMemConsistent ?a ?m,
                  IH : forall _, SCProcMemConsistent ?a _ -> _
                            |- _ ] => specialize (IH m H)
          end.
          shatter.
          eexists.
          split.
          -- eapply htFh.
             ++ reflexivity.
             ++ match goal with
                | [ H : context[rv32iGetOptype] |- _ ] =>
                  evex H
                end.
                boolex.
                assumption.
             ++ match goal with
                | [ Hfu : foldSSUpds ss = _,
                          Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
                  replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                    replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                    replace (getrf o') with x1 in Hht;
                    try eassumption
                end.
                match goal with
                | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
                end.
                unfold getrf.
                FMap.findeq.
                simplify_match.
                unfold rset.
                evexg.
                apply functional_extensionality.
                intros.
                match goal with
                | [ H : context[(#(evalExpr (rv32iGetDst _ _)) == _)%kami_expr] |- _ ] => evex H
                end.
                boolex.
                match goal with
                | [ |- (if ?eq then _ else _) _ = _ ] => destruct eq; tauto
                end.
          -- constructor; try assumption.
             FMap.findeq.
        * match goal with
          | [ Hpm : FMap.M.find "pgm" _ = Some (existT _ _ ?pm),
                    Hpc : FMap.M.find "pc" _ = Some (existT _ _ ?pc)
              |- _ ] =>
            destruct (weq
                        (evalExpr (getOpcodeE # (pm (evalExpr (rv32iAlignPc type pc)))%kami_expr))
                        rv32iOpBRANCH)
          end.
          -- Opaque evalExpr.
             match goal with
             | [ H : SCProcMemConsistent (_ :: _) _ |- _ ] => inversion H
             end.
             subst.
             simpl in *.
             Transparent evalExpr.
             subst.
             match goal with
             | [ H : SCProcMemConsistent ?a ?m,
                     IH : forall _, SCProcMemConsistent ?a _ -> _
                               |- _ ] => specialize (IH m H)
             end.
             shatter.
             eexists.
             split.
             ++ eapply htNmBranch.
                ** reflexivity.
                ** match goal with
                   | [ H : context[rv32iGetOptype] |- _ ] =>
                     evex H
                   end.
                   boolex.
                   assumption.
                ** assumption.
                ** match goal with
                   | [ Hfu : foldSSUpds ss = _,
                             Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
                     replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                       replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                       replace (getrf o') with x1 in Hht;
                       try eassumption
                   end.
                   match goal with
                   | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
                   end.
                   unfold getrf.
                   FMap.findeq.
                   simplify_match.
                   evexg.
                   apply functional_extensionality.
                   intros.
                   match goal with
                   | [ H : context[(#(evalExpr (rv32iGetDst _ _)) == _)%kami_expr] |- _ ] => evex H
                   end.
                   boolex.
                   match goal with
                   | [ Hdst : evalExpr (rv32iGetDst _ _) <> _,
                              Hopc : evalExpr (getOpcodeE _) = _
                       |- _ ] =>
                     unfold rv32iGetDst in Hdst;
                       evex Hdst;
                       rewrite Hopc in Hdst
                   end.
                   tauto.
             ++ constructor; (eauto || discriminate).
          -- Opaque evalExpr.
             match goal with
             | [ H : SCProcMemConsistent (_ :: _) _ |- _ ] => inversion H
             end.
             subst.
             simpl in *.
             Transparent evalExpr.
             subst.
             match goal with
             | [ H : SCProcMemConsistent ?a ?m,
                     IH : forall _, SCProcMemConsistent ?a _ -> _
                               |- _ ] => specialize (IH m H)
             end.
             shatter.
             eexists.
             split.
             ++ eapply htNm.
                ** reflexivity.
                ** match goal with
                   | [ H : context[rv32iGetOptype] |- _ ] =>
                     evex H
                   end.
                   boolex.
                   assumption.
                ** assumption.
                ** match goal with
                   | [ Hfu : foldSSUpds ss = _,
                             Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
                     replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                       replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                       replace (getrf o') with x1 in Hht;
                       try eassumption
                   end.
                   match goal with
                   | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
                   end.
                   unfold getrf.
                   FMap.findeq.
                   simplify_match.
                   unfold rset.
                   evexg.
                   apply functional_extensionality.
                   intros.
                   match goal with
                   | [ H : context[(#(evalExpr (rv32iGetDst _ _)) == _)%kami_expr] |- _ ] => evex H
                   end.
                   boolex.
                   match goal with
                   | [ |- (if ?eq then _ else _) _ = _ ] => destruct eq; tauto
                   end.
             ++ constructor; (eauto || discriminate).
        * match goal with
          | [ Hpm : FMap.M.find "pgm" _ = Some (existT _ _ ?pm),
                    Hpc : FMap.M.find "pc" _ = Some (existT _ _ ?pc)
              |- _ ] =>
            destruct (weq
                        (evalExpr (getOpcodeE # (pm (evalExpr (rv32iAlignPc type pc)))%kami_expr))
                        rv32iOpBRANCH)
          end.
          -- Opaque evalExpr.
             match goal with
             | [ H : SCProcMemConsistent (_ :: _) _ |- _ ] => inversion H
             end.
             subst.
             simpl in *.
             Transparent evalExpr.
             subst.
             match goal with
             | [ H : SCProcMemConsistent ?a ?m,
                     IH : forall _, SCProcMemConsistent ?a _ -> _
                               |- _ ] => specialize (IH m H)
             end.
             shatter.
             eexists.
             split.
             ++ eapply htNmBranch.
                ** reflexivity.
                ** match goal with
                   | [ H : context[rv32iGetOptype] |- _ ] =>
                     evex H
                   end.
                   boolex.
                   assumption.
                ** assumption.
                ** match goal with
                   | [ Hfu : foldSSUpds ss = _,
                             Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
                     replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                       replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                       replace (getrf o') with x1 in Hht by (rewrite Hfu; unfold getrf; FMap.findeq);
                       eassumption
                   end.
             ++ constructor; (eauto || discriminate).
          -- Opaque evalExpr.
             match goal with
             | [ H : SCProcMemConsistent (_ :: _) _ |- _ ] => inversion H
             end.
             subst.
             simpl in *.
             Transparent evalExpr.
             subst.
             match goal with
             | [ H : SCProcMemConsistent ?a ?m,
                     IH : forall _, SCProcMemConsistent ?a _ -> _
                               |- _ ] => specialize (IH m H)
             end.
             shatter.
             eexists.
             split.
             ++ eapply htNm.
                ** reflexivity.
                ** match goal with
                   | [ H : context[rv32iGetOptype] |- _ ] =>
                     evex H
                   end.
                   boolex.
                   assumption.
                ** assumption.
                ** match goal with
                   | [ Hfu : foldSSUpds ss = _,
                             Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
                     replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                       replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                       replace (getrf o') with x1 in Hht;
                       try eassumption
                   end.
                   match goal with
                   | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
                   end.
                   unfold getrf.
                   FMap.findeq.
                   simplify_match.
                   unfold rset.
                   evexg.
                   match goal with
                   | [ H : context[(#(evalExpr (rv32iGetDst _ _)) == _)%kami_expr] |- _ ] => evex H
                   end.
                   boolex.
                   match goal with
                   | [ |- (if ?eq then _ else _) = _ ] => destruct eq; tauto
                   end.
             ++ constructor; (eauto || discriminate).
  Qed.

  Theorem abstractToProcHiding :
    forall rf pm pc mem,
      abstractHiding rf pm pc mem ->
      SCProcHiding p (SCProcRegs rf pm pc) mem.
  Proof.
    unfold abstractHiding, SCProcHiding.
    intros.
    match goal with
    | [ H : ForwardMultistep _ _ _ _ |- _ ] => let H' := fresh in assert (H' := H); eapply SCToAbstractRelated in H'; try eassumption
    end.
    shatter.
    match goal with
    | [ Hrel : relatedTrace ?t ?ls,
               Hextract : extractFhLabelSeq fhMeth ?ls = _,
                          Htrace : hasTrace _ _ _ _ _,
                                   Habs : forall _ _, hasTrace _ _ _ _ _ -> extractFhTrace _ = _ -> forall _, length _ = length _ -> _,
          Hlen : length _ = length _
          |- context[extractFhLabelSeq fhMeth _ = ?fhTrace] ] =>
      rewrite <- (relatedFhTrace _ _ Hrel) in Hextract; specialize (Habs _ _ Htrace Hextract fhTrace Hlen)
    end.
    shatter.
    match goal with
    | [ Htrace : hasTrace _ _ _ _ ?t,
                 Hextract : extractFhTrace ?t = ?fhTrace
        |- context[?fhTrace] ] => pose (abstractToSCRelated _ _ _ _ _ Htrace)
    end.
    shatter.
    match goal with
    | [ Hht0 : hasTrace _ _ _ _ ?t0,
        Hht1 : hasTrace _ _ _ _ ?t1,
        Hrt0 : relatedTrace ?t0 ?ls0,
        Hrt1 : relatedTrace ?t1 ?ls1,
        Heft : extractFhTrace ?t1 = _,
        Hfm : ForwardMultistep _ _ _ ?ls1,
        Hmc : SCProcMemConsistent ?ls1 _
        |- _ ] =>
      let Hcanon := fresh in
      let Heq := fresh in
      assert (censorLabelSeq censorSCMeth (canonicalize ls0) = censorLabelSeq censorSCMeth (canonicalize ls1)) as Hcanon by (eapply (relatedCensor _ _ _ _ _ _ _ _ _ _ _ _ Hht0 Hht1); eassumption);
        pose (Heq := relatedFhTrace _ _ Hrt1);
        rewrite Heq in Heft;
        pose (decanon _ _ _ _ _ _ _ Hfm Hmc Hcanon Heft)
    end.
    shatter.
    eauto.
  Qed.

  Lemma SCMemSubsteps :
    forall o (ss : Substeps m o),
      SubstepsInd m o (foldSSUpds ss) (foldSSLabel ss) ->
      (((foldSSLabel ss) = {| annot := None; defs := FMap.M.empty _; calls := FMap.M.empty _ |}
        \/ (foldSSLabel ss) = {| annot := Some None; defs := FMap.M.empty _; calls := FMap.M.empty _ |})
       /\ (foldSSUpds ss) = FMap.M.empty _)
      \/ (exists a argV retV u,
            (a = None \/ a = Some None)
            /\ SemAction o (rv32iMemInstExec argV) u (FMap.M.empty _) retV
            /\ (foldSSLabel ss) = {| annot := a; defs := FMap.M.add "exec" (existT _
                       {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                                 "op" :: Bool;
                                                 "data" :: Bit 32});
                          ret := Struct (STRUCT {"data" :: Bit 32}) |}
                       (argV, retV)) (FMap.M.empty _); calls := FMap.M.empty _ |}
            /\ (foldSSUpds ss) = u).
  Proof.
    intros.
    match goal with
    | [ H : SubstepsInd _ _ _ _ |- _ ] => induction H
    end.
    - tauto.
    - intuition idtac;
        simpl;
        shatter;
        intuition idtac;
        subst;
        match goal with
        | [ H : Substep _ _ _ _ _ |- _ ] => destruct H
        end;
        try tauto;
        try solve [right; repeat eexists; FMap.findeq];
        match goal with
        | [ HIn : In _ (getRules m) |- _ ] => simpl in HIn; tauto
        | _ => idtac
        end.
      + right.
        simpl in HIn.
        intuition idtac.
        subst.
        simpl in *.
        exists None, argV, retV, u.
        replace cs with (FMap.M.empty {x : SignatureT & SignT x}) in *.
        * intuition idtac.
        * kinv_action_dest; FMap.findeq.
      + right.
        simpl in HIn.
        intuition idtac.
        subst.
        simpl in *.
        exists (Some None), argV, retV, u.
        replace cs with (FMap.M.empty {x : SignatureT & SignT x}) in *.
        * intuition idtac.
        * kinv_action_dest; FMap.findeq.
      + exfalso.
        simpl in HIn.
        intuition idtac.
        subst.
        unfold CanCombineUUL in H1.
        simpl in H1.
        intuition idtac.
        apply H3.
        FMap.findeq.
      + exfalso.
        simpl in HIn.
        intuition idtac.
        subst.
        unfold CanCombineUUL in H1.
        simpl in H1.
        intuition idtac.
        apply H3.
        FMap.findeq.
  Qed.

  Lemma SCMemRegs_find_mem : forall (mem mem' : memory),
      FMap.M.find (elt:={x : FullKind & fullType type x}) "mem"
                                   (SCMemRegs mem) =
                       Some
                         (existT (fullType type) (SyntaxKind (Vector (Bit 32) 16)) mem') -> mem = mem'.
  Proof.
    intros.
    unfold SCMemRegs in *.
    rewrite FMap.M.find_add_1 in H.
    match goal with
    | [ H : Some ?x = Some ?y |- _ ] => remember x as x'; remember y as y'; inv H
    end.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1).
  Qed.

  Theorem MemHiding : SCMemHiding m.
  Proof.
    unfold SCMemHiding.
    induction 1; intros.
    - exists nil.
      eexists.
      intuition idtac.
      + constructor; reflexivity.
      + constructor.
      + simpl in *.
        subst.
        simpl in *.
        apply eq_sym.
        rewrite <- length_zero_iff_nil.
        congruence.
    - match goal with
      | [ H : ForwardMultistep _ _ _ _ |- _ ] => inversion H
      end.
      match goal with
      | [ H : Step _ _ _ _ |- _ ] => inversion H
      end.
      subst.
      match goal with
      | [ H : substepsComb _ |- _ ] =>
        apply substepsComb_substepsInd in H;
          apply SCMemSubsteps in H
      end.
      intuition idtac; shatter; subst;
        try match goal with
            | [ H : foldSSLabel ss = _ |- _ ] => rewrite H in *
            end;
        try match goal with
            | [ H : foldSSUpds ss = _ |- _ ] => rewrite H in *
            end;
        simpl in *;
        subst;
        FMap.mred;
        try tauto.
      + match goal with
        | [ Hl : length _ = length _,
            Hfm : ForwardMultistep _ _ _ _ |- _ ] =>
          specialize (IHSCMemMemConsistent Hfm _ eq_refl mem'0 wrs' Hl)
        end.
        shatter.
        exists ({| annot := None; defs := FMap.M.empty _; calls := FMap.M.empty _ |} :: x), x0.
        intuition idtac.
        * econstructor; eauto.
          -- match goal with
             | [ |- Step _ _ _ ?l ] => replace l with (hide (foldSSLabel [{| upd := FMap.M.empty _; unitAnnot := Meth None; cms := FMap.M.empty _; substep := EmptyMeth m (SCMemRegs mem'0) |}])) by reflexivity
             end.
             constructor; eauto.
             constructor; try solve [ constructor ].
             intros.
             match goal with
             | [ H : In _ nil |- _ ] => inversion H
             end.
          -- eauto.
        * econstructor.
          -- simpl. reflexivity.
          -- assumption.
        * simpl.
          f_equal.
          assumption.
      + match goal with
        | [ Hl : length _ = length _,
            Hfm : ForwardMultistep _ _ _ _ |- _ ] =>
          specialize (IHSCMemMemConsistent Hfm _ eq_refl mem'0 wrs' Hl)
        end.
        shatter.
        exists ({| annot := Some None; defs := FMap.M.empty _; calls := FMap.M.empty _ |} :: x), x0.
        intuition idtac.
        * econstructor; eauto.
          -- match goal with
             | [ |- Step _ _ _ ?l ] => replace l with (hide (foldSSLabel [{| upd := FMap.M.empty _; unitAnnot := Rle None; cms := FMap.M.empty _; substep := EmptyRule m (SCMemRegs mem'0) |}])) by reflexivity
             end.
             constructor; eauto.
             constructor; try solve [ constructor ].
             intros.
             match goal with
             | [ H : In _ nil |- _ ] => inversion H
             end.
          -- eauto.
        * econstructor.
          -- simpl. reflexivity.
          -- assumption.
        * simpl.
          f_equal.
          assumption.
      + pose (Hrq := inv_rq x0).
        pose (Hrs := inv_rs x1).
        destruct Hrq as [adr [op [dat Heqq]]].
        destruct Hrs as [val Heqs].
        simpl in adr, op, dat, val.
        subst.
        destruct op;
          kinv_action_dest;
          match goal with
          | [ H : foldSSUpds _ = _ |- _ ] => rewrite H in *
          end;
          simpl in *;
          subst;
          try match goal with
              | [ H : ForwardMultistep _ (FMap.M.union _ _) _ _ |- _ ] =>
                unfold SCMemRegs in H;
                  FMap.mred;
                  rewrite FMap.M.union_add in H;
                  FMap.mred;
                  rewrite FMap.M.add_idempotent in H
              end.
        * destruct wrs'; try discriminate.
          match goal with
          | [ H : S (length _) = length _ |- _ ] => simpl in H; inversion H
          end.
          match goal with
          | [ H : _ |- _ ] => apply SCMemRegs_find_mem in H; subst
          end.
          match goal with
          | [ Hl : length _ = length _,
              Hfm : ForwardMultistep _ _ _ _ |- _ ] =>
            specialize (IHSCMemMemConsistent Hfm _ eq_refl
                                           (fun a => if weq a adr then w else mem'0 a)
                                           _ Hl)
          end.
          shatter.
          match goal with
          | [ H : extractMemWrValSeq ?ls = wrs', Hfm : ForwardMultistep _ _ ?r ?ls |- _ ] =>
            exists ({| annot := x;
                  defs := FMap.M.add "exec"
                                     (existT SignT {| arg := Struct STRUCT {"addr" :: Bit 16; "op" :: Bool; "data" :: Bit 32}; ret := Struct STRUCT {"data" :: Bit 32} |}
                                             (evalExpr (STRUCT { "addr" ::= Var _ (SyntaxKind (Bit 16)) adr;
                                                                 "op" ::= $$(true);
                                                                 "data" ::= Var _ (SyntaxKind (Bit 32)) w})%kami_expr,
                                              evalExpr (STRUCT { "data" ::= $0 })%kami_expr)) (FMap.M.empty _); calls := FMap.M.empty _|} :: ls), r
          end.
          intuition idtac; subst.
          -- econstructor; try discriminate.
             ++ match goal with
                | [ |- Step ?m ?o _ {| annot := _; defs := FMap.M.add _ (existT _ _ (?av, ?rv)) _; calls := _ |} ] =>
                  let ss := fresh in
                  simple refine (let ss := (_ : Substeps m o) in _);
                    [ apply cons; [ idtac | apply nil ];
                      eapply Build_SubstepRec;
                      eapply SingleMeth;
                      try (simpl; tauto);
                      instantiate (4 := av);
                      instantiate (1 := rv);
                      eapply SemIfElseFalse;
                      try match goal with
                         | [ |- SemAction _ _ _ _ _ ] => repeat econstructor
                          end;
                      eauto
                    | match goal with
                      | [ |- Step ?m ?o _ ?l ] => replace l with (hide (foldSSLabel ss)) by reflexivity
                      end
                    ]
                end.
                apply StepIntro; repeat (apply AddSubstep || apply NilSubsteps);
                match goal with
                | [ |- forall _, In _ _ -> _ ] =>
                  let Hin := fresh in
                  intros ? Hin;
                    simpl in Hin;
                    intuition idtac;
                    subst;
                    unfold canCombine;
                    simpl;
                    intuition idtac;
                    eauto;
                    discriminate
                | [ |- wellHidden _ _ ] =>
                  unfold wellHidden, m, getCalls, getDefs, FMap.M.KeysDisj;
                    simpl;
                    FMap.mred;
                    rewrite FMap.M.subtractKV_empty_1;
                    intuition idtac;
                    rewrite FMap.M.F.P.F.empty_in_iff in *;
                    tauto
                end.
             ++ match goal with
                | [ H : ForwardMultistep ?m ?o ?n ?l |- ForwardMultistep ?m ?o' ?n ?l ] => replace o' with o; [ assumption | idtac ]
                end.
                unfold foldSSUpds, upd.
                unfold SCMemRegs.
                FMap.mred.
                rewrite FMap.M.union_add.
                FMap.mred.
                rewrite FMap.M.add_idempotent.
                reflexivity.
          -- econstructor.
             ++ FMap.findeq.
             ++ assumption.
          -- subst.
             simpl.
             f_equal; try assumption.
             f_equal.
             FMap.M.ext k.
             do 2 rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
             FMap.mred.
          -- simpl.
             congruence.
          -- econstructor; try discriminate.
             ++ match goal with
                | [ |- Step ?m ?o _ {| annot := _; defs := FMap.M.add _ (existT _ _ (?av, ?rv)) _; calls := _ |} ] =>
                  let ss := fresh in
                  simple refine (let ss := (_ : Substeps m o) in _);
                    [ apply cons;
                      [ exact (Build_SubstepRec (EmptyRule _ _))
                      | apply cons; [ idtac | apply nil ]];
                      eapply Build_SubstepRec;
                      eapply SingleMeth;
                      try (simpl; tauto);
                      instantiate (4 := av);
                      instantiate (1 := rv);
                      eapply SemIfElseFalse;
                      try match goal with
                         | [ |- SemAction _ _ _ _ _ ] => repeat econstructor
                          end;
                      eauto
                    | match goal with
                      | [ |- Step ?m ?o _ ?l ] => replace l with (hide (foldSSLabel ss)) by reflexivity
                      end
                    ]
                end.
                apply StepIntro; repeat (apply AddSubstep || apply NilSubsteps);
                match goal with
                | [ |- forall _, In _ _ -> _ ] =>
                  let Hin := fresh in
                  intros ? Hin;
                    simpl in Hin;
                    intuition idtac;
                    subst;
                    unfold canCombine;
                    simpl;
                    intuition idtac;
                    eauto;
                    discriminate
                | [ |- wellHidden _ _ ] =>
                  unfold wellHidden, m, getCalls, getDefs, FMap.M.KeysDisj;
                    simpl;
                    FMap.mred;
                    rewrite FMap.M.subtractKV_empty_1;
                    intuition idtac;
                    rewrite FMap.M.F.P.F.empty_in_iff in *;
                    tauto
                end.
             ++ match goal with
                | [ H : ForwardMultistep ?m ?o ?n ?l |- ForwardMultistep ?m ?o' ?n ?l ] => replace o' with o; [ assumption | idtac ]
                end.
                unfold foldSSUpds, upd.
                unfold SCMemRegs.
                FMap.mred.
                rewrite FMap.M.union_add.
                FMap.mred.
                rewrite FMap.M.add_idempotent.
                reflexivity.
          -- econstructor.
             ++ FMap.findeq.
             ++ assumption.
          -- subst.
             simpl.
             f_equal; try assumption.
             f_equal.
             FMap.M.ext k.
             do 2 rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
             FMap.mred.
          -- simpl.
             congruence.
        * shatter; subst.
          match goal with
          | [ H : _ |- _ ] => apply SCMemRegs_find_mem in H; subst
          end.
          match goal with
          | [ Hl : length _ = length _,
              Hfm : ForwardMultistep _ _ _ _ |- _ ] =>
            specialize (IHSCMemMemConsistent Hfm _ eq_refl mem'0 _ Hl)
          end.
          shatter.
          match goal with
          | [ H : extractMemWrValSeq ?ls = wrs', Hfm : ForwardMultistep _ _ ?r ?ls |- _ ] =>
            exists ({| annot := x;
                  defs := FMap.M.add "exec"
                                     (existT SignT {| arg := Struct STRUCT {"addr" :: Bit 16; "op" :: Bool; "data" :: Bit 32}; ret := Struct STRUCT {"data" :: Bit 32} |}
                                             (evalExpr (STRUCT { "addr" ::= Var _ (SyntaxKind (Bit 16)) adr;
                                                                 "op" ::= $$(false);
                                                                 "data" ::= $0 })%kami_expr,
                                              evalExpr (STRUCT { "data" ::= Var _ (SyntaxKind (Bit 32)) (mem'0 adr) })%kami_expr)) (FMap.M.empty _); calls := FMap.M.empty _|} :: ls), r
          end.
          intuition idtac; subst.
          -- econstructor; try discriminate.
             ++ match goal with
                | [ |- Step ?m ?o _ {| annot := _; defs := FMap.M.add _ (existT _ _ (?av, ?rv)) _; calls := _ |} ] =>
                  let ss := fresh in
                  simple refine (let ss := (_ : Substeps m o) in _);
                    [ apply cons; [ idtac | apply nil ];
                      eapply Build_SubstepRec;
                      eapply SingleMeth;
                      try (simpl; tauto);
                      instantiate (4 := av);
                      instantiate (1 := rv);
                      eapply SemIfElseTrue;
                      try match goal with
                         | [ |- SemAction _ _ _ _ _ ] => repeat econstructor
                          end;
                      eauto
                    | match goal with
                      | [ |- Step ?m ?o _ ?l ] => replace l with (hide (foldSSLabel ss)) by reflexivity
                      end
                    ]
                end.
                apply StepIntro; repeat (apply AddSubstep || apply NilSubsteps);
                match goal with
                | [ |- forall _, In _ _ -> _ ] =>
                  let Hin := fresh in
                  intros ? Hin;
                    simpl in Hin;
                    intuition idtac;
                    subst;
                    unfold canCombine;
                    simpl;
                    intuition idtac;
                    eauto;
                    discriminate
                | [ |- wellHidden _ _ ] =>
                  unfold wellHidden, m, getCalls, getDefs, FMap.M.KeysDisj;
                    simpl;
                    FMap.mred;
                    rewrite FMap.M.subtractKV_empty_1;
                    intuition idtac;
                    rewrite FMap.M.F.P.F.empty_in_iff in *;
                    tauto
                end.
             ++ match goal with
                | [ H : ForwardMultistep ?m ?o ?n ?l |- ForwardMultistep ?m ?o' ?n ?l ] => replace o' with o; [ assumption | idtac ]
                end.
                match goal with
                | [ H : foldSSUpds _ = _ |- _ ] => rewrite H in *
                end.
                unfold foldSSUpds, upd.
                unfold SCMemRegs.
                FMap.mred.
          -- econstructor; simpl; tauto.
          -- subst.
             simpl.
             f_equal; try assumption.
             f_equal.
             FMap.M.ext k.
             do 2 rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
             FMap.mred.
          -- econstructor; try discriminate.
             ++ match goal with
                | [ |- Step ?m ?o _ {| annot := _; defs := FMap.M.add _ (existT _ _ (?av, ?rv)) _; calls := _ |} ] =>
                  let ss := fresh in
                  simple refine (let ss := (_ : Substeps m o) in _);
                    [ apply cons;
                      [ exact (Build_SubstepRec (EmptyRule _ _))
                      | apply cons; [ idtac | apply nil ]];
                      eapply Build_SubstepRec;
                      eapply SingleMeth;
                      try (simpl; tauto);
                      instantiate (4 := av);
                      instantiate (1 := rv);
                      eapply SemIfElseTrue;
                      try match goal with
                         | [ |- SemAction _ _ _ _ _ ] => repeat econstructor
                          end;
                      eauto
                    | match goal with
                      | [ |- Step ?m ?o _ ?l ] => replace l with (hide (foldSSLabel ss)) by reflexivity
                      end
                    ]
                end.
                apply StepIntro; repeat (apply AddSubstep || apply NilSubsteps);
                match goal with
                | [ |- forall _, In _ _ -> _ ] =>
                  let Hin := fresh in
                  intros ? Hin;
                    simpl in Hin;
                    intuition idtac;
                    subst;
                    unfold canCombine;
                    simpl;
                    intuition idtac;
                    eauto;
                    discriminate
                | [ |- wellHidden _ _ ] =>
                  unfold wellHidden, m, getCalls, getDefs, FMap.M.KeysDisj;
                    simpl;
                    FMap.mred;
                    rewrite FMap.M.subtractKV_empty_1;
                    intuition idtac;
                    rewrite FMap.M.F.P.F.empty_in_iff in *;
                    tauto
                end.
             ++ match goal with
                | [ H : ForwardMultistep ?m ?o ?n ?l |- ForwardMultistep ?m ?o' ?n ?l ] => replace o' with o; [ assumption | idtac ]
                end.
                match goal with
                | [ H : foldSSUpds _ = _ |- _ ] => rewrite H in *
                end.
                unfold foldSSUpds, upd.
                unfold SCMemRegs.
                FMap.mred.
          -- econstructor; simpl; tauto.
          -- subst.
             simpl.
             f_equal; try assumption.
             f_equal.
             FMap.M.ext k.
             do 2 rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
             FMap.mred.
  Qed.

  Theorem MemSpec : SCMemSpec m.
  Proof.
    unfold SCMemSpec; induction 1; intros.
    - constructor.
    - match goal with
      | [ H : Step _ _ _ _ |- _ ] => inv H
      end.
      match goal with
      | [ H : substepsComb _ |- _ ] =>
        apply substepsComb_substepsInd in H;
          apply SCMemSubsteps in H
      end.
      intuition idtac; shatter; subst;
        try match goal with
            | [ H : foldSSLabel ss = _ |- _ ] => rewrite H in *
            end;
        try match goal with
            | [ H : foldSSUpds ss = _ |- _ ] => rewrite H in *
            end;
        unfold hide in *;
        simpl in *;
        subst.
      + econstructor; FMap.findeq; apply IHForwardMultistep; reflexivity.
      + econstructor; FMap.findeq; apply IHForwardMultistep; reflexivity.
      + pose (Hrq := inv_rq x0).
        destruct Hrq as [adr [op [dat Heqq]]].
        simpl in adr, op, dat.
        subst.
        destruct op;
          kinv_action_dest;
          match goal with
          | [ H : _ |- _ ] => apply SCMemRegs_find_mem in H; subst
          end;
          match goal with
          | [ H : foldSSUpds _ = _ |- _ ] => rewrite H in *
          end;
          simpl in *;
          subst;
          econstructor;
          simpl;
          try split;
          try reflexivity;
          apply IHForwardMultistep;
          eauto.
  Qed.

End SCSingleModularHiding.

Module SCSingleHiding := SCHiding SCSingle SCSingleModularHiding.
Check SCSingleHiding.abstractToSCHiding.

Section ThreeStageTiming.

  Definition S3Regs rf pm pc : RegsT :=
    FMap.M.add "rf" (existT _ (SyntaxKind (Vector (Bit 32) 5)) rf)
               (FMap.M.add "pgm" (existT _ (SyntaxKind (Vector (Bit 32) 8)) pm)
                           (FMap.M.add "pc" (existT _ (SyntaxKind (Bit 16)) pc)
                                                   (FMap.M.empty _))).

  Lemma S3Regs_find_rf : forall rf pm pc rf',
      FMap.M.find (elt:={x : FullKind & fullType type x}) "rf"
                                   (S3Regs rf pm pc) =
                       Some
                         (existT (fullType type) (SyntaxKind (Vector (Bit 32) 5)) rf') -> rf = rf'.
  Proof.
    intros.
    unfold S3Regs in *.
    FMap.findeq.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1).
  Qed.

  Lemma S3Regs_find_pm : forall rf pm pc pm',
      FMap.M.find (elt:={x : FullKind & fullType type x}) "pgm"
                  (S3Regs rf pm pc) =
      Some
        (existT (fullType type) (SyntaxKind (Vector (Bit 32) 8)) pm') -> pm = pm'.
  Proof.
    intros.
    unfold S3Regs in *.
    FMap.findeq.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1).
  Qed.

  Lemma S3Regs_find_pc : forall rf pm pc pc',
      FMap.M.find (elt:={x : FullKind & fullType type x}) "pc"
                  (S3Regs rf pm pc) =
      Some
        (existT (fullType type) (SyntaxKind (Bit 16)) pc') -> pc = pc'.
  Proof.
    intros.
    unfold S3Regs in *.
    FMap.findeq.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1).
  Qed.

  Ltac S3Regs_find :=
    repeat match goal with
           | [ H : FMap.M.find "rf" (S3Regs ?rf _ _) = Some (existT _ _ ?rf') |- _ ] => assert (rf = rf') by (eapply S3Regs_find_rf; eassumption); subst; clear H
           | [ H : FMap.M.find "pgm" (S3Regs _ ?pm _) = Some (existT _ _ ?pm') |- _ ] => assert (pm = pm') by (eapply S3Regs_find_pm; eassumption); subst; clear H
           | [ H : FMap.M.find "pc" (S3Regs _ _ ?pc) = Some (existT _ _ ?pc') |- _ ] => assert (pc = pc') by (eapply S3Regs_find_pc; eassumption); subst; clear H
           end.

  Definition censorS3Meth (n : String.string) (t : {x : SignatureT & SignT x}) : {x : SignatureT & SignT x} :=
    if String.string_dec n ("rqFromProc" -- "enq")
    then match t with
         | existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Bit 0 |}
                  (argV, _) =>
           existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Bit 0 |}
                  (evalExpr (STRUCT { "addr" ::= #argV!rv32iRq@."addr";
                                      "op" ::= #argV!rv32iRq@."op";
                                      "data" ::= $0 })%kami_expr,
                   $0)
         | _ => t
         end
    else if String.string_dec n ("rsToProc" -- "deq")
    then match t with
         | existT _
                  {| arg := Bit 0;
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (argV, retV) =>
           existT _
                  {| arg := Bit 0;
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  ($0,
                   evalExpr (STRUCT { "data" ::= $0 })%kami_expr)
         | _ => t
         end
    else if String.string_dec n "toHost"
    then match t with
         | existT _
                  {| arg := Bit 32;
                     ret := Bit 0 |}
                  (argV, retV) =>
           existT _
                  {| arg := Bit 32;
                     ret := Bit 0 |}
                  ($0, retV)
         | _ => t
         end
    else if String.string_dec n "fromHost"
    then match t with
         | existT _
                  {| arg := Bit 0;
                     ret := Bit 32 |}
                  (argV, retV) =>
           existT _
                  {| arg := Bit 0;
                     ret := Bit 32 |}
                  (argV, $0)
         | _ => t
         end
    else t.

  Definition extractFhS3 (cs : MethsT) : list (word 32) :=
    match FMap.M.find "fromHost" cs with
    | Some (existT _
                   {| arg := Bit 0;
                      ret := Bit 32 |}
                   (argV, retV)) =>
      [retV]
    | _ => nil
    end.

  Definition predictNextPc ty (ppc: fullType ty (SyntaxKind (Bit rv32iAddrSize))) :=
    (#ppc + $4)%kami_expr.

  Definition rv32iS3 :=
    p3st rv32iGetOptype
             rv32iGetLdDst rv32iGetLdAddr rv32iGetLdSrc rv32iCalcLdAddr
             rv32iGetStAddr rv32iGetStSrc rv32iCalcStAddr rv32iGetStVSrc
             rv32iGetSrc1 rv32iGetSrc2 rv32iGetDst
             rv32iExec rv32iNextPc rv32iAlignPc rv32iAlignAddr
             predictNextPc
             (d2ePackI (rfIdx := _))
             (d2eOpTypeI _ _ _) (d2eDstI _ _ _) (d2eAddrI _ _ _)
             (d2eVal1I _ _ _) (d2eVal2I _ _ _) (d2eRawInstI _ _ _)
             (d2eCurPcI _ _ _) (d2eNextPcI _ _ _) (d2eEpochI _ _ _)
             (e2wPackI (rfIdx := _))
             (e2wDecInstI _ _ _) (e2wValI _ _ _)
             (procInitDefault  _ _ _ _).

  Definition rv32iFetchDecode :=
    fetchDecode rv32iGetOptype
                rv32iGetLdDst rv32iGetLdAddr rv32iGetLdSrc rv32iCalcLdAddr
                rv32iGetStAddr rv32iGetStSrc rv32iCalcStAddr rv32iGetStVSrc
                rv32iGetSrc1 rv32iGetSrc2 rv32iGetDst rv32iAlignPc
                (d2ePackI (rfIdx := _))
                predictNextPc
                Default Default.

  Definition rv32iExecuter :=
    executer rv32iAddrSize rv32iExec
             (d2eOpTypeI _ _ _)
             (d2eVal1I _ _ _) (d2eVal2I _ _ _) (d2eRawInstI _ _ _)
             (d2eCurPcI _ _ _)
             (e2wPackI (rfIdx := rv32iRfIdx)).

  Definition rv32iWB :=
    wb "rqFromProc" "rsToProc"
       rv32iNextPc rv32iAlignAddr
       (d2eOpTypeI _ _ _) (d2eDstI _ _ _) (d2eAddrI _ _ _)
       (d2eVal1I _ _ _) (d2eRawInstI _ _ _)
       (d2eCurPcI _ _ _) (d2eNextPcI _ _ _) (d2eEpochI _ _ _)
       (e2wDecInstI _ _ _) (e2wValI _ _ _).

  Lemma S3Step :
    forall o u l, Step rv32iS3 o u l ->
             exists k a u' cs,
               In (k :: a)%struct (getRules rv32iS3)
               /\ SemAction o (a type) u' cs WO.
    idtac.
(*wellHidden Step Substep StepInd
  Lemma S3Substeps :
    forall o (ss : Substeps rv32iS3 o),
      SubstepsInd rv32iS3 o (foldSSUpds ss) (foldSSLabel ss) ->
(*      ((foldSSLabel ss) = {| annot := None; defs := FMap.M.empty _; calls := FMap.M.empty _ |}
       /\ (foldSSUpds ss) = FMap.M.empty _)
      \/*) (exists b1 b2 b3 k1 k2 k3 a1 a2 a3 u1 u2 u3 cs1 cs2 cs3 annot,
            ((b1 = true
              /\ In (k1 :: a1)%struct (getRules rv32iFetchDecode)
              /\ SemAction o (a1 type) u1 cs1 WO)
             \/ (b1 = false /\ u1 = FMap.M.empty _ /\ cs1 = FMap.M.empty _))
           /\ ((b2 = true
               /\ In (k2 :: a2)%struct (getRules rv32iExecuter)
              /\ SemAction o (a2 type) u2 cs2 WO)
             \/ (b2 = false /\ u2 = FMap.M.empty _ /\ cs2 = FMap.M.empty _))
           /\ ((b3 = true
              /\ In (k3 :: a3)%struct (getRules rv32iWB)
              /\ SemAction o (a3 type) u3 cs3 WO)
              \/ (b3 = false /\ u3 = FMap.M.empty _ /\ cs3 = FMap.M.empty _))
(*           /\ ((b1 = true /\ k = Some k1) \/ (b2 = true /\ k = Some k2) \/ (b3 = true /\ k = Some k3) \/ (b1 = false /\ b2 = false /\ b3 = false /\ k = None))*)
           /\ (foldSSLabel ss) = {| annot := annot; defs := FMap.M.empty _; calls := FMap.M.union cs1 (FMap.M.union cs2 cs3) |}
           /\ (foldSSUpds ss) = FMap.M.union u1 (FMap.M.union u2 u3)).
  Proof.
    intros.
    match goal with
    | [ H : SubstepsInd _ _ _ _ |- _ ] => induction H
    end.
    - exists false, false, false.
      repeat eexists; (tauto || reflexivity).
    - shatter.
      intuition idtac; subst.
      + exists true, true, true, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13.
        match goal with
        | [ H : Substep _ _ _ _ _ |- _ ] => destruct H
        end; simpl.
        * exists (Some None).
          destruct x14; intuition idtac; FMap.findeq.
        * exists x14.
          intuition idtac; FMap.findeq.
        * exfalso.
          unfold rv32iS3, p3st, procThreeStage in HInRules.
          unfold getRules in HInRules; fold getRules in HInRules.
          repeat (apply in_app_or in HInRules; destruct HInRules as [HInRules|HInRules]); simpl in HInRules.
          -- clear H10 H13 H12 H15.
             simpl in H9.
             intuition idtac;
               repeat match goal with
                      | [ H : _ = (_ :: _)%struct |- _ ] => inversion H; clear H
                      end;
               subst.
             ++ kinv_action_dest.
                clear - H1.
                unfold CanCombineUUL in H1.
                simpl in H1.
                intuition idtac.
                apply FMap.M.Disj_add_2 in H1.
                FMap.findeq.
             ++ Opaque evalExpr.
                kinv_action_dest.
                Transparent evalExpr.
                
      + 
        simpl;
        shatter;
        intuition idtac;
        subst.
    - intuition idtac;
        simpl;
        shatter;
        intuition idtac;
        subst;
        match goal with
        | [ H : Substep _ _ _ _ _ |- _ ] => destruct H
        end;
        try tauto;
        match goal with
        | [ HCCU : CanCombineUUL _ {| annot := Some _; defs := FMap.M.empty _; calls := _ |} _ _ (Rle _) |- _ ] =>
          unfold CanCombineUUL in HCCU;
            simpl in HCCU;
            tauto
        | [ HIn : In _ (getDefsBodies rv32iProcInst) |- _ ] =>
          simpl in HIn;
            tauto
        | [ HIR : In (?k :: ?a)%struct _, HA : SemAction _ _ ?u ?cs _ |- _ ] =>
          right;
            exists k, a, u, cs;
            simpl in HIR;
            intuition idtac;
            simpl;
            FMap.findeq
        end.
  Qed.*)

  Theorem abstractToS3Hiding :
    forall rf pm pc maxsp,
      abstractHiding rf pm pc maxsp ->
      kamiHiding censorS3Meth extractFhS3
                 rv32iS3
                 maxsp
                 (S3Regs rf pm pc).
  Proof.
    unfold abstractHiding, kamiHiding.
    intros.
    generalize fhs, fhs', H1, H2.
    clear fhs fhs' H1 H2.
    induction H0.
    - exists nil.
      eexists.
      simpl in *.
      subst.
      simpl in *.
      destruct fhs'; simpl in *; try discriminate.
      repeat econstructor.
    - intros.
      simpl in H5.
    match goal with
    | [ H : ForwardMultistep _ _ _ _ |- _ ] => let H' := fresh in assert (H' := H); eapply SCToAbstractRelated in H'
    end.
    shatter.
    match goal with
    | [ Hrel : relatedTrace ?t ?ls,
               Hextract : extractFhLabelSeq extractFhSC ?ls = _,
                          Htrace : hasTrace _ _ _ _ _,
                                   Habs : forall _ _, hasTrace _ _ _ _ _ -> extractFhTrace _ = _ -> forall _, length _ = length _ -> _,
          Hlen : length _ = length _
          |- context[extractFhLabelSeq _ _ = ?fhTrace] ] =>
      rewrite <- (relatedFhTrace _ _ Hrel) in Hextract; specialize (Habs _ _ Htrace Hextract fhTrace Hlen)
    end.
    shatter.
    match goal with
    | [ Htrace : hasTrace _ _ _ _ ?t,
                 Hextract : extractFhTrace ?t = ?fhTrace
        |- context[?fhTrace] ] => pose (abstractToSCRelated _ _ _ _ _ Htrace)
    end.
    shatter.
    match goal with
    | [ H : ForwardMultistep _ _ ?regs ?ls |- _ ] => exists ls, regs
    end.
    repeat split;
      match goal with
      | [ |- ForwardMultistep _ _ _ _ ] => assumption
      | [ Htrace1 : hasTrace _ _ _ _ _, Htrace2 : hasTrace _ _ _ _ _ |- censorLabelSeq _ _ = censorLabelSeq _ _ ] => eapply (relatedCensor _ _ _ _ _ _ _ _ _ _ _ Htrace1 Htrace2); eassumption
      | [ |- extractFhLabelSeq _ _ = _ ] => erewrite <- relatedFhTrace; eassumption
      end.
  Qed.

End ThreeStageTiming.
