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

  Ltac register_op_funct3 inst op expr :=
    refine (IF (getFunct3E #inst == $$op) then expr else _)%kami_expr.
(* probably this should be elsewhere *)
  Definition rv32iBranchTaken:
    forall ty : Kind -> Type,
      StateT rv32iDataBytes rv32iRfIdx ty ->
      fullType ty (SyntaxKind (MemTypes.Data rv32iDataBytes)) ->
      (Bool) @ (ty).
    intros ty st inst.
    refine (IF (getOpcodeE #inst == $$rv32iOpBRANCH) then _ else Const ty (ConstBool false))%kami_expr.
    register_op_funct3 inst rv32iF3BEQ
                       (getRs1ValueE st #inst == getRs2ValueE st #inst)%kami_expr.
    register_op_funct3 inst rv32iF3BNE
                       (getRs1ValueE st #inst != getRs2ValueE st #inst)%kami_expr.
    register_op_funct3 inst rv32iF3BLT
                       ((UniBit (TruncLsb 31 1)
                                (getRs1ValueE st #inst - getRs2ValueE st #inst)) == $1)%kami_expr.
    register_op_funct3 inst rv32iF3BGE
                       ((UniBit (TruncLsb 31 1)
                                (getRs1ValueE st #inst - getRs2ValueE st #inst)) == $0)%kami_expr.
    register_op_funct3 inst rv32iF3BLTU
                       (getRs1ValueE st #inst < getRs2ValueE st #inst)%kami_expr.
    register_op_funct3 inst rv32iF3BGEU
                       (getRs1ValueE st #inst >= getRs2ValueE st #inst)%kami_expr.
    exact (Const ty (ConstBool false)).
  Defined.

    
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

    Lemma pc_from_trace : forall rf pm pc mem tr,
        hasTrace rf pm pc mem tr ->
        match tr with
        | nil => True
        | te :: _ => pc = match te with
                          | Nop pc' => pc'
                          | Nm pc' => pc'
                          | Branch pc' _ => pc'
                          | RdZ pc' _ => pc'
                          | Rd pc' _ _ => pc'
                          | Wr pc' _ _ => pc'
                          | ToHost pc' _ => pc'
                          | FromHost pc' _ => pc'
                          end
        end.
    Proof.
      intros.
      destruct H; tauto.
    Qed.

    Lemma censorEq_same_pc :
      forall rf1 rf2 pm1 pm2 pc1 pc2 mem1 mem2 tr1 tr2,
        hasTrace rf1 pm1 pc1 mem1 tr1
        -> hasTrace rf2 pm2 pc2 mem2 tr2
        -> censorTrace tr1 = censorTrace tr2
        -> (tr1 = nil /\ tr2 = nil)
           \/ pc1 = pc2.
    Proof.
      intros ? ? ? ? ? ? ? ? ? ? Hht1 Hht2 Hct.
      destruct tr1; destruct tr2; try solve [tauto | simpl in Hct; discriminate].
      right.
      rewrite (pc_from_trace _ _ _ _ _ Hht1).
      rewrite (pc_from_trace _ _ _ _ _ Hht2).
      destruct t; destruct t0; simpl in Hct; congruence.
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
