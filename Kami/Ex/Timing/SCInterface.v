Require Import List.
Require Import Notations.
Require Import Coq.Numbers.BinNums.
Require Import Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.SymEvalTac Kami.Tactics Kami.ModularFacts Kami.SemFacts.
Require Import Ex.SC Ex.IsaRv32 Ex.ProcThreeStage Ex.OneEltFifo.
Require Import Ex.Timing.Specification.
Require Import Lib.CommonTactics.
Require Import Compile.Rtl Compile.CompileToRtlTryOpt.
Require Import Logic.FunctionalExtensionality.
Require Import Renaming.

Open Scope string_scope.

Ltac shatter := repeat match goal with
                       | [ H : exists _, _ |- _ ] => destruct H
                       | [ H : _ /\ _ |- _ ] => destruct H
                       end.

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
  Axiom pcth : In thMeth (getCalls p).
  Axiom pndfh : ~ In fhMeth (getDefs p).
  Axiom mndfh : ~ In fhMeth (getDefs m).
  Axiom pndth : ~ In thMeth (getDefs p).
  Axiom mndth : ~ In thMeth (getDefs m).

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

  Definition SCProcLabelAirtight (l : LabelT) : Prop :=
    match FMap.M.find execMeth (calls l) with
    | Some (existT _
                   {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                             "op" :: Bool;
                                             "data" :: Bit 32});
                      ret := Struct (STRUCT {"data" :: Bit 32}) |}
                   (argV, _)) =>
      if evalExpr (#argV!rv32iRq@."op")%kami_expr
      then True
      else evalExpr (#argV!rv32iRq@."data")%kami_expr = $0
    | _ => True
    end.

  Definition SCProcLabelSeqAirtight : LabelSeqT -> Prop := Forall SCProcLabelAirtight.

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

  Definition SCMemLabelAirtight (l : LabelT) : Prop :=
    match FMap.M.find execMeth (defs l) with
    | Some (existT _
                   {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                             "op" :: Bool;
                                             "data" :: Bit 32});
                      ret := Struct (STRUCT {"data" :: Bit 32}) |}
                   (argV, retV)) =>
      if evalExpr (#argV!rv32iRq@."op")%kami_expr
      then evalExpr (#retV!rv32iRs@."data")%kami_expr = $0
      else True
    | _ => True
    end.

  Definition SCMemLabelSeqAirtight : LabelSeqT -> Prop := Forall SCMemLabelAirtight.

End SCDefs.

Module Type SCModularHiding (SC : SCInterface).
  Module Defs := SCDefs SC.
  Import SC Defs.

  Axiom abstractToProcHiding :
    forall rf pm pc mem,
      abstractHiding rf pm pc mem ->
      SCProcHiding p (SCProcRegs rf pm pc) mem.

  Axiom ProcAirtight : forall oldregs newregs labels,
      ForwardMultistep p oldregs newregs labels ->
      SCProcLabelSeqAirtight labels.
  
  Axiom MemHiding : SCMemHiding m.

  Axiom MemSpec : SCMemSpec m.

  Axiom MemAirtight : forall oldregs newregs labels,
      ForwardMultistep m oldregs newregs labels ->
      SCMemLabelSeqAirtight labels.

End SCModularHiding.

Module SCHiding (SC : SCInterface) (Hiding : SCModularHiding SC).
  Module Defs := SCDefs SC.
  Import SC Defs Hiding.

  Lemma mncfh : ~ In fhMeth (getCalls m).
    pose (callsDisj fhMeth).
    pose pcfh.
    tauto.
  Qed.

  Lemma mncth : ~ In thMeth (getCalls m).
    pose (callsDisj thMeth).
    pose pcth.
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
    destruct (inv_censor_exec_calls la _ eq_refl) as [Haeq | [adra [opa [arga [vala [Ha Hac]]]]]];
      destruct (inv_censor_exec_calls lb _ eq_refl) as [Hbeq | [adrb [opb [argb [valb [Hb Hbc]]]]]].
    - left.
      congruence.
    - right.
      rewrite H in Haeq.
      rewrite Hbc in Haeq.
      exists adrb, opb.
      destruct opb.
      + exists $0, argb, valb, valb.
        eauto.
      + exists argb, argb, $0, valb.
        eauto.
    - right.
      rewrite <- H in Hbeq.
      rewrite Hac in Hbeq.
      exists adra, opa.
      destruct opa.
      + exists arga, $0, vala, vala. eauto.
      + exists arga, arga, vala, $0. eauto.
    - right.
      rewrite H in Hac.
      rewrite Hbc in Hac.
      inv_meth_eq.
      exists adra, opa.
      destruct opa;
      repeat match goal with
             | [ H : evalExpr _ = evalExpr _ |- _ ] => simpl in H
             end;
      subst;
      repeat eexists;
      eauto.
  Qed.

  Lemma censor_length_extract : forall la lb,
      censorLabel Defs.censorSCMeth la = censorLabel Defs.censorSCMeth lb ->
      length (Defs.extractMethsWrVals (calls la)) = length (Defs.extractMethsWrVals (calls lb)).
  Proof.
    intros la lb H.
    unfold Defs.extractMethsWrVals.
    destruct (inv_censoreq_exec_calls _ _ H) as [Heq | [? [? [? [? [? [? [Ha [Hb Hopeq]]]]]]]]].
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
                      evalExpr (STRUCT { "data" ::= #val' })%kami_expr)) /\ if op then val = val' else arg = arg'.
  Proof.
    intros la lb H.
    destruct (inv_censor_exec_memdefs la _ eq_refl) as [Haeq | [adra [opa [arga [vala [Ha Hac]]]]]];
      destruct (inv_censor_exec_memdefs lb _ eq_refl) as [Hbeq | [adrb [opb [argb [valb [Hb Hbc]]]]]].
    - left.
      congruence.
    - right.
      rewrite H in Haeq.
      rewrite Hbc in Haeq.
      exists adrb, opb.
      destruct opb.
      + exists $0, argb, valb, valb.
        eauto.
      + exists argb, argb, $0, valb.
        eauto.
    - right.
      rewrite <- H in Hbeq.
      rewrite Hac in Hbeq.
      exists adra, opa.
      destruct opa.
      + exists arga, $0, vala, vala. eauto.
      + exists arga, arga, vala, $0. eauto.
    - right.
      rewrite H in Hac.
      rewrite Hbc in Hac.
      inv_meth_eq.
      exists adra, opa.
      destruct opa;
      repeat match goal with
             | [ H : evalExpr _ = evalExpr _ |- _ ] => simpl in H
             end;
      subst;
      repeat eexists;
      eauto.
  Qed.

  Lemma censor_mem_length_extract : forall la lb,
      censorLabel Defs.censorSCMemDefs la = censorLabel Defs.censorSCMemDefs lb ->
      length (Defs.extractMethsWrVals (defs la)) = length (Defs.extractMethsWrVals (defs lb)).
  Proof.
    intros la lb H.
    unfold Defs.extractMethsWrVals.
    destruct (inv_censoreq_exec_memdefs _ _ H) as [Heq | [? [? [? [? [? [? [Ha [Hb _]]]]]]]]].
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
    exists adr, op, dat, val.
    subst.
    destruct op; tauto.
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
    exists adr, op, dat, val.
    subst.
    destruct op; tauto.
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

  Ltac meth_equal :=
    match goal with
    | [ |- Some (existT _ _ (evalExpr STRUCT {"addr" ::= #(?a); "op" ::= #(?o); "data" ::= #(?d)}%kami_expr, evalExpr STRUCT {"data" ::= #(?v)}%kami_expr)) = Some (existT _ _ (evalExpr STRUCT {"addr" ::= #(?a'); "op" ::= #(?o'); "data" ::= #(?d')}%kami_expr, evalExpr STRUCT {"data" ::= #(?v')}%kami_expr)) ] => replace a with a'; [replace o with o'; [replace d with d'; [replace v with v'; [reflexivity|]|]|]|]
    end; try reflexivity.

  Lemma inv_censor_other_calls : forall l l' meth,
      censorLabel Defs.censorSCMeth l = l' ->
      meth <> execMeth ->
      meth <> fhMeth ->
      meth <> thMeth ->
      FMap.M.find meth (calls l) = FMap.M.find meth (calls l').
  Proof.
    intros l l' meth H He Hf Ht.
    destruct l. destruct l'.
    unfold censorLabel, Defs.censorSCMeth in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f calls = calls0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find meth (FMap.M.mapi f calls) = FMap.M.find meth calls0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind He Hf Ht
    end.
    unfold Semantics.calls, Semantics.defs in *.
    remember (FMap.M.find meth calls0) as e' eqn:He'.
    clear He'.
    match goal with
    | [ H : match ?x with | _ => _ end = _ |- _ ] => destruct x
    end; try assumption.
    match goal with
    | [ H : Some _ = ?e |- _ ] => destruct e; [inv_some | discriminate]
    end.
    repeat (match goal with
            | [ H : (if ?x then _ else _) = _ |- _ ] => destruct x
            end; try tauto).
    subst.
    reflexivity.
  Qed.

  Lemma inv_censor_other_defs : forall l l' meth,
      censorLabel Defs.censorSCMeth l = l' ->
      meth <> execMeth ->
      meth <> fhMeth ->
      meth <> thMeth ->
      FMap.M.find meth (defs l) = FMap.M.find meth (defs l').
  Proof.
    intros l l' meth H He Hf Ht.
    destruct l. destruct l'.
    unfold censorLabel, Defs.censorSCMeth in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f defs = defs0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find meth (FMap.M.mapi f defs) = FMap.M.find meth defs0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind He Hf Ht
    end.
    unfold Semantics.calls, Semantics.defs in *.
    remember (FMap.M.find meth defs0) as e' eqn:He'.
    clear He'.
    match goal with
    | [ H : match ?x with | _ => _ end = _ |- _ ] => destruct x
    end; try assumption.
    match goal with
    | [ H : Some _ = ?e |- _ ] => destruct e; [inv_some | discriminate]
    end.
    repeat (match goal with
            | [ H : (if ?x then _ else _) = _ |- _ ] => destruct x
            end; try tauto).
    subst.
    reflexivity.
  Qed.

  Lemma inv_censor_other_mem_calls : forall l l' meth,
      censorLabel Defs.censorSCMemDefs l = l' ->
      meth <> execMeth ->
      FMap.M.find meth (calls l) = FMap.M.find meth (calls l').
  Proof.
    intros l l' meth H He.
    destruct l. destruct l'.
    unfold censorLabel, Defs.censorSCMemDefs in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f calls = calls0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find meth (FMap.M.mapi f calls) = FMap.M.find meth calls0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind He
    end.
    unfold Semantics.calls, Semantics.defs in *.
    remember (FMap.M.find meth calls0) as e' eqn:He'.
    clear He'.
    match goal with
    | [ H : match ?x with | _ => _ end = _ |- _ ] => destruct x
    end; try assumption.
    match goal with
    | [ H : Some _ = ?e |- _ ] => destruct e; [inv_some | discriminate]
    end.
    match goal with
    | [ H : (if ?x then _ else _) = _ |- _ ] => destruct x
    end; try tauto.
    subst.
    reflexivity.
  Qed.

  Lemma inv_censor_other_mem_defs : forall l l' meth,
      censorLabel Defs.censorSCMemDefs l = l' ->
      meth <> execMeth ->
      FMap.M.find meth (defs l) = FMap.M.find meth (defs l').
  Proof.
    intros l l' meth H He.
    destruct l. destruct l'.
    unfold censorLabel, Defs.censorSCMemDefs in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f defs = defs0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find meth (FMap.M.mapi f defs) = FMap.M.find meth defs0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind He
    end.
    unfold Semantics.calls, Semantics.defs in *.
    remember (FMap.M.find meth defs0) as e' eqn:He'.
    clear He'.
    match goal with
    | [ H : match ?x with | _ => _ end = _ |- _ ] => destruct x
    end; try assumption.
    match goal with
    | [ H : Some _ = ?e |- _ ] => destruct e; [inv_some | discriminate]
    end.
    repeat (match goal with
            | [ H : (if ?x then _ else _) = _ |- _ ] => destruct x
            end; try tauto).
    subst.
    reflexivity.
  Qed.

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
    match goal with
    | [ H : ForwardMultistep p _ _ _ |- _ ] => pose (ProcAirtight _ _ _ H)
    end.
    match goal with
    | [ H : ForwardMultistep m _ _ _ |- _ ] => pose (MemAirtight _ _ _ H)
    end.
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
          destruct (inv_censor_exec_memdefs_with_mem _ _ _ _ eq_refl H14);
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
          subst;
          try congruence;
          try reflexivity;
          try (match goal with
               | [ H : ?x = _ |- _ = ?x ] => rewrite H
               | [ H : ?x = _ |- ?x = _ ] => rewrite H
               end;
               apply functional_extensionality;
               intros;
               match goal with
               | [ |- context[if ?b then _ else _] ] => destruct b
               end;
               reflexivity).
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
                   --- unfold Defs.extractMethsWrVals in *;
                         destruct (inv_censoreq_exec_calls _ _ H6) as [Hceq | [? [? [? [? [? [? [Hca [Hcb Hceq]]]]]]]]];
                         destruct (inv_censoreq_exec_memdefs _ _ H7) as [Hdeq | [? [? [? [? [? [? [Hda [Hdb Hdeq]]]]]]]]];
                         unfold Semantics.calls, Semantics.defs in *;
                         shatter;
                         exhibit_finds;
                         subst_finds;
                         try meth_equal;
                         repeat inv_meth_eq;
                         simpl in *;
                         try match goal with
                             | [ H : (if ?x then _ else _) = (if ?x then _ else _) |- _ ] => destruct x; try inv H; subst
                             end;
                         shatter;
                         try congruence.
                   --- match goal with
                       | [ H : Step m _ _ _ |- _ ] =>
                         let Hsci := fresh in
                         pose (step_calls_in mequiv H) as Hsci;
                           unfold Semantics.calls in Hsci;
                           specialize (Hsci execMeth)
                       end.
                       erewrite <- FMap.M.F.P.F.mapi_in_iff in H23.
                       unfold censorLabel in H7.
                       inv_label.
                       rewrite H24 in H23.
                       rewrite FMap.M.F.P.F.mapi_in_iff in H23.
                       rewrite FMap.M.F.P.F.in_find_iff in H23.
                       destruct (FMap.M.find execMeth calls2); try reflexivity.
                       assert (In execMeth (getCalls m)) by (apply H23; congruence).
                       pose (callsDisj execMeth).
                       pose pcexec.
                       tauto.
                   --- match goal with
                       | [ H : Step p _ _ _ |- _ ] =>
                         let Hsdi := fresh in
                         pose (step_defs_in H) as Hsdi;
                           unfold Semantics.defs in Hsdi;
                           specialize (Hsdi execMeth)
                       end.
                       erewrite <- FMap.M.F.P.F.mapi_in_iff in H23.
                       unfold censorLabel in H6.
                       inv_label.
                       rewrite H25 in H23.
                       rewrite FMap.M.F.P.F.mapi_in_iff in H23.
                       rewrite FMap.M.F.P.F.in_find_iff in H23.
                       destruct (FMap.M.find execMeth defs1); try reflexivity.
                       assert (In execMeth (getDefs p)) by (apply H23; congruence).
                       exfalso.
                       apply pndex.
                       assumption.
                ** assert (k <> fhMeth /\ k <> thMeth).
                   --- apply FMap.M.union_In in H5.
                       destruct H5.
                       +++ match goal with
                           | [ H : Step p _ _ _ |- _ ] =>
                             let Hsdi := fresh in
                             pose (step_defs_in H) as Hsdi;
                               unfold Semantics.defs in Hsdi;
                               specialize (Hsdi k)
                           end.
                           erewrite <- FMap.M.F.P.F.mapi_in_iff in H23.
                           unfold censorLabel in H6.
                           inv_label.
                           rewrite H25 in H23.
                           rewrite FMap.M.F.P.F.mapi_in_iff in H23.
                           specialize (H23 H5).
                           pose pndfh.
                           pose pndth.
                           destruct (String.string_dec k fhMeth); subst; auto.
                           destruct (String.string_dec k thMeth); subst; auto.
                       +++ match goal with
                           | [ H : Step m _ _ _ |- _ ] =>
                             let Hsdi := fresh in
                             pose (step_defs_in H) as Hsdi;
                               unfold Semantics.defs in Hsdi;
                               specialize (Hsdi k)
                           end.
                           erewrite <- FMap.M.F.P.F.mapi_in_iff in H23.
                           unfold censorLabel in H7.
                           inv_label.
                           rewrite H25 in H23.
                           rewrite FMap.M.F.P.F.mapi_in_iff in H23.
                           specialize (H23 H5).
                           pose mndfh.
                           pose mndth.
                           destruct (String.string_dec k fhMeth); subst; auto.
                           destruct (String.string_dec k thMeth); subst; auto.
                   --- shatter.
                       repeat match goal with
                              | [ H : censorLabel ?c ?l = censorLabel ?c ?l' |- _ ] =>
                                assert (FMap.M.find k (Semantics.calls (censorLabel c l)) = FMap.M.find k (Semantics.calls (censorLabel c l'))) by (rewrite H; reflexivity);
                                  assert (FMap.M.find k (Semantics.defs (censorLabel c l)) = FMap.M.find k (Semantics.defs (censorLabel c l'))) by (rewrite H; reflexivity);
                                  clear H
                              end.
                       repeat rewrite <- (inv_censor_other_calls _ _ _ eq_refl) in H25 by assumption.
                       repeat rewrite <- (inv_censor_other_defs _ _ _ eq_refl) in H26 by assumption.
                       repeat rewrite <- (inv_censor_other_mem_calls _ _ _ eq_refl) in H6 by assumption.
                       repeat rewrite <- (inv_censor_other_mem_defs _ _ _ eq_refl) in H27 by assumption.
                       unfold Semantics.calls, Semantics.defs in *.
                       repeat rewrite FMap.M.find_union.
                       repeat rewrite FMap.M.find_union in H18.
                       simpl in *.
                       rewrite <- H25.
                       rewrite <- H26.
                       rewrite <- H6.
                       rewrite <- H27.
                       assumption.
        * unfold FMap.M.DomainSubset.
          intros.
          destruct la. destruct lb. destruct l. destruct l0.
          unfold hide, mergeLabel, Semantics.calls, Semantics.defs in *.
          rewrite In_subtractKV in *; shatter; split.
          -- match goal with
             | [ H : FMap.M.In k (FMap.M.union _ _) |- _ ] => rewrite In_union in *; destruct H
             end;
               match goal with
               | [ Hin : FMap.M.In k ?c, Hcen : _ = censorLabel _ {| annot := _; defs := _; calls := ?c |} |- _ ] =>
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
                  | [ Hin : FMap.M.In k ?d, Hcen : censorLabel _ {| annot := _; defs := ?d; calls := _ |} = _ |- _ ] =>
                    unfold censorLabel in Hcen;
                      inv_label;
                      erewrite <- FMap.M.F.P.F.mapi_in_iff in Hin;
                      match goal with
                      | [ Heq : _ |- _ ] => rewrite -> Heq in Hin
                      end;
                      rewrite FMap.M.F.P.F.mapi_in_iff in Hin;
                      tauto
                  end.
             ++ destruct (String.string_dec k fhMeth);
                  [left|destruct (String.string_dec k thMeth); [left|right]];
                  subst;
                  intros.
                ** apply FMap.M.union_In in H18.
                   destruct H18.
                   --- match goal with
                       | [ H : Step p _ _ _ |- _ ] =>
                         let Hin := fresh in
                         pose (step_defs_in H) as Hin;
                           unfold Semantics.defs in Hin;
                           specialize (Hin fhMeth)
                       end.
                       specialize (H24 H18).
                       pose pndfh.
                       auto.
                   --- match goal with
                       | [ H : Step m _ _ _ |- _ ] =>
                         let Hin := fresh in
                         pose (step_defs_in H) as Hin;
                           unfold Semantics.defs in Hin;
                           specialize (Hin fhMeth)
                       end.
                       specialize (H24 H18).
                       pose mndfh.
                       auto.
                ** apply FMap.M.union_In in H18.
                   destruct H18.
                   --- match goal with
                       | [ H : Step p _ _ _ |- _ ] =>
                         let Hin := fresh in
                         pose (step_defs_in H) as Hin;
                           unfold Semantics.defs in Hin;
                           specialize (Hin thMeth)
                       end.
                       specialize (H24 H18).
                       pose pndth.
                       auto.
                   --- match goal with
                       | [ H : Step m _ _ _ |- _ ] =>
                         let Hin := fresh in
                         pose (step_defs_in H) as Hin;
                           unfold Semantics.defs in Hin;
                           specialize (Hin thMeth)
                       end.
                       specialize (H24 H18).
                       pose mndth.
                       auto.
                ** match goal with
                   | [ H : _ -> False |- _ ] => apply H; clear H
                   end.
                   destruct (String.string_dec k execMeth).
                   --- subst.
                       repeat rewrite FMap.M.find_union.
                       replace (FMap.M.find execMeth defs1) with (None (A := {x : SignatureT & SignT x}));
                         [replace (FMap.M.find execMeth calls2) with (None (A := {x : SignatureT & SignT x}));
                          [replace (FMap.M.find execMeth calls1) with (FMap.M.find execMeth defs2); [destruct (FMap.M.find execMeth defs2); auto|]|]|].
                       +++ unfold Defs.extractMethsWrVals in *;
                             destruct (inv_censoreq_exec_calls _ _ H6) as [Hceq | [? [? [? [? [? [? [Hca [Hcb Hceq]]]]]]]]];
                             destruct (inv_censoreq_exec_memdefs _ _ H7) as [Hdeq | [? [? [? [? [? [? [Hda [Hdb Hdeq]]]]]]]]];
                             unfold Semantics.calls, Semantics.defs in *;
                             shatter;
                             exhibit_finds;
                             subst_finds;
                             try meth_equal;
                             repeat inv_meth_eq;
                             simpl in *;
                             try match goal with
                                 | [ H : (if ?x then _ else _) = (if ?x then _ else _) |- _ ] => destruct x; try inv H; subst
                                 end;
                             shatter;
                             try congruence.
                       +++ match goal with
                           | [ H : Step m _ _ _ |- _ ] =>
                             let Hsci := fresh in
                             pose (step_calls_in mequiv H) as Hsci;
                               unfold Semantics.calls in Hsci;
                               specialize (Hsci execMeth)
                           end.
                           erewrite <- FMap.M.F.P.F.mapi_in_iff in H23.
                           unfold censorLabel in H7.
                           inv_label.
                           rewrite H24 in H23.
                           rewrite FMap.M.F.P.F.mapi_in_iff in H23.
                           rewrite FMap.M.F.P.F.in_find_iff in H23.
                           destruct (FMap.M.find execMeth calls2); try reflexivity.
                           assert (In execMeth (getCalls m)) by (apply H23; congruence).
                           pose (callsDisj execMeth).
                           pose pcexec.
                           tauto.
                       +++ match goal with
                           | [ H : Step p _ _ _ |- _ ] =>
                             let Hsdi := fresh in
                             pose (step_defs_in H) as Hsdi;
                               unfold Semantics.defs in Hsdi;
                               specialize (Hsdi execMeth)
                           end.
                           erewrite <- FMap.M.F.P.F.mapi_in_iff in H23.
                           unfold censorLabel in H6.
                           inv_label.
                           rewrite H25 in H23.
                           rewrite FMap.M.F.P.F.mapi_in_iff in H23.
                           rewrite FMap.M.F.P.F.in_find_iff in H23.
                           destruct (FMap.M.find execMeth defs1); try reflexivity.
                           assert (In execMeth (getDefs p)) by (apply H23; congruence).
                           exfalso.
                           apply pndex.
                           assumption.
                   --- repeat match goal with
                              | [ H : censorLabel ?c ?l = censorLabel ?c ?l' |- _ ] =>
                                assert (FMap.M.find k (Semantics.calls (censorLabel c l)) = FMap.M.find k (Semantics.calls (censorLabel c l'))) by (rewrite H; reflexivity);
                                  assert (FMap.M.find k (Semantics.defs (censorLabel c l)) = FMap.M.find k (Semantics.defs (censorLabel c l'))) by (rewrite H; reflexivity);
                                  clear H
                              end.
                       repeat rewrite <- (inv_censor_other_calls _ _ _ eq_refl) in H23 by assumption.
                       repeat rewrite <- (inv_censor_other_defs _ _ _ eq_refl) in H24 by assumption.
                       repeat rewrite <- (inv_censor_other_mem_calls _ _ _ eq_refl) in H6 by assumption.
                       repeat rewrite <- (inv_censor_other_mem_defs _ _ _ eq_refl) in H25 by assumption.
                       unfold Semantics.calls, Semantics.defs in *.
                       repeat rewrite FMap.M.find_union.
                       repeat rewrite FMap.M.find_union in H18.
                       rewrite <- H23.
                       rewrite <- H24.
                       rewrite <- H6.
                       rewrite <- H25.
                       assumption.
    - erewrite <- censor_length_extract by eassumption.
      erewrite <- censor_mem_length_extract by eassumption.
      pose (concatWrLen [la] [lb]).
      unfold Defs.extractProcWrValSeq, Defs.extractMemWrValSeq, flat_map  in e.
      repeat rewrite app_nil_r in e.
      eapply e; repeat (econstructor; eauto).
  Qed.

  Lemma inv_censor_fh_calls : forall l l',
      censorLabel Defs.censorSCMeth l = l' ->
      FMap.M.find fhMeth (calls l) = FMap.M.find fhMeth (calls l') \/
      exists val,
        FMap.M.find fhMeth (calls l) = 
        Some (existT _
                       {| arg := Bit 0;
                          ret := Bit 32 |}
                       ($0, val)) /\
        FMap.M.find fhMeth (calls l') = 
        Some (existT _
                       {| arg := Bit 0;
                          ret := Bit 32 |}
                       ($0, $0)).
  Proof.
    intros l l' H.
    destruct l. destruct l'.
    destruct methsDistinct as [Hft [Hte Hef]].
    unfold censorLabel, Defs.censorSCMeth in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f calls = calls0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find fhMeth (FMap.M.mapi f calls) = FMap.M.find fhMeth calls0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind Hft Hte Hef
    end.
    unfold Semantics.calls, Semantics.defs in *.
    remember (FMap.M.find fhMeth calls0) as e' eqn:He'.
    clear He'.
    match goal with
    | [ H : match ?x with | _ => _ end = _ |- _ ] => destruct x
    end; try solve [ left; assumption ].
    match goal with
    | [ H : Some _ = ?e |- _ ] => destruct e; [inv_some | discriminate]
    end.
    repeat (match goal with
            | [ H : (if ?x then _ else _) = _ |- _ ] => destruct x
            end; try solve [ congruence ]).
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
    simpl in t.
    match goal with
    | [ x : word 0 |- _ ] => shatter_word x; clear x
    end.
    exists t0.
    tauto.
  Qed.

  Lemma inv_censor_th_calls : forall l l',
      censorLabel Defs.censorSCMeth l = l' ->
      FMap.M.find thMeth (calls l) = FMap.M.find thMeth (calls l') \/
      exists val,
        FMap.M.find thMeth (calls l) = 
        Some (existT _
                       {| arg := Bit 32;
                          ret := Bit 0 |}
                       (val, $0)) /\
        FMap.M.find thMeth (calls l') = 
        Some (existT _
                       {| arg := Bit 32;
                          ret := Bit 0 |}
                       ($0, $0)).
  Proof.
    intros l l' H.
    destruct l. destruct l'.
    destruct methsDistinct as [Hft [Hte Hef]].
    unfold censorLabel, Defs.censorSCMeth in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f calls = calls0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find thMeth (FMap.M.mapi f calls) = FMap.M.find thMeth calls0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind Hft Hte Hef
    end.
    unfold Semantics.calls, Semantics.defs in *.
    remember (FMap.M.find thMeth calls0) as e' eqn:He'.
    clear He'.
    match goal with
    | [ H : match ?x with | _ => _ end = _ |- _ ] => destruct x
    end; try solve [ left; assumption ].
    match goal with
    | [ H : Some _ = ?e |- _ ] => destruct e; [inv_some | discriminate]
    end.
    repeat (match goal with
            | [ H : (if ?x then _ else _) = _ |- _ ] => destruct x
            end; try solve [ congruence ]).
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
    simpl in t0.
    match goal with
    | [ x : word 0 |- _ ] => shatter_word x; clear x
    end.
    exists t.
    tauto.
  Qed.

  Ltac forgetful_subst x :=
    let Hold := fresh in
    let Hnew := fresh in
    let Hdiscard := fresh in
    pose x as Hold;
    remember Hold as Hnew eqn:Hdiscard;
    clear Hold Hdiscard;
    subst.

  Lemma inv_censor_host_fh : forall s s',
      censorHostMeth fhMeth thMeth fhMeth s = s' ->
      (s = s' /\ Defs.censorSCMeth fhMeth s = s) \/
      exists val,
        s = existT _
                   {| arg := Bit 0;
                      ret := Bit 32 |}
                   ($0, val) /\
        s' = existT _
                    {| arg := Bit 0;
                       ret := Bit 32 |}
                    ($0, $0).
  Proof.
    intros s s' H.
    pose methsDistinct. shatter.
    unfold censorHostMeth in H.
    unfold Defs.censorSCMeth.
    repeat match goal with
           | [ H : (if ?x then _ else _) = _ |- _ ] => destruct x
           | [ |- context[String.string_dec ?x ?y] ] => destruct (String.string_dec x y)
           end; try solve [ congruence ].
    repeat match goal with
           | [ s : {_ : _ & _} |- _ ] => destruct s
           end.
    repeat (match goal with
            | [ H : match ?x with | _ => _ end _ = _ |- _ ] => destruct x
            end; try solve [ left; split; auto ]).
    right.
    destruct s.
    forgetful_subst (EqdepFacts.eq_sigT_fst H).
    forgetful_subst (Semantics.sigT_eq H).
    simpl in t.
    shatter_word t.
    eexists; eauto.
  Qed.

  Lemma inv_censor_host_th : forall s s',
      censorHostMeth fhMeth thMeth thMeth s = s' ->
      (s = s' /\ Defs.censorSCMeth thMeth s = s) \/
      exists val,
        s = existT _
                   {| arg := Bit 32;
                      ret := Bit 0 |}
                   (val, $0) /\
        s' = existT _
                    {| arg := Bit 32;
                       ret := Bit 0 |}
                    ($0, $0).
  Proof.
    intros s s' H.
    pose methsDistinct. shatter.
    unfold censorHostMeth in H.
    unfold Defs.censorSCMeth.
    repeat match goal with
           | [ H : (if ?x then _ else _) = _ |- _ ] => destruct x
           | [ |- context[String.string_dec ?x ?y] ] => destruct (String.string_dec x y)
           end; try solve [ congruence ].
    repeat match goal with
           | [ s : {_ : _ & _} |- _ ] => destruct s
           end.
    repeat (match goal with
            | [ H : match ?x with | _ => _ end _ = _ |- _ ] => destruct x
            end; try solve [ left; split; auto ]).
    right.
    destruct s.
    forgetful_subst (EqdepFacts.eq_sigT_fst H).
    forgetful_subst (Semantics.sigT_eq H).
    simpl in t0.
    shatter_word t0.
    eexists; eauto.
  Qed.

  Ltac normalize := repeat match goal with
                           | [ H : context[@FMap.M.find (@sigT SignatureT (fun x : SignatureT => SignT x)) ?k ?mp] |- _ ] => replace (@FMap.M.find (@sigT SignatureT (fun x : SignatureT => SignT x)) k mp) with (@FMap.M.find (@sigT SignatureT SignT) k mp) in H by reflexivity
                           end.

  Lemma composeCensor : forall lsp lsm,
      CanCombineLabelSeq lsp lsm ->
      forall rp up rm um lsp' lsm',
      WellHiddenConcatSeq p m lsp lsm ->
      ForwardMultistep p rp up lsp ->
      ForwardMultistep m rm um lsm ->
        censorLabelSeq Defs.censorSCMeth lsp = censorLabelSeq Defs.censorSCMeth lsp' ->
        censorLabelSeq Defs.censorSCMemDefs lsm = censorLabelSeq Defs.censorSCMemDefs lsm' ->
        WellHiddenConcatSeq p m lsp' lsm' ->
        censorLabelSeq (censorHostMeth fhMeth thMeth) (composeLabels lsp lsm) =
        censorLabelSeq (censorHostMeth fhMeth thMeth) (composeLabels lsp' lsm').
  Proof.
    intro lsp;
      induction lsp as [ | lp lsp IH];
      intros;
      destruct lsm as [ | lm lsm];
      destruct lsp' as [ | lp' lsp'];
      destruct lsm' as [ | lm' lsm'];
      try solve [ simpl in *; congruence ].
    repeat match goal with
           | [ H : context[_ :: _] |- _ ] => inv H
           end.
    unfold censorLabelSeq.
    unfold composeLabels; fold composeLabels.
    repeat match goal with
           | [ |- context[map ?f (?h :: ?t)] ] => replace (map f (h :: t)) with (f h :: map f t) by reflexivity
           end.
    repeat match goal with
           | [ |- context[map (censorLabel ?f) ?ls] ] => replace (map (censorLabel f) ls) with (censorLabelSeq f ls) by reflexivity
           end.
    f_equal; try solve [ eapply IH; eauto ].
    destruct lp as [ap dp cp].
    destruct lm as [am dm cm].
    destruct lp' as [ap' dp' cp'].
    destruct lm' as [am' dm' cm'].
    unfold mergeLabel, annot, defs, calls in *.
    unfold censorLabel, hide, annot, calls, defs.
    f_equal.
    - unfold censorLabel in *.
      repeat inv_label.
      subst.
      reflexivity.
    - FMap.M.ext k.
      repeat rewrite FMap.M.F.P.F.mapi_o by (intros ? ? ? Heq; rewrite Heq; reflexivity).
      destruct (String.string_dec k execMeth);
        [|destruct (String.string_dec k fhMeth);
          [|destruct (String.string_dec k thMeth)]];
        subst.
      + unfold WellHiddenConcat, wellHidden, mergeLabel, hide, calls, defs in H16, H11.
        shatter.
        specialize (H execMeth).
        specialize (H3 execMeth).
        rewrite FMap.M.F.P.F.not_find_in_iff in H.
        rewrite FMap.M.F.P.F.not_find_in_iff in H3.
        assert (In execMeth (getCalls (p ++ m)%kami));
          [|rewrite H by assumption; rewrite H3 by assumption; reflexivity].
        apply getCalls_in_1.
        apply pcexec.
      + repeat rewrite FMap.M.subtractKV_find.
        repeat rewrite FMap.M.find_union.
        assert (FMap.M.find fhMeth dp = (None (A := {x : SignatureT & SignT x})));
          [|assert (FMap.M.find fhMeth dm = (None (A := {x : SignatureT & SignT x})))].
        * match goal with
          | [ H : Step p _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_defs_in H) as Hin;
              simpl in Hin;
              specialize (Hin fhMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find fhMeth dp); try reflexivity.
          assert (In fhMeth (getDefs p)) by (apply H; congruence).
          apply pndfh in H2.
          tauto.
        * match goal with
          | [ H : Step m _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_defs_in H) as Hin;
              simpl in Hin;
              specialize (Hin fhMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find fhMeth dm); try reflexivity.
          assert (In fhMeth (getDefs m)) by (apply H2; congruence).
          apply mndfh in H3.
          tauto.
        * rewrite H.
          rewrite H2.
          unfold censorLabel in *; repeat inv_label.
          repeat match goal with
                 | [ H : FMap.M.mapi ?f ?mp = FMap.M.mapi ?f ?mp' |- _ ] => assert (FMap.M.find fhMeth (FMap.M.mapi f mp) = FMap.M.find fhMeth (FMap.M.mapi f mp')) by (f_equal; assumption); clear H
                 end.
          repeat rewrite FMap.M.F.P.F.mapi_o in * by (intros ? ? ? Heq; rewrite Heq; reflexivity).
          normalize.
          rewrite H in H19.
          destruct (FMap.M.find fhMeth dp'); try solve [simpl in H19; congruence].
          rewrite H2 in H5.
          destruct (FMap.M.find fhMeth dm'); try solve [simpl in H5; congruence].
      + repeat rewrite FMap.M.subtractKV_find.
        repeat rewrite FMap.M.find_union.
        assert (FMap.M.find thMeth dp = (None (A := {x : SignatureT & SignT x})));
          [|assert (FMap.M.find thMeth dm = (None (A := {x : SignatureT & SignT x})))].
        * match goal with
          | [ H : Step p _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_defs_in H) as Hin;
              simpl in Hin;
              specialize (Hin thMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find thMeth dp); try reflexivity.
          assert (In thMeth (getDefs p)) by (apply H; congruence).
          apply pndth in H2.
          tauto.
        * match goal with
          | [ H : Step m _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_defs_in H) as Hin;
              simpl in Hin;
              specialize (Hin thMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find thMeth dm); try reflexivity.
          assert (In thMeth (getDefs m)) by (apply H2; congruence).
          apply mndth in H3.
          tauto.
        * rewrite H.
          rewrite H2.
          unfold censorLabel in *.
          repeat inv_label.
          repeat match goal with
                 | [ H : FMap.M.mapi ?f ?mp = FMap.M.mapi ?f ?mp' |- _ ] => assert (FMap.M.find thMeth (FMap.M.mapi f mp) = FMap.M.find thMeth (FMap.M.mapi f mp')) by (f_equal; assumption); clear H
                 end.
          repeat rewrite FMap.M.F.P.F.mapi_o in * by (intros ? ? ? Heq; rewrite Heq; reflexivity).
          normalize.
          rewrite H in H19.
          destruct (FMap.M.find thMeth dp'); try solve [simpl in H19; congruence].
          rewrite H2 in H5.
          destruct (FMap.M.find thMeth dm'); try solve [simpl in H5; congruence].
      + repeat match goal with
               | [ H : censorLabel ?c ?l = censorLabel ?c ?l' |- _ ] =>
                 assert (FMap.M.find k (Semantics.calls (censorLabel c l)) = FMap.M.find k (Semantics.calls (censorLabel c l'))) by (rewrite H; reflexivity);
                   assert (FMap.M.find k (Semantics.defs (censorLabel c l)) = FMap.M.find k (Semantics.defs (censorLabel c l'))) by (rewrite H; reflexivity);
                   clear H
               end.
        repeat rewrite <- (inv_censor_other_calls _ _ _ eq_refl) in H by assumption.
        repeat rewrite <- (inv_censor_other_defs _ _ _ eq_refl) in H2 by assumption.
        repeat rewrite <- (inv_censor_other_mem_calls _ _ _ eq_refl) in H3 by assumption.
        repeat rewrite <- (inv_censor_other_mem_defs _ _ _ eq_refl) in H5 by assumption.
        unfold calls, defs in *.
        repeat rewrite FMap.M.subtractKV_find.
        repeat rewrite FMap.M.find_union.
        rewrite H; rewrite H2; rewrite H3; rewrite H5; reflexivity.
    - FMap.M.ext k.
      repeat rewrite FMap.M.F.P.F.mapi_o by (intros ? ? ? Heq; rewrite Heq; reflexivity).
      destruct (String.string_dec k execMeth);
        [|destruct (String.string_dec k fhMeth);
          [|destruct (String.string_dec k thMeth)]];
        subst.
      + unfold WellHiddenConcat, wellHidden, mergeLabel, hide, calls, defs in H16, H11.
        shatter.
        specialize (H2 execMeth).
        specialize (H10 execMeth).
        rewrite FMap.M.F.P.F.not_find_in_iff in H2.
        rewrite FMap.M.F.P.F.not_find_in_iff in H10.
        assert (In execMeth (getDefs (p ++ m)%kami));
          [|rewrite H2 by assumption; rewrite H10 by assumption; reflexivity].
        apply getDefs_in_2.
        apply mdexec.
      + repeat rewrite FMap.M.subtractKV_find.
        repeat rewrite FMap.M.find_union.
        assert (FMap.M.find fhMeth dp = (None (A := {x : SignatureT & SignT x})));
          [|assert (FMap.M.find fhMeth dm = (None (A := {x : SignatureT & SignT x})));
            [|assert (FMap.M.find fhMeth cm = (None (A := {x : SignatureT & SignT x})))]].
        * match goal with
          | [ H : Step p _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_defs_in H) as Hin;
              simpl in Hin;
              specialize (Hin fhMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find fhMeth dp); try reflexivity.
          assert (In fhMeth (getDefs p)) by (apply H; congruence).
          apply pndfh in H2.
          tauto.
        * match goal with
          | [ H : Step m _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_defs_in H) as Hin;
              simpl in Hin;
              specialize (Hin fhMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find fhMeth dm); try reflexivity.
          assert (In fhMeth (getDefs m)) by (apply H2; congruence).
          apply mndfh in H3.
          tauto.
        * match goal with
          | [ H : Step m _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_calls_in mequiv H) as Hin;
              simpl in Hin;
              specialize (Hin fhMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find fhMeth cm); try reflexivity.
          assert (In fhMeth (getCalls m)) by (apply H3; congruence).
          apply mncfh in H10.
          tauto.
        * rewrite H.
          rewrite H2.
          rewrite H3.
          unfold censorLabel in *; repeat inv_label.
          repeat match goal with
                 | [ H : FMap.M.mapi ?f ?mp = FMap.M.mapi ?f ?mp' |- _ ] => assert (FMap.M.find fhMeth (FMap.M.mapi f mp) = FMap.M.find fhMeth (FMap.M.mapi f mp')) by (f_equal; assumption); clear H
                 end.
          repeat rewrite FMap.M.F.P.F.mapi_o in * by (intros ? ? ? Heq; rewrite Heq; reflexivity).
          normalize.
          rewrite H in H20.
          destruct (FMap.M.find fhMeth dp'); try solve [simpl in H20; congruence].
          rewrite H2 in H10.
          destruct (FMap.M.find fhMeth dm'); try solve [simpl in H10; congruence].
          rewrite H3 in H19.
          destruct (FMap.M.find fhMeth cm'); try solve [simpl in H19; congruence].
          destruct (FMap.M.Map.find fhMeth cp); destruct (FMap.M.Map.find fhMeth cp'); simpl in *; try congruence.
          f_equal.
          pose methsDistinct.
          destruct (inv_censor_host_fh s _ eq_refl);
            destruct (inv_censor_host_fh s0 _ eq_refl);
            shatter; subst; try congruence.
          -- rewrite H23 in H17.
             inv H17.
             unfold Defs.censorSCMeth, censorHostMeth.
             repeat match goal with
                    | [ |- context[String.string_dec ?x ?y] ] => destruct (String.string_dec x y); try congruence
                    end.
             reflexivity.
          -- rewrite H22 in H17.
             inv H17.
             unfold Defs.censorSCMeth, censorHostMeth.
             repeat match goal with
                    | [ |- context[String.string_dec ?x ?y] ] => destruct (String.string_dec x y); try congruence
                    end.
             reflexivity.
      + repeat rewrite FMap.M.subtractKV_find.
        repeat rewrite FMap.M.find_union.
        assert (FMap.M.find thMeth dp = (None (A := {x : SignatureT & SignT x})));
          [|assert (FMap.M.find thMeth dm = (None (A := {x : SignatureT & SignT x})));
            [|assert (FMap.M.find thMeth cm = (None (A := {x : SignatureT & SignT x})))]].
        * match goal with
          | [ H : Step p _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_defs_in H) as Hin;
              simpl in Hin;
              specialize (Hin thMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find thMeth dp); try reflexivity.
          assert (In thMeth (getDefs p)) by (apply H; congruence).
          apply pndth in H2.
          tauto.
        * match goal with
          | [ H : Step m _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_defs_in H) as Hin;
              simpl in Hin;
              specialize (Hin thMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find thMeth dm); try reflexivity.
          assert (In thMeth (getDefs m)) by (apply H2; congruence).
          apply mndth in H3.
          tauto.
        * match goal with
          | [ H : Step m _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_calls_in mequiv H) as Hin;
              simpl in Hin;
              specialize (Hin thMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find thMeth cm); try reflexivity.
          assert (In thMeth (getCalls m)) by (apply H3; congruence).
          apply mncth in H10.
          tauto.
        * rewrite H.
          rewrite H2.
          rewrite H3.
          unfold censorLabel in *.
          repeat inv_label.
          repeat match goal with
                 | [ H : FMap.M.mapi ?f ?mp = FMap.M.mapi ?f ?mp' |- _ ] => assert (FMap.M.find thMeth (FMap.M.mapi f mp) = FMap.M.find thMeth (FMap.M.mapi f mp')) by (f_equal; assumption); clear H
                 end.
          repeat rewrite FMap.M.F.P.F.mapi_o in * by (intros ? ? ? Heq; rewrite Heq; reflexivity).
          normalize.
          rewrite H in H20.
          destruct (FMap.M.find thMeth dp'); try solve [simpl in H20; congruence].
          rewrite H2 in H10.
          destruct (FMap.M.find thMeth dm'); try solve [simpl in H10; congruence].
          rewrite H3 in H19.
          destruct (FMap.M.find thMeth cm'); try solve [simpl in H19; congruence].
          destruct (FMap.M.Map.find thMeth cp); destruct (FMap.M.Map.find thMeth cp'); simpl in *; try congruence.
          f_equal.
          pose methsDistinct.
          destruct (inv_censor_host_th s _ eq_refl);
            destruct (inv_censor_host_th s0 _ eq_refl);
            shatter; subst; try congruence.
          -- rewrite H23 in H17.
             inv H17.
             unfold Defs.censorSCMeth, censorHostMeth.
             repeat match goal with
                    | [ |- context[String.string_dec ?x ?y] ] => destruct (String.string_dec x y); try congruence
                    end.
             reflexivity.
          -- rewrite H22 in H17.
             inv H17.
             unfold Defs.censorSCMeth, censorHostMeth.
             repeat match goal with
                    | [ |- context[String.string_dec ?x ?y] ] => destruct (String.string_dec x y); try congruence
                    end.
             reflexivity.
      + repeat match goal with
               | [ H : censorLabel ?c ?l = censorLabel ?c ?l' |- _ ] =>
                 assert (FMap.M.find k (Semantics.calls (censorLabel c l)) = FMap.M.find k (Semantics.calls (censorLabel c l'))) by (rewrite H; reflexivity);
                   assert (FMap.M.find k (Semantics.defs (censorLabel c l)) = FMap.M.find k (Semantics.defs (censorLabel c l'))) by (rewrite H; reflexivity);
                   clear H
               end.
        repeat rewrite <- (inv_censor_other_calls _ _ _ eq_refl) in H by assumption.
        repeat rewrite <- (inv_censor_other_defs _ _ _ eq_refl) in H2 by assumption.
        repeat rewrite <- (inv_censor_other_mem_calls _ _ _ eq_refl) in H3 by assumption.
        repeat rewrite <- (inv_censor_other_mem_defs _ _ _ eq_refl) in H5 by assumption.
        unfold calls, defs in *.
        repeat rewrite FMap.M.subtractKV_find.
        repeat rewrite FMap.M.find_union.
        rewrite H; rewrite H2; rewrite H3; rewrite H5; reflexivity.
  Qed.

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
      eapply composeCensor; eauto.
      eapply concatCensor; eauto.
    - erewrite fhCombine; eauto.
      eapply combineCensor; eauto.
  Qed.

End SCHiding.
