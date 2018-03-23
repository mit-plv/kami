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
  | Nop
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
      hasTrace rf pm pc mem (Nop :: trace')
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
                | Nop => Nop
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
  Proof. (*
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
    Qed. *) Admitted.

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
      match FMap.M.find "fromHost" cs with
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
    if String.string_dec n "toHost"
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

  (* Security property to be applied to a complete processor++memory
   module, where the only external method calls are toHost/fromHost *)
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

Ltac shatter := repeat match goal with
                       | [ H : exists _, _ |- _ ] => destruct H
                       | [ H : _ /\ _ |- _ ] => destruct H
                       end.

Section SCTiming.

  Definition rv32iRq := RqFromProc rv32iAddrSize rv32iDataBytes.
  Definition rv32iRs := RsToProc rv32iDataBytes.

  Definition rv32iProcInst :=
    procInst rv32iGetOptype
             rv32iGetLdDst rv32iGetLdAddr rv32iGetLdSrc rv32iCalcLdAddr
             rv32iGetStAddr rv32iGetStSrc rv32iCalcStAddr rv32iGetStVSrc
             rv32iGetSrc1 rv32iGetSrc2 rv32iGetDst
             rv32iExec rv32iNextPc rv32iAlignPc rv32iAlignAddr
             (procInitDefault  _ _ _ _).

  Definition SCRegs rf pm pc : RegsT :=
    FMap.M.add "rf" (existT _ (SyntaxKind (Vector (Bit 32) 5)) rf)
               (FMap.M.add "pgm" (existT _ (SyntaxKind (Vector (Bit 32) 8)) pm)
                           (FMap.M.add "pc" (existT _ (SyntaxKind (Bit 16)) pc)
                                                   (FMap.M.empty _))).

  Lemma SCRegs_find_rf : forall rf pm pc rf',
      FMap.M.find (elt:={x : FullKind & fullType type x}) "rf"
                                   (SCRegs rf pm pc) =
                       Some
                         (existT (fullType type) (SyntaxKind (Vector (Bit 32) 5)) rf') -> rf = rf'.
  Proof.
    intros.
    unfold SCRegs in *.
    FMap.findeq.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1).
  Qed.

  Lemma SCRegs_find_pm : forall rf pm pc pm',
      FMap.M.find (elt:={x : FullKind & fullType type x}) "pgm"
                  (SCRegs rf pm pc) =
      Some
        (existT (fullType type) (SyntaxKind (Vector (Bit 32) 8)) pm') -> pm = pm'.
  Proof.
    intros.
    unfold SCRegs in *.
    FMap.findeq.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1).
  Qed.

  Lemma SCRegs_find_pc : forall rf pm pc pc',
      FMap.M.find (elt:={x : FullKind & fullType type x}) "pc"
                  (SCRegs rf pm pc) =
      Some
        (existT (fullType type) (SyntaxKind (Bit 16)) pc') -> pc = pc'.
  Proof.
    intros.
    unfold SCRegs in *.
    FMap.findeq.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1).
  Qed.

  Ltac SCRegs_find :=
    repeat match goal with
           | [ H : FMap.M.find "rf" (SCRegs ?rf _ _) = Some (existT _ _ ?rf') |- _ ] => assert (rf = rf') by (eapply SCRegs_find_rf; eassumption); subst; clear H
           | [ H : FMap.M.find "pgm" (SCRegs _ ?pm _) = Some (existT _ _ ?pm') |- _ ] => assert (pm = pm') by (eapply SCRegs_find_pm; eassumption); subst; clear H
           | [ H : FMap.M.find "pc" (SCRegs _ _ ?pc) = Some (existT _ _ ?pc') |- _ ] => assert (pc = pc') by (eapply SCRegs_find_pc; eassumption); subst; clear H
           end.
  
  Definition censorSCMeth (n : String.string) (t : {x : SignatureT & SignT x}) : {x : SignatureT & SignT x} :=
    if String.string_dec n "exec"
    then match t with
         | existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (argV, retV) =>
           existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (evalExpr (STRUCT { "addr" ::= #argV!rv32iRq@."addr";
                                      "op" ::= #argV!rv32iRq@."op";
                                      "data" ::= $0 })%kami_expr,
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

  Definition callsToTraceEvent (c : MethsT) : option TraceEvent :=
    match FMap.M.find "fromHost" c with
    | Some (existT _
                   {| arg := Bit 0;
                      ret := Bit 32 |}
                   (argV, retV)) =>
      Some (FromHost $0 retV)
    | None =>
      match FMap.M.find "toHost" c with
      | Some (existT _
                     {| arg := Bit 32;
                        ret := Bit 0 |}
                     (argV, retV)) =>
        Some (ToHost $0 argV)
      | None =>
        match FMap.M.find "exec" c with
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
  | RtNop : forall lbl trace' ls',
      annot lbl = None \/ annot lbl = Some None ->
      calls lbl = FMap.M.empty _ ->
      relatedTrace trace' ls' ->
      relatedTrace (Nop :: trace') (lbl :: ls')
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
      relatedTrace trace ls -> extractFhTrace trace = extractFhLabelSeq ls.
  Proof. (*
    induction 1; try eauto;
      simpl;
      match goal with
      | [ H : ?a = ?b |- ?a = ?c ++ ?b ] => assert (Hnil : c = nil); [ idtac | rewrite Hnil; simpl; assumption ]
      | [ H : ?a = ?b |- ?v :: ?a = ?c ++ ?b ] => assert (Hval : c = cons v nil); [ idtac | rewrite Hval; simpl; rewrite H; reflexivity ]
      end;
      match goal with
      | [ |- extractFhLabel ?l = _ ] => destruct l
      end;
      unfold labelToTraceEvent, callsToTraceEvent in *;
      unfold extractFhLabel, extractFhMeths;
      repeat (match goal with
              | [ H : match ?x with | _ => _ end = _ |- _ ] => destruct x
              | [ H : match ?x with | _ => _ end _ = _ |- _ ] => destruct x
              | [ s : {_ : _ & _} |- _ ] => destruct s
              | [ x : SignatureT |- _ ] => destruct x
              end; try congruence; try discriminate).
    - match goal with
      | [ H : Some _ = Some _ |- _ ] => inversion H
      end.
      reflexivity.
    - simpl in *.
      subst.
      FMap.findeq.
  Qed. *) Admitted.

  Inductive SCProcMemConsistent : LabelSeqT -> memory -> Prop :=
  | SPMCnil : forall mem, SCProcMemConsistent nil mem
  | SPMCcons : forall mem l mem' ls,
      match FMap.M.find "exec" (calls l) with
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
      extractFhLabelSeq labels = fhs ->
      forall fhs',
        length fhs = length fhs' ->
        exists labels' newRegs',
          ForwardMultistep m regs newRegs' labels' /\
          SCProcMemConsistent labels' mem /\
          censorLabelSeq censorSCMeth labels = censorLabelSeq censorSCMeth  labels' /\
          extractFhLabelSeq labels' = fhs'.

  (* A [subst] tactic that doesn't unfold definitions *)
  Ltac opaque_subst :=
    repeat match goal with
           | [ Heq : ?x = ?y |- _ ] => ((tryif unfold x then fail else subst x) || (tryif unfold y then fail else subst y))
           end.

  Lemma SCProcSubsteps :
    forall o (ss : Substeps rv32iProcInst o),
      SubstepsInd rv32iProcInst o (foldSSUpds ss) (foldSSLabel ss) ->
      (((foldSSLabel ss) = {| annot := None; defs := FMap.M.empty _; calls := FMap.M.empty _ |}
        \/ (foldSSLabel ss) = {| annot := Some None; defs := FMap.M.empty _; calls := FMap.M.empty _ |})
       /\ (foldSSUpds ss) = FMap.M.empty _)
      \/ (exists k a u cs,
            In (k :: a)%struct (getRules rv32iProcInst)
            /\ SemAction o (a type) u cs WO
            /\ (foldSSLabel ss) = {| annot := Some (Some k); defs := FMap.M.empty _; calls := cs |}
            /\ (foldSSUpds ss) = u).
  Proof. (*
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
  Qed. *) Admitted.

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
      extractFhLabelSeq l1 = f ->
      exists l1',
        ForwardMultistep m o n l1' /\
        SCProcMemConsistent l1' mem /\
        censorLabelSeq censorSCMeth l0 = censorLabelSeq censorSCMeth l1' /\
        extractFhLabelSeq l1' = f.
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
      ForwardMultistep rv32iProcInst (SCRegs rf1 pm pc) newRegs1 ls1 ->
      SCProcMemConsistent ls1 mem1 ->
      ForwardMultistep rv32iProcInst (SCRegs rf2 pm pc) newRegs2 ls2 ->
      SCProcMemConsistent ls2 mem2 ->
      relatedTrace trace1 ls1 ->
      relatedTrace trace2 ls2 ->
      censorTrace trace1 = censorTrace trace2 ->
      censorLabelSeq censorSCMeth (canonicalize ls1) = censorLabelSeq censorSCMeth (canonicalize ls2).
  Proof. (*
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
      | [ Hct : censorTrace (Nop :: _) = censorTrace ?tr |- _ ] =>
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
        end; try discriminate.
      f_equal.
      match goal with
      | [ H : foldSSUpds ss = _, H0 : foldSSUpds ss0 = _ |- _ ] => rewrite H in *; rewrite H0 in *; simpl
      end.
      match goal with
      | [ H : hasTrace _ _ _ _ (Nop :: _) |- _ ] => inversion H
      end; subst.
      eapply IHHht1; try eassumption;
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
      intuition idtac; kinv_action_dest; SCRegs_find; expr_equalities; try tauto; try discriminate.
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
      intuition idtac; kinv_action_dest; SCRegs_find;
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
        unfold censorLabel, censorSCMeth, hide, annot, calls, defs.
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
          | [ |- FMap.M.union (FMap.M.add "rf" (existT _ _ ?r1) (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _))) _ = SCRegs ?r2 _ ?p2 ] => unfold SCRegs; replace r1 with r2
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
          | [ |- FMap.M.union (FMap.M.add "rf" (existT _ _ ?r1) (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _))) _ = SCRegs ?r2 _ ?p2 ] => unfold SCRegs; replace r1 with r2; [ replace p1 with p2 by congruence | idtac ]
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
      intuition idtac; kinv_action_dest; SCRegs_find; expr_equalities; try tauto; try discriminate.
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
        intuition idtac; kinv_action_dest; SCRegs_find;
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
             unfold SCRegs; clear; eauto.
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
             | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) _ = SCRegs _ _ ?p2 ] => unfold SCRegs; replace p1 with p2 by congruence
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
      intuition idtac; kinv_action_dest; SCRegs_find; expr_equalities; try tauto; try discriminate.
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
      intuition idtac; kinv_action_dest; SCRegs_find;
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
        unfold censorLabel, censorSCMeth, hide, annot, calls, defs.
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
          unfold SCRegs; clear; eauto.
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
          | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) _ = SCRegs _ _ ?p2 ] => unfold SCRegs; replace p1 with p2 by congruence
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
      intuition idtac; kinv_action_dest; SCRegs_find; expr_equalities; try tauto; try discriminate.
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
      intuition idtac; kinv_action_dest; SCRegs_find;
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
        unfold censorLabel; f_equal.
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
          clear; unfold SCRegs; eauto.
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
          | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) _ = SCRegs _ _ ?p2 ] => unfold SCRegs; replace p1 with p2 by congruence
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
      intuition idtac; kinv_action_dest; SCRegs_find; expr_equalities; try tauto; try discriminate.
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
        intuition idtac; kinv_action_dest; SCRegs_find;
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
          unfold censorLabel; f_equal.
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
             | [ |- FMap.M.union (FMap.M.add "rf" (existT _ _ ?r1) (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _))) _ = SCRegs ?r2 _ ?p2 ] => unfold SCRegs; replace r1 with r2
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
             | [ |- FMap.M.union (FMap.M.add "rf" (existT _ _ ?r1) (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _))) _ = SCRegs ?r2 _ ?p2 ] => unfold SCRegs; replace r1 with r2; [ replace p1 with p2 by congruence | idtac ]
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
        intuition idtac; kinv_action_dest; SCRegs_find;
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
          unfold censorLabel; f_equal.
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
             | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) (SCRegs ?r1 _ _) = SCRegs ?r2 _ ?p2 ] => unfold SCRegs; replace r2 with r1
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
             | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) (SCRegs ?r1 _ _) = SCRegs ?r2 _ ?p2 ] => unfold SCRegs; replace r2 with r1; [ replace p1 with p2 by congruence | idtac ]
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
        intuition idtac; kinv_action_dest; SCRegs_find; expr_equalities; try tauto; try discriminate.
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
          intuition idtac; kinv_action_dest; SCRegs_find;
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
             unfold SCRegs; clear; eauto.
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
             | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) _ = SCRegs _ _ ?p2 ] => unfold SCRegs; replace p1 with p2 by congruence
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
        intuition idtac; kinv_action_dest; SCRegs_find; expr_equalities; try tauto; try discriminate.
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
          intuition idtac; kinv_action_dest; SCRegs_find;
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
             unfold SCRegs; clear; eauto.
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
             | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) _ = SCRegs _ _ ?p2 ] => unfold SCRegs; replace p1 with p2 by congruence
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
      intuition idtac; kinv_action_dest; SCRegs_find; expr_equalities; try tauto; try discriminate.
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
        intuition idtac; kinv_action_dest; SCRegs_find;
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
          | [ |- FMap.M.union (FMap.M.add "rf" (existT _ _ ?r1) (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _))) _ = SCRegs ?r2 _ ?p2 ] => unfold SCRegs; replace r1 with r2
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
          | [ |- FMap.M.union (FMap.M.add "rf" (existT _ _ ?r1) (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _))) _ = SCRegs ?r2 _ ?p2 ] => unfold SCRegs; replace r1 with r2; [ replace p1 with p2 by congruence | idtac ]
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
        intuition idtac; kinv_action_dest; SCRegs_find;
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
          | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) (SCRegs ?r1 _ _) = SCRegs ?r2 _ ?p2 ] => unfold SCRegs; replace r2 with r1
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
          | [ |- FMap.M.union (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _)) (SCRegs ?r1 _ _) = SCRegs ?r2 _ ?p2 ] => unfold SCRegs; replace r2 with r1; [ replace p1 with p2 by congruence | idtac ]
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
  Qed. *) Admitted.

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
        ForwardMultistep rv32iProcInst (SCRegs rf pm pc) newRegs ls /\
        SCProcMemConsistent ls mem /\
        relatedTrace trace ls.
  Proof. (*
    induction 1.
    - repeat eexists; repeat econstructor.
    - shatter.
      repeat eexists.
      + eapply FMulti.
        * apply SemFacts.substepZero_imp_step.
          -- reflexivity.
          -- eapply EmptyRule.
        * simpl. congruence.
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
        * simpl. congruence.
        * match goal with
          | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
          end.
          unfold SCRegs, rset.
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
        * simpl. congruence.
        * match goal with
          | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
          end.
          unfold SCRegs, rset.
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
        * simpl. congruence.
        * match goal with
          | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
          end.
          unfold SCRegs.
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
        * simpl. congruence.
        * match goal with
          | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
          end.
          unfold SCRegs.
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
          -- simpl. congruence.
          -- match goal with
             | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
             end.
             unfold SCRegs, rset.
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
          -- simpl. congruence.
          -- match goal with
             | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
             end.
             unfold SCRegs, rset.
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
        * simpl. congruence.
        * match goal with
          | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
          end.
          unfold SCRegs, rset.
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
          -- simpl. congruence.
          -- match goal with
             | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
             end.
             unfold SCRegs, rset.
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
          -- simpl. congruence.
          -- match goal with
             | [ IH : ForwardMultistep _ ?r _ _ |- ForwardMultistep _ ?r' _ _ ] => replace r' with r; try eassumption
             end.
             unfold SCRegs, rset.
             eauto.
        * econstructor; try eassumption.
          simplify_match.
          reflexivity.
        * constructor; (eauto || discriminate).
          Unshelve.
          -- exact (evalExpr (STRUCT { "data" ::= $0 }))%kami_expr.
          -- exact (wzero _).
  Qed. *) Admitted.

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
      ForwardMultistep rv32iProcInst (SCRegs rf pm pc) newRegs ls ->
      SCProcMemConsistent ls mem ->
      exists trace,
        hasTrace rf pm pc mem trace /\
        relatedTrace trace ls.
  Proof. (*
    intros rf pm pc mem newRegs ls Hfm Hmem.
    let Heq := fresh in
    remember (SCRegs rf pm pc) as regs eqn:Heq; unfold SCRegs in Heq;
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
        | [ H : relatedTrace ?t ?ls |- exists _, _ /\ relatedTrace _ (_ :: ?ls) ] => exists (Nop :: t)
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
  Qed. *) Admitted.

  Theorem abstractToSCProcHiding :
    forall rf pm pc mem,
      abstractHiding rf pm pc mem ->
      SCProcHiding rv32iProcInst (SCRegs rf pm pc) mem.
  Proof.
    unfold abstractHiding, SCProcHiding.
    intros.
    match goal with
    | [ H : ForwardMultistep _ _ _ _ |- _ ] => let H' := fresh in assert (H' := H); eapply SCToAbstractRelated in H'; try eassumption
    end.
    shatter.
    match goal with
    | [ Hrel : relatedTrace ?t ?ls,
               Hextract : extractFhLabelSeq ?ls = _,
                          Htrace : hasTrace _ _ _ _ _,
                                   Habs : forall _ _, hasTrace _ _ _ _ _ -> extractFhTrace _ = _ -> forall _, length _ = length _ -> _,
          Hlen : length _ = length _
          |- context[extractFhLabelSeq _ = ?fhTrace] ] =>
      rewrite <- (relatedFhTrace _ _ Hrel) in Hextract; specialize (Habs _ _ Htrace Hextract fhTrace Hlen)
    end.
    shatter.
    match goal with
    | [ Htrace : hasTrace _ _ _ _ ?t,
                 Hextract : extractFhTrace ?t = ?fhTrace
        |- context[?fhTrace] ] => pose (abstractToSCRelated _ _ _ _ _ Htrace)
    end.
    shatter.
    assert (censorLabelSeq censorSCMeth (canonicalize labels) = censorLabelSeq censorSCMeth (canonicalize x2)).
    - eapply (relatedCensor _ _ _ _ _ _ _ _ _ _ _ _ H4 H(* H0 H1 H8 H9 H5*)); eassumption.
    - pose (decanon _ 
    match goal with
    | [ H : ForwardMultistep _ _ ?regs ?ls |- _ ] => exists ls, regs
    end.
    intuition idtac; try assumption;
      match goal with
      | [ Htrace1 : hasTrace _ _ _ _ _, Htrace2 : hasTrace _ _ _ _ _ |- censorLabelSeq _ _ = censorLabelSeq _ _ ] =>
(*        pose (relatedCensor _ _ _ _ _ _ _ _ _ _ _ _ Htrace1 Htrace2)(*; eassumption*)*) idtac
      | [ |- extractFhLabelSeq _ = _ ] => erewrite <- relatedFhTrace; eassumption
      end.
    pose (relatedCensor _ _ _ _ _ _ _ _ _ _ _ _ H4 H H0 H1 H8 H9).
    pose (relatedCensor 
  Qed.

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

  Definition rv32iMemInstSingle := MODULE {
    Register "mem" : Vector (MemTypes.Data rv32iDataBytes) rv32iAddrSize <- Default

    with Method "exec" (a : Struct rv32iRq) : Struct rv32iRs := (rv32iMemInstExec a)
  }.

  Lemma SCMemSubsteps :
    forall o (ss : Substeps rv32iMemInstSingle o),
      SubstepsInd rv32iMemInstSingle o (foldSSUpds ss) (foldSSLabel ss) ->
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
        | [ HIn : In _ (getRules rv32iMemInstSingle) |- _ ] => simpl in HIn; tauto
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

  Definition censorSCMemDefs (n : String.string) (t : {x : SignatureT & SignT x}) : {x : SignatureT & SignT x} :=
    if String.string_dec n "exec"
    then match t with
         | existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (argV, retV) =>
           existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (evalExpr (STRUCT { "addr" ::= #argV!rv32iRq@."addr";
                                      "op" ::= #argV!rv32iRq@."op";
                                      "data" ::= $0 })%kami_expr,
                   evalExpr (STRUCT { "data" ::= $0 })%kami_expr)
         | _ => t
         end
    else t.

  Definition extractWrVals (l : LabelT) : list (word 32) :=
    match l with
    | {| annot := _;
         defs := ds;
         calls := _; |} => 
      match FMap.M.find "exec" ds with
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
      end
    end.
    
  Definition extractWrValSeq : LabelSeqT -> list (word 32) :=
    flat_map extractWrVals.

  Definition SCMemRegs mem : RegsT :=
    FMap.M.add "mem" (existT _ (SyntaxKind (Vector (Bit 32) 16)) mem)
               (FMap.M.empty _).

  Definition SCMemHiding m : Prop :=
    forall mem labels newRegs,
      ForwardMultistep m (SCMemRegs mem) newRegs labels ->
      forall wrs,
        extractWrValSeq labels = wrs ->
        forall mem' wrs',
          length wrs = length wrs' ->
          exists labels' newRegs',
            ForwardMultistep m (SCMemRegs mem') newRegs' labels' /\
            censorLabelSeq censorSCMemDefs labels = censorLabelSeq censorSCMemDefs labels' /\
            extractWrValSeq labels' = wrs'.

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

  Lemma MemInstHiding : SCMemHiding rv32iMemInstSingle.
  Proof.
    unfold SCMemHiding.
    induction 1; intros.
    - exists nil.
      eexists.
      intuition idtac.
      + constructor; reflexivity.
      + simpl in *.
        subst.
        simpl in *.
        apply eq_sym.
        rewrite <- length_zero_iff_nil.
        congruence.
    - match goal with
      | [ H : Step _ _ _ _ |- _ ] => inversion H
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
        try tauto.
      + match goal with
        | [ H : length _ = length _ |- _ ] =>
          specialize (IHForwardMultistep _ eq_refl mem' wrs' H)
        end.
        shatter.
        exists ({| annot := Some None; defs := FMap.M.empty _; calls := FMap.M.empty _ |} :: x), x0.
        intuition idtac.
        * econstructor; eauto.
          -- match goal with
             | [ |- Step _ _ _ ?l ] => replace l with (hide (foldSSLabel [{| upd := FMap.M.empty _; unitAnnot := Rle None; cms := FMap.M.empty _; substep := EmptyRule rv32iMemInstSingle (SCMemRegs mem') |}])) by reflexivity
             end.
             constructor; eauto.
             constructor; try solve [ constructor ].
             intros.
             match goal with
             | [ H : In _ nil |- _ ] => inversion H
             end.
          -- eauto.
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
        match goal with
        | [ H : length _ = length _ |- _ ] => simpl in H
        end.
        * destruct wrs'; try discriminate.
          match goal with
          | [ H : S (length _) = length _ |- _ ] => simpl in H; inversion H
          end.
          match goal with
          | [ H : length _ = length _ |- _ ] =>
          specialize (IHForwardMultistep _ eq_refl
                                         (fun a => if weq a adr then w else mem' a)
                                         _ H)
          end.
          shatter.
          match goal with
          | [ H : extractWrValSeq ?ls = wrs', Hfm : ForwardMultistep _ _ ?r ?ls |- _ ] =>
            exists ({| annot := Some None;
                  defs := FMap.M.add "exec"
                                     (existT SignT {| arg := Struct STRUCT {"addr" :: Bit 16; "op" :: Bool; "data" :: Bit 32}; ret := Struct STRUCT {"data" :: Bit 32} |}
                                             (evalExpr (STRUCT { "addr" ::= Var _ (SyntaxKind (Bit 16)) adr;
                                                                 "op" ::= $$(true);
                                                                 "data" ::= Var _ (SyntaxKind (Bit 32)) w})%kami_expr,
                                              evalExpr (STRUCT { "data" ::= $0 })%kami_expr)) (FMap.M.empty _); calls := FMap.M.empty _|} :: ls), r
          end.
          intuition idtac.
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
                  unfold wellHidden, rv32iMemInstSingle, getCalls, getDefs, FMap.M.KeysDisj;
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
          -- subst.
             simpl.
             f_equal; try assumption.
             f_equal.
             FMap.M.ext k.
             do 2 rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
             FMap.mred.
          -- simpl.
             congruence.
        * match goal with
          | [ H : length _ = length _ |- _ ] =>
            specialize (IHForwardMultistep _ eq_refl mem' _ H)
          end.
          shatter.
          match goal with
          | [ H : extractWrValSeq ?ls = wrs', Hfm : ForwardMultistep _ _ ?r ?ls |- _ ] =>
            exists ({| annot := Some None;
                  defs := FMap.M.add "exec"
                                     (existT SignT {| arg := Struct STRUCT {"addr" :: Bit 16; "op" :: Bool; "data" :: Bit 32}; ret := Struct STRUCT {"data" :: Bit 32} |}
                                             (evalExpr (STRUCT { "addr" ::= Var _ (SyntaxKind (Bit 16)) adr;
                                                                 "op" ::= $$(false);
                                                                 "data" ::= $0 })%kami_expr,
                                              evalExpr (STRUCT { "data" ::= Var _ (SyntaxKind (Bit 32)) (mem' adr) })%kami_expr)) (FMap.M.empty _); calls := FMap.M.empty _|} :: ls), r
          end.
          intuition idtac.
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
                  unfold wellHidden, rv32iMemInstSingle, getCalls, getDefs, FMap.M.KeysDisj;
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
          -- subst.
             simpl.
             f_equal; try assumption.
             f_equal.
             FMap.M.ext k.
             do 2 rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
             FMap.mred.
  Qed.

  Lemma SCHiding : forall p m regs mem,
      SCProcHiding p regs mem ->
      SCMemHiding m ->
      kamiHiding (p ++ m)%kami (FMap.M.union (SCMemRegs mem) regs).
  Proof.
    unfold kamiHiding.
    intros.
    match goal with
    | [ H : ForwardMultistep (p ++ m)%kami _ _ _ |- _ ] =>
      apply FMulti_Multi in H
    end.
    apply multistep_split in H1.
  Admitted.

End SCTiming.

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
