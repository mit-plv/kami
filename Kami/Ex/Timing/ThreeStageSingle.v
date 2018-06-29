Require Import List.
Require Import Notations.
Require Import Coq.Numbers.BinNums.
Require Import Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.SymEvalTac Kami.ModuleBoundEx Kami.Tactics Kami.ModularFacts Kami.SemFacts.
Require Import Ex.SC Ex.IsaRv32 Ex.ProcThreeStage Ex.OneEltFifo.
Require Import Ex.Timing.Specification Ex.Timing.ThreeStageInterface.
Require Import Lib.CommonTactics.
Require Import Compile.Rtl Compile.CompileToRtlTryOpt.
Require Import Logic.FunctionalExtensionality.
Require Import Renaming.

Open Scope string_scope.

Ltac shatter := repeat match goal with
                       | [ H : exists _, _ |- _ ] => destruct H
                       | [ H : _ /\ _ |- _ ] => destruct H
                       end.

Parameter predictNextPc : forall ty : Kind -> Type, fullType ty (SyntaxKind (Bit rv32iAddrSize)) -> (Bit rv32iAddrSize) @ (ty).
Parameter d2eElt : Kind.
Parameter d2ePack : (forall ty : Kind -> Type,
                         (Bit optypeBits) @ (ty) ->
                         (Bit rv32iRfIdx) @ (ty) ->
                         (Bit rv32iAddrSize) @ (ty) ->
                         (MemTypes.Data rv32iDataBytes) @ (ty) ->
                         (MemTypes.Data rv32iDataBytes) @ (ty) ->
                         (MemTypes.Data rv32iDataBytes) @ (ty) -> (Bit rv32iAddrSize) @ (ty) -> (Bit rv32iAddrSize) @ (ty) -> (Bool) @ (ty) -> (d2eElt) @ (ty)).

Parameters
    (d2eOpType : (forall ty : Kind -> Type, fullType ty (SyntaxKind d2eElt) -> (Bit optypeBits) @ (ty)))
    (d2eDst : (forall ty : Kind -> Type, fullType ty (SyntaxKind d2eElt) -> (Bit rv32iRfIdx) @ (ty)))
    (d2eAddr :  (forall ty : Kind -> Type, fullType ty (SyntaxKind d2eElt) -> (Bit rv32iAddrSize) @ (ty)) )
    (d2eVal1 d2eVal2 : (forall ty : Kind -> Type, fullType ty (SyntaxKind d2eElt) -> (MemTypes.Data rv32iDataBytes) @ (ty)))
    (d2eRawInst : (forall ty : Kind -> Type, fullType ty (SyntaxKind d2eElt) -> (MemTypes.Data rv32iDataBytes) @ (ty)))
    (d2eCurPc : (forall ty : Kind -> Type, fullType ty (SyntaxKind d2eElt) -> (Bit rv32iAddrSize) @ (ty)))
    (d2eNextPc : (forall ty : Kind -> Type, fullType ty (SyntaxKind d2eElt) -> (Bit rv32iAddrSize) @ (ty)))
    (d2eEpoch : (forall ty : Kind -> Type, fullType ty (SyntaxKind d2eElt) -> (Bool) @ (ty))).

Parameter e2wElt : Kind.

Parameter e2wPack : (forall ty : Kind -> Type, (d2eElt) @ (ty) -> (MemTypes.Data rv32iDataBytes) @ (ty) -> (e2wElt) @ (ty)).

Parameters 
  (e2wDecInst : (forall ty : Kind -> Type, fullType ty (SyntaxKind e2wElt) -> (d2eElt) @ (ty)))
  (e2wVal : forall ty : Kind -> Type, fullType ty (SyntaxKind e2wElt) -> (MemTypes.Data rv32iDataBytes) @ (ty)).

Module ThreeStageSingle <: ThreeStageInterface.

  Definition p :=
    p3st rv32iGetOptype
             rv32iGetLdDst rv32iGetLdAddr rv32iGetLdSrc rv32iCalcLdAddr
             rv32iGetStAddr rv32iGetStSrc rv32iCalcStAddr rv32iGetStVSrc
             rv32iGetSrc1 rv32iGetSrc2 rv32iGetDst
             rv32iExec rv32iNextPc rv32iAlignPc rv32iAlignAddr
             predictNextPc d2ePack d2eOpType d2eDst d2eAddr d2eVal1 d2eVal2 d2eRawInst d2eCurPc d2eNextPc d2eEpoch
             e2wPack e2wDecInst e2wVal (procInitDefault _ _ _ _).

  (* Eval compute in (getCalls p). (* demonstrates that some methods occur twice *) *)
 
  Definition rv32iMemInstRs {ty} : ty (Bit 0) -> ActionT ty (Struct rv32iRs) :=
    fun a =>
      (Read response : MemTypes.Data rv32iDataBytes <- "nextRs";
         Write "nextRs" <- $$Default :: MemTypes.Data rv32iDataBytes;
            (Ret (STRUCT { "data" ::= #response } : Expr ty (SyntaxKind (Struct rv32iRs)))))%kami_action.
  
  Definition rv32iMemInstRq {ty} : ty (Struct rv32iRq) -> ActionT ty (Bit 0) :=
    fun (a: ty (Struct rv32iRq)) =>
      (If !#a!rv32iRq@."op" then (* load, because op is negated *)
         Read memv <- "mem";
           LET ldval <- #memv@[#a!rv32iRq@."addr"];
           Ret (#ldval :: MemTypes.Data rv32iDataBytes)
       else (* store *)
         Read memv <- "mem";
         Write "mem" <- #memv@[ #a!rv32iRq@."addr" <- #a!rv32iRq@."data" ];
         Ret ($$Default :: MemTypes.Data rv32iDataBytes)
       as na;
         Write "nextRs" <- #na;
         Ret $0)%kami_action.

    Definition m :=
      MODULE {
          Register "mem" : Vector (MemTypes.Data rv32iDataBytes) rv32iAddrSize <- Default
            with Register "nextRs" : MemTypes.Data rv32iDataBytes <- Default                                            
            with Method "rqFromProc" -- "enq" (a : Struct rv32iRq) : Bit 0 := (rv32iMemInstRq a)
            with Method "rsToProc" -- "deq" (a : Bit 0) : Struct rv32iRs := (rv32iMemInstRs a)
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
    kdisj_regs_ex 0.
  Qed.

  Theorem validRegs : Wf.ValidRegsModules type (p ++ m)%kami.
  Proof.
    kvr.
  Qed.

  Theorem defsDisj : FMap.DisjList (getDefs p) (getDefs m).
  Proof.
    kdisj_dms_ex 0.
  Qed.
  
  Theorem callsDisj : FMap.DisjList (getCalls p) (getCalls m).
  Proof.
    kdisj_cms_ex 0.
  Qed.
  
  Definition ThreeStageProcRegs rf pm pc : RegsT :=
    FMap.M.add "rf" (existT _ (SyntaxKind (Vector (Bit 32) 5)) rf)
               (FMap.M.add "pgm" (existT _ (SyntaxKind (Vector (Bit 32) 8)) pm)
                           (FMap.M.add "pc" (existT _ (SyntaxKind (Bit 16)) pc)
                                                   (FMap.M.empty _))).
  
  Definition ThreeStageMemRegs mem nextRs : RegsT :=
    FMap.M.add "mem" (existT _ (SyntaxKind (Vector (Bit 32) 16)) mem)
               (FMap.M.add "nextRs" (existT _ (SyntaxKind (Bit 32)) nextRs)
                           (FMap.M.empty _)).

  Definition fhMeth := "fromHost".
  Definition thMeth := "toHost".
  Definition rqMeth := "rqFromProc" -- "enq".
  Definition rsMeth := "rsToProc" -- "deq".

  Theorem methsDistinct : fhMeth <> thMeth /\ thMeth <> rqMeth /\ rqMeth <> fhMeth /\ rqMeth <> rsMeth /\ thMeth <> rsMeth /\ rsMeth <> fhMeth.
  Proof.
    intuition idtac; discriminate.
  Qed.
  
  Theorem mdrq : In rqMeth (getDefs m).
  Proof.
    simpl; auto.
  Qed.

  Theorem pcrq : In rqMeth (getCalls p).
  Proof.
    simpl; auto.
    repeat (try (left; reflexivity); right).
  Qed.

  Theorem pcfh : In fhMeth (getCalls p).
  Proof.
    simpl; repeat (try (left; reflexivity); right).
  Qed.

  Theorem pcth : In thMeth (getCalls p).
  Proof.
    simpl; repeat (try (left; reflexivity); right).
  Qed.

  Theorem pcrs : In rsMeth (getCalls p).
  Proof.
    simpl; repeat (try (left; reflexivity); right).
  Qed.

  Theorem pndfh : ~ In fhMeth (getDefs p).
  Proof.
    intuition. unfold p, getDefs in H; simpl in H.
    intuition discriminate.
  Qed.

  Theorem mndfh : ~ In fhMeth (getDefs m).
  Proof.
    simpl.
    intuition idtac;
    discriminate.
  Qed.

  Theorem pndth : ~ In thMeth (getDefs p).
  Proof.
    intuition simpl. unfold p, getDefs in H; simpl in H; intuition discriminate.
  Qed.

  Theorem mndth : ~ In thMeth (getDefs m).
  Proof.
    simpl.
    intuition idtac;
    discriminate.
  Qed.

  Theorem mdrs : In rsMeth (getDefs m).
  Proof.
    simpl. intuition reflexivity.
  Qed.

  Theorem pRegs : forall rf pm pc, FMap.M.KeysSubset (ThreeStageProcRegs rf pm pc) (Struct.namesOf (getRegInits p)).
  Proof.
    intros; simpl.
    unfold ThreeStageProcRegs, FMap.M.KeysSubset.
    intro.
    repeat rewrite FMap.M.F.P.F.add_in_iff.
    rewrite FMap.M.F.P.F.empty_in_iff.
    intuition idtac; subst; simpl; tauto.
  Qed.
    
  Theorem mRegs : forall mem nextRs, FMap.M.KeysSubset (ThreeStageMemRegs mem nextRs) (Struct.namesOf (getRegInits m)).
  Proof.
    intros; simpl.
    unfold ThreeStageMemRegs, FMap.M.KeysSubset.
    intro.
    repeat rewrite FMap.M.F.P.F.add_in_iff.
    rewrite FMap.M.F.P.F.empty_in_iff.
    intuition idtac; subst; simpl; tauto.
  Qed.

  Theorem pRqRs : forall rf u l,
      Step p rf u l ->
      (FMap.M.find rqMeth (calls l) = None \/
       FMap.M.find rsMeth (calls l) = None).
  Proof.
    intros. (* rule exec = Prule; method exec = Pmethod; combining two w/Prule, Pmethod => PRule |- any exec, Prule *)
    inv H. induction HSubsteps. tauto.
    (* substepsInd_rule_split? *)
  Admitted.
  
  Theorem mRqRs : forall rp rm up um lp lm,
      Step p rp up lp ->
      Step m rm um lm ->
      WellHiddenConcat p m lp lm -> 
      (FMap.M.find rqMeth (defs lm) = None \/
       FMap.M.find rsMeth (defs lm) = None).
  Proof.
    
  Admitted.
   
  End ThreeStageSingle.

Module ThreeStageSingleModularHiding <: (ThreeStageModularHiding ThreeStageSingle).
  Module Defs := ThreeStageDefs ThreeStageSingle.
  Import ThreeStageSingle Defs.

  Lemma ThreeStageProcRegs_find_rf : forall rf pm pc rf',
      FMap.M.find (elt:={x : FullKind & fullType type x}) "rf"
                  (ThreeStageProcRegs rf pm pc) =
      Some
        (existT (fullType type) (SyntaxKind (Vector (Bit 32) 5)) rf') -> rf = rf'.
  Proof.
    intros.
    unfold ThreeStageProcRegs in *.
    FMap.findeq.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1).
  Qed.

  Lemma ThreeStageProcRegs_find_pm : forall rf pm pc pm',
      FMap.M.find (elt:={x : FullKind & fullType type x}) "pgm"
                  (ThreeStageProcRegs rf pm pc) =
      Some
        (existT (fullType type) (SyntaxKind (Vector (Bit 32) 8)) pm') -> pm = pm'.
  Proof.
    intros.
    unfold ThreeStageProcRegs in *.
    FMap.findeq.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1).
  Qed.

  Lemma ThreeStageProcRegs_find_pc : forall rf pm pc pc',
      FMap.M.find (elt:={x : FullKind & fullType type x}) "pc"
                  (ThreeStageProcRegs rf pm pc) =
      Some
        (existT (fullType type) (SyntaxKind (Bit 16)) pc') -> pc = pc'.
  Proof.
    intros.
    unfold ThreeStageProcRegs in *.
    FMap.findeq.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1).
  Qed.

  Ltac ThreeStageProcRegs_find :=
    repeat match goal with
           | [ H : FMap.M.find "rf" (ThreeStageProcRegs ?rf _ _) = Some (existT _ _ ?rf') |- _ ] => assert (rf = rf') by (eapply ThreeStageProcRegs_find_rf; eassumption); subst; clear H
           | [ H : FMap.M.find "pgm" (ThreeStageProcRegs _ ?pm _) = Some (existT _ _ ?pm') |- _ ] => assert (pm = pm') by (eapply ThreeStageProcRegs_find_pm; eassumption); subst; clear H
           | [ H : FMap.M.find "pc" (ThreeStageProcRegs _ _ ?pc) = Some (existT _ _ ?pc') |- _ ] => assert (pc = pc') by (eapply ThreeStageProcRegs_find_pc; eassumption); subst; clear H
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

  Definition zeroRet (n : String.string) (t : {x : SignatureT & SignT x}) : {x : SignatureT & SignT x} :=
    if String.string_dec n execMeth
    then match t with
         | existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (argV, retV) =>
           if evalExpr (#argV!rv32iRq@."op")%kami_expr
           then existT _
                       {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                                 "op" :: Bool;
                                                 "data" :: Bit 32});
                          ret := Struct (STRUCT {"data" :: Bit 32}) |}
                       (argV,
                        evalExpr (STRUCT { "data" ::= $0 })%kami_expr)
           else t
         | _ => t
         end
    else t.

  Definition canonicalizeLabel (l : LabelT) : LabelT :=
    match l with
    | {| annot := None;
        defs := d;
        calls := c |} => {| annot := Some None; defs := d; calls := FMap.M.mapi zeroRet c |}
    | {| annot := Some a;
        defs := d;
        calls := c |} => {| annot := Some a; defs := d; calls := FMap.M.mapi zeroRet c |}
    end.

  Definition canonicalize := map canonicalizeLabel.

  Lemma inv_label : forall a a' c c' d d',
      {| annot := a; calls := c; defs := d |} = {| annot := a'; calls := c'; defs := d' |} -> a = a' /\ c = c' /\ d = d'.
  Proof.
    intros.
    match goal with
    | [ H : _ = _ |- _ ] => inv H
    end.
    tauto.
  Qed.

  Ltac zr_noop := 
    repeat match goal with
           | [ |- context[FMap.M.mapi zeroRet ?mp] ] =>
             let Heq := fresh in
             let k := fresh in
             assert (FMap.M.mapi zeroRet mp = mp) as Heq
                 by (clear;
                     FMap.M.ext k;
                     rewrite FMap.M.F.P.F.mapi_o
                       by (intros; subst; reflexivity);
                     FMap.mred);
             repeat rewrite Heq;
             repeat rewrite Heq in *;
             clear Heq
           | [ H : context[FMap.M.mapi zeroRet ?mp] |- _ ] =>
             let Heq := fresh in
             let k := fresh in
             assert (FMap.M.mapi zeroRet mp = mp) as Heq
                 by (clear;
                     FMap.M.ext k;
                     rewrite FMap.M.F.P.F.mapi_o
                       by (intros; subst; reflexivity);
                     FMap.mred);
             repeat rewrite Heq;
             repeat rewrite Heq in *;
             clear Heq
           end.

  Lemma decanon : forall o o' n n' mem f l0 l1,
      ForwardMultistep p o n l1 ->
      SCProcMemConsistent l1 mem ->
      ForwardMultistep p o' n' l0 ->
      censorLabelSeq censorSCMeth (canonicalize l0) = censorLabelSeq censorSCMeth (canonicalize l1) ->
      extractFhLabelSeq fhMeth l1 = f ->
      exists l1',
        ForwardMultistep p o n l1' /\
        SCProcMemConsistent l1' mem /\
        censorLabelSeq censorSCMeth l0 = censorLabelSeq censorSCMeth l1' /\
        extractFhLabelSeq fhMeth l1' = f.
  Proof.
    intros o o' n n' mem f l0 l1 Hfm.
    move Hfm at top.
    generalize mem, f, l0, o', n'.
    clear mem f l0 o' n'.
    induction Hfm; intros; simpl in *; subst.
    - exists nil; intuition idtac.
      + constructor; congruence.
      + destruct l0; simpl in *; try congruence.
    - destruct l0; simpl in *; try congruence.
      match goal with
      | [ H : _ :: _ = _ :: _ |- _ ] => inv H
      end.
      match goal with
      | [ H : ForwardMultistep _ _ _ (_ :: _) |- _ ] => inv H
      end.
      match goal with
      | [ H : SCProcMemConsistent _ _ |- _ ] => inv H
      end.
      match goal with
      | [ Hc : censorLabelSeq censorSCMeth _ = censorLabelSeq censorSCMeth _,
               Hm : SCProcMemConsistent _ _,
                    Hfm : ForwardMultistep _ _ _ _,
                          IHHfm : forall _ _ _ _ _, SCProcMemConsistent _ _ -> ForwardMultistep _ _ _ _ -> _ = _ -> _ |- _ ] =>
        specialize (IHHfm _ _ _ _ _ Hm Hfm Hc eq_refl)
      end.
      shatter.
      match goal with
      | [ H : Step _ _ _ _, H' : Step _ _ _ _ |- _ ] => inversion H; inversion H'
      end.
      apply substepsComb_substepsInd in HSubsteps.
      apply SCProcSubsteps in HSubsteps.
      apply substepsComb_substepsInd in HSubsteps0.
      apply SCProcSubsteps in HSubsteps0.
      intuition idtac;
        shatter;
        match goal with
        | [ H : foldSSLabel ss = _ |- _ ] => rewrite H in *
        end;
        match goal with
        | [ H : foldSSLabel ss0 = _ |- _ ] => rewrite H in *
        end;
        subst;
        match goal with
        | [ H : censorLabel _ _ = censorLabel _ _ |- _ ] => simpl in H
        end;
        try discriminate;
        try match goal with
            | [ |- context[censorLabel censorSCMeth (hide {| annot := ?ant; defs := FMap.M.empty _; calls := FMap.M.empty _ |})] ] =>
              exists ({| annot := ant; defs := FMap.M.empty _; calls := FMap.M.empty _ |} :: x);
                intuition idtac; eauto;
                  match goal with
                  | [ |- ForwardMultistep _ _ _ _ ] =>
                    econstructor; eauto; 
                      (apply step_rule_annot_1 || apply step_rule_annot_2);
                      assumption
                  | [ |- SCProcMemConsistent _ _ ] => econstructor; eauto
                  | [ |- _ = _ ] => simpl; f_equal; eauto
                  end
            end.
      repeat rewrite FMap.M.subtractKV_empty_1 in H4.
      repeat rewrite FMap.M.subtractKV_empty_2 in H4.
      assert (x4 = x0) by (inversion H4; reflexivity); subst.
      repeat match goal with
             | [ H : In _ (getRules p) |- _ ] => simpl in H
             end.
      Opaque evalExpr.
      intuition idtac;
        repeat match goal with
        | [ H : _ = (_ :: _)%struct |- _ ] => inv H
        end;
        match goal with
        | [ |- context["execSt"] ] => idtac
        | [ H : _ = {| annot := Some (Some ?mn); defs := _; calls := FMap.M.mapi _ ?mths |} |- _ ] =>
          exists ({| annot := Some (Some mn); defs := FMap.M.empty _; calls := mths |} :: x)
        end;
        kinv_action_dest.
      + Transparent evalExpr.
        zr_noop.
        Opaque evalExpr.
        intuition idtac; try solve [ econstructor; eauto | simpl; f_equal; eauto ].
      + Transparent evalExpr.
        zr_noop.
        Opaque evalExpr.
        intuition idtac; try solve [ econstructor; eauto | simpl; f_equal; eauto ].
      + match goal with
        | [ H : Step p o _ (hide {| annot := _; defs := _; calls := FMap.M.add _ (existT _ ?typ (?argV, _)) _ |})
          |- context[censorLabel censorSCMeth (hide {| annot := _; defs := _; calls := FMap.M.add _ (existT _ _ (_, ?retV)) _ |})] ] =>
          exists ({| annot := Some (Some "execSt"); defs := FMap.M.empty _; calls := FMap.M.add "exec" (existT _ typ (argV, retV)) (FMap.M.empty _) |} :: x)
        end.
        intuition idtac.
        * econstructor; eauto.
          match goal with
          | [ |- Step ?m ?o _ {| annot := _; defs := _; calls := ?cs (*FMap.M.add _ (existT _ _ (?av, ?rv)) _*) |} ] =>
            let ss := fresh in
            simple refine (let ss := (_ : Substeps m o) in _);
              [ apply cons; [ idtac | apply nil ];
                eapply Build_SubstepRec;
                eapply (SingleRule p "execSt");
                try (simpl; tauto);
                instantiate (1 := cs);
                try match goal with
                    | [ |- SemAction _ _ _ _ _ ] => repeat econstructor
                    end;
                eauto
              | match goal with
                | [ |- Step ?m ?o ?u ?l ] => replace l with (hide (foldSSLabel ss)) by reflexivity; replace u with (foldSSUpds ss) by reflexivity
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
        * match goal with
          | [ |- context[evalExpr STRUCT {"addr" ::= ?adr; "op" ::= _; "data" ::= ?dat}%kami_expr] ] =>
            let adr' := fresh in
            let dat' := fresh in
            let Hdiscard := fresh in
            remember adr as adr' eqn:Hdiscard;
              clear Hdiscard;
              remember dat as dat' eqn:Hdiscard;
              clear Hdiscard
          end.
          Transparent evalExpr.
          econstructor; eauto.
          simpl.
          simpl in H3.
          assumption.
        * repeat match goal with
                 | [ |- context[evalExpr STRUCT {"addr" ::= @rv32iAlignAddr ?ty ?adr; "op" ::= _; "data" ::= ?dat}%kami_expr] ] =>
                   let adr' := fresh in
                   let dat' := fresh in
                   let Hdiscard := fresh in
                   remember (@rv32iAlignAddr ty adr) as adr' eqn:Hdiscard;
                     clear Hdiscard;
                     remember dat as dat' eqn:Hdiscard;
                     clear Hdiscard
                 end.
          match goal with
          | [ |- context[censorLabelSeq censorSCMeth (?hd :: ?tl)] ] =>
            replace (censorLabelSeq censorSCMeth (hd :: tl)) with (censorLabel censorSCMeth hd :: censorLabelSeq censorSCMeth tl) by reflexivity
          end.
          f_equal; auto.
          destruct (inv_rs x4).
          destruct (inv_rs x8).
          subst.
          unfold hide, calls, defs, annot in *.
          repeat rewrite FMap.M.subtractKV_empty_1.
          repeat rewrite FMap.M.subtractKV_empty_2.
          unfold censorLabel.
          f_equal.
          match goal with
          | [ |- FMap.M.mapi _ (FMap.M.add _ (existT _ _ (?argV, _)) _) = FMap.M.mapi _ (FMap.M.add _ (existT _ _ (?argV', _)) _) ] =>
            replace argV with (evalExpr STRUCT {"addr" ::= #(evalExpr H28); "op" ::= $$(true); "data" ::= H29}%kami_expr) by eauto;
              replace argV' with (evalExpr STRUCT {"addr" ::= #(evalExpr H30); "op" ::= $$(true); "data" ::= H31}%kami_expr) by eauto
          end.
          replace (evalExpr H28) with (evalExpr H30).
          -- FMap.M.ext k.
             repeat rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
             FMap.mred.
          -- clear - H4.
             apply inv_label in H4.
             shatter.
             repeat match goal with
                    | [ H : ?x = ?x |- _ ] => clear H
                    end.
             match goal with
             | [ H : ?x = ?y |- _ ] =>
               let H' := fresh in
               assert (FMap.M.find "exec" x = FMap.M.find "exec" y) as H' by (rewrite H; reflexivity);
                 clear H;
                 repeat rewrite FMap.M.F.P.F.mapi_o in H' by (intros; subst; reflexivity)
             end.
             FMap.mred.
             unfold option_map in *.
             match goal with
             | [ H : Some ?x = Some ?y |- _ ] => assert (x = y) by congruence; clear H
             end.
             match goal with
             | [ H : ?x = ?y |- _ ] =>
               replace x with
                   (existT SignT
                           {|
                             arg := Struct (SC.RqFromProc rv32iAddrSize rv32iDataBytes);
                             ret := Struct (SC.RsToProc rv32iDataBytes) |}
                           (evalExpr
                              STRUCT {"addr" ::= H28; "op" ::= $$ (true);
                                      "data" ::= $0}%kami_expr,
                            evalExpr STRUCT {"data" ::= $0}%kami_expr)) in H by eauto;
                 replace y with
                     (existT SignT
                             {|
                               arg := Struct (SC.RqFromProc rv32iAddrSize rv32iDataBytes);
                               ret := Struct (SC.RsToProc rv32iDataBytes) |}
                             (evalExpr
                                STRUCT {"addr" ::= H30; "op" ::= $$ (true);
                                        "data" ::= $0}%kami_expr,
                              evalExpr STRUCT {"data" ::= $0}%kami_expr)) in H by eauto
             end.
             apply Semantics.sigT_eq in H0.
             match goal with
             | [ H : (?x, _) = (?y, _) |- _ ] => assert (x = y) by congruence; clear H
             end.
             match goal with
             | [ H : ?x = ?y |- _ ] => assert (x Fin.F1 = y Fin.F1) by congruence; clear H
             end.
             simpl in H0.
             congruence.
      + Transparent evalExpr.
        zr_noop.
        Opaque evalExpr.
        intuition idtac; try solve [ econstructor; eauto | simpl; f_equal; eauto ].
      + Transparent evalExpr.
        zr_noop.
        Opaque evalExpr.
        intuition idtac; try solve [ econstructor; eauto | simpl; f_equal; eauto ].
      + Transparent evalExpr.
        zr_noop.
        Opaque evalExpr.
        intuition idtac; try solve [ econstructor; eauto | simpl; f_equal; eauto ].
      + Transparent evalExpr.
        zr_noop.
        Opaque evalExpr.
        intuition idtac; try solve [ econstructor; eauto | simpl; f_equal; eauto ].
      + Transparent evalExpr.
        zr_noop.
        Opaque evalExpr.
        intuition idtac; try solve [ econstructor; eauto | simpl; f_equal; eauto ].
  Qed. Transparent evalExpr.

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

  Opaque rv32iAlignAddr.
  Opaque evalUniBit.
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
        try (f_equal;
             repeat rewrite FMap.M.subtractKV_empty_1;
             FMap.M.ext k;
             FMap.findeq);
        try (eapply IHHht1;
             try eassumption;
             match goal with
             | [ H : SCProcMemConsistent _ ?m |- SCProcMemConsistent _ ?m ] => inversion H; simpl in *; subst; assumption
             end).
    - match goal with
      | [ Hct : censorTrace (Rd _ _ _ :: _) = censorTrace ?tr |- _ ] =>
        let t := fresh in
        destruct tr as [|t tr];
          simpl in Hct;
          try destruct t;
          try congruence
      end.
      match goal with
      | [ H : Rd ?p ?a _ :: ?ct = Rd ?p' ?a' _ :: ?ct' |- _ ] =>
        assert (p = p') by congruence;
          assert (a = a') by congruence;
          assert (ct = ct') by congruence;
          clear H
      end.
      opaque_subst.
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
          match goal with
          | [ H : Some (Rd _ ?x _) = Some (Rd _ ?y _) |- _ ] => assert (x = y) by congruence; clear H
          end.
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
        * rewrite H.
          repeat match goal with
                 | [ H : hasTrace _ _ _ _ (_ :: _), H' : _ |- _ ] => clear H'
                 end.
          remember (Rd x2 laddr_aligned val0) as rd.
          match goal with
          | [ Hht : hasTrace _ _ _ _ (_ :: ?t) |- hasTrace _ _ _ _ ?t ] => inversion Hht
          end; subst; try discriminate; eassumption.
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
                 replace (labelToTraceEvent l) with (Some (Rd $ (0) (evalExpr adr) (evalExpr (#x!rv32iRs@."data")%kami_expr))) in H by eauto
               end
             end.
             match goal with
             | [ H : Some (Rd _ _ ?x) = Some (Rd _ _ ?y) |- _ ] => assert (x = y) by congruence
             end.
             rewrite <- H2.
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
                | [ H : Some (Rd _ _ ?x) = Some (Rd _ _ ?y) |- _ ] => assert (x = y) by congruence
                end.
                replace (evalExpr (#x3)!rv32iRs@.("data"))%kami_expr with (x3 Fin.F1) in H2 by reflexivity.
                rewrite H2.
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
                | [ H : ?m ?a = ?v |- ?x = ?m ?y ] => replace (m a) with (m y) in H; [replace v with x in H|]
                end.
                ** congruence.
                ** reflexivity.
                ** match goal with
                   | [ |- context[(evalExpr STRUCT {"addr" ::= ?a; "op" ::= _; "data" ::= _ })%kami_expr] ] => replace laddr_aligned with (evalExpr a) by congruence
                   end.
                   Transparent rv32iAlignAddr.
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
          try congruence
      end.
      match goal with
      | [ H : RdZ ?p ?a :: ?ct = RdZ ?p' ?a' :: ?ct' |- _ ] =>
        assert (p = p') by congruence;
          assert (a = a') by congruence;
          assert (ct = ct') by congruence;
          clear H;
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
             | [ Hht : hasTrace _ _ _ _ (?e :: ?t) |- hasTrace _ _ _ _ ?t ] => remember e as e'; inversion Hht; subst; try discriminate
             end.
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
          try congruence
      end.
      match goal with
      | [ H : Wr ?p ?a _ :: ?ct = Wr ?p' ?a' _ :: ?ct' |- _ ] =>
        assert (p = p') by congruence;
          assert (a = a') by congruence;
          assert (ct = ct') by congruence;
          clear H;
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
        unfold canonicalizeLabel, hide, annot, calls, defs.
        unfold censorLabel, censorSCMeth, canonicalizeLabel, hide, annot, calls, defs.
        f_equal.
        match goal with
        | [ H1 : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add "exec" (existT _ _ (evalExpr STRUCT {"addr" ::= ?addr1; "op" ::= _; "data" ::= _}%kami_expr, _)) _ |}) = _,
                 H2 : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add "exec" (existT _ _ (evalExpr STRUCT {"addr" ::= ?addr2; "op" ::= _; "data" ::= _}%kami_expr, _)) _ |}) = _
            |- _ ] => replace (evalExpr addr1) with (evalExpr addr2)
        end.
        * repeat rewrite FMap.M.subtractKV_empty_2.
          FMap.M.ext k.
          repeat rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
          Opaque evalExpr.
          unfold execMeth.
          destruct (String.string_dec k "exec").
          -- subst.
             repeat rewrite FMap.M.F.P.F.add_eq_o by reflexivity.
             unfold option_map.
             f_equal.
          -- repeat rewrite FMap.M.F.P.F.add_neq_o by congruence.
             repeat rewrite FMap.M.find_empty.
             unfold option_map.
             reflexivity.
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
          match goal with
          | [ H : Some (Wr _ ?x _) = Some (Wr _ ?y _) |- _ ] => assert (x = y) by congruence; clear H
          end.
          match goal with
          | [ H : ?x = _ |- _ = ?x ] => rewrite H
          end.
          unfold saddr_aligned, saddr, addr, srcVal, srcIdx.
          reflexivity.
      + Transparent evalExpr.
        match goal with
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
        * rewrite H.
          Opaque evalExpr.
          match goal with
          | [ Hht : hasTrace _ _ _ _ (?e :: ?t) |- hasTrace _ _ _ _ ?t ] => remember e as e'; inversion Hht; subst e'
          end;
            match goal with
            | [ H : Wr _ _ _ = Wr _ _ _ |- _ ] => idtac
            | _ => discriminate
            end.
          subst.
          match goal with
          | [ Hht : hasTrace _ _ ?pc1 _ ?t |- hasTrace _ _ ?pc2 _ ?t ] => replace pc2 with pc1 by congruence; eassumption
          end.
          Transparent evalExpr.
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
          shatter.
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
          shatter.
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
          match goal with
          | [ H : Some (Wr _ ?x1 ?x2) = Some (Wr _ ?y1 ?y2) |- _ ] =>
            assert (x1 = y1) by congruence;
              assert (x2 = y2) by congruence;
              clear H
          end.
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
        repeat rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
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
          repeat rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
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
          repeat rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
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
        repeat split; try reflexivity.
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
          -- exact (evalExpr STRUCT {"data" ::= $0}%kami_expr).
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
                          Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') ?mem _ |- hasTrace ?x1 ?x2 ?x3 ?x4 _ ] =>
                  replace (getrf o') with x1 in Hht by (rewrite Hfu; unfold getrf; FMap.findeq);
                    replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                    replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq) end.
                eassumption.
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
  Transparent rv32iAlignAddr.

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
        Hmc : SCProcMemConsistent ?ls1 _,
        Hfm0 : ForwardMultistep _ _ _ ?ls0
        |- _ ] =>
      let Hcanon := fresh in
      let Heq := fresh in
      assert (censorLabelSeq censorSCMeth (canonicalize ls0) = censorLabelSeq censorSCMeth (canonicalize ls1)) as Hcanon by (eapply (relatedCensor _ _ _ _ _ _ _ _ _ _ _ _ Hht0 Hht1); eassumption);
        pose (Heq := relatedFhTrace _ _ Hrt1);
        rewrite Heq in Heft;
        pose (decanon _ _ _ _ _ _ _ _ Hfm Hmc Hfm0 Hcanon Heft)
    end.
    shatter.
    eauto.
  Qed.

  Theorem ProcAirtight : forall oldregs newregs labels,
      ForwardMultistep p oldregs newregs labels ->
      SCProcLabelSeqAirtight labels.
  Proof.
    induction 1; constructor; auto.
    match goal with
    | [ H : Step _ _ _ _ |- _ ] => inv H
    end.
    match goal with
    | [ H : substepsComb ss |- _ ] => apply substepsComb_substepsInd in H; apply SCProcSubsteps in H
    end.
    intuition idtac; shatter; subst;
      match goal with
      | [ H : foldSSLabel ss = _ |- _ ] => rewrite H in *
      end;
      unfold hide, annot, calls, defs;
      repeat rewrite FMap.M.subtractKV_empty_1;
      repeat rewrite FMap.M.subtractKV_empty_2;
      try solve [ constructor ].
    Opaque evalExpr.
    match goal with
    | [ H : In _ _ |- _ ] => simpl in H
    end;
      intuition idtac;
      match goal with
      | [ H : (_ :: _)%struct = _ |- _ ] => inv H
      end;
      kinv_action_dest;
      constructor.
    Transparent evalExpr.
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
          match goal with
          | [ H : ?x = ?y |- _ ] =>
            let x' := fresh in
            let y' := fresh in
            remember x as x';
              remember y as y';
              assert (x' Fin.F1 = y' Fin.F1) by (rewrite H; reflexivity);
              subst
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
          | [ H : _ |- _ ] => apply SCMemRegs_find_mem in H; shatter; subst
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
             ++ simpl.
                reflexivity.
             ++ assumption.
          -- subst.
             simpl.
             f_equal; try assumption.
             f_equal.
             FMap.M.ext k.
             repeat rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
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
             ++ simpl.
                reflexivity.
             ++ assumption.
          -- subst.
             simpl.
             f_equal; try assumption.
             f_equal.
             FMap.M.ext k.
             repeat rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
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
                                                                 "data" ::= Var _ (SyntaxKind (Bit 32)) dat })%kami_expr,
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
             repeat rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
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
             repeat rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity).
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
          repeat split;
          try reflexivity;
          try apply IHForwardMultistep;
          eauto.
  Qed.

  Theorem MemAirtight : forall oldregs newregs labels,
      ForwardMultistep m oldregs newregs labels ->
      SCMemLabelSeqAirtight labels.
  Proof.
    induction 1; constructor; auto.
    match goal with
    | [ H : Step _ _ _ _ |- _ ] => inv H
    end.
    match goal with
    | [ H : substepsComb ss |- _ ] => apply substepsComb_substepsInd in H; apply SCMemSubsteps in H
    end.
    intuition idtac; shatter; subst;
      match goal with
      | [ H : foldSSLabel ss = _ |- _ ] => rewrite H in *
      end;
      unfold hide, annot, calls, defs;
      repeat rewrite FMap.M.subtractKV_empty_1;
      repeat rewrite FMap.M.subtractKV_empty_2;
      try solve [ constructor ].
    destruct (inv_rq x0) as [? [op [? ?]]]; destruct (inv_rs x1); subst; destruct op; try solve [ constructor ].
    kinv_action_dest.
    match goal with
    | [ H : ?x = ?y |- _ ] =>
      let x' := fresh in
      let y' := fresh in
      remember x as x';
        remember y as y';
        assert (x' Fin.F1 = y' Fin.F1) by (rewrite H; reflexivity);
        subst
    end.
    subst.
    constructor.
  Qed.

End SCSingleModularHiding.

Module SCSingleHiding := SCHiding SCSingle SCSingleModularHiding.
Check SCSingleHiding.abstractToSCHiding.
