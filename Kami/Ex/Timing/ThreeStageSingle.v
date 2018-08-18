Require Import List.
Require Import Notations.
Require Import Coq.Numbers.BinNums.
Require Import Lib.Word Lib.Indexer Lib.FMap.
Require Import Kami.Syntax Kami.Semantics Kami.SymEvalTac Kami.ModuleBoundEx Kami.Tactics Kami.ModularFacts Kami.SemFacts.
Require Import Ex.SC Ex.IsaRv32 Ex.ProcThreeStage Ex.OneEltFifo.
Require Import Ex.Timing.Specification Ex.Timing.ThreeStageInterface Ex.Timing.LabelDecomposition Ex.Timing.Inversion.
Require Import Lib.CommonTactics Lib.Struct.
Require Import Compile.Rtl Compile.CompileToRtlTryOpt.
Require Import Logic.FunctionalExtensionality.
Require Import Renaming.
Require Import InlineFacts.
Require Import omega.Omega.

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

  Definition rv32iMemInstRs {ty} : ty (Bit 0) -> ActionT ty (Struct rv32iRs) :=
      fun a  =>
        (Read response : MemTypes.Data rv32iDataBytes <- "nextRs";
           Write "nextRs" : MemTypes.Data rv32iDataBytes <- $$Default;
           LET ret : Struct rv32iRs <- STRUCT { "data" ::= #response };
           Ret #ret)%kami_action.
  
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


  (* A snippet to print out what registers p has and their types *)
  (* Eval compute in (map *)
  (*                    (fun z => match z with *)
  (*                           | (name :: more)%struct => *)
  (*                             match more with *)
  (*                             | RegInitCustom (existT _ ty _) => (name, ty) *)
  (*                             | RegInitDefault ty => (name, ty) *)
  (*                             end *)
  (*                           end) *)
  (*                    (getRegInits p)). *)
  
  Definition ThreeStageAllRegs rf pm pc fEpoch sbF d2e_elt d2e_full w2d_elt w2d_full eEpoch e2w_elt e2w_full stall stalled : RegsT :=
    (FMap.M.add "stalled" (existT _ (SyntaxKind d2eElt) stalled)
    (FMap.M.add "stall" (existT _ (SyntaxKind Bool) stall)
    (FMap.M.add "e2w" -- "full" (existT _ (SyntaxKind Bool) e2w_full)
    (FMap.M.add "e2w" -- "elt" (existT _ (SyntaxKind e2wElt) e2w_elt)
    (FMap.M.add "eEpoch" (existT _ (SyntaxKind Bool) eEpoch)
    (FMap.M.add "w2d" -- "full" (existT _ (SyntaxKind Bool) w2d_full)
    (FMap.M.add "w2d" -- "elt" (existT _ (SyntaxKind (Bit 11)) w2d_elt)
    (FMap.M.add "d2e" -- "full" (existT _ (SyntaxKind Bool) d2e_full)
    (FMap.M.add "d2e" -- "elt" (existT _ (SyntaxKind d2eElt) d2e_elt)
    (FMap.M.add "sbFlags" (existT _ (SyntaxKind (Vector Bool 5)) sbF)
    (FMap.M.add "fEpoch" (existT _ (SyntaxKind Bool) fEpoch)
    (FMap.M.add "rf" (existT _ (SyntaxKind (Vector (Bit 32) 5)) rf)
    (FMap.M.add "pgm" (existT _ (SyntaxKind (Vector (Bit 32) 8)) pm)
    (FMap.M.add "pc" (existT _ (SyntaxKind (Bit 11)) pc)
    (FMap.M.empty _))))))))))))))).

  Definition ThreeStageProcRegs rf pm pc : RegsT :=
      (FMap.M.add "rf" (existT _ (SyntaxKind (Vector (Bit 32) 5)) rf)
                  (FMap.M.add "pgm" (existT _ (SyntaxKind (Vector (Bit 32) 8)) pm)
                              (FMap.M.add "pc" (existT _ (SyntaxKind (Bit 11)) pc)
                                          (FMap.M.empty _)))).

  
  Definition ThreeStageMemRegs mem nextRs : RegsT :=
    FMap.M.add "mem" (existT _ (SyntaxKind (Vector (Bit 32) 11)) mem)
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

  Theorem pndrs : ~ In rsMeth (getDefs p).
  Proof.
    intuition simpl. unfold p, getDefs in H; simpl in H; intuition discriminate.
  Qed.

  
  Theorem pndrq : ~ In rqMeth (getDefs p).
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

  Theorem pRegs : forall rf pm pc,
      FMap.M.KeysSubset (ThreeStageProcRegs rf pm pc)
                        (Struct.namesOf (getRegInits p)).
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

  Module LabelMod <: LabelDecomposition.Assumptions.
    Definition m := p.
    (* we'll use the argument-form from LabelDecomposition to prove that this predicate holds of the label generated by any step: *)
    Definition Prule := fun m => (FMap.M.find rqMeth m = None) \/ (FMap.M.find (elt := {x : SignatureT & SignT x}) rsMeth m = None).
    (* This predicate holds if only methods are executed: *)
    Definition Pmeth := fun m => (FMap.M.find rqMeth m = None) /\ (FMap.M.find (elt := {x : SignatureT & SignT x}) rsMeth m = None).

    Lemma Pmeth_empty : (Pmeth (FMap.M.empty _)).
    Proof. unfold Pmeth. rewrite !FMap.M.find_empty; auto. Qed.

    Lemma Prule_empty : (Prule (FMap.M.empty _)).
    Proof. unfold Prule. rewrite !FMap.M.find_empty; auto. Qed.

    Lemma Prules : forall k a, List.In {| attrName := k; attrType := a |} (getRules m) ->
                        forall o u cs retVal, SemAction o (a type) u cs retVal ->
                                       Prule cs.
    Proof.
      intros; unfold Prule.
      rewrite <- !FMap.M.Map.Facts.P.F.not_find_in_iff.
      let H := fresh in
      pose proof pequiv as H;
      unfold Wf.ModEquiv in H;
      destruct H; simpl in H.
      repeat match goal with
             | [ H : Wf.RulesEquiv _ _ _ |- _ ] => inversion H
             end.
      unfold Wf.RuleEquiv in *; simpl in *; subst.
      
      simpl in H;
        repeat match goal with
               | [ H : _ \/ _ |- _ ] => destruct H
               end;
        try match goal with
            | [ H : @eq (Attribute (Action Void)) _ _ |- _ ] => inv H
            end;
        let K1 := fresh in 
        match goal with
        | [ H : SemAction _ ?x _ _ _, H' : Wf.ActionEquiv ?x _ |- _ ] => pose proof (callsA_subset H' H) as K1
        | [ H : SemAction _ _ _ _ _ |- _ ] => auto
        end;
        repeat match goal with
               | [ H : Wf.ActionEquiv _ _ |- _ ] => clear H
               | [ H : Wf.RulesEquiv _ _ _ |- _ ] => clear H
               | [ H : Wf.MethsEquiv _ _ _ |- _ ] => clear H
               end;
        try (left; let K2 := fresh in
                   intro K2; specialize (K1 _ K2);
                   unfold getCallsA in K1; compute in K1; intuition congruence);
        try (right; let K2 := fresh in
                    intro K2; specialize (K1 _ K2);
                    unfold getCallsA in K1; compute in K1; intuition congruence).
    Qed.
    
    Lemma Pmeths : forall f, In f (getDefsBodies m) ->
                       forall o (u : UpdatesT) (cs : MethsT) (argV : type (arg (projT1 (attrType f)))) (retV : type (ret (projT1 (attrType f)))),
                         SemAction o (projT2 (attrType f) type argV) u cs retV ->
                         Pmeth cs.
    Proof.
      intros; unfold Pmeth.
      rewrite <- !FMap.M.Map.Facts.P.F.not_find_in_iff.
      let H := fresh in
      pose proof pequiv as H;
      unfold Wf.ModEquiv in H;
      destruct H; simpl in H.
      repeat match goal with
             | [ H : Wf.MethsEquiv _ _ _ |- _ ] => inversion H
             end.
      unfold Wf.MethEquiv in *; simpl in *; subst.
      
      simpl in H;
        repeat match goal with
               | [ H : _ \/ _ |- _ ] => destruct H
               end; subst;
          try match goal with
              | [ H : @eq (Attribute (Action Void)) _ _ |- _ ] => inv H
              end;
          simpl in *;        
          let K1 := fresh in 
          match goal with
          | [ H : SemAction _ ?x _ _ _, H' : forall a : ?A, forall b : ?B, Wf.ActionEquiv _ _ |- _ ] => epose proof (callsA_subset (H' _ _) H) as K1
          | _ => auto
          end;     
            repeat match goal with
                   | [ H : context[Wf.ActionEquiv] |- _ ] => clear H
                   | [ H : Wf.RulesEquiv _ _ _ |- _ ] => clear H
                   | [ H : Wf.MethsEquiv _ _ _ |- _ ] => clear H
                   end;
      try (split; let K2 := fresh in
                  intro K2; specialize (K1 _ K2);
                  unfold getCallsA in K1; compute in K1; intuition congruence).
      Unshelve.
      all: eauto; exact tt.
    Qed.

    Lemma Prume : forall rcs, Prule rcs ->
                         forall mcs, Pmeth mcs ->
                                Prule (FMap.M.union rcs mcs).  
    Proof.
      intros; unfold Prule, Pmeth in *.
      rewrite !FMap.M.find_union.
      intuition (repeat match goal with [ H : _ = _ |- _ ] => rewrite H end; try reflexivity).
    Qed.

    Lemma Pmeru : forall mcs, Pmeth mcs ->
                       forall rcs, Prule rcs ->
                              Prule (FMap.M.union mcs rcs).  
    Proof.
      intros; unfold Prule, Pmeth in *.
      rewrite !FMap.M.find_union.
      intuition (repeat match goal with [ H : _ = _ |- _ ] => rewrite H end; try reflexivity).
    Qed.

    Lemma Pmeme : forall mcs, Pmeth mcs ->
                       forall mcs', Pmeth mcs' ->
                               Pmeth (FMap.M.union mcs mcs').
    Proof.
      intros; unfold Prule, Pmeth in *.
      rewrite !FMap.M.find_union.
      intuition (repeat match goal with [ H : _ = _ |- _ ] => rewrite H end; try reflexivity).
    Qed.

    Lemma Prsub : forall rcs rcs', Prule rcs' -> FMap.M.Sub rcs rcs' -> Prule rcs.
    Proof.
      intros. unfold Prule in *.
      unfold FMap.M.Sub in *.
      intuition match goal with
                | [ H : context[FMap.M.find ?x] |- _ ] => specialize (H0 x)
                end;
        match goal with [ H : _ = _ |- _ ] => repeat rewrite H in *; clear H end;
        match goal with
        | [ H : forall v : _, ?x = _ -> _ |- _ ] => destruct x
        end;
        try match goal with
            | [ s : {x : SignatureT & SignT x} |- _ ] => specialize (H0 s)
            end;
       intuition congruence.
    Qed.
          
  End LabelMod.

  Module LabelFacts := (LabelDecomposition.Conclusions LabelMod).
  
  Theorem pRqRs : forall rf u l,
      Step p rf u l ->
      (FMap.M.find rqMeth (calls l) = None \/
       FMap.M.find rsMeth (calls l) = None).
  Proof.
    apply LabelFacts.Prule_Step.
  Qed.
  
End ThreeStageSingle.

Module ThreeStageSingleModularHiding <: (ThreeStageModularHiding ThreeStageSingle).
  Module Defs := ThreeStageDefs ThreeStageSingle.
  Module Invs := Inversions ThreeStageSingle.
  Import ThreeStageSingle Defs Invs.

  (* Lemma p_refine_inline : forall (o : RegsT) (u : RegsT) (ls : LabelSeqT),  Multistep p o u ls -> *)
  (*                                              Multistep (fst (Inline.inline p)) o u ls. *)
  (* Proof. *)
  (* [omitted, but it exists. basically can copy the existing proofs of inline-refinement..] *)
  (* Qed. *)
  (* Since inlining refinement doesn't go the other direction as well, this isn't directly applicable. *)

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
        (existT (fullType type) (SyntaxKind (Bit 11)) pc') -> pc = pc'.
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

  Definition getRuleBody (r : String.string) (n : Modules) : option (Action Void) :=
    match (find (fun (x : Attribute (Action Void)) => StringEq.string_eq r (attrName x)) (getRules n)) with
    | Some x => Some (attrType x)
    | None => None
    end.

  Definition getRuleCalls (r : String.string) (n : Modules) : option (list String.string) :=
    match (getRuleBody r n) with
    | Some x => Some (getCallsA (x typeUT))
    | None => None
    end.

  Record d2e_data :=
    { d2e_pc : address }
  .

  
  Record e2w_data :=
    { e2w_pc : address }
  .

  Record stall_data :=
    { stall_pc : address ;
      stall_val : data ;
      stall_op : bool }
  .

  Definition req_addr (m : MethsT) : option address :=
    match M.find rqMeth m with
    | Some (existT _
                   {| arg := Struct (STRUCT {"addr" :: Bit 11; 
                                             "op" :: Bool;
                                             "data" :: Bit 32});
                      ret := Bit 0 |}
                   (argV, retV)) =>
      Some (evalExpr (#argV!rv32iRq@."addr")%kami_expr)
    | _ => None
    end.

  
  Definition req_value (m : MethsT) : option data :=
    match M.find rqMeth m with
    | Some (existT _
                   {| arg := Struct (STRUCT {"addr" :: Bit 11; 
                                             "op" :: Bool;
                                             "data" :: Bit 32});
                      ret := Bit 0 |}
                   (argV, retV)) =>
      Some (evalExpr (#argV!rv32iRq@."data")%kami_expr)
    | _ => None
    end.
  
  Definition rep_value (m : MethsT) : option data :=
    match M.find rsMeth m with
    | Some (existT _
                   {| arg := Bit 0;
                      ret := Struct (STRUCT {"data" :: Bit 32} ) |}
                   (argV, retV)) =>
      Some (evalExpr (#retV!rv32iRs@."data")%kami_expr)
    | _ => None
    end.

  Definition fromHost_value (m : MethsT) : option data :=
    match M.find fhMeth m with
    | Some (existT _
                   {| arg := Bit 0; 
                      ret := Bit 32 |}
                   (argV, retV)) =>
      Some retV
    | _ => None
    end.

  Definition toHost_value (m : MethsT) : option data :=
    match M.find thMeth m with
    | Some (existT _
                   {| arg := Bit 32; 
                      ret := Bit 0 |}
                   (argV, retV)) =>
      Some argV
    | _ => None
    end.  

  (* Assumes that the LabelSeqT actually comes from a forward multistep *)
  Inductive relatedTrace : LabelSeqT -> option (d2e_data) -> option (e2w_data) -> option (stall_data) -> list TraceEvent -> Prop :=
  | rtNil : forall d2e e2w stall, relatedTrace nil d2e e2w stall nil
  (* Needs to deal with nops somehow. *)
  | rt_instFetch : forall pc d2w stall rle l ls trace, 
      rle = "instFetchNm" \/ rle = ("instFetchLd") \/ rle = ("instFetchSt") \/ rle = "instFetchFh" \/ rle = "instFetchTh"
      -> annot l = Some (Some rle)
      -> match (getRuleCalls rle p) with | Some cs => M.KeysSubset (calls l) cs | None => False end
      -> relatedTrace ls (Some {| d2e_pc := pc |}) d2w stall trace
      -> relatedTrace (l :: ls) None d2w stall trace
  | rt_exec : forall pc stall rle l ls trace,
      rle = "execBypass" \/ rle = "execNm"
      -> annot l = Some (Some rle)
      -> match (getRuleCalls rle p) with | Some cs => M.KeysSubset (calls l) cs | None => False end
      -> relatedTrace ls None (Some {| e2w_pc := pc |}) stall trace
      -> relatedTrace (l :: ls) (Some {| d2e_pc := pc |}) None stall trace
  | rtNm : forall pc d2e rle l ls trace',
      rle = "wbNm" \/ rle = "wbNmZ"
      -> annot l = Some (Some rle)
      -> match (getRuleCalls rle p) with | Some cs => M.KeysSubset (calls l) cs | None => False end
      -> relatedTrace ls d2e None None trace' (* instxns only show up in the abstract trace when they pass writeback *)
      -> relatedTrace (l :: ls) d2e (Some {| e2w_pc := pc |}) None (Nm pc :: trace')  
  | rtRd : forall pc addr val d2e rle l ls trace', 
      rle = "reqLd"
      -> annot l = Some (Some rle)
      -> match (getRuleCalls rle p) with | Some cs => M.KeysSubset (calls l) cs | None => False end
      -> req_addr (calls l) = Some addr
      -> relatedTrace ls d2e None (Some {| stall_pc := pc; stall_val := val; stall_op := false |}) trace' 
      -> relatedTrace (l :: ls) d2e (Some {| e2w_pc := pc |}) None (Rd pc addr val :: trace')
  | rtRd' : forall pc val d2e e2w rle l ls trace,
      rle = "repLd"
      -> annot l = Some (Some rle)
      -> match (getRuleCalls rle p) with | Some cs => M.KeysSubset (calls l) cs | None => False end
      -> rep_value (calls l) = Some val 
      -> relatedTrace ls d2e e2w None trace
      -> relatedTrace (l :: ls) d2e e2w (Some {| stall_pc := pc; stall_val := val; stall_op := false |}) trace
  | rtRdZ : forall pc addr d2e rle l ls trace',
      rle = "reqLdZ"
      -> annot l = Some (Some rle)
      -> match (getRuleCalls rle p) with | Some cs => M.KeysSubset (calls l) cs | None => False end
      -> relatedTrace ls d2e None None trace'
      -> relatedTrace (l :: ls) d2e (Some {| e2w_pc := pc |}) None (RdZ pc addr :: trace')
  | rtWr : forall pc addr d2e val rle l ls trace',
      rle = "reqSt"
      -> annot l = Some (Some rle)
      -> match (getRuleCalls rle p) with | Some cs => M.KeysSubset (calls l) cs | None => False end
      -> req_addr (calls l) = Some addr
      -> req_value (calls l) = Some val 
      -> relatedTrace ls d2e None (Some {| stall_pc := pc; stall_val := val; stall_op := true |}) trace'
      -> relatedTrace (l :: ls) d2e (Some {| e2w_pc := pc |}) None (Wr pc addr val :: trace')
  | rtWr' : forall pc val d2e e2w rle l ls trace, 
      rle = "repSt"
      -> annot l = Some (Some rle)
      -> match (getRuleCalls rle p) with | Some cs => M.KeysSubset (calls l) cs | None => False end
      -> relatedTrace ls d2e e2w None trace
      -> relatedTrace (l :: ls) d2e e2w (Some {| stall_pc := pc; stall_val := val; stall_op := true |}) trace
  | rtFH : forall pc (val : data) d2e val rle l ls trace',
      rle = "execFromHost" \/ rle = "execFromHostZ"
      -> annot l = Some (Some rle)
      -> match (getRuleCalls rle p) with | Some cs => M.KeysSubset (calls l) cs | None => False end
      -> fromHost_value (calls l) = Some val 
      -> relatedTrace ls d2e None None trace' 
      -> relatedTrace (l :: ls) d2e (Some {| e2w_pc := pc |}) None (FromHost pc val :: trace')
  | rtTH : forall pc (val : data) d2e val rle l ls trace',
      rle = "execToHost"
      -> annot l = Some (Some rle)
      -> match (getRuleCalls rle p) with | Some cs => M.KeysSubset (calls l) cs | None => False end
      -> toHost_value (calls l) = Some val
      -> relatedTrace ls d2e None None trace'
      -> relatedTrace (l :: ls) d2e (Some {| e2w_pc := pc |}) None (ToHost pc val :: trace')
  .

    Lemma relatedFhTrace :
    forall trace ls d2e e2w stall,
      relatedTrace ls d2e e2w stall trace -> extractFhTrace trace = extractFhLabelSeq fhMeth ls.
  Proof.
    induction 1; simpl; eauto; try match goal with [ |- ?a = _ ] => change a with (nil ++ a)%list; f_equal; [| assumption ] end.
    9: {
      destruct l as [a d c]; simpl in *.
      match goal with [ |- context[?x::?y] ] => change (x :: y) with ([x] ++ y) end. f_equal; try assumption.
      unfold extractFhMeths. unfold fromHost_value in *.
      destruct ((c)@[ fhMeth ])%fmap; simpl.
      destruct s.
      repeat match goal with
               [ |- context[match ?a with | _ => _ end] ] => destruct a
             end.
      all: try congruence. match goal with [ H : _ |- _ ] => inversion H; reflexivity end.
    }
      
    all: intuition subst;  destruct l as [a d c]; 
      destruct (M.F.P.F.In_dec c fhMeth); [
      specialize (H1 fhMeth i); simpl in *;
      intuition repeat match goal with [ H : (@eq M.Map.key _ _) |- _ ] => inversion H end
      | rewrite M.F.P.F.not_find_in_iff in n; simpl;
      unfold extractFhMeths; rewrite n; reflexivity ].
  Qed.
  
  (* A [subst] tactic that doesn't unfold definitions *)
  Ltac opaque_subst :=
    repeat match goal with
           | [ Heq : ?x = ?y |- _ ] => ((tryif unfold x then fail else subst x) || (tryif unfold y then fail else subst y))
           end.


  Lemma Sub_trans : forall A x y z, FMap.M.Sub (A:=A) x y -> FMap.M.Sub y z -> FMap.M.Sub x z.
  Proof.
    unfold FMap.M.Sub in *; auto.
  Qed.



  Lemma no_calls_from_calls : forall f o u cs argV retV,
      In f (getDefsBodies p) -> SemAction o (projT2 (attrType f) type argV) u cs retV ->
      cs = FMap.M.empty _.
  Proof.
    intros.
    apply FMap.M.Sub_empty_2. unfold FMap.M.Sub; intros. rewrite <- H1, FMap.M.find_empty. clear H1 v.
    symmetry; rewrite <- FMap.M.Map.Facts.P.F.not_find_in_iff.
          let H := fresh in
      pose proof pequiv as H;
      unfold Wf.ModEquiv in H;
      destruct H; simpl in H.
      repeat match goal with
             | [ H : Wf.MethsEquiv _ _ _ |- _ ] => inversion H
             end.
      unfold Wf.MethEquiv in *; simpl in *; subst.
      
      simpl in H;
        repeat match goal with
               | [ H : _ \/ _ |- _ ] => destruct H
               end; subst;
          try match goal with
              | [ H : @eq (Attribute (Action Void)) _ _ |- _ ] => inv H
              end;
          simpl in *;        
          let K1 := fresh in 
          match goal with
          | [ H : SemAction _ ?x _ _ _, H' : forall a : ?A, forall b : ?B, Wf.ActionEquiv _ _ |- _ ] => epose proof (callsA_subset (H' _ _) H) as K1
          | _ => auto
          end;     
            repeat match goal with
                   | [ H : context[Wf.ActionEquiv] |- _ ] => clear H
                   | [ H : Wf.RulesEquiv _ _ _ |- _ ] => clear H
                   | [ H : Wf.MethsEquiv _ _ _ |- _ ] => clear H
                   end;
      try (let K2 := fresh in
                  intro K2; specialize (K1 _ K2);
                  unfold getCallsA in K1; compute in K1; intuition congruence).
      Unshelve.
      all: eauto; exact tt.
  Qed.
 
  Lemma ThreeStageProcSubsteps :
    forall o (ss : Substeps p o),
      SubstepsInd p o (foldSSUpds ss) (foldSSLabel ss) ->
      (exists ds, ((foldSSLabel ss) = {| annot := None; defs := ds; calls := FMap.M.empty _ |}
        \/ (foldSSLabel ss) = {| annot := Some None; defs := ds; calls := FMap.M.empty _ |}))
      \/ (exists k a u ds cs,
            In (k :: a)%struct (getRules p)
            /\ SemAction o (a type) u cs WO
            /\ (foldSSLabel ss) = {| annot := Some (Some k); defs := ds; calls := cs |}
            /\ FMap.M.Sub u (foldSSUpds ss)).
  Proof.
    intros.
    match goal with
    | [ H : SubstepsInd _ _ _ _ |- _ ] => induction H
    end.
    - eauto.
    - intuition idtac;
        simpl;
        shatter;
        intuition idtac;
        subst;
        match goal with
        | [ H : Substep _ _ _ _ _ |- _ ] => destruct H
        end; try (
                 unfold getLabel, mergeLabel; eauto);
        try (right;
             exists k, a, u0, x, cs;
             simpl in HInRules;
             intuition idtac;
             simpl;
             FMap.findeq;
             try (apply FMap.M.Sub_union_2; apply FMap.M.Disj_comm; unfold CanCombineUUL in H1; tauto)).
      left; eexists; left. assert (cs = FMap.M.empty _) by (eapply no_calls_from_calls; eassumption).
      subst; eauto.
      left; eexists; right. assert (cs = FMap.M.empty _) by (eapply no_calls_from_calls; eassumption).
      subst; eauto.
      unfold CanCombineUUL in H1; simpl in H1; tauto. 
      right. simpl in H4; intuition idtac;
      match goal with
      | [ H : (_::_)%struct = (?k::?a)%struct, _ : SemAction o (?a type) ?u0 ?cs WO,
                                                   _ : SubstepsInd p o u {| annot := Some (Some ?k); defs := ?ds; calls := ?cs |} |- _ ] =>
        exists k, a, u0, ds, cs; intuition idtac; try (rewrite FMap.M.union_empty_R; auto)
      end.
      unfold CanCombineUUL in H1; simpl in H1. tauto.
      right. simpl in H4; intuition idtac; subst sig; assert (cs = FMap.M.empty _)
               by (eapply no_calls_from_calls; eassumption); subst cs;
      match goal with
      | [ H : (_::_)%struct = (?k::?a)%struct, _ : SemAction o (?a type) ?u0 ?cs WO |- _ ] =>
        exists k, a, u0;
          match goal with
          | [ |- context[{| annot := _ ; defs := ?ds ; calls := _ |} = _] ] => exists ds
          end;
          exists cs; intuition idtac; try (rewrite FMap.M.union_empty_R; auto);
            try (eapply Sub_trans; [ eassumption | apply FMap.M.Sub_union_1])
      end.
  Qed.
            
  Definition zeroRet (lastRq : option bool) (n : String.string) (t : {x : SignatureT & SignT x}) : {x : SignatureT & SignT x} :=
    if String.string_dec n rsMeth (* zeroes responses to STOREs *)
    then match t with
         | existT _
                  {| arg := Bit 0;
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (argV, retV) =>
           match lastRq with
             | Some op => 
               if op
               then existT _
                           {| arg := Bit 0;
                              ret := Struct (STRUCT {"data" :: Bit 32}) |}
                           (argV,
                            evalExpr (STRUCT { "data" ::= $0 })%kami_expr)
               else t
             | None => t (* unbalanced *)
           end
         | _ => t
         end
    else t.

  Definition canonicalizeLabel (lastRq : option bool) (l : LabelT) : LabelT :=
    match l with
    | {| annot := None;
        defs := d;
        calls := c |} => {| annot := Some None; defs := d; calls := FMap.M.mapi (zeroRet lastRq)  c |}
    | {| annot := Some a;
        defs := d;
        calls := c |} => {| annot := Some a; defs := d; calls := FMap.M.mapi (zeroRet lastRq) c |}
    end.

  Fixpoint canonicalize (lastRq : option bool) (ls : list LabelT) : list LabelT :=
    match ls with
    | nil => nil
    | l :: ls' => (canonicalizeLabel lastRq l) :: (canonicalize (getRqCall lastRq l) ls')
    end.

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
    | [ |- context[FMap.M.mapi (zeroRet ?lRq) ?mp] ] =>
      let Heq := fresh in
      let k := fresh in
      assert (FMap.M.mapi (zeroRet lRq) mp = mp) as Heq
          by (clear;
              FMap.M.ext k;
              rewrite FMap.M.F.P.F.mapi_o
                by congruence;
              FMap.mred);
      repeat rewrite Heq;
      repeat rewrite Heq in *;
      clear Heq
    | [ H : context[FMap.M.mapi (zeroRet ?lRq) ?mp] |- _ ] =>
      let Heq := fresh in
      let k := fresh in
      assert (FMap.M.mapi (zeroRet lRq) mp = mp) as Heq
          by (clear;
              FMap.M.ext k;
              rewrite FMap.M.F.P.F.mapi_o
                by congruence;
              FMap.mred);
      repeat rewrite Heq;
      repeat rewrite Heq in *;
      clear Heq
    end.
  
  Lemma canonicalize_same_getRqCall : forall lastRq lastRq' l,
      getRqCall lastRq' (canonicalizeLabel lastRq l) = getRqCall lastRq' l.
  Proof.
    intros.
    unfold canonicalizeLabel.
    destruct l. destruct annot.
    - unfold getRqCall; simpl.
      repeat rewrite FMap.M.F.P.F.mapi_o.
      2, 3: firstorder congruence.
      change FMap.M.Map.find with FMap.M.find.
      destruct (FMap.M.find rqMeth calls); 
        destruct (FMap.M.find rsMeth calls); simpl.
      unfold zeroRet; simpl.
      all: reflexivity.
    - unfold getRqCall; simpl.
      repeat rewrite FMap.M.F.P.F.mapi_o.
      2, 3: firstorder congruence.
      change FMap.M.Map.find with FMap.M.find.
      destruct (FMap.M.find rqMeth calls); 
        destruct (FMap.M.find rsMeth calls); simpl.
      unfold zeroRet; simpl.
      all: reflexivity.
  Qed.

  
  Lemma getRqCall_rqMeth_present :
    forall l lastRq argV retV,
      FMap.M.find rqMeth (calls l) =
      Some (existT SignT {| arg := Struct STRUCT {"addr" :: Bit 11; "op" :: Bool; "data" :: Bit 32}; ret := Bit 0 |} (argV, retV)) ->
      getRqCall lastRq l = Some (evalExpr ((# (argV)) ! rv32iRq @.("op"))%kami_expr).
  Proof.
    intros l lastRq argV retV H.
    unfold getRqCall. rewrite !H. reflexivity.
  Qed.

  
  Lemma getRqCall_rqMeth_absent :
    forall l lastRq,
      FMap.M.find rqMeth (calls l) = None ->
      getRqCall lastRq l = match (calls l) @[ rsMeth]%fmap with
                           | Some _ => None
                           | None => lastRq
                           end.
  Proof.
    intros l lastRq H.
    unfold getRqCall. rewrite !H. reflexivity.
  Qed.

  Lemma mapi_empty : forall {elt elt'} (f : _ -> elt -> elt'),
      FMap.M.mapi f (FMap.M.empty _) = FMap.M.empty _.
  Proof.
    intros. apply FMap.M.Sub_empty_2; try congruence.
    unfold FMap.M.Sub; intros. rewrite FMap.M.F.P.F.mapi_o in H; try congruence.
    inv H.
  Qed.

  Lemma p_no_def_rs_substeps : forall o (ss : Substeps p o) a d c,
      (foldSSLabel ss) = {| annot := a; defs := d; calls := c|} -> 
      ~ FMap.M.In rsMeth d.
  Proof.
    intuition intros. apply (f_equal defs) in H; simpl in H; subst. apply getDefs_substeps in H0.
    apply pndrs. tauto.
  Qed.

  Lemma p_no_def_rq_substeps : forall o (ss : Substeps p o) a d c,
      (foldSSLabel ss) = {| annot := a; defs := d; calls := c|} -> 
      ~ FMap.M.In rqMeth d.
  Proof.
    intuition intros. apply (f_equal defs) in H; simpl in H; subst. apply getDefs_substeps in H0.
    apply pndrq. tauto.
  Qed.

  Lemma p_substeps_defs_pointwise_fixed : forall lastRq k v o (ss : Substeps p o) a d c,
      (foldSSLabel ss) = {| annot := a; defs := d; calls := c|} -> 
      v = FMap.M.find k d -> 
      option_map (zeroRet lastRq k) v = v.
  Proof.
    intros.
    destruct v; try reflexivity.
    simpl; f_equal. unfold zeroRet. destruct (String.string_dec k rsMeth).
    exfalso. subst. pose proof (p_no_def_rs_substeps o ss _ _ _ H).
    rewrite FMap.M.F.P.F.not_find_in_iff in *.
    all: congruence.
  Qed.

  Lemma mapi_subtractKV_1 : forall de lastRq o a d c (ss : Substeps p o) m1,
      (foldSSLabel ss) = {| annot := a; defs := d; calls := c |} ->
      FMap.M.mapi (zeroRet lastRq) (FMap.M.subtractKV de d m1) =
      FMap.M.subtractKV de d (FMap.M.mapi (zeroRet lastRq) m1).
  Proof.
    intros; match goal with [ H : _ |- _ ] => apply (f_equal defs) in H end; simpl in *; subst; clear a c.
    apply FMap.M.leibniz; unfold FMap.M.Equal.
    intro k.
    destruct (foldSSLabel ss) as [a d c] eqn:Q; simpl.
    pose proof (p_substeps_defs_pointwise_fixed lastRq k _ _ ss _ _ _ Q eq_refl).
    repeat (try rewrite FMap.M.subtractKV_find; try rewrite FMap.M.F.P.F.mapi_o); try congruence.
    remember (FMap.M.find k m1) as f1; remember (FMap.M.find k d) as f2.
    destruct f1; destruct f2; simpl;
      repeat match goal with [ |- context[if ?x then _ else _] ] => destruct x end; subst; simpl in *; try congruence.
    clear H; exfalso. unfold zeroRet in *;
    destruct (String.string_dec k rsMeth); simpl in *.
    subst. pose proof (p_no_def_rs_substeps o ss _ _ _ Q).
    rewrite FMap.M.F.P.F.not_find_in_iff in *.
    all: intuition congruence.
  Qed.

  Lemma mapi_subtractKV_2 : forall de lastRq o a d c (ss : Substeps p o) m1,
      (foldSSLabel ss) = {| annot := a; defs := d; calls := c |} ->
      FMap.M.mapi (zeroRet lastRq) (FMap.M.subtractKV de m1 d) =
      FMap.M.subtractKV de (FMap.M.mapi (zeroRet lastRq) m1) d.
  Proof.
    intros; match goal with [ H : _ |- _ ] => apply (f_equal defs) in H end; simpl in *; subst; clear a c.
    apply FMap.M.leibniz; unfold FMap.M.Equal.
    intro k.
    destruct (foldSSLabel ss) as [a d c] eqn:Q; simpl in *.
    pose proof (p_substeps_defs_pointwise_fixed lastRq k _ _ ss _ _ _ Q eq_refl).
    repeat (try rewrite FMap.M.subtractKV_find; try rewrite FMap.M.F.P.F.mapi_o); try congruence.
    remember (FMap.M.find k m1) as f1; remember (FMap.M.find k d) as f2.
    destruct f1; destruct f2; simpl;
      repeat match goal with [ |- context[if ?x then _ else _] ] => destruct x end; subst; simpl in *; try congruence.
    clear H; exfalso. unfold zeroRet in *;
    destruct (String.string_dec k rsMeth); simpl in *.
    subst. pose proof (p_no_def_rs_substeps o ss _ _ _ Q).
    rewrite FMap.M.F.P.F.not_find_in_iff in *.
    all: intuition congruence.    
  Qed.

  Lemma subtractKV_found : forall {elt de} k (v:elt) m1 m2, FMap.M.find k (FMap.M.subtractKV de m1 m2) = Some v ->
                                                       FMap.M.find k m1 = Some v.
  Proof.
    intros elt de k v m1 m2 H.
    rewrite FMap.M.subtractKV_find in H.
    destruct (FMap.M.find k m1); destruct (FMap.M.find k m2);
      try match goal with [ H : context[if ?x then _ else _] |- _ ] => destruct x end;
      congruence.
  Qed.

  Lemma same_name_same_rule : forall name rule rule',
      In (name :: rule)%struct (getRules p) ->
      In (name :: rule')%struct (getRules p) ->
      rule = rule'.
  Proof.
    intros name rule rule' H H'.
    simpl in H; simpl in H'; intuition congruence.
  Qed.

  Lemma Rules_Rule_equiv : forall t1 t2 rules rule,
      In rule rules -> Wf.RulesEquiv t1 t2 rules -> Wf.RuleEquiv t1 t2 rule.
  Proof.
    intros t1 t2 rules rule H H0.
    induction rules; inv H; inv H0; auto.
  Qed.


  Lemma who_calls_rq : forall name rule o u cs v,
      In (( name :: rule%struct )%struct) (getRules p) ->
      SemAction o (rule type) u cs v ->
      (FMap.M.In rqMeth cs) -> (name = "reqLd" \/ name = "reqSt").
  Proof.
    intros. 
    eapply callsA_subset in H1.
    2: { pose proof pequiv. unfold Wf.ModEquiv in *; shatter. eapply Rules_Rule_equiv in H2. unfold Wf.RuleEquiv in H2.
         eassumption. eassumption.
    }
    2: { eassumption. }
    simpl in H; intuition;
      match goal with [ H : _ = (_::_)%struct |- _ ] => inv H end.
    all: compute in H1.
    all: intuition congruence.
  Qed.

    Lemma who_calls_rs : forall name rule o u cs v,
      In (( name :: rule%struct )%struct) (getRules p) ->
      SemAction o (rule type) u cs v ->
      (FMap.M.In rsMeth cs) -> (name = "repLd" \/ name = "repSt").
  Proof.
    intros. 
    eapply callsA_subset in H1.
    2: { pose proof pequiv. unfold Wf.ModEquiv in *; shatter. eapply Rules_Rule_equiv in H2. unfold Wf.RuleEquiv in H2.
         eassumption. eassumption.
    }
    2: { eassumption. }
    simpl in H; intuition;
      match goal with [ H : _ = (_::_)%struct |- _ ] => inv H end.
    all: compute in H1.
    all: intuition congruence.
  Qed.

  Lemma zeroRet_LD : forall s m, zeroRet (Some false) s m = m. (* only zeroes responses to ST *)
  Proof.
    intros.
    unfold zeroRet. destruct m0. destruct (String.string_dec s rsMeth);
    repeat (try reflexivity; match goal with
                             | [ |- context[match ?z with | _ => _ end] ] => destruct z
                             end).
  Qed.

  Lemma mapi_global_fix : forall {e} (f : _ -> e -> e),
      (forall n x, f n x = x) ->
      forall l, M.mapi f l = l.
  Proof.
    intros.
    apply M.leibniz. unfold FMap.M.Equal.
    intro. rewrite M.F.P.F.mapi_o by congruence.
    destruct (l@[y])%fmap;
      simpl; congruence.
  Qed.    
        
  Lemma decanon : forall lastRq o o' n n' mem f l0 l1,
      ForwardMultistep p o n l1 ->
      ThreeStageProcMemConsistent l1 lastRq mem ->
      ForwardMultistep p o' n' l0 ->
      let lRq := (option_map fst lastRq) in
      censorThreeStageLabelSeq lRq getRqCall censorThreeStageMeth (canonicalize lRq l0) =
      censorThreeStageLabelSeq lRq getRqCall censorThreeStageMeth (canonicalize lRq l1) ->
      extractFhLabelSeq fhMeth l1 = f ->
      exists l1',
        ForwardMultistep p o n l1' /\
        ThreeStageProcMemConsistent l1' lastRq mem /\
        censorThreeStageLabelSeq lRq getRqCall censorThreeStageMeth l0 =
        censorThreeStageLabelSeq lRq getRqCall censorThreeStageMeth l1' /\
        extractFhLabelSeq fhMeth l1' = f.
  Proof.
    intros lastRq o o' n n' mem f l0 l1 Hfm.
    move Hfm at top.
    generalize lastRq, mem, f, l0, o', n'.
    clear lastRq mem f l0 o' n'.
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
      | [ H : ThreeStageProcMemConsistent _ _ _ |- _ ] => inv H
      end;
      specialize (IHHfm last' mem' (extractFhLabelSeq fhMeth a) _ _ _ H10 H9);
      match goal with [ _ : ?a -> ?x = ?x -> _ |- _ ] => assert a as Htemp end.
      1: {
        clear - H4 H5 H3; cbv zeta in *; shatter; subst; simpl in *;
        pose proof (rqCall_from_censor _ _ _ H4) as H6;
        change (Defs.getRqCall) with getRqCall in *;
        rewrite H6 in *;
        repeat rewrite canonicalize_same_getRqCall in *;
        rewrite H6 in *;
        repeat erewrite getRqCall_rqMeth_present in H5 by eassumption;
        simpl in H5. assumption.
      }
      2: {
        clear - H H4 H5 H3; cbv zeta in *; shatter; subst; simpl in *.
        pose proof (rqCall_from_censor _ _ _ H4) as H6;
        change (Defs.getRqCall) with getRqCall in *;
        rewrite H6 in *;
        repeat rewrite canonicalize_same_getRqCall in *;
        rewrite H6 in *.
        eassert _ by (eapply pRqRs; eassumption).
        destruct X; try congruence.
        repeat erewrite getRqCall_rqMeth_absent in H5 by eassumption.
        repeat rewrite H0 in H5.
        simpl in H5. assumption.
      }
      3: {
        clear - H H4 H5 H3; cbv zeta in *; shatter; subst; simpl in *.
        pose proof (rqCall_from_censor _ _ _ H4) as H6;
        change (Defs.getRqCall) with getRqCall in *;        
        rewrite H6 in *;
        repeat rewrite canonicalize_same_getRqCall in *;
        rewrite H6 in *.
        repeat erewrite getRqCall_rqMeth_absent in H5 by eassumption.
        repeat rewrite H1 in H5.
        simpl in H5. assumption.
      }
      
      all: specialize (IHHfm Htemp eq_refl);
      shatter;
      match goal with
      | [ H : Step _ _ _ _, H' : Step _ _ _ _ |- _ ] => inversion H; inversion H'
      end;
      apply substepsComb_substepsInd in HSubsteps;
      apply substepsComb_substepsInd in HSubsteps0;
      apply ThreeStageProcSubsteps in HSubsteps;
      apply ThreeStageProcSubsteps in HSubsteps0;
      intuition idtac;
        shatter; intuition idtac; subst;
          try (repeat match goal with
                      | [ H : FMap.M.find _ _ = Some _, H' : _ = _ |- _ ] => rewrite H' in H
                      end; (* here we're eliminating cases where we assume we find something in nothing *)
               match goal with
               | [ H : FMap.M.find _ _ = Some _ |- _ ] => unfold hide in H; simpl in H;
                                                        apply subtractKV_found in H;
                                                        repeat ((rewrite M.find_add_1 in H || rewrite M.find_add_2 in H by auto || rewrite M.find_empty in H); try reflexivity);
                                                        inv H
               end);
          repeat match goal with
                 | [ H : foldSSLabel _ = _ |- _ ] => rewrite H in *
                 end;
          try (simpl in *; congruence); (* gets rid of cases where the allegedly censor-equivalent things can't actually be *)
          try match goal with
              | [ H : censorLabel _ (canonicalizeLabel _ (hide {| annot := ?al; defs := ?dl; calls := ?cl |})) =
                      censorLabel _ (canonicalizeLabel _ (hide {| annot := ?ar; defs := ?dr; calls := ?cr |})) |- _ ] =>
                simpl in H; repeat rewrite FMap.M.subtractKV_empty_1 in H; repeat rewrite FMap.M.subtractKV_empty_2 in H;
                  let H1 := fresh in assert (al = ar) as H1 by (inversion H; reflexivity); inv H1
              end;
          try match goal with
              | [ H : In (?a :: ?b)%struct (getRules p), H' : In (?a :: ?b')%struct (getRules p) |- _ ] =>
                assert (b = b') by (eapply same_name_same_rule; eassumption);
                  subst; clear H'
              end;
          try match goal with
              | [ H : In _ (getRules p) , H' : SemAction _ _ _ ?cs _, Hfind : (FMap.M.find rqMeth ?cs) = Some _ |- _ ] =>
                let HIn := fresh in
                (assert (FMap.M.In rqMeth cs) as HIn by (rewrite M.F.P.F.in_find_iff; destruct (FMap.M.find rqMeth cs); congruence);
                 pose proof (who_calls_rq _ _ _ _ _ _ H H' HIn))
              | [ H : In _ (getRules p) , H' : SemAction _ _ _ ?cs _, Hfind : (FMap.M.find rsMeth ?cs) = Some _ |- _ ] =>
                let HIn := fresh in
                (assert (FMap.M.In rsMeth cs) as HIn by (rewrite M.F.P.F.in_find_iff; destruct (FMap.M.find rsMeth cs); congruence);
                 pose proof (who_calls_rs _ _ _ _ _ _ H H' HIn))
              end;
          try match goal with
              | [ H : In _ (getRules p) |- _ ] => simpl in H
              end;
          intuition idtac;
          repeat match goal with
                 | [ H : _ = (_::_)%struct |- _ ] => inv H
                 end; try (exfalso; congruence);
            try match goal with
                | [ |- context["repLd"] ] => idtac
                | [ |- context["repSt"] ] => idtac
                (* | [ |- context["reqLd"] ] => idtac *)
                (* | [ |- context["reqSt"] ] => idtac *)
                | [ H : _ = {| annot := Some (Some ?mn); defs := M.mapi _ ?dfs; calls := M.mapi _ ?mths |} |- _ ] =>
                  exists ({| annot := Some (Some mn); defs := dfs; calls := mths |} :: x)
                end.

      + Opaque evalExpr. 
        kinv_action_dest. (* fully inverts the SemAction *)
      erewrite !mapi_subtractKV_2 by eassumption.
      repeat ((rewrite M.find_add_1 in H11 || rewrite M.find_add_2 in H11 by auto); try reflexivity).
      inv_some; destruct_existT; inv H11.
      Transparent evalExpr.
      zr_noop. (* verifies when zeroRet doesn't change an explicit list *)
      Opaque evalExpr.
      split.
      econstructor.
      eassumption. assumption.
      split.
      eapply S3PMCrq. cbv zeta.
      split. simpl.
      rewrite FMap.M.subtractKV_find.
      M.find_add_tac.
      replace (FMap.M.find rqMeth x8) with (None (A:={x:SignatureT & SignT x})).
      reflexivity.
      pose proof (p_no_def_rq_substeps _ _ _ _ _ H21). rewrite M.F.P.F.not_find_in_iff in H11.
      rewrite H11. reflexivity.
      split. reflexivity. eassumption. eassumption.
      split. simpl. f_equal.
      assumption.
      match goal with [ H : censorThreeStageLabelSeq ?a _ _ ?l = censorThreeStageLabelSeq ?a _ _ ?r |-
                        censorThreeStageLabelSeq ?b _ _ ?l = censorThreeStageLabelSeq ?b' _ _ ?r ] =>
                      replace a with b in H at 1; [replace a with b' in H at 1; try apply H|] end.
      unfold getRqCall. simpl.
      rewrite FMap.M.subtractKV_find.
      M.find_add_tac.
      replace (FMap.M.find rqMeth x8) with (None (A:={x:SignatureT & SignT x})).
      reflexivity.
      symmetry; rewrite <- FMap.M.F.P.F.not_find_in_iff;
        eapply p_no_def_rq_substeps; eassumption.

      
      unfold getRqCall. simpl.
      rewrite FMap.M.subtractKV_find.
      M.find_add_tac.
      replace (FMap.M.find rqMeth x3) with (None (A:={x:SignatureT & SignT x})).
      reflexivity.
      symmetry; rewrite <- FMap.M.F.P.F.not_find_in_iff;
        eapply p_no_def_rq_substeps; eassumption.
      simpl; f_equal; assumption.
      
      (* That does one of the rules. Theoretically, the rest of them in which zeroRet doesn't actually make a change --- *)
      (* ie, everything but the responses from the memory --- should yield to a similar strategy, but the time that kinv_action_dest *)
      (* and find_add_tac take becomes too much. findReify can replace the latter. Commented out below is some still-very-slow script that *)
      (* handles most of the other non-response-from-memory cases. *)

     (*   + Opaque evalExpr. *)
    (*   kinv_action_dest. *)
    (*   erewrite !mapi_subtractKV_2 by eassumption. *)
    (*   repeat ((rewrite M.find_add_1 in H11 || rewrite M.find_add_2 in H11 by auto); try reflexivity). *)
    (*   inv_some; destruct_existT; inv H11. *)
    (*   Transparent evalExpr. *)
    (*   zr_noop. *)
    (*   Opaque evalExpr.  *)
    (*   split. *)
    (*   econstructor. *)
    (*   eassumption. assumption. *)
    (*   split. *)
    (*   eapply S3PMCrq. cbv zeta. *)
    (*   split. simpl. *)
    (*   rewrite FMap.M.subtractKV_find. *)
    (*   M.find_add_tac. *)
    (*   replace (FMap.M.find rqMeth x8) with (None (A:={x:SignatureT & SignT x})). *)
    (*   reflexivity. *)
    (*   pose proof (p_no_def_rq_substeps _ _ _ _ _ H21). rewrite M.F.P.F.not_find_in_iff in H11. *)
    (*   rewrite H11. reflexivity. *)
    (*   split. reflexivity. eassumption. eassumption. *)
    (*   split. simpl. f_equal. *)
    (*   assumption. *)
    (*   match goal with [ H : censorThreeStageLabelSeq ?a _ _ ?l = censorThreeStageLabelSeq ?a _ _ ?r |- *)
    (*                     censorThreeStageLabelSeq ?b _ _ ?l = censorThreeStageLabelSeq ?b' _ _ ?r ] => *)
    (*                   replace a with b in H at 1; [replace a with b' in H at 1; try apply H|] end.  *)
    (*   unfold getRqCall. simpl. *)
    (*   rewrite FMap.M.subtractKV_find. *)
    (*   M.find_add_tac. *)
    (*   replace (FMap.M.find rqMeth x8) with (None (A:={x:SignatureT & SignT x})). *)
    (*   reflexivity. *)
    (*   symmetry; rewrite <- FMap.M.F.P.F.not_find_in_iff; *)
    (*     eapply p_no_def_rq_substeps; eassumption. *)

      
    (*   unfold getRqCall. simpl. *)
    (*   rewrite FMap.M.subtractKV_find. *)
    (*   M.find_add_tac. *)
    (*   replace (FMap.M.find rqMeth x3) with (None (A:={x:SignatureT & SignT x})). *)
    (*   reflexivity. *)
    (*   symmetry; rewrite <- FMap.M.F.P.F.not_find_in_iff; *)
    (*     eapply p_no_def_rq_substeps; eassumption. *)
    (*   simpl; f_equal; assumption.  *)

    (*   + (* repLd *) *)
    (*     assert (lRq = Some false) by admit. *)
    (*     subst lRq. destruct lastRq. destruct p0. destruct b. *)
    (*     all: try (exfalso; simpl in *; congruence). *)
    (*     clear H2 H15. simpl in *. *)
    (*     repeat erewrite (mapi_global_fix (zeroRet (Some false))) in * by (apply zeroRet_LD).         *)
    (*     eexists (_ :: x). *)
    (*     simpl. *)
    (*     split. econstructor. *)
    (*     eassumption. *)
    (*     eassumption. *)
    (*     split. eapply S3PMCrs. *)
    (*     split.  symmetry. simpl. rewrite M.subtractKV_find.  *)
    (*     change (sigT (fun x0 : SignatureT => SignT x0)) with (sigT SignT). rewrite H12. simpl. *)
    (*     replace ((x8 @[rsMeth])%fmap) with (None (A:={x:SignatureT & SignT x})) by admit. *)
    (*     unfold zeroRet; simpl. *)
    (*     reflexivity.  *)
    (*     split. reflexivity.  *)
    (*     eassumption. *)
    (*     assumption. *)
    (*     simpl. split. f_equal. assumption. *)
    (*     rewrite !getRqCall_rqMeth_absent. simpl. *)
    (*     rewrite !M.subtractKV_find. rewrite !H12. replace ((x8)@[rsMeth])%fmap with (None(A:={x:SignatureT & SignT x})) by admit. *)
    (*     simpl. admit. admit. admit. *)
    (*     f_equal. assumption. *)
    (*   + admit. (* repSt *) *)
    (*   + rewrite mapi_empty in H4. *)
    (*     eexists (_ :: x). split. *)
    (*     econstructor. eassumption. eassumption. *)
    (*     intuition idtac. *)
    (*     eapply S3PMCcons. *)
    (*     intuition congruence. assumption. *)
    (*     simpl. f_equal. *)
    (*     rewrite !M.subtractKV_empty_1, !M.subtractKV_empty_2. *)
    (*     inv_label. congruence. *)
    (*     unfold hide; simpl; rewrite !M.subtractKV_empty_1, !M.subtractKV_empty_2. *)
    (*     unfold getRqCall at 1 3; simpl. assumption. *)
    (*     simpl. f_equal. assumption. *)
    (*   + unfold hide, canonicalizeLabel in H4; simpl in H4. rewrite !M.subtractKV_empty_1, !M.subtractKV_empty_2 in H4. rewrite mapi_empty in H4. *)
    (*     unfold hide in H; apply step_rule_annot_1 in H. *)
    (*     eexists (_ :: x). split. *)
    (*     econstructor. eassumption. eassumption. *)
    (*     intuition idtac. *)
    (*     eapply S3PMCcons. *)
    (*     intuition congruence. assumption. *)
    (*     simpl. f_equal. *)
    (*     rewrite !M.subtractKV_empty_1, !M.subtractKV_empty_2. *)
    (*     congruence. *)
    (*     unfold hide; simpl; rewrite !M.subtractKV_empty_1, !M.subtractKV_empty_2. *)
    (*     unfold getRqCall at 1 3; simpl. assumption. *)
    (*     simpl. f_equal. assumption. *)
    (*   + apply step_rule_annot_2 in H. *)
    (*     eexists (_ :: x). split. *)
    (*     econstructor. eassumption. eassumption. *)
    (*     intuition idtac. *)
    (*     eapply S3PMCcons. *)
    (*     intuition congruence. assumption. *)
    (*     simpl. f_equal. *)
    (*     rewrite !M.subtractKV_empty_1, !M.subtractKV_empty_2. *)
    (*     f_equal. simpl in H4.  *)
    (*     inv_label.  *)
    (*     rewrite !M.subtractKV_empty_2 in H6. *)
    (*     congruence. *)
    (*     unfold hide; simpl; rewrite !M.subtractKV_empty_1, !M.subtractKV_empty_2. *)
    (*     unfold getRqCall at 1 3; simpl. assumption. *)
    (*     simpl. f_equal. assumption. *)
    (*   + eexists (_ :: x). split. *)
    (*     econstructor. eassumption. eassumption. *)
    (*     intuition idtac. *)
    (*     eapply S3PMCcons. *)
    (*     intuition congruence. assumption. *)
    (*     simpl. f_equal. *)
    (*     rewrite !M.subtractKV_empty_1, !M.subtractKV_empty_2. *)
    (*     simpl in H4.  *)
    (*     inv_label.  *)
    (*     congruence. *)
    (*     unfold hide; simpl; rewrite !M.subtractKV_empty_1, !M.subtractKV_empty_2. *)
    (*     unfold getRqCall at 1 3; simpl. assumption. *)
    (*     simpl. f_equal. assumption. *)
    (*   + kinv_action_dest. simpl. *)
    (*     zr_noop. *)
    (*     split. *)
    (*     econstructor. *)
    (*     eassumption. eassumption. *)
    (*     intuition idtac. *)
    (*     eapply S3PMCcons. *)
    (*     intuition congruence. assumption. *)
    (*     simpl. f_equal. *)
    (*     simpl in H4.  *)
    (*     inv_label.  *)
    (*     congruence. *)
    (*     unfold hide; simpl. *)
    (*     unfold getRqCall at 1 3; simpl. *)
    (*     rewrite !M.subtractKV_find. *)
    (*     findReify. simpl. *)
    (*     (*M.find_add_tac.*) assumption.  *)
    (*     simpl. f_equal. assumption. *)
    (*   + kinv_action_dest. simpl. *)
    (*     zr_noop. *)
    (*     split. *)
    (*     econstructor. *)
    (*     eassumption. eassumption. *)
    (*     intuition idtac. *)
    (*     eapply S3PMCcons. *)
    (*     intuition congruence. assumption. *)
    (*     simpl. f_equal. *)
    (*     simpl in H4.  *)
    (*     inv_label.  *)
    (*     congruence. *)
    (*     unfold hide; simpl. *)
    (*     unfold getRqCall at 1 3; simpl. *)
    (*     rewrite !M.subtractKV_find. *)
    (*     findReify. simpl. *)
    (*     (*M.find_add_tac.*)  *)
    (*     assumption. *)
    (*     simpl. f_equal. assumption. *)
    (*   + kinv_action_dest. simpl. *)
    (*     zr_noop. *)
    (*     split. *)
    (*     econstructor. *)
    (*     eassumption. eassumption. *)
    (*     intuition idtac. *)
    (*     eapply S3PMCcons. *)
    (*     intuition congruence. assumption. *)
    (*     simpl. f_equal. *)
    (*     simpl in H4.  *)
    (*     inv_label.  *)
    (*     congruence. *)
    (*     unfold hide; simpl. *)
    (*     unfold getRqCall at 1 3; simpl. *)
    (*     rewrite !M.subtractKV_find. *)
    (*     findReify. simpl. *)
    (*     (*M.find_add_tac.*) assumption. *)
    (*     simpl. f_equal. assumption. *)
    (*   + kinv_action_dest. simpl. *)
    (*     zr_noop. *)
    (*     split. *)
    (*     econstructor. *)
    (*     eassumption. eassumption. *)
    (*     intuition idtac. *)
    (*     eapply S3PMCcons. *)
    (*     intuition congruence. assumption. *)
    (*     simpl. f_equal. *)
    (*     simpl in H4.  *)
    (*     inv_label.  *)
    (*     congruence. *)
    (*     unfold hide; simpl. *)
    (*     unfold getRqCall at 1 3; simpl. *)
    (*     rewrite !M.subtractKV_find. *)
    (*     findReify. simpl. *)
    (*     (*M.find_add_tac.*) *)
    (*     assumption. *)
    (*     simpl. f_equal. assumption. *)
    (*   + kinv_action_dest. simpl. *)
    (*     zr_noop. *)
    (*     split. *)
    (*     econstructor. *)
    (*     eassumption. eassumption. *)
    (*     intuition idtac. *)
    (*     eapply S3PMCcons. *)
    (*     intuition congruence. assumption. *)
    (*     simpl. f_equal. *)
    (*     simpl in H4.  *)
    (*     inv_label.  *)
    (*     congruence. *)
    (*     unfold hide; simpl. *)
    (*     unfold getRqCall at 1 3; simpl. *)
    (*     rewrite !M.subtractKV_find. *)
    (*     findReify. simpl. *)
    (*     (*M.find_add_tac.*)  *)
    (*     assumption. *)
    (*     simpl. f_equal. assumption. *)
        
    (*   + kinv_action_dest. simpl. *)
    (*     zr_noop. *)
    (*     split. *)
    (*     econstructor. *)
    (*     eassumption. eassumption. *)
    (*     intuition idtac. *)
    (*     eapply S3PMCcons. *)
    (*     intuition congruence. assumption. *)
    (*     simpl. f_equal. *)
    (*     simpl in H4.  *)
    (*     inv_label.  *)
    (*     congruence. *)
    (*     unfold hide; simpl. *)
    (*     unfold getRqCall at 1 3; simpl. *)
    (*     rewrite !M.subtractKV_find. *)
    (*     findReify. simpl. *)
    (*     (*M.find_add_tac.*)  *)
    (*     assumption. *)
    (*     simpl. f_equal. assumption. *)
    (*   + kinv_action_dest. simpl. *)
    (*     zr_noop. *)
    (*     split. *)
    (*     econstructor. *)
    (*     eassumption. eassumption. *)
    (*     intuition idtac. *)
    (*     eapply S3PMCcons. *)
    (*     intuition congruence. assumption. *)
    (*     simpl. f_equal. *)
    (*     simpl in H4.  *)
    (*     inv_label.  *)
    (*     congruence. *)
    (*     unfold hide; simpl. *)
    (*     unfold getRqCall at 1 3; simpl. *)
    (*     rewrite !M.subtractKV_find. *)
    (*     findReify. simpl. *)
    (*     (*M.find_add_tac.*)  *)
    (*     assumption. *)
    (*     simpl. f_equal. assumption. *)
    (*   + kinv_action_dest. simpl. *)
    (*     zr_noop. *)
    (*     split. *)
    (*     econstructor. *)
    (*     eassumption. eassumption. *)
    (*     intuition idtac. *)
    (*     eapply S3PMCcons. *)
    (*     intuition congruence. assumption. *)
    (*     simpl. f_equal. *)
    (*     simpl in H4.  *)
    (*     inv_label.  *)
    (*     congruence. *)
    (*     unfold hide; simpl. *)
    (*     unfold getRqCall at 1 3; simpl. *)
    (*     rewrite !M.subtractKV_find. *)
    (*     findReify. simpl. *)
    (*     (*M.find_add_tac.*)  *)
    (*     assumption. *)
    (*     simpl. f_equal. assumption. *)
    (*   + kinv_action_dest. *)
    (*     * simpl.  *)
    (*       zr_noop. *)
    (*       split. *)
    (*       econstructor. *)
    (*       eassumption. eassumption. *)
    (*       intuition idtac. *)
    (*       eapply S3PMCcons. *)
    (*       intuition congruence. assumption. *)
    (*       simpl. f_equal. *)
    (*       simpl in H4.   *)
    (*       inv_label. *)
    (*       unfold e2wFifoName in *. *)
    (*       congruence. *)
    (*       unfold hide; simpl. *)
    (*       unfold getRqCall at 1 3; simpl. *)
    (*       rewrite !M.subtractKV_find. *)
    (*       findReify. simpl. *)
    (*       (*M.find_add_tac.*)  *)
    (*       assumption. *)
    (*       simpl. f_equal. assumption. *)
    (*     * simpl.  *)
    (*       zr_noop. *)
    (*       split. *)
    (*       econstructor. *)
    (*       eassumption. eassumption. *)
    (*       intuition idtac. *)
    (*       eapply S3PMCcons. *)
    (*       intuition congruence. assumption. *)
    (*       simpl. f_equal. *)
    (*       simpl in H4.   *)
    (*       inv_label. *)
    (*       unfold e2wFifoName in *. *)
    (*       congruence. *)
    (*       unfold hide; simpl. *)
    (*       unfold getRqCall at 1 3; simpl. *)
    (*       rewrite !M.subtractKV_find. *)
    (*       findReify. simpl. *)
    (*       (*M.find_add_tac.*)  *)
    (*       assumption. *)
    (*       simpl. f_equal. assumption. *)
    (*     * simpl.  *)
    (*       zr_noop. *)
    (*       split. *)
    (*       econstructor. *)
    (*       eassumption. eassumption. *)
    (*       intuition idtac. *)
    (*       eapply S3PMCcons. *)
    (*       intuition congruence. assumption. *)
    (*       simpl. f_equal. *)
    (*       simpl in H4.   *)
    (*       inv_label. *)
    (*       unfold e2wFifoName in *. *)
    (*       congruence. *)
    (*       unfold hide; simpl. *)
    (*       unfold getRqCall at 1 3; simpl. *)
    (*       rewrite !M.subtractKV_find. *)
    (*       findReify. simpl. *)
    (*       (*M.find_add_tac.*)  *)
    (*       assumption. *)
    (*       simpl. f_equal. assumption. *)
    (*     * simpl.  *)
    (*       zr_noop. *)
    (*       split. *)
    (*       econstructor. *)
    (*       eassumption. eassumption. *)
    (*       intuition idtac. *)
    (*       eapply S3PMCcons. *)
    (*       intuition congruence. assumption. *)
    (*       simpl. f_equal. *)
    (*       simpl in H4.   *)
    (*       inv_label. *)
    (*       unfold e2wFifoName in *. *)
    (*       congruence. *)
    (*       unfold hide; simpl. *)
    (*       unfold getRqCall at 1 3; simpl. *)
    (*       rewrite !M.subtractKV_find. *)
    (*       findReify. simpl. *)
    (*       (*M.find_add_tac.*)  *)
    (*       assumption. *)
    (*       simpl. f_equal. assumption. *)
    (*   + (* reqLd *)  admit. *)
    (*   + (* reqLdZ *) admit. *)
    (*   + (* reqSt *) admit. *)
    (*   + (* repLd *) admit. *)
    (*   + (* repSt *) admit. *)
    (*   + (* execToHost *) admit. *)
    (*   + (* execFromHost *) admit. *)
    (*   + (* execFromHostZ *) admit. *)
    (*   + (* wbNm *) admit. *)
    (*   + (* wbNmZ *) admit. *)
    all: admit.
  Admitted.

  Transparent evalExpr.
  
        
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
  

  Lemma eval_const : forall n (t : Expr type (SyntaxKind (Bit n))) c, evalExpr t = c -> evalExpr (t == (Const _ (ConstBit c)))%kami_expr = true.
    simpl.
    intros.
    rewrite H.
    destruct (weq c c); tauto.
  Qed.


    Ltac emp_disj :=
    try apply M.Disj_empty_1; try apply M.Disj_empty_2
  .

  Lemma not_None_Some : forall {A} (x : option A), x <> None -> exists y, x = Some y.
  Proof.
    intros.
    destruct x.
    eauto. congruence.
  Qed.


  Lemma ForwardMultistep_trans : forall modules r1 r2 r3 l12 l23,
      ForwardMultistep modules r1 r2 l12 -> ForwardMultistep modules r2 r3 l23 ->
      ForwardMultistep modules r1 r3 (l12 ++ l23).
  Proof.
    intros. apply FMulti_Multi in H. apply FMulti_Multi in H0.
    pose proof (multistep_app_inv H H0).
    apply Multi_FMulti in H1. rewrite rev_app_distr in H1.
    rewrite !rev_involutive in H1.
    assumption.
  Qed.

  Theorem validRegs_p : Wf.ValidRegsModules type p.
  Proof.
    kvr.
  Qed.

  Definition regType (x : RegInitValue) : FullKind :=
    match x with
    | RegInitCustom (existT _ a _) => a
    | RegInitDefault a => a
    end.

  Section ExtraValidRegs. (* Follows very closely Wf.ValidRegs , but with additional condition that when the registers are accessed they're *)
                          (* the correct type. *)
  Variable type: Kind -> Type.

  Section GivenRegs.
    Variable regs: list RegInitT.

    Inductive ExtraValidRegsAction:
      forall {retT}, ActionT type retT -> Prop :=
    | VRMCall:
        forall name sig ar {retT} cont,
          (forall t, ExtraValidRegsAction (cont t)) ->
          ExtraValidRegsAction (MCall (lretT:= retT) name sig ar cont)
    | VRLet:
        forall {argT retT} ar cont,
          (forall t, ExtraValidRegsAction (cont t)) ->
          ExtraValidRegsAction (Let_ (lretT':= argT) (lretT:= retT) ar cont)
    | VRReadNondet:
        forall {retT} k cont,
          (forall t, ExtraValidRegsAction (cont t)) ->
          ExtraValidRegsAction (ReadNondet (lretT:= retT) k cont)
    | VRReadReg:
        forall {retT} reg k cont a,
          In reg regs ->
          (forall t, ExtraValidRegsAction (cont t)) ->
          a = attrName reg -> 
          ExtraValidRegsAction (ReadReg (lretT:= retT) a k cont)
    | VRWriteReg:
        forall {writeT retT} reg e cont a,
          In reg regs ->
          ExtraValidRegsAction cont ->
          a = (attrName reg) ->
          writeT = (regType (attrType reg)) -> 
          ExtraValidRegsAction (WriteReg (k:= writeT) (lretT:= retT)
                                    a e cont)
    | VRIfElse:
        forall {retT1 retT2} ce (ta fa: ActionT type retT1)
               (cont: type retT1 -> ActionT type retT2),
          ExtraValidRegsAction ta ->
          ExtraValidRegsAction fa ->
          (forall t, ExtraValidRegsAction (cont t)) ->
          ExtraValidRegsAction (IfElse ce ta fa cont)
    | VRAssert:
        forall {retT} e cont,
          ExtraValidRegsAction cont ->
          ExtraValidRegsAction (Assert_ (lretT:= retT) e cont)
    | VRReturn:
        forall {retT} (e: Expr type (SyntaxKind retT)),
          ExtraValidRegsAction (Return e).

    Inductive ExtraValidRegsRules: list (Attribute (Action Void)) -> Prop :=
    | ExtraValidRegsRulesNil: ExtraValidRegsRules nil
    | ExtraValidRegsRulesCons:
        forall rule rules,
          ExtraValidRegsRules rules ->
          ExtraValidRegsAction ((attrType rule) type) ->
          ExtraValidRegsRules (rule :: rules).

    Lemma ExtraValidRegsRules_app:
      forall r1 r2,
        ExtraValidRegsRules r1 -> ExtraValidRegsRules r2 ->
        ExtraValidRegsRules (r1 ++ r2).
    Proof.
      induction r1; simpl; intros; auto.
      inv H; constructor; auto.
    Qed.

    Inductive ExtraValidRegsDms: list DefMethT -> Prop :=
    | ExtraValidRegsDmsNil: ExtraValidRegsDms nil
    | ExtraValidRegsDmsCons:
        forall (dm: DefMethT) dms,
          ExtraValidRegsDms dms ->
          (forall argV,
              ExtraValidRegsAction (projT2 (attrType dm) type argV)) ->
          ExtraValidRegsDms (dm :: dms).

    Lemma ExtraValidRegsDms_app:
      forall dms1 dms2,
        ExtraValidRegsDms dms1 -> ExtraValidRegsDms dms2 ->
        ExtraValidRegsDms (dms1 ++ dms2).
    Proof.
      induction dms1; simpl; intros; auto.
      inv H; constructor; auto.
    Qed.

  End GivenRegs.

  Fixpoint ExtraValidRegsModules (m: Modules): Prop :=
    match m with
      | RegFile dataArray read write IdxBits  =>
        ExtraValidRegsRules (getRegInits m) (getRules m) /\
        ExtraValidRegsDms (getRegInits m) (getDefsBodies m)
    | Mod regs rules dms =>
      ExtraValidRegsRules regs rules /\
      ExtraValidRegsDms regs dms
    | ConcatMod ma mb =>
      ExtraValidRegsModules ma /\ ExtraValidRegsModules mb
    end.

  Lemma ExtraValidRegsRules_rule:
    forall regs rules,
      ExtraValidRegsRules regs rules ->
      forall rn rb,
        In (rn :: rb)%struct rules ->
        ExtraValidRegsAction regs (rb type).
  Proof.
    induction 1; simpl; intros; [inv H|].
    inv H1; eauto.
  Qed.

  
  Lemma ExtraValidRegsRules_weakening:
    forall regs rules,
      ExtraValidRegsRules regs rules ->
      forall rules',
        SubList rules' rules ->
        ExtraValidRegsRules regs rules'.
  Proof.
    induction rules'; simpl; intros; [constructor|].
    constructor.
    - apply IHrules'.
      apply SubList_cons_inv in H0; dest; auto.
    - eapply ExtraValidRegsRules_rule with (rn:= attrName a); eauto using H.
      apply H0; left; destruct a; auto.
  Qed.

  Lemma ExtraValidRegsAction_regs_weakening:
    forall {retT} (a: ActionT type retT) regs,
      ExtraValidRegsAction regs a ->
      forall regs',
        SubList regs regs' ->
        ExtraValidRegsAction regs' a.
  Proof.
    induction 1; simpl; intros; try (econstructor; eauto).
  Qed.

  
  Lemma ExtraValidRegsRules_regs_weakening:
    forall regs rules,
      ExtraValidRegsRules regs rules ->
      forall regs',
        SubList regs regs' ->
        ExtraValidRegsRules regs' rules.
  Proof.
    induction 1; simpl; intros; [constructor|].
    constructor; auto.
    eapply ExtraValidRegsAction_regs_weakening; eauto.
  Qed.

  
  Lemma ExtraValidRegsDms_regs_weakening:
    forall regs dms,
      ExtraValidRegsDms regs dms ->
      forall regs',
        SubList regs regs' ->
        ExtraValidRegsDms regs' dms.
  Proof.
    induction 1; simpl; intros; [constructor|].
    constructor; auto.
    intros; eapply ExtraValidRegsAction_regs_weakening; eauto.
  Qed.

  Lemma ExtraValidRegsModules_flatten:
    forall m,
      ExtraValidRegsModules m ->
      ExtraValidRegsModules (Syntax.Mod (getRegInits m) (getRules m) (getDefsBodies m)).
  Proof.
    intro m.
    induction m; simpl; intros; auto.
    dest; specialize (IHm1 H); specialize (IHm2 H0).
    inv IHm1; inv IHm2.
    split.
    - apply ExtraValidRegsRules_app.
      + eapply ExtraValidRegsRules_regs_weakening; eauto. 
        apply SubList_app_1, SubList_refl.
      + eapply ExtraValidRegsRules_regs_weakening; eauto.
        apply SubList_app_2, SubList_refl.
    - apply ExtraValidRegsDms_app.
      + eapply ExtraValidRegsDms_regs_weakening; eauto.
        apply SubList_app_1, SubList_refl.
      + eapply ExtraValidRegsDms_regs_weakening; eauto.
        apply SubList_app_2, SubList_refl.
  Qed.

End ExtraValidRegs.

  
  Theorem ExtraValidRegs_p : ExtraValidRegsModules type p.
  Proof.  (* essentially imitation by hand of the kvr tactic *)
    repeat match goal with [ |- ExtraValidRegsModules _ ?mm ] => unfold_head mm end.
    constructor. constructor.
    all: repeat match goal with [ |- ExtraValidRegsRules _ _ _ ] => constructor end.
    all: repeat match goal with [ |- ExtraValidRegsAction _ _ _ ] =>
                                econstructor; intros;
                                  try match goal with [ |- ?s = attrName _ ] => instantiate (1 := (s :: _)%struct); reflexivity end
                end.
    all: try match goal with [ |- In _ _ ] => simpl; intuition reflexivity end.
    all: try reflexivity.
    repeat match goal with [ |- ExtraValidRegsDms _ _ _ ] => constructor end.
    simpl; repeat split. 
    all: repeat match goal with [ |- ExtraValidRegsRules _ _ _ ] => constructor end.
    all: repeat match goal with [ |- ExtraValidRegsDms _ _ _ ] => constructor end.
    
    all: intros; repeat match goal with [ |- ExtraValidRegsAction _ _ _ ] =>
                                econstructor; intros;
                                  try match goal with [ |- ?s = attrName _ ] => instantiate (1 := (s :: _)%struct); reflexivity end
                        end.
    all: try (simpl; intuition reflexivity).
  Qed.

  Lemma registers_correct_types : forall regs rules dms r t val,
      NoDup (map (attrName (A:=RegInitValue)) regs) -> 
      let modules := Mod regs rules dms in
      ((In (r :: (RegInitDefault t))%struct (getRegInits modules)) \/
       (In (r :: (RegInitCustom (existT _ t val)))%struct (getRegInits modules))) ->
      ExtraValidRegsModules type modules ->
      (forall o u l, Step modules o u l ->
               u @[ r ] <> None ->
               exists val', u @[ r ] = Some (existT _ t val'))%fmap.
  Proof.
    cbv zeta.
    intros regs rules dms r t val ND Hin Hwf.
    simpl in Hwf.
    intros o u l s; rewrite step_consistent in s. shatter.
    assert (Forall (fun rule => ExtraValidRegsAction _ regs (attrType rule type)) rules) as EachRule by 
        (clear - H; induction H; auto).
    assert (Forall (fun (meth : DefMethT) => (forall argV, ExtraValidRegsAction _ regs ((projT2 (attrType meth)) type argV)))
                   (getDefsBodies (Mod regs rules dms))) as EachMeth
      by (clear - H0; induction H0; simpl; auto).     
    destruct s. 
    clear HWellHidden.
    induction HSubSteps;
      intros. mred.
    subst. rewrite M.find_union in *.
    destruct H1.
    - remember (u @[ r ])%fmap as r'.
      destruct r'; try mred.
      apply IHHSubSteps; try assumption.
    - remember (u @[ r ])%fmap as r'.
      destruct r'; try mred.
      apply IHHSubSteps; try assumption.
    - remember (u @[ r ])%fmap as r'.
      destruct r'.
      + apply IHHSubSteps; try assumption. 
      + simpl in HInRules.
        rewrite Forall_forall in EachRule; specialize (EachRule _ HInRules).
        simpl in Hin.
        clear - ND Hin HAction EachRule H5.
        generalize dependent a. simpl. 
        assert (
             forall t' (a : Action t') retV,
               SemAction o (a type) u0 cs retV ->
               ExtraValidRegsAction _ regs (a type) -> exists val' : fullType type t, (val' === u0 .[ r])%fmap).
        induction 1; intros.
        all: try (inversion H0; repeat match goal with [ H : _ |- _ ] => apply Eqdep.EqdepTheory.inj_pair2 in H end; subst;
                  apply IHSemAction; [ assumption | shelve | match goal with [ H : forall _, ExtraValidRegsAction _ _ _ |- _ ] => apply H end ]).
        * inversion H0; repeat match goal with [ H : _ |- _ ] => apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
          pose proof (String.string_dec r (attrName reg)) as [|]; subst.  mred.
          assert (t = (regType (attrType reg))). clear - ND Hin H7.
          (* need some form of 'no duplicates', which I think exists *)
          destruct Hin. 
          -- assert (reg = (attrName reg :: RegInitDefault t)%struct).
             eapply in_NoDup_attr. eassumption. 2: eassumption. 2: eapply H. simpl; congruence.
          rewrite H0. simpl; reflexivity.
          -- assert (reg = (attrName reg :: RegInitCustom (existT ConstFullT t val))%struct).
             eapply in_NoDup_attr. eassumption. 2: eassumption. 2: eapply H. simpl; congruence.
          rewrite H0. simpl; reflexivity.
          
          -- subst; simpl. eexists; eauto.
          -- rewrite M.find_add_2 in * by assumption.
          apply IHSemAction; eassumption.
        * inversion H1; repeat match goal with [ H : _ |- _ ] => apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
          rewrite FMap.M.find_union in *.
          destruct (newRegs1 @[ r ])%fmap.
          -- eapply IHSemAction1; eauto. shelve.
          -- eapply IHSemAction2; eauto.
        * inversion H1; repeat match goal with [ H : _ |- _ ] => apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
          rewrite FMap.M.find_union in *.
          destruct (newRegs1 @[ r ])%fmap.
          -- eapply IHSemAction1; eauto. shelve.
          -- eapply IHSemAction2; eauto.
        * inversion H0; repeat match goal with [ H : _ |- _ ] => apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
          eapply IHSemAction; eauto.
        * inversion H0; repeat match goal with [ H : _ |- _ ] => apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
        * exfalso. rewrite FMap.M.find_empty in H5. congruence.
        * intros a HAction H1. specialize (H Void a WO HAction H1). assumption.
    - remember (u @[ r ])%fmap as r'.
      destruct r'.
      + apply IHHSubSteps; auto.
      + clear IHHSubSteps.
        rewrite Forall_forall in EachMeth; specialize (EachMeth _ HIn argV).
        destruct f; simpl in *.
        destruct attrType; simpl in *.  subst.
        clear - ND Hin HAction EachMeth H5. 
        generalize dependent m0.
        assert (
             forall t' (a : ActionT type t') (retV : type t'),
               SemAction o a u0 cs retV ->
               ExtraValidRegsAction _ regs a -> exists val' : fullType type t, (val' === u0 .[ r])%fmap).
        induction 1; intros.
        all: try (inversion H0; repeat match goal with [ H : _ |- _ ] => apply Eqdep.EqdepTheory.inj_pair2 in H end; subst;
                  apply IHSemAction;  [ assumption | match goal with [ H : forall _, ExtraValidRegsAction _ _ _ |- _ ] => apply H end ]).
        * inversion H0; repeat match goal with [ H : _ |- _ ] => apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
          pose proof (String.string_dec r (attrName reg)) as [|]; subst.  mred.
          assert (t = (regType (attrType reg))). clear - ND Hin H7.
          destruct Hin. 
          -- assert (reg = (attrName reg :: RegInitDefault t)%struct).
             eapply in_NoDup_attr. eassumption. 2: eassumption. 2: eapply H. simpl; congruence.
          rewrite H0. simpl; reflexivity.
          -- assert (reg = (attrName reg :: RegInitCustom (existT ConstFullT t val))%struct).
             eapply in_NoDup_attr. eassumption. 2: eassumption. 2: eapply H. simpl; congruence.
          rewrite H0. simpl; reflexivity.

          -- subst; simpl. eexists; eauto.
          -- rewrite M.find_add_2 in * by assumption.
          apply IHSemAction; eassumption.
        * inversion H1; repeat match goal with [ H : _ |- _ ] => apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
          rewrite FMap.M.find_union in *.
          destruct (newRegs1 @[ r ])%fmap.
          -- eapply IHSemAction1; eauto. 
          -- eapply IHSemAction2; eauto.
        * inversion H1; repeat match goal with [ H : _ |- _ ] => apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
          rewrite FMap.M.find_union in *.
          destruct (newRegs1 @[ r ])%fmap.
          -- eapply IHSemAction1; eauto. 
          -- eapply IHSemAction2; eauto.
        * inversion H0; repeat match goal with [ H : _ |- _ ] => apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
          eapply IHSemAction; eauto.
        * inversion H0; repeat match goal with [ H : _ |- _ ] => apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.
        * exfalso. rewrite FMap.M.find_empty in H5. congruence.
        * intros m0 HAction H1.
          eapply H; eassumption.
          Unshelve.
          all: try intro.
          all: eauto.
          all: eapply ReadReg. all: try exact "w".
          all: intro. all: apply Return. all: apply Var. all: eassumption.
  Qed.

  Lemma p_init_NoDup : NoDup (map (attrName (A:=RegInitValue)) (getRegInits p)).
  Proof. knodup_regs. Qed.

  (* This lemma is supposed to make synthesis of multisteps easier by showing that after a step is taken, the state of the registers is still *)
  (* describable as some ThreeStageAllRegs. It is almost proven, but there are some difficult things relating to evar contexts. *)
  (* Basically, you want to eexists all, then pose registers_correct_types for any that were touched in this step, but then you can't instantiate *)
  (* with the value you got form registers_correct_types. *)
  Lemma all_registers_inclusive : forall u l rf pm pc fEpoch sbF d2e_elt d2e_full w2d_elt w2d_full eEpoch e2w_elt e2w_full stall stalled,
      Step p (ThreeStageAllRegs rf pm pc fEpoch sbF d2e_elt d2e_full w2d_elt w2d_full eEpoch e2w_elt e2w_full stall stalled)
           u l ->
      exists rf' pm' pc' fEpoch' sbF' d2e_elt' d2e_full' w2d_elt' w2d_full' eEpoch' e2w_elt' e2w_full' stall' stalled', 
        (FMap.M.union u (ThreeStageAllRegs rf pm pc fEpoch sbF d2e_elt d2e_full w2d_elt w2d_full eEpoch e2w_elt e2w_full stall stalled)) =
        (ThreeStageAllRegs rf' pm' pc' fEpoch' sbF' d2e_elt' d2e_full' w2d_elt' w2d_full' eEpoch' e2w_elt' e2w_full' stall' stalled').
  Proof.
    intros.
    eassert _ by (eapply Wf.validRegsModules_step_newregs_subset; try eapply validRegs_p; try eassumption).
    simpl in X.
    eassert (forall y t val, (u) @[ y]%fmap <> None -> (In (y :: RegInitDefault t)%struct (getRegInits (Mod (getRegInits p) (getRules p) (getDefsBodies p))) \/
                       In (y :: RegInitCustom (existT ConstFullT t val))%struct (getRegInits (Mod (getRegInits p) (getRules p) (getDefsBodies p)))) -> _).
    intros. eapply registers_correct_types. 
    eapply p_init_NoDup.
    eassumption.
    apply ExtraValidRegsModules_flatten, ExtraValidRegs_p.
    eapply flatten_preserves_step; eassumption. eassumption.

    (* eassert (u @[ "pc" ] <> None -> _)%fmap.  *)
    (* intro; eapply (X0 "pc"). assumption. *)
    (* right; simpl; intuition reflexivity. *)

    (* eassert (u @[ "pgm" ] <> None -> _)%fmap.  *)
    (* intro; eapply (X0 "pgm"). assumption. *)
    (* right; simpl; intuition reflexivity. *)
    (* eassert (u @[ "fEpoch" ] <> None -> _)%fmap.  *)
    (* intro; eapply (X0 "fEpoch"). assumption. *)
    (* right; simpl; intuition reflexivity. *)
    (* eassert (u @[ "rf" ] <> None -> _)%fmap.  *)
    (* intro; eapply (X0 "rf"). assumption. *)
    (* right; simpl; intuition reflexivity. *)
    (* eassert (u @[ "sbFlags" ] <> None -> _)%fmap.  *)
    (* intro; eapply (X0 "sbFlags"). assumption. *)
    (* left; simpl; repeat (try (left; reflexivity); right).  *)
    (* eassert (u @[ "d2e" -- "elt" ] <> None -> _)%fmap.  *)
    (* intro; eapply (X0 "d2e" -- "elt"). assumption. *)
    (* left; simpl; repeat (try (left; reflexivity); right). *)
    (* eassert (u @[ "d2e" -- "full" ] <> None -> _)%fmap.  *)
    (* intro; eapply (X0 "d2e" -- "full"). assumption. *)
    (* left; simpl; repeat (try (left; reflexivity); right). *)
    (* eassert (u @[ "w2d" -- "elt" ] <> None -> _)%fmap.  *)
    (* intro; eapply (X0 "w2d" -- "elt"). assumption. *)
    (* left; simpl; repeat (try (left; reflexivity); right). *)
    (* eassert (u @[ "w2d" -- "full" ] <> None -> _)%fmap.  *)
    (* intro; eapply (X0 "w2d" -- "full"). assumption. *)
    (* left; simpl; repeat (try (left; reflexivity); right). *)
    (* eassert (u @[ "stall" ] <> None -> _)%fmap.  *)
    (* intro; eapply (X0 "stall"). assumption. *)
    (* right; simpl; repeat (try (left; reflexivity); right). *)
    (* eassert (u @[ "stalled" ] <> None -> _)%fmap.  *)
    (* intro; eapply (X0 "stalled"). assumption. *)
    (* left; simpl; repeat (try (left; reflexivity); right). *)
    (* clear X0. *)
       
    (* repeat eexists. unfold ThreeStageAllRegs. *)
    (* apply M.leibniz; intro. *)
    (* specialize (X y). *)
    (* remember (u @[ y ])%fmap as y'. *)
    
    (* instantiate (1 := match (u @[ "pc" ])%fmap with | Some w => _ | None => _ end). *)
    (* instantiate (3 := match (u @[ "pgm" ])%fmap with | Some w => _ | None => _ end). *)
    (* instantiate (5 := match (u @[ "rf" ])%fmap with | Some w => _ | None => _ end). *)
    (* instantiate (7 := match (u @[ "fEpoch" ])%fmap with | Some w => _ | None => _ end). *)
    (* instantiate (9 := match (u @[ "sbFlags" ])%fmap with | Some w => _ | None => _ end). *)
    (* instantiate (11 := match (u @[ "d2e"--"elt" ])%fmap with | Some w => _ | None => _ end). *)
    (* instantiate (13 := match (u @[ "d2e"--"full" ])%fmap with | Some w => _ | None => _ end). *)
    (* instantiate (15 := match (u @[ "w2d"--"elt" ])%fmap with | Some w => _ | None => _ end). *)
    (* instantiate (17 := match (u @[ "w2d"--"full" ])%fmap with | Some w => _ | None => _ end). *)
    (* instantiate (19 := match (u @[ "eEpoch" ])%fmap with | Some w => _ | None => _ end). *)
    (* instantiate (21 := match (u @[ "e2w"--"elt" ])%fmap with | Some w => _ | None => _ end). *)
    (* instantiate (23 := match (u @[ "e2w"--"full" ])%fmap with | Some w => _ | None => _ end). *)
    (* instantiate (25 := match (u @[ "stall" ])%fmap with | Some w => _ | None => _ end). *)
    (* instantiate (27 := match (u @[ "stalled" ])%fmap with | Some w => _ | None => _ end). *)
    (* destruct y'. *)
    (* - eassert _ by (eapply X; rewrite M.F.P.F.in_find_iff; intuition congruence). *)
    (*   simpl in X12. intuition subst. *)
    (*   rewrite M.find_union. M.find_add_tac. *)
    (*   rewrite <- !Heqy'. *)
    (*   dest. rewrite H0 in Heqy'. rewrite Heqy'. reflexivity.  *)
    
    (* rewrite step_consistent in H. *)
    (* destruct H. *)
    (* generalize HWellHidden; clear HWellHidden. *)
    (* induction HSubSteps; intros. *)
    (* - rewrite M.union_empty_L. repeat eexists; eauto. *)
    (* - subst. *)
    (*   destruct H. *)
    (*   + rewrite M.union_empty_R. apply IHHSubSteps. *)
    (*     destruct l. unfold wellHidden, hide in HWellHidden. simpl in HWellHidden. *)
    (*     rewrite !M.union_empty_L in HWellHidden. *)
    (*     unfold wellHidden, hide. simpl. assumption. *)
    (*   + rewrite M.union_empty_R. apply IHHSubSteps. *)
    (*     destruct l. unfold wellHidden, hide in HWellHidden. simpl in HWellHidden. *)
    (*     rewrite !M.union_empty_L in HWellHidden. *)
    (*     unfold wellHidden, hide. simpl. assumption. *)
    (*   + simpl in HInRules. *)
    (*     intuition; match goal with [ H : ((?a :: ?b) = (?a' :: ?b'))%struct |- _ ] => *)
    (*                                assert (a = a' /\ b = b') by (split; congruence) end; *)
    (*     shatter; subst. *)
    (*     Ltac t := match goal with [ H : SemAction _ _ _ _ _ |- _ ] => *)
    (*                               let H' := fresh in  *)
    (*                               pose proof (inversionSemAction H) as H'; simpl in H'; clear H; *)
    (*                               shatter; subst *)
    (*               end. *)
    (*     t. t. t. t. t. *)
    (*     rewrite <- M.union_assoc. *)
    admit.
  Admitted.

  Lemma invariant_compose : forall rf0 pm0 pc0 fEpoch0 sbF0 d2e_elt0 d2e_full0 w2d_elt0 w2d_full0 eEpoch0 e2w_elt0 e2w_full0 stall0 stalled0 stall_data0 e2w_data0 d2e_data0
                              rf1 pm1 pc1 fEpoch1 sbF1 d2e_elt1 d2e_full1 w2d_elt1 w2d_full1 eEpoch1 e2w_elt1 e2w_full1 stall1 stalled1 stall_data1 e2w_data1 d2e_data1
                              rf2 pm2 pc2 fEpoch2 sbF2 d2e_elt2 d2e_full2 w2d_elt2 w2d_full2 eEpoch2 e2w_elt2 e2w_full2 stall2 stalled2 
    ls0 ls1 rs0 rs1 lastRq0 lastRq1 mem,
    ForwardMultistep p (ThreeStageAllRegs rf0 pm0 pc0 fEpoch0 sbF0 d2e_elt0 d2e_full0 w2d_elt0 w2d_full0 eEpoch0 e2w_elt0 e2w_full0 stall0 stalled0)                       (ThreeStageAllRegs rf1 pm1 pc1 fEpoch1 sbF1 d2e_elt1 d2e_full1 w2d_elt1 w2d_full1 eEpoch1 e2w_elt1 e2w_full1 stall1 stalled1) ls0 -> 
        ThreeStageProcMemConsistent ls0 lastRq0 mem -> 
        relatedTrace ls0 d2e_data0 e2w_data0 stall_data0 rs0 ->
ForwardMultistep p (ThreeStageAllRegs rf1 pm1 pc1 fEpoch1 sbF1 d2e_elt1 d2e_full1 w2d_elt1 w2d_full1 eEpoch1 e2w_elt1 e2w_full1 stall1 stalled1)                       (ThreeStageAllRegs rf2 pm2 pc2 fEpoch2 sbF2 d2e_elt2 d2e_full2 w2d_elt2 w2d_full2 eEpoch2 e2w_elt2 e2w_full2 stall2 stalled2) ls1 -> 
        ThreeStageProcMemConsistent ls1 lastRq1 mem -> 
        relatedTrace ls1 d2e_data1 e2w_data1 stall_data1 rs1 ->
        ForwardMultistep p (ThreeStageAllRegs rf0 pm0 pc0 fEpoch0 sbF0 d2e_elt0 d2e_full0 w2d_elt0 w2d_full0 eEpoch0 e2w_elt0 e2w_full0 stall0 stalled0)                       (ThreeStageAllRegs rf2 pm2 pc2 fEpoch2 sbF2 d2e_elt2 d2e_full2 w2d_elt2 w2d_full2 eEpoch2 e2w_elt2 e2w_full2 stall2 stalled2) (ls0 ++ ls1) /\
        ThreeStageProcMemConsistent (ls0 ++ ls1) lastRq0 mem /\
        relatedTrace (ls0++ls1) d2e_data0 e2w_data0 stall_data0 (rs0++rs1).
  Proof.
    intros.
    repeat match goal with
             | [ |- _ /\ _ ] => split
           end.
    - eapply ForwardMultistep_trans; eassumption.
    - admit. (* Needs lastrq1 = getRqcall (last ls0) and another arg to ThreeStageProcMemConsistent that gives the ending state of the memory. *)
    - generalize dependent ls1.
      generalize H; clear H. generalize H0; clear H0.
      repeat match goal with
               [ H : relatedTrace _ _ _ _ _ , K : _ |- _ ] =>
               generalize K; clear K
             end.
      induction H1; intros; simpl.
      + move H at bottom. inversion H. clear dependent o1. clear dependent o2.
        (* Here we need a connection between the _data and the actual register contents. *)
        admit.
      + inversion H3; subst. 
        * inversion H4; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H14).
          dest.  rewrite H8 in H15.        
          econstructor; try eassumption.
          eapply IHrelatedTrace. eassumption.
          eassumption. eassumption. admit.
          eassumption.
        * inversion H4; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H14).
          dest.  rewrite H8 in H15.        
          econstructor; try eassumption.
          eapply IHrelatedTrace. eassumption.
          eassumption. eassumption. admit.
          eassumption.
        * inversion H4; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H14).
          dest.  rewrite H8 in H15.        
          econstructor; try eassumption.
          eapply IHrelatedTrace. eassumption.
          eassumption. eassumption. admit.
          eassumption.
      + inversion H3; subst. 
        * inversion H4; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H14).
          dest.  rewrite H8 in H15.        
          econstructor; try eassumption.
          eapply IHrelatedTrace. eassumption.
          eassumption. eassumption. admit.
          eassumption.
        * inversion H4; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H14).
          dest.  rewrite H8 in H15.        
          econstructor; try eassumption.
          eapply IHrelatedTrace. eassumption.
          eassumption. eassumption. admit.
          eassumption.
        * inversion H4; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H14).
          dest.  rewrite H8 in H15.        
          econstructor; try eassumption.
          eapply IHrelatedTrace. eassumption.
          eassumption. eassumption. admit.
          eassumption.
      + inversion H3; subst. 
        * inversion H4; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H14).
          dest.  rewrite H8 in H15.        
          econstructor; try eassumption.
          eapply IHrelatedTrace. eassumption.
          eassumption. eassumption. admit.
          eassumption.
        * inversion H4; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H14).
          dest.  rewrite H8 in H15.        
          econstructor; try eassumption.
          eapply IHrelatedTrace. eassumption.
          eassumption. eassumption. admit.
          eassumption.
        * inversion H4; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H14).
          dest.  rewrite H8 in H15.        
          econstructor; try eassumption.
          eapply IHrelatedTrace. eassumption.
          eassumption. eassumption. admit.
          eassumption.
      + inversion H4; subst. 
        * inversion H5; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H13).
          dest. rewrite H in H15.        
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.          
          eassumption. eassumption. admit.
          eassumption.
        * inversion H5; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H13).
          dest.  rewrite H in H15.        
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.
          eassumption. eassumption. admit.
          eassumption.
        * inversion H5; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H13).
          dest. rewrite H in H15.        
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.
          eassumption. eassumption. admit.
          eassumption.
      + inversion H4; subst. 
        * inversion H5; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H13).
          dest. rewrite H in H15.        
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.          
          eassumption. eassumption. admit.
          eassumption.
        * inversion H5; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H13).
          dest.  rewrite H in H15.        
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.
          eassumption. eassumption. admit.
          eassumption.
        * inversion H5; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H13).
          dest. rewrite H in H15.        
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.
          eassumption. eassumption. admit.
          eassumption.
      + inversion H3; subst. 
        * inversion H4; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H12).
          dest. rewrite H in H14.        
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.          
          eassumption. eassumption. admit.
          eassumption.
        * inversion H4; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H12).
          dest. rewrite H in H14.        
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.          
          eassumption. eassumption. admit.
          eassumption.
        * inversion H4; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H12).
          dest. rewrite H in H14.        
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.          
          eassumption. eassumption. admit.
          eassumption.
      + inversion H5; subst. 
        * inversion H6; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H14).
          dest. rewrite H in H16.        
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.          
          eassumption. eassumption. admit.
          eassumption.
        * inversion H6; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H14).
          dest. rewrite H in H16.        
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.          
          eassumption. eassumption. admit.
          eassumption.
        * inversion H6; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H14).
          dest. rewrite H in H16.        
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.          
          eassumption. eassumption. admit.
          eassumption.
      + inversion H3; subst. 
        * inversion H4; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H12).
          dest. rewrite H in H14.        
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.          
          eassumption. eassumption. admit.
          eassumption.
        * inversion H4; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H12).
          dest. rewrite H in H14.        
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.          
          eassumption. eassumption. admit.
          eassumption.
        * inversion H4; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H12).
          dest. rewrite H in H14.        
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.          
          eassumption. eassumption. admit.
          eassumption.
      + inversion H4; subst. 
        * inversion H5; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H15).
          dest. rewrite H9 in H16.        
          econstructor; try eassumption. 
          eapply IHrelatedTrace. eassumption.          
          eassumption. eassumption. admit.
          eassumption.
        * inversion H5; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H15).
          dest. rewrite H9 in H16.        
          econstructor; try eassumption. 
          eapply IHrelatedTrace. eassumption.          
          eassumption. eassumption. admit.
          eassumption.
        * inversion H5; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H15).
          dest. rewrite H9 in H16. 
          econstructor; try eassumption. 
          eapply IHrelatedTrace. eassumption.          
          eassumption. eassumption. admit.
          eassumption.
      + inversion H4; subst. 
        * inversion H5; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H13).
          dest. rewrite H in H15.        
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.          
          eassumption. eassumption. admit.
          eassumption.
        * inversion H5; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H13).
          dest. rewrite H in H15.
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.          
          eassumption. eassumption. admit.
          eassumption.
        * inversion H5; subst.
          pose proof (all_registers_inclusive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H13).
          dest. rewrite H in H15.        
          econstructor; try eassumption. reflexivity.
          eapply IHrelatedTrace. eassumption.          
          eassumption. eassumption. admit.
          eassumption.
  Admitted.
          
        
  Lemma canClearW2D : forall lastRq mem rf pm pc fEpoch sbF d2e_data d2e_elt d2e_full w2d_elt w2d_full eEpoch e2w_data e2w_elt e2w_full stall_data stall stalled,
       exists pc' fEpoch' w2d_elt' ls rs,
         ForwardMultistep p (ThreeStageAllRegs rf pm pc fEpoch sbF d2e_elt d2e_full w2d_elt w2d_full eEpoch e2w_elt e2w_full stall stalled)
                          (ThreeStageAllRegs rf pm pc' fEpoch' sbF d2e_elt d2e_full w2d_elt' false eEpoch e2w_elt e2w_full stall stalled) ls /\
         ThreeStageProcMemConsistent ls lastRq mem /\
         relatedTrace ls d2e_data e2w_data stall_data rs.
  Proof.
    intros.
    destruct w2d_full.
    - repeat eexists.
      + eapply FMulti.
        rewrite step_consistent.
        constructor.
        econstructor 2. econstructor 2. econstructor.
        1: { eapply SingleRule. instantiate (2 := "modifyPc"). simpl; intuition reflexivity.
             repeat match goal with
                    | [ |- SemAction _ (@IfElse _ _ ?cond _ _ _ _) _ _ _ ] =>
                      let x := fresh in remember (evalExpr cond) as x; destruct x;
                                          [ eapply SemIfElseTrue | eapply SemIfElseFalse ]
                    | [ |- SemAction _ _ _ _ _ ] => econstructor
                    end.
             
             all: try reflexivity.
             all: try mred.
        }
        
        4: { eapply SingleMeth; try reflexivity. instantiate (1 := ("w2d" -- "deq"::_)%struct). simpl; intuition reflexivity.
             repeat econstructor. all: reflexivity.
        }
        
        split. emp_disj. split.
        unfold M.Disj; intro; rewrite !M.F.P.F.not_find_in_iff.
        mred. firstorder. reflexivity. reflexivity.

        split. 
        unfold M.Disj; intro; rewrite !M.F.P.F.not_find_in_iff.
        mred.
        split. emp_disj.
        simpl. mred. rewrite M.F.P.F.empty_in_iff; tauto.
        reflexivity. reflexivity.

        unfold wellHidden, hide. simpl. split; unfold M.KeysDisj; intros;
                                          rewrite M.F.P.F.not_find_in_iff; simpl in H; intuition (subst; mred).
        apply NilFMultistep.
        unfold ThreeStageAllRegs. meq.
      + eapply S3PMCcons.
        split. unfold hide; simpl. mred.
        split. unfold hide; simpl. mred.
        intuition reflexivity. constructor.
      + unfold hide; simpl.
        admit. (* haven't related Nops yet ... *)
    - repeat eexists.
      + apply NilFMultistep. reflexivity.
      + constructor.
      + constructor.
        Unshelve. exact nil.
  Admitted.

  Lemma canClearStall : forall lastRq mem rf pm pc fEpoch sbF d2e_data d2e_elt d2e_full w2d_elt eEpoch e2w_data e2w_elt e2w_full stall_data stall stalled,
      match stall_data with
      | Some {| stall_op := op |} => stall = true /\ if op
                                                   then ((evalExpr (d2eOpType _ stalled)) = opSt /\
                                                         (evalExpr (getOpcodeE (d2eRawInst _ stalled))) = rv32iOpSTORE)
                                                   else ((evalExpr (d2eOpType _ stalled)) = opLd /\
                                                         (evalExpr (getOpcodeE (d2eRawInst _ stalled))) = rv32iOpLOAD)
      | None => stall = false
      end ->
      match lastRq with
      | Some (false, addr) => match stall_data with
                             | Some {| stall_val := val |} => mem addr = val
                             | _ => False
                             end
      | _ => True
      end
      -> exists rf' sbF' w2d_elt' w2d_full' eEpoch' ls rs,
        ForwardMultistep p (ThreeStageAllRegs rf pm pc fEpoch sbF d2e_elt d2e_full w2d_elt false (* <- w2d_full *) eEpoch e2w_elt e2w_full stall stalled) (ThreeStageAllRegs rf' pm pc fEpoch sbF' d2e_elt d2e_full w2d_elt' w2d_full' eEpoch' e2w_elt e2w_full false stalled) ls /\
        ThreeStageProcMemConsistent ls lastRq mem /\
        relatedTrace ls d2e_data e2w_data stall_data rs.
  Proof.
    intros lastRq mem rf pm pc fEpoch sbF d2e_data0 d2e_elt d2e_full w2d_elt eEpoch e2w_data0 e2w_elt e2w_full stall_data0 stall stalled H H10.
    destruct stall.
    2: { repeat eexists. eapply NilFMultistep. reflexivity. constructor. econstructor. }
    (* yes, something is stalled. *)
    (* now we need to know that it was actually a load or store... *)
    assert (((evalExpr (d2eOpType _ stalled)) = opLd /\ (evalExpr (getOpcodeE (d2eRawInst _ stalled))) = rv32iOpLOAD) \/
    ((evalExpr (d2eOpType _ stalled) = opSt) /\ (evalExpr (getOpcodeE (d2eRawInst _ stalled))) = rv32iOpSTORE))%kami_expr. {
      destruct stall_data0. destruct s. destruct stall_op0. all: intuition congruence. }
    destruct H0; shatter;
    remember (weq ((evalExpr (d2eCurPc type stalled)) ^+ natToWord _ 4)%kami_expr (evalExpr (d2eNextPc type stalled))) as br;
    destruct br.
    
    - repeat eexists. 
      simpl in * |-.
      + eapply FMulti.
        rewrite step_consistent.
        econstructor.

        
        
        instantiate (1 := {| calls := (([]%fmap
                                          #[ "rsToProc"--"deq" |-->
       existT _ {| arg := Void; ret := Struct (RsToProc rv32iDataBytes) |} (WO, (evalExpr (STRUCT { "data" ::= _ })))])%kami_expr
                                          #[ "getRf2" |--> _ ]
                                          #[ "setRf" |--> _ ]
                                          #[ "sbRemove" |--> _ ])%fmap;
                             defs := (([]%fmap
                                         #[ "getRf2" |--> _ ]
                                         #[ "setRf" |--> _ ]
                                         #[ "sbRemove" |--> _ ]))%fmap; annot := Some (Some "repLd") |}).

        econstructor; try reflexivity. econstructor 2; try reflexivity. econstructor 2; try reflexivity. econstructor 2; try reflexivity.
        econstructor.

        1: {     
          eapply SingleRule. instantiate (2 := "repLd"). simpl; intuition reflexivity.
          repeat match goal with
                 | [ |- SemAction _ (@IfElse _ _ ?cond _ _ _ _) _ _ _ ] =>
                   let x := fresh in remember (evalExpr cond) as x; destruct x;
                                       [ eapply SemIfElseTrue | eapply SemIfElseFalse ]
                 | [ |- SemAction _ _ _ _ _ ] => econstructor
                 end.


          all: try (unfold ThreeStageAllRegs; mred).
          all: try reflexivity.
          all: try mred.
          simpl; rewrite H0; reflexivity.
          all: try emp_disj.
          all: try congruence.
          simpl in HeqH2.
          unfold MemTypes.Data, rv32iDataBytes in HeqH2; simpl in HeqH2.
          rewrite !H1 in HeqH2; simpl in HeqH2.
          remember ( weq (evalExpr (d2eCurPc type stalled) ^+ $ (4)) (evalExpr (d2eNextPc type stalled))) as x.
          unfold MemTypes.Data, rv32iDataBytes in Heqx; simpl in Heqx.
          rewrite <- Heqx in HeqH2. destruct x. exfalso; inversion HeqH2. rewrite <-  Heqx in Heqbr; inversion Heqbr.
        }       
        2: {
          eapply SingleMeth. instantiate (1 := ("getRf2" :: _)%struct). simpl; intuition reflexivity.
          repeat econstructor. reflexivity.
        }
        3: {
          eapply SingleMeth. instantiate (1 := ("setRf" :: _)%struct). simpl; intuition reflexivity.
          repeat econstructor. all: reflexivity.
        }
        4: {
          eapply SingleMeth. instantiate (1 := ("sbRemove" :: _)%struct). simpl; intuition reflexivity.
          repeat econstructor. all: reflexivity.
        }
        
        repeat split; emp_disj.
        repeat split; emp_disj.
        simpl. mred. rewrite M.F.P.F.empty_in_iff; tauto.
        repeat split.
        mred. intro. rewrite !M.F.P.F.in_find_iff. mred.
        emp_disj.
        simpl. rewrite !M.F.P.F.in_find_iff. mred.
        repeat split; emp_disj.
        intro. rewrite !M.F.P.F.in_find_iff. mred.
        simpl. rewrite !M.F.P.F.in_find_iff. mred.
        simpl. f_equal; apply FMap.M.leibniz; intro; mred.
                
        unfold wellHidden, hide. simpl. split.
        intro. intro. rewrite !M.F.P.F.in_find_iff in *. mred.
        intro. intro. rewrite !M.F.P.F.in_find_iff in *. mred.
        simpl in H0. exfalso. compute in H2; intuition congruence.
        apply NilFMultistep. unfold ThreeStageAllRegs.
        meqReify.
      + eapply S3PMCrs; cbv zeta. simpl. repeat split.
        mred. simpl.
        instantiate (1 := mem).
        instantiate (1 := (#(_)%kami_expr)).
        instantiate (1 := (match lastRq with | Some (false, adr) => (mem adr) | _ =>
                           match stall_data0 with | Some {| stall_val := val |} => val | _ => _ end end)).
        destruct lastRq as [[[|] ?] |]; intuition congruence.
        econstructor.
      + unfold hide; simpl.
        destruct stall_data0; try congruence.
        destruct s; shatter. 
        destruct stall_op0. shatter. rewrite H1 in e2. inversion e2.
        eapply rtRd'; try reflexivity.
        eassert (getRuleCalls "repLd" p = _) by (compute; reflexivity).
        rewrite H. simpl. intro. intro. simpl in *. 
        rewrite M.F.P.F.in_find_iff in H2. apply not_None_Some in H2. shatter. apply subtractKV_found in H2.
        generalize dependent H2.  mred.
        simpl. unfold rep_value. mred. simpl.
        destruct lastRq as [[[|] ?] |]. reflexivity. rewrite H10; reflexivity. reflexivity.
        constructor.
    - repeat eexists. 
      simpl in * |-.
      + eapply FMulti.
        rewrite step_consistent.
        econstructor.

        instantiate (1 := {| calls := (([]%fmap
                                          #[ "w2d" -- "enq"  |--> _ ] 
                                          #[ "toggleEpoch" |--> _ ]
                                          #[ "rsToProc"--"deq" |-->
       existT _ {| arg := Void; ret := Struct (RsToProc rv32iDataBytes) |} (WO, (evalExpr (STRUCT { "data" ::= _ })))])%kami_expr
                                          #[ "getRf2" |--> _ ]
                                          #[ "setRf" |--> _ ]
                                          #[ "sbRemove" |--> _ ])%fmap;
                             defs := (([]%fmap
                                         #[ "w2d" -- "enq"  |--> _ ] 
                                         #[ "toggleEpoch" |--> _ ]
                                         #[ "getRf2" |--> _ ]
                                         #[ "setRf" |--> _ ]
                                         #[ "sbRemove" |--> _ ]))%fmap; annot := Some (Some "repLd") |}).

        econstructor; try reflexivity. econstructor 2; try reflexivity. econstructor 2; try reflexivity. econstructor 2; try reflexivity.
        econstructor 2; try reflexivity. econstructor 2; try reflexivity.
        econstructor.

        1: {     
          eapply SingleRule. instantiate (2 := "repLd"). simpl; intuition reflexivity.
          repeat match goal with
                 | [ |- SemAction _ (@IfElse _ _ ?cond _ _ _ _) _ _ _ ] =>
                   let x := fresh in remember (evalExpr cond) as x; destruct x;
                                       [ eapply SemIfElseTrue | eapply SemIfElseFalse ]
                 | [ |- SemAction _ _ _ _ _ ] => econstructor
                 end.


          
          all: try reflexivity.
          all: try (unfold ThreeStageAllRegs; mred).
          all: try mred.
          simpl; rewrite H0; reflexivity.
          all: try emp_disj.
          all: try congruence.
          simpl in HeqH2.
          unfold MemTypes.Data, rv32iDataBytes in HeqH2; simpl in HeqH2.
          rewrite !H1 in HeqH2; simpl in HeqH2.
          rewrite <- Heqbr in HeqH2. exfalso; inversion HeqH2.
        }       
        2: {
          eapply SingleMeth. instantiate (1 := ("getRf2" :: _)%struct). simpl; intuition reflexivity.
          repeat econstructor. reflexivity.
        }
        3: {
          eapply SingleMeth. instantiate (1 := ("setRf" :: _)%struct). simpl; intuition reflexivity.
          repeat econstructor. all: reflexivity.
        }
        4: {
          eapply SingleMeth. instantiate (1 := ("sbRemove" :: _)%struct). simpl; intuition reflexivity.
          repeat econstructor. all: reflexivity.
        }
        5: {
          eapply SingleMeth. instantiate (1 := ("toggleEpoch" :: _)%struct). simpl; intuition reflexivity.
          repeat econstructor. all: reflexivity.
        }
        6: {
          eapply SingleMeth. instantiate (1 := ("w2d" -- "enq" :: _)%struct). simpl; intuition  reflexivity.
          repeat econstructor. all: reflexivity.
        }
        
        repeat split; emp_disj.
        repeat split; emp_disj.
        simpl. mred. rewrite M.F.P.F.empty_in_iff; tauto.
        repeat split.
        mred. intro. rewrite !M.F.P.F.in_find_iff. mred.
        emp_disj.
        simpl. rewrite !M.F.P.F.in_find_iff. mred.
        repeat split; emp_disj.
        intro. rewrite !M.F.P.F.in_find_iff. mred.
        simpl. rewrite !M.F.P.F.in_find_iff. mred.
        simpl. split. intro. rewrite !M.F.P.F.in_find_iff. mred.
        split. emp_disj. simpl. rewrite !M.F.P.F.in_find_iff. mred.
        split. intro. rewrite !M.F.P.F.in_find_iff. mred.
        split. emp_disj. simpl. rewrite !M.F.P.F.in_find_iff. mred.
        simpl.
        f_equal; apply FMap.M.leibniz; intro; mred.
                
        unfold wellHidden, hide. simpl. split.
        intro. intro. rewrite !M.F.P.F.in_find_iff in *. mred.
        intro. intro. rewrite !M.F.P.F.in_find_iff in *. mred.
        exfalso. compute in H2; intuition congruence.
        apply NilFMultistep. unfold ThreeStageAllRegs; meqReify.
      + eapply S3PMCrs; cbv zeta. simpl. repeat split.
        mred. simpl.
        instantiate (1 := mem).
        instantiate (1 := (#(_)%kami_expr)).
        instantiate (1 := (match lastRq with | Some (false, adr) => mem adr | _ =>
                           match stall_data0 with | Some {| stall_val := val |} => val | _ => _ end end)).
        destruct lastRq as [[[|] ?] |]; intuition congruence.
        econstructor.
      + unfold hide; simpl.
        destruct stall_data0; try congruence.
        destruct s; shatter. 
        destruct stall_op0. shatter. exfalso.
        rewrite H1 in e1. inversion e1.
        eapply rtRd'; try reflexivity.
        eassert (getRuleCalls "repLd" p = _) by (compute; reflexivity).
        rewrite H. simpl. intro. intro. simpl in *. 
        rewrite M.F.P.F.in_find_iff in H2. apply not_None_Some in H2. shatter. apply subtractKV_found in H2.
        generalize dependent H2.  mred.
        simpl. unfold rep_value. mred. simpl.
        destruct lastRq as [[[|] ?] |]; try reflexivity. rewrite H10; reflexivity.
        constructor.
    - (* and the other cases: for if we take the branch / for if it's a ST *)
      repeat eexists. 
      simpl in * |-.
      + eapply FMulti.
        rewrite step_consistent.
        econstructor.

        
        
        instantiate (1 := {| calls := (([]%fmap
                                          #[ "rsToProc"--"deq" |-->
        existT _ {| arg := Void; ret := Struct (RsToProc rv32iDataBytes) |} (WO, (evalExpr (STRUCT { "data" ::= _ })))])%kami_expr
                                          #[ "getRf2" |--> _ ])%fmap;
                             defs := ([]%fmap
                                         #[ "getRf2" |--> _ ])%fmap ; annot := Some (Some "repSt") |}).

        econstructor; try reflexivity. econstructor 2; try reflexivity.
        econstructor.

        1: {     
          eapply SingleRule. instantiate (2 := "repSt"). simpl; intuition reflexivity.
          repeat match goal with
                 | [ |- SemAction _ (@IfElse _ _ ?cond _ _ _ _) _ _ _ ] =>
                   let x := fresh in remember (evalExpr cond) as x; destruct x;
                                       [ eapply SemIfElseTrue | eapply SemIfElseFalse ]
                 | [ |- SemAction _ _ _ _ _ ] => econstructor
                 end.


          all: try (unfold ThreeStageAllRegs; mred).
          all: try reflexivity.
          all: try mred.
          simpl; rewrite H0; reflexivity.
          all: try emp_disj.
          all: try congruence.
          simpl in HeqH2.
          unfold MemTypes.Data, rv32iDataBytes in HeqH2; simpl in HeqH2.
          rewrite !H1 in HeqH2; simpl in HeqH2.
          remember ( weq (evalExpr (d2eCurPc type stalled) ^+ $ (4)) (evalExpr (d2eNextPc type stalled))) as x.
          unfold MemTypes.Data, rv32iDataBytes in Heqx; simpl in Heqx.
          rewrite <- Heqx in HeqH2. destruct x. exfalso; inversion HeqH2. rewrite <-  Heqx in Heqbr; inversion Heqbr.
        }       
        2: {
          eapply SingleMeth. instantiate (1 := ("getRf2" :: _)%struct). simpl; intuition reflexivity.
          repeat econstructor. reflexivity.
        }
        
        repeat split; emp_disj.
        repeat split; emp_disj.
        simpl. mred. rewrite M.F.P.F.empty_in_iff; tauto.
        repeat split.                
        unfold wellHidden, hide. simpl. split.
        intro. intro. rewrite !M.F.P.F.in_find_iff in *. mred.
        intro. intro. rewrite !M.F.P.F.in_find_iff in *. mred.
        simpl in H0. exfalso. compute in H2; intuition congruence.
        apply NilFMultistep. meq.
      + eapply S3PMCrs; cbv zeta. simpl. repeat split.
        mred. simpl.
        instantiate (1 := mem).
        instantiate (1 := (#(_)%kami_expr)).
        instantiate (1 := (match lastRq with | Some (false, adr) => mem adr | _ => _ end)).
        destruct lastRq as [[[|] ?] |]; intuition congruence.
        econstructor.
      + unfold hide; simpl.
        destruct stall_data0; try congruence.
        destruct s; shatter. 
        destruct stall_op0. shatter. rewrite H1 in e2. inversion e2.
        eapply rtWr'; try reflexivity.
        eassert (getRuleCalls "repSt" p = _) by (compute; reflexivity).
        rewrite H. simpl. intro. intro. simpl in *. 
        rewrite M.F.P.F.in_find_iff in H2. apply not_None_Some in H2. shatter. apply subtractKV_found in H2.
        generalize dependent H2.  mred.
        constructor.
        exfalso; shatter. rewrite H1 in H2.  inversion H2. 
    - repeat eexists. 
      simpl in * |-.
      + eapply FMulti.
        rewrite step_consistent.
        econstructor.

        instantiate (1 := {| calls := (([]%fmap
                                          #[ "w2d" -- "enq"  |--> _ ] 
                                          #[ "toggleEpoch" |--> _ ]
                                          #[ "rsToProc"--"deq" |-->
       existT _ {| arg := Void; ret := Struct (RsToProc rv32iDataBytes) |} (WO, (evalExpr (STRUCT { "data" ::= _ })))])%kami_expr
                                          #[ "getRf2" |--> _ ])%fmap;
                             defs := (([]%fmap
                                         #[ "w2d" -- "enq"  |--> _ ] 
                                         #[ "toggleEpoch" |--> _ ]
                                         #[ "getRf2" |--> _ ]))%fmap; annot := Some (Some "repSt") |}).

        econstructor; try reflexivity. econstructor 2; try reflexivity.
        econstructor 2; try reflexivity. econstructor 2; try reflexivity.
        econstructor.

        1: {     
          eapply SingleRule. instantiate (2 := "repSt"). simpl; intuition reflexivity.
          repeat match goal with
                 | [ |- SemAction _ (@IfElse _ _ ?cond _ _ _ _) _ _ _ ] =>
                   let x := fresh in remember (evalExpr cond) as x; destruct x;
                                       [ eapply SemIfElseTrue | eapply SemIfElseFalse ]
                 | [ |- SemAction _ _ _ _ _ ] => econstructor
                 end.


          
          all: try reflexivity.
          all: try (unfold ThreeStageAllRegs; mred).
          all: try mred.
          simpl; rewrite H0; reflexivity.
          all: try emp_disj.
          all: try congruence.
          simpl in HeqH2.
          unfold MemTypes.Data, rv32iDataBytes in HeqH2; simpl in HeqH2.
          rewrite !H1 in HeqH2; simpl in HeqH2.
          rewrite <- Heqbr in HeqH2. exfalso; inversion HeqH2.
        }       
        2: {
          eapply SingleMeth. instantiate (1 := ("getRf2" :: _)%struct). simpl; intuition reflexivity.
          repeat econstructor. reflexivity.
        }
        3: {
          eapply SingleMeth. instantiate (1 := ("toggleEpoch" :: _)%struct). simpl; intuition reflexivity.
          repeat econstructor. all: reflexivity.
        }
        4: {
          eapply SingleMeth. instantiate (1 := ("w2d" -- "enq" :: _)%struct). simpl; intuition  reflexivity.
          repeat econstructor. all: reflexivity.
        }
        
        repeat split; emp_disj.
        repeat split; emp_disj.
        simpl. mred. rewrite M.F.P.F.empty_in_iff; tauto.
        repeat split.
        mred. intro. rewrite !M.F.P.F.in_find_iff. mred.
        emp_disj.
        simpl. rewrite !M.F.P.F.in_find_iff. mred.
        repeat split; emp_disj.
        intro. rewrite !M.F.P.F.in_find_iff. mred.
        simpl. rewrite !M.F.P.F.in_find_iff. mred.
        simpl.         f_equal; apply FMap.M.leibniz; intro; mred.
                
        unfold wellHidden, hide. simpl. split.
        intro. intro. rewrite !M.F.P.F.in_find_iff in *. mred.
        intro. intro. rewrite !M.F.P.F.in_find_iff in *. mred.
        exfalso. compute in H2; intuition congruence.
        apply NilFMultistep. meq.
      + eapply S3PMCrs; cbv zeta. simpl. repeat split.
        mred. simpl.
        instantiate (1 := mem).
        instantiate (1 := (#(_)%kami_expr)).
        instantiate (1 := (match lastRq with | Some (false, adr) => (mem adr) | _ => _ end)).
        destruct lastRq as [[[|] ?] |]; intuition congruence.
        econstructor.
      + unfold hide; simpl.
        destruct stall_data0; try congruence.
        destruct s; shatter. 
        destruct stall_op0. shatter.
        eapply rtWr'; try reflexivity.
        eassert (getRuleCalls "repSt" p = _) by (compute; reflexivity).
        rewrite H. simpl. intro. intro. simpl in *. 
        rewrite M.F.P.F.in_find_iff in H2. apply not_None_Some in H2. shatter. apply subtractKV_found in H2.
        generalize dependent H2.  mred.
        constructor.
        exfalso; shatter. rewrite H0 in H.  inversion H.
        Grab Existential Variables.
        all: exact $0.
  Qed.

  (* This, or something like it, should follow from the above; we want to be able to prove "step from X to Y" and "step from "Y to Z" *)
  (* and combine them into "step from X to Z". *)
  (* Corollary combination_test : forall lastRq mem rf pm pc fEpoch sbF d2e_data d2e_elt d2e_full w2d_elt w2d_full eEpoch e2w_data e2w_elt e2w_full stall_data stall stalled, *)
  (*     match stall_data with *)
  (*     | Some {| stall_op := op |} => stall = true /\ if op *)
  (*                                                  then ((evalExpr (d2eOpType _ stalled)) = opSt /\ *)
  (*                                                        (evalExpr (getOpcodeE (d2eRawInst _ stalled))) = rv32iOpSTORE) *)
  (*                                                  else ((evalExpr (d2eOpType _ stalled)) = opLd /\ *)
  (*                                                        (evalExpr (getOpcodeE (d2eRawInst _ stalled))) = rv32iOpLOAD) *)
  (*     | None => stall = false *)
  (*     end -> *)
  (*     match lastRq with *)
  (*     | Some (false, addr) => match stall_data with *)
  (*                            | Some {| stall_val := val |} => mem addr = val *)
  (*                            | _ => False *)
  (*                            end *)
  (*     | _ => True *)
  (*     end *)
  (*     -> exists newRegs ls rs, *)
  (*       ForwardMultistep p (ThreeStageAllRegs rf pm pc fEpoch sbF d2e_elt d2e_full w2d_elt w2d_full eEpoch e2w_elt e2w_full stall stalled) newRegs ls /\ *)
  (*       ThreeStageProcMemConsistent ls lastRq mem /\ *)
  (*       relatedTrace ls d2e_data e2w_data stall_data rs /\ *)
  (*       FMap.M.find ("stall") newRegs = Some (existT _ (SyntaxKind Bool) false). *) 
  
  
  Conjecture abstractToThreeStageRelated :
    forall rf pm pc mem trace lastRq,
      hasTrace rf pm pc mem trace ->
      exists newRegs ls,
        ForwardMultistep p (ThreeStageProcRegs rf pm pc) newRegs ls /\
        ThreeStageProcMemConsistent ls lastRq mem /\
        relatedTrace ls None None None trace.
  (* To prove this requires more lemmata along the lines of canClearStall. Probably, in fact, one wants a theorem combining them all, saying that *)
  (* no matter what state the pipeline is in, it can always process some instruction, after clearing sufficently many things. *)

  Conjecture ThreeStageToAbstractRelated :
    forall lastRq rf pm pc mem newRegs ls,
      ForwardMultistep p (ThreeStageProcRegs rf pm pc) newRegs ls ->
      ThreeStageProcMemConsistent ls lastRq mem ->
      exists trace,
        hasTrace rf pm pc mem trace /\
        relatedTrace ls None None None trace.
  (* Probably "threestageprocregs" should be "threestageallregs" in many of these. *)
  Conjecture relatedCensor :
    forall (lastRq : option (bool * address)) rf1 rf2 pm pc mem1 mem2 trace1 trace2 newRegs1 newRegs2 ls1 ls2,
      hasTrace rf1 pm pc mem1 trace1 ->
      hasTrace rf2 pm pc mem2 trace2 ->
      ForwardMultistep p (ThreeStageProcRegs rf1 pm pc) newRegs1 ls1 ->
      ThreeStageProcMemConsistent ls1 lastRq mem1 ->
      ForwardMultistep p (ThreeStageProcRegs rf2 pm pc) newRegs2 ls2 ->
      ThreeStageProcMemConsistent ls2 lastRq mem2 ->
      relatedTrace ls1 None None None trace1 ->
      relatedTrace ls2 None None None trace2 ->
      censorTrace trace1 = censorTrace trace2 ->
      censorThreeStageLabelSeq (option_map fst lastRq)
                               getRqCall censorThreeStageMeth (canonicalize (option_map fst lastRq) ls1) =
      censorThreeStageLabelSeq (option_map fst lastRq) getRqCall censorThreeStageMeth (canonicalize (option_map fst lastRq) ls2).


    Theorem abstractToProcHiding :
    forall lastRq rf pm pc mem,
      abstractHiding rf pm pc mem ->
      ThreeStageProcHiding p lastRq (ThreeStageProcRegs rf pm pc) mem.
  Proof. 
    unfold abstractHiding, ThreeStageProcHiding. 
    intros.
    match goal with
    | [ H : ForwardMultistep _ _ _ _ |- _ ] => let H' := fresh in assert (H' := H); eapply ThreeStageToAbstractRelated in H'; try eassumption
    end.
    shatter. rename x into trace.
    match goal with
    | [ Hrel : relatedTrace ?ls _ _ _ ?t,
               Hextract : extractFhLabelSeq fhMeth ?ls = _,
                          Htrace : hasTrace _ _ _ _ _,
                                   Habs : forall _ _, hasTrace _ _ _ _ _ -> extractFhTrace _ = _ -> forall _, length _ = length _ -> _,
          Hlen : length _ = length _
          |- context[extractFhLabelSeq fhMeth _ = ?fhTrace] ] =>
      rewrite <- (relatedFhTrace _ _ _ _ _ Hrel) in Hextract; specialize (Habs _ _ Htrace Hextract fhTrace Hlen)
    end.
    shatter. rename x into trace'.
    match goal with
    | [ Htrace : hasTrace _ _ _ _ ?t,
                 Hextract : extractFhTrace ?t = ?fhTrace
        |- context[?fhTrace] ] => pose proof (abstractToThreeStageRelated _ _ _ _ _ lastRq Htrace)
    end.
    shatter. rename x into newRegs'. rename x0 into labels'.
    match goal with
    | [ Hht0 : hasTrace _ _ _ _ ?t0,
        Hht1 : hasTrace _ _ _ _ ?t1,
        Hrt0 : relatedTrace ?ls0 _ _ _ ?t0,
        Hrt1 : relatedTrace ?ls1 _ _ _ ?t1,
        Heft : extractFhTrace ?t1 = _,
        Hfm : ForwardMultistep _ _ _ ?ls1,
        Hmc : ThreeStageProcMemConsistent ?ls1 _ _,
        Hfm0 : ForwardMultistep _ _ _ ?ls0
        |- _ ] => 
      let Hcanon := fresh in
      let Heq := fresh in 
        eassert (_ = _) as Hcanon by (eapply (relatedCensor _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrt0 Hrt1); eassumption);
        pose proof (relatedFhTrace _ _ _ _ _ Hrt1) as Heq;
        rewrite Heq in Heft
    end.
    eassert _. eapply decanon. 4: eapply H11. eassumption. eassumption. eassumption.
    reflexivity.
    shatter. 
    exists x, newRegs'.  
    split. assumption.
    split. assumption.
    split. assumption.
    subst. assumption.
    Unshelve. (* weird but straightforward unification things - just make sure to do the ones with evars in the goals first. *)
    9: eassumption.
    5: eassumption.
    3: eassumption.
    3: eassumption.
    assumption. assumption.
  Qed.
  
  (** Beyond here, the proofs are all just what they were in origin-timing/Ex/Timing/SCSingle.v with no effort yet made to adapt them to the
   * new target. The theorem statements are changed, so that it fits the correct module type. *)

  Theorem ProcAirtight : forall oldregs newregs labels,
      ForwardMultistep p oldregs newregs labels ->
      ThreeStageProcLabelSeqAirtight labels.
  Proof. admit.
    (* induction 1; constructor; auto. *)
    (* match goal with *)
    (* | [ H : Step _ _ _ _ |- _ ] => inv H *)
    (* end. *)
    (* match goal with *)
    (* | [ H : substepsComb ss |- _ ] => apply substepsComb_substepsInd in H; apply SCProcSubsteps in H *)
    (* end. *)
    (* intuition idtac; shatter; subst; *)
    (*   match goal with *)
    (*   | [ H : foldSSLabel ss = _ |- _ ] => rewrite H in * *)
    (*   end; *)
    (*   unfold hide, annot, calls, defs; *)
    (*   repeat rewrite FMap.M.subtractKV_empty_1; *)
    (*   repeat rewrite FMap.M.subtractKV_empty_2; *)
    (*   try solve [ constructor ]. *)
    (* Opaque evalExpr. *)
    (* match goal with *)
    (* | [ H : In _ _ |- _ ] => simpl in H *)
    (* end; *)
    (*   intuition idtac; *)
    (*   match goal with *)
    (*   | [ H : (_ :: _)%struct = _ |- _ ] => inv H *)
    (*   end; *)
    (*   kinv_action_dest; *)
    (*   constructor. *)
    (* Transparent evalExpr. *)
  Admitted.

  (* Lemma SCMemSubsteps : *)
  (*   forall o (ss : Substeps m o), *)
  (*     SubstepsInd m o (foldSSUpds ss) (foldSSLabel ss) -> *)
  (*     (((foldSSLabel ss) = {| annot := None; defs := FMap.M.empty _; calls := FMap.M.empty _ |} *)
  (*       \/ (foldSSLabel ss) = {| annot := Some None; defs := FMap.M.empty _; calls := FMap.M.empty _ |}) *)
  (*      /\ (foldSSUpds ss) = FMap.M.empty _) *)
  (*     \/ (exists a argV retV u, *)
  (*           (a = None \/ a = Some None) *)
  (*           /\ SemAction o (rv32iMemInstExec argV) u (FMap.M.empty _) retV *)
  (*           /\ (foldSSLabel ss) = {| annot := a; defs := FMap.M.add "exec" (existT _ *)
  (*                      {| arg := Struct (STRUCT {"addr" :: Bit 16; *)
  (*                                                "op" :: Bool; *)
  (*                                                "data" :: Bit 32}); *)
  (*                         ret := Struct (STRUCT {"data" :: Bit 32}) |} *)
  (*                      (argV, retV)) (FMap.M.empty _); calls := FMap.M.empty _ |} *)
  (*           /\ (foldSSUpds ss) = u). *)
  (* Proof. *)
  (*   intros. *)
  (*   match goal with *)
  (*   | [ H : SubstepsInd _ _ _ _ |- _ ] => induction H *)
  (*   end. *)
  (*   - tauto. *)
  (*   - intuition idtac; *)
  (*       simpl; *)
  (*       shatter; *)
  (*       intuition idtac; *)
  (*       subst; *)
  (*       match goal with *)
  (*       | [ H : Substep _ _ _ _ _ |- _ ] => destruct H *)
  (*       end; *)
  (*       try tauto; *)
  (*       try solve [right; repeat eexists; FMap.findeq]; *)
  (*       match goal with *)
  (*       | [ HIn : In _ (getRules m) |- _ ] => simpl in HIn; tauto *)
  (*       | _ => idtac *)
  (*       end. *)
  (*     + right. *)
  (*       simpl in HIn. *)
  (*       intuition idtac. *)
  (*       subst. *)
  (*       simpl in *. *)
  (*       exists None, argV, retV, u. *)
  (*       replace cs with (FMap.M.empty {x : SignatureT & SignT x}) in *. *)
  (*       * intuition idtac. *)
  (*       * kinv_action_dest; FMap.findeq. *)
  (*     + right. *)
  (*       simpl in HIn. *)
  (*       intuition idtac. *)
  (*       subst. *)
  (*       simpl in *. *)
  (*       exists (Some None), argV, retV, u. *)
  (*       replace cs with (FMap.M.empty {x : SignatureT & SignT x}) in *. *)
  (*       * intuition idtac. *)
  (*       * kinv_action_dest; FMap.findeq. *)
  (*     + exfalso. *)
  (*       simpl in HIn. *)
  (*       intuition idtac. *)
  (*       subst. *)
  (*       unfold CanCombineUUL in H1. *)
  (*       simpl in H1. *)
  (*       intuition idtac. *)
  (*       apply H3. *)
  (*       FMap.findeq. *)
  (*     + exfalso. *)
  (*       simpl in HIn. *)
  (*       intuition idtac. *)
  (*       subst. *)
  (*       unfold CanCombineUUL in H1. *)
  (*       simpl in H1. *)
  (*       intuition idtac. *)
  (*       apply H3. *)
  (*       FMap.findeq. *)
  (* Qed. *)

  Lemma SCMemRegs_find_mem : forall mem mem' nextRs,
      FMap.M.find (elt:={x : FullKind & fullType type x}) "mem"
                                   (ThreeStageMemRegs mem nextRs) =
                       Some
                         (existT (fullType type) (SyntaxKind (Vector (Bit 32) 11)) mem') -> mem = mem'.
  Proof.
    intros.
    unfold ThreeStageMemRegs in *.
    rewrite FMap.M.find_add_1 in H.
    match goal with
    | [ H : Some ?x = Some ?y |- _ ] => remember x as x'; remember y as y'; inv H
    end.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1).
  Qed.

  Theorem MemHiding : ThreeStageMemHiding m.
  Proof. admit.
    (* unfold ThreeStageMemHiding. *)
    (* induction 1; intros. *)
    (* - exists nil. *)
    (*   eexists. *)
    (*   intuition idtac. *)
    (*   + constructor; reflexivity. *)
    (*   + constructor. *)
    (*   + simpl in *. *)
    (*     subst. *)
    (*     simpl in *. *)
    (*     apply eq_sym. *)
    (*     rewrite <- length_zero_iff_nil. *)
    (*     congruence. *)
    (* - match goal with *)
    (*   | [ H : ForwardMultistep _ _ _ _ |- _ ] => inversion H *)
    (*   end. *)
    (*   match goal with *)
    (*   | [ H : Step _ _ _ _ |- _ ] => inversion H *)
    (*   end. *)
    (*   subst. *)
    (*   match goal with *)
    (*   | [ H : substepsComb _ |- _ ] => *)
    (*     apply substepsComb_substepsInd in H; *)
    (*       apply ThreeStageMemSubsteps in H *)
    (*   end. *)
    (*   intuition idtac; shatter; subst; *)
    (*     try match goal with *)
    (*         | [ H : foldSSLabel ss = _ |- _ ] => rewrite H in * *)
    (*         end; *)
    (*     try match goal with *)
    (*         | [ H : foldSSUpds ss = _ |- _ ] => rewrite H in * *)
    (*         end; *)
    (*     simpl in *; *)
    (*     subst; *)
    (*     FMap.mred; *)
    (*     try tauto. *)
    (*   + match goal with *)
    (*     | [ Hl : length _ = length _, *)
    (*         Hfm : ForwardMultistep _ _ _ _ |- _ ] => *)
    (*       specialize (IHSCMemMemConsistent Hfm _ eq_refl mem'0 wrs' Hl) *)
    (*     end. *)
    (*     shatter. *)
    (*     exists ({| annot := None; defs := FMap.M.empty _; calls := FMap.M.empty _ |} :: x), x0. *)
    (*     intuition idtac. *)
    (*     * econstructor; eauto. *)
    (*       -- match goal with *)
    (*          | [ |- Step _ _ _ ?l ] => replace l with (hide (foldSSLabel [{| upd := FMap.M.empty _; unitAnnot := Meth None; cms := FMap.M.empty _; substep := EmptyMeth m (SCMemRegs mem'0) |}])) by reflexivity *)
    (*          end. *)
    (*          constructor; eauto. *)
    (*          constructor; try solve [ constructor ]. *)
    (*          intros. *)
    (*          match goal with *)
    (*          | [ H : In _ nil |- _ ] => inversion H *)
    (*          end. *)
    (*       -- eauto. *)
    (*     * econstructor. *)
    (*       -- simpl. reflexivity. *)
    (*       -- assumption. *)
    (*     * simpl. *)
    (*       f_equal. *)
    (*       assumption. *)
    (*   + match goal with *)
    (*     | [ Hl : length _ = length _, *)
    (*         Hfm : ForwardMultistep _ _ _ _ |- _ ] => *)
    (*       specialize (IHSCMemMemConsistent Hfm _ eq_refl mem'0 wrs' Hl) *)
    (*     end. *)
    (*     shatter. *)
    (*     exists ({| annot := Some None; defs := FMap.M.empty _; calls := FMap.M.empty _ |} :: x), x0. *)
    (*     intuition idtac. *)
    (*     * econstructor; eauto. *)
    (*       -- match goal with *)
    (*          | [ |- Step _ _ _ ?l ] => replace l with (hide (foldSSLabel [{| upd := FMap.M.empty _; unitAnnot := Rle None; cms := FMap.M.empty _; substep := EmptyRule m (SCMemRegs mem'0) |}])) by reflexivity *)
    (*          end. *)
    (*          constructor; eauto. *)
    (*          constructor; try solve [ constructor ]. *)
    (*          intros. *)
    (*          match goal with *)
    (*          | [ H : In _ nil |- _ ] => inversion H *)
    (*          end. *)
    (*       -- eauto. *)
    (*     * econstructor. *)
    (*       -- simpl. reflexivity. *)
    (*       -- assumption. *)
    (*     * simpl. *)
    (*       f_equal. *)
    (*       assumption. *)
    (*   + pose (Hrq := inv_rq x0). *)
    (*     pose (Hrs := inv_rs x1). *)
    (*     destruct Hrq as [adr [op [dat Heqq]]]. *)
    (*     destruct Hrs as [val Heqs]. *)
    (*     simpl in adr, op, dat, val. *)
    (*     subst. *)
    (*     destruct op; *)
    (*       kinv_action_dest; *)
    (*       match goal with *)
    (*       | [ H : foldSSUpds _ = _ |- _ ] => rewrite H in * *)
    (*       end; *)
    (*       match goal with *)
    (*       | [ H : ?x = ?y |- _ ] => *)
    (*         let x' := fresh in *)
    (*         let y' := fresh in *)
    (*         remember x as x'; *)
    (*           remember y as y'; *)
    (*           assert (x' Fin.F1 = y' Fin.F1) by (rewrite H; reflexivity); *)
    (*           subst *)
    (*       end; *)
    (*       simpl in *; *)
    (*       subst; *)
    (*       try match goal with *)
    (*           | [ H : ForwardMultistep _ (FMap.M.union _ _) _ _ |- _ ] => *)
    (*             unfold SCMemRegs in H; *)
    (*               FMap.mred; *)
    (*               rewrite FMap.M.union_add in H; *)
    (*               FMap.mred; *)
    (*               rewrite FMap.M.add_idempotent in H *)
    (*           end. *)
    (*     * destruct wrs'; try discriminate. *)
    (*       match goal with *)
    (*       | [ H : S (length _) = length _ |- _ ] => simpl in H; inversion H *)
    (*       end. *)
    (*       match goal with *)
    (*       | [ H : _ |- _ ] => apply SCMemRegs_find_mem in H; shatter; subst *)
    (*       end. *)
    (*       match goal with *)
    (*       | [ Hl : length _ = length _, *)
    (*           Hfm : ForwardMultistep _ _ _ _ |- _ ] => *)
    (*         specialize (IHSCMemMemConsistent Hfm _ eq_refl *)
    (*                                        (fun a => if weq a adr then w else mem'0 a) *)
    (*                                        _ Hl) *)
    (*       end. *)
    (*       shatter. *)
    (*       match goal with *)
    (*       | [ H : extractMemWrValSeq ?ls = wrs', Hfm : ForwardMultistep _ _ ?r ?ls |- _ ] => *)
    (*         exists ({| annot := x; *)
    (*               defs := FMap.M.add "exec" *)
    (*                                  (existT SignT {| arg := Struct STRUCT {"addr" :: Bit 16; "op" :: Bool; "data" :: Bit 32}; ret := Struct STRUCT {"data" :: Bit 32} |} *)
    (*                                          (evalExpr (STRUCT { "addr" ::= Var _ (SyntaxKind (Bit 16)) adr; *)
    (*                                                              "op" ::= $$(true); *)
    (*                                                              "data" ::= Var _ (SyntaxKind (Bit 32)) w})%kami_expr, *)
    (*                                           evalExpr (STRUCT { "data" ::= $0 })%kami_expr)) (FMap.M.empty _); calls := FMap.M.empty _|} :: ls), r *)
    (*       end. *)
    (*       intuition idtac; subst. *)
    (*       -- econstructor; try discriminate. *)
    (*          ++ match goal with *)
    (*             | [ |- Step ?m ?o _ {| annot := _; defs := FMap.M.add _ (existT _ _ (?av, ?rv)) _; calls := _ |} ] => *)
    (*               let ss := fresh in *)
    (*               simple refine (let ss := (_ : Substeps m o) in _); *)
    (*                 [ apply cons; [ idtac | apply nil ]; *)
    (*                   eapply Build_SubstepRec; *)
    (*                   eapply SingleMeth; *)
    (*                   try (simpl; tauto); *)
    (*                   instantiate (4 := av); *)
    (*                   instantiate (1 := rv); *)
    (*                   eapply SemIfElseFalse; *)
    (*                   try match goal with *)
    (*                      | [ |- SemAction _ _ _ _ _ ] => repeat econstructor *)
    (*                       end; *)
    (*                   eauto *)
    (*                 | match goal with *)
    (*                   | [ |- Step ?m ?o _ ?l ] => replace l with (hide (foldSSLabel ss)) by reflexivity *)
    (*                   end *)
    (*                 ] *)
    (*             end. *)
    (*             apply StepIntro; repeat (apply AddSubstep || apply NilSubsteps); *)
    (*             match goal with *)
    (*             | [ |- forall _, In _ _ -> _ ] => *)
    (*               let Hin := fresh in *)
    (*               intros ? Hin; *)
    (*                 simpl in Hin; *)
    (*                 intuition idtac; *)
    (*                 subst; *)
    (*                 unfold canCombine; *)
    (*                 simpl; *)
    (*                 intuition idtac; *)
    (*                 eauto; *)
    (*                 discriminate *)
    (*             | [ |- wellHidden _ _ ] => *)
    (*               unfold wellHidden, m, getCalls, getDefs, FMap.M.KeysDisj; *)
    (*                 simpl; *)
    (*                 FMap.mred; *)
    (*                 rewrite FMap.M.subtractKV_empty_1; *)
    (*                 intuition idtac; *)
    (*                 rewrite FMap.M.F.P.F.empty_in_iff in *; *)
    (*                 tauto *)
    (*             end. *)
    (*          ++ match goal with *)
    (*             | [ H : ForwardMultistep ?m ?o ?n ?l |- ForwardMultistep ?m ?o' ?n ?l ] => replace o' with o; [ assumption | idtac ] *)
    (*             end. *)
    (*             unfold foldSSUpds, upd. *)
    (*             unfold SCMemRegs. *)
    (*             FMap.mred. *)
    (*             rewrite FMap.M.union_add. *)
    (*             FMap.mred. *)
    (*             rewrite FMap.M.add_idempotent. *)
    (*             reflexivity. *)
    (*       -- econstructor. *)
    (*          ++ simpl. *)
    (*             reflexivity. *)
    (*          ++ assumption. *)
    (*       -- subst. *)
    (*          simpl. *)
    (*          f_equal; try assumption. *)
    (*          f_equal. *)
    (*          FMap.M.ext k. *)
    (*          repeat rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity). *)
    (*          FMap.mred. *)
    (*       -- simpl. *)
    (*          congruence. *)
    (*       -- econstructor; try discriminate. *)
    (*          ++ match goal with *)
    (*             | [ |- Step ?m ?o _ {| annot := _; defs := FMap.M.add _ (existT _ _ (?av, ?rv)) _; calls := _ |} ] => *)
    (*               let ss := fresh in *)
    (*               simple refine (let ss := (_ : Substeps m o) in _); *)
    (*                 [ apply cons; *)
    (*                   [ exact (Build_SubstepRec (EmptyRule _ _)) *)
    (*                   | apply cons; [ idtac | apply nil ]]; *)
    (*                   eapply Build_SubstepRec; *)
    (*                   eapply SingleMeth; *)
    (*                   try (simpl; tauto); *)
    (*                   instantiate (4 := av); *)
    (*                   instantiate (1 := rv); *)
    (*                   eapply SemIfElseFalse; *)
    (*                   try match goal with *)
    (*                      | [ |- SemAction _ _ _ _ _ ] => repeat econstructor *)
    (*                       end; *)
    (*                   eauto *)
    (*                 | match goal with *)
    (*                   | [ |- Step ?m ?o _ ?l ] => replace l with (hide (foldSSLabel ss)) by reflexivity *)
    (*                   end *)
    (*                 ] *)
    (*             end. *)
    (*             apply StepIntro; repeat (apply AddSubstep || apply NilSubsteps); *)
    (*             match goal with *)
    (*             | [ |- forall _, In _ _ -> _ ] => *)
    (*               let Hin := fresh in *)
    (*               intros ? Hin; *)
    (*                 simpl in Hin; *)
    (*                 intuition idtac; *)
    (*                 subst; *)
    (*                 unfold canCombine; *)
    (*                 simpl; *)
    (*                 intuition idtac; *)
    (*                 eauto; *)
    (*                 discriminate *)
    (*             | [ |- wellHidden _ _ ] => *)
    (*               unfold wellHidden, m, getCalls, getDefs, FMap.M.KeysDisj; *)
    (*                 simpl; *)
    (*                 FMap.mred; *)
    (*                 rewrite FMap.M.subtractKV_empty_1; *)
    (*                 intuition idtac; *)
    (*                 rewrite FMap.M.F.P.F.empty_in_iff in *; *)
    (*                 tauto *)
    (*             end. *)
    (*          ++ match goal with *)
    (*             | [ H : ForwardMultistep ?m ?o ?n ?l |- ForwardMultistep ?m ?o' ?n ?l ] => replace o' with o; [ assumption | idtac ] *)
    (*             end. *)
    (*             unfold foldSSUpds, upd. *)
    (*             unfold SCMemRegs. *)
    (*             FMap.mred. *)
    (*             rewrite FMap.M.union_add. *)
    (*             FMap.mred. *)
    (*             rewrite FMap.M.add_idempotent. *)
    (*             reflexivity. *)
    (*       -- econstructor. *)
    (*          ++ simpl. *)
    (*             reflexivity. *)
    (*          ++ assumption. *)
    (*       -- subst. *)
    (*          simpl. *)
    (*          f_equal; try assumption. *)
    (*          f_equal. *)
    (*          FMap.M.ext k. *)
    (*          repeat rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity). *)
    (*          FMap.mred. *)
    (*       -- simpl. *)
    (*          congruence. *)
    (*     * shatter; subst. *)
    (*       match goal with *)
    (*       | [ H : _ |- _ ] => apply SCMemRegs_find_mem in H; subst *)
    (*       end. *)
    (*       match goal with *)
    (*       | [ Hl : length _ = length _, *)
    (*           Hfm : ForwardMultistep _ _ _ _ |- _ ] => *)
    (*         specialize (IHSCMemMemConsistent Hfm _ eq_refl mem'0 _ Hl) *)
    (*       end. *)
    (*       shatter. *)
    (*       match goal with *)
    (*       | [ H : extractMemWrValSeq ?ls = wrs', Hfm : ForwardMultistep _ _ ?r ?ls |- _ ] => *)
    (*         exists ({| annot := x; *)
    (*               defs := FMap.M.add "exec" *)
    (*                                  (existT SignT {| arg := Struct STRUCT {"addr" :: Bit 16; "op" :: Bool; "data" :: Bit 32}; ret := Struct STRUCT {"data" :: Bit 32} |} *)
    (*                                          (evalExpr (STRUCT { "addr" ::= Var _ (SyntaxKind (Bit 16)) adr; *)
    (*                                                              "op" ::= $$(false); *)
    (*                                                              "data" ::= Var _ (SyntaxKind (Bit 32)) dat })%kami_expr, *)
    (*                                           evalExpr (STRUCT { "data" ::= Var _ (SyntaxKind (Bit 32)) (mem'0 adr) })%kami_expr)) (FMap.M.empty _); calls := FMap.M.empty _|} :: ls), r *)
    (*       end. *)
    (*       intuition idtac; subst. *)
    (*       -- econstructor; try discriminate. *)
    (*          ++ match goal with *)
    (*             | [ |- Step ?m ?o _ {| annot := _; defs := FMap.M.add _ (existT _ _ (?av, ?rv)) _; calls := _ |} ] => *)
    (*               let ss := fresh in *)
    (*               simple refine (let ss := (_ : Substeps m o) in _); *)
    (*                 [ apply cons; [ idtac | apply nil ]; *)
    (*                   eapply Build_SubstepRec; *)
    (*                   eapply SingleMeth; *)
    (*                   try (simpl; tauto); *)
    (*                   instantiate (4 := av); *)
    (*                   instantiate (1 := rv); *)
    (*                   eapply SemIfElseTrue; *)
    (*                   try match goal with *)
    (*                      | [ |- SemAction _ _ _ _ _ ] => repeat econstructor *)
    (*                       end; *)
    (*                   eauto *)
    (*                 | match goal with *)
    (*                   | [ |- Step ?m ?o _ ?l ] => replace l with (hide (foldSSLabel ss)) by reflexivity *)
    (*                   end *)
    (*                 ] *)
    (*             end. *)
    (*             apply StepIntro; repeat (apply AddSubstep || apply NilSubsteps); *)
    (*             match goal with *)
    (*             | [ |- forall _, In _ _ -> _ ] => *)
    (*               let Hin := fresh in *)
    (*               intros ? Hin; *)
    (*                 simpl in Hin; *)
    (*                 intuition idtac; *)
    (*                 subst; *)
    (*                 unfold canCombine; *)
    (*                 simpl; *)
    (*                 intuition idtac; *)
    (*                 eauto; *)
    (*                 discriminate *)
    (*             | [ |- wellHidden _ _ ] => *)
    (*               unfold wellHidden, m, getCalls, getDefs, FMap.M.KeysDisj; *)
    (*                 simpl; *)
    (*                 FMap.mred; *)
    (*                 rewrite FMap.M.subtractKV_empty_1; *)
    (*                 intuition idtac; *)
    (*                 rewrite FMap.M.F.P.F.empty_in_iff in *; *)
    (*                 tauto *)
    (*             end. *)
    (*          ++ match goal with *)
    (*             | [ H : ForwardMultistep ?m ?o ?n ?l |- ForwardMultistep ?m ?o' ?n ?l ] => replace o' with o; [ assumption | idtac ] *)
    (*             end. *)
    (*             match goal with *)
    (*             | [ H : foldSSUpds _ = _ |- _ ] => rewrite H in * *)
    (*             end. *)
    (*             unfold foldSSUpds, upd. *)
    (*             unfold SCMemRegs. *)
    (*             FMap.mred. *)
    (*       -- econstructor; simpl; tauto. *)
    (*       -- subst. *)
    (*          simpl. *)
    (*          f_equal; try assumption. *)
    (*          f_equal. *)
    (*          FMap.M.ext k. *)
    (*          repeat rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity). *)
    (*          FMap.mred. *)
    (*       -- econstructor; try discriminate. *)
    (*          ++ match goal with *)
    (*             | [ |- Step ?m ?o _ {| annot := _; defs := FMap.M.add _ (existT _ _ (?av, ?rv)) _; calls := _ |} ] => *)
    (*               let ss := fresh in *)
    (*               simple refine (let ss := (_ : Substeps m o) in _); *)
    (*                 [ apply cons; *)
    (*                   [ exact (Build_SubstepRec (EmptyRule _ _)) *)
    (*                   | apply cons; [ idtac | apply nil ]]; *)
    (*                   eapply Build_SubstepRec; *)
    (*                   eapply SingleMeth; *)
    (*                   try (simpl; tauto); *)
    (*                   instantiate (4 := av); *)
    (*                   instantiate (1 := rv); *)
    (*                   eapply SemIfElseTrue; *)
    (*                   try match goal with *)
    (*                      | [ |- SemAction _ _ _ _ _ ] => repeat econstructor *)
    (*                       end; *)
    (*                   eauto *)
    (*                 | match goal with *)
    (*                   | [ |- Step ?m ?o _ ?l ] => replace l with (hide (foldSSLabel ss)) by reflexivity *)
    (*                   end *)
    (*                 ] *)
    (*             end. *)
    (*             apply StepIntro; repeat (apply AddSubstep || apply NilSubsteps); *)
    (*             match goal with *)
    (*             | [ |- forall _, In _ _ -> _ ] => *)
    (*               let Hin := fresh in *)
    (*               intros ? Hin; *)
    (*                 simpl in Hin; *)
    (*                 intuition idtac; *)
    (*                 subst; *)
    (*                 unfold canCombine; *)
    (*                 simpl; *)
    (*                 intuition idtac; *)
    (*                 eauto; *)
    (*                 discriminate *)
    (*             | [ |- wellHidden _ _ ] => *)
    (*               unfold wellHidden, m, getCalls, getDefs, FMap.M.KeysDisj; *)
    (*                 simpl; *)
    (*                 FMap.mred; *)
    (*                 rewrite FMap.M.subtractKV_empty_1; *)
    (*                 intuition idtac; *)
    (*                 rewrite FMap.M.F.P.F.empty_in_iff in *; *)
    (*                 tauto *)
    (*             end. *)
    (*          ++ match goal with *)
    (*             | [ H : ForwardMultistep ?m ?o ?n ?l |- ForwardMultistep ?m ?o' ?n ?l ] => replace o' with o; [ assumption | idtac ] *)
    (*             end. *)
    (*             match goal with *)
    (*             | [ H : foldSSUpds _ = _ |- _ ] => rewrite H in * *)
    (*             end. *)
    (*             unfold foldSSUpds, upd. *)
    (*             unfold SCMemRegs. *)
    (*             FMap.mred. *)
    (*       -- econstructor; simpl; tauto. *)
    (*       -- subst. *)
    (*          simpl. *)
    (*          f_equal; try assumption. *)
    (*          f_equal. *)
    (*          FMap.M.ext k. *)
    (*          repeat rewrite FMap.M.F.P.F.mapi_o by (intros; subst; reflexivity). *)
    (*          FMap.mred. *)
  Admitted.

  Theorem MemSpec : ThreeStageMemSpec m.
  Proof. admit.
    (* unfold ThreeStageMemSpec; induction 1; intros. *)
    (* - exists None. constructor. *)
    (* - match goal with *)
    (*   | [ H : Step _ _ _ _ |- _ ] => inv H *)
    (*   end. *)
    (*   match goal with *)
    (*   | [ H : substepsComb _ |- _ ] => *)
    (*     apply substepsComb_substepsInd in H; *)
    (*       apply ThreeStageMemSubsteps in H *)
    (*   end. *)
    (*   intuition idtac; shatter; subst; *)
    (*     try match goal with *)
    (*         | [ H : foldSSLabel ss = _ |- _ ] => rewrite H in * *)
    (*         end; *)
    (*     try match goal with *)
    (*         | [ H : foldSSUpds ss = _ |- _ ] => rewrite H in * *)
    (*         end; *)
    (*     unfold hide in *; *)
    (*     simpl in *; *)
    (*     subst. *)
    (*   + econstructor; FMap.findeq; apply IHForwardMultistep; reflexivity. *)
    (*   + econstructor; FMap.findeq; apply IHForwardMultistep; reflexivity. *)
    (*   + pose (Hrq := inv_rq x0). *)
    (*     destruct Hrq as [adr [op [dat Heqq]]]. *)
    (*     simpl in adr, op, dat. *)
    (*     subst. *)
    (*     destruct op; *)
    (*       kinv_action_dest; *)
    (*       match goal with *)
    (*       | [ H : _ |- _ ] => apply SCMemRegs_find_mem in H; subst *)
    (*       end; *)
    (*       match goal with *)
    (*       | [ H : foldSSUpds _ = _ |- _ ] => rewrite H in * *)
    (*       end; *)
    (*       simpl in *; *)
    (*       subst; *)
    (*       econstructor; *)
    (*       simpl; *)
    (*       repeat split; *)
    (*       try reflexivity; *)
    (*       try apply IHForwardMultistep; *)
    (*       eauto. *)
  Admitted.
  
  Theorem MemAirtight : forall oldregs newregs labels lastRq,
      ForwardMultistep m oldregs newregs labels ->
      ThreeStageMemLabelSeqAirtight labels lastRq.
  Proof. admit.
    (* induction 1; econstructor; eauto. *)
    (* match goal with *)
    (* | [ H : Step _ _ _ _ |- _ ] => inv H *)
    (* end. *)
    (* match goal with *)
    (* | [ H : substepsComb ss |- _ ] => apply substepsComb_substepsInd in H; apply ThreeStageMemSubsteps in H *)
    (* end. *)
    (* intuition idtac; shatter; subst; *)
    (*   match goal with *)
    (*   | [ H : foldSSLabel ss = _ |- _ ] => rewrite H in * *)
    (*   end; *)
    (*   unfold hide, annot, calls, defs; *)
    (*   repeat rewrite FMap.M.subtractKV_empty_1; *)
    (*   repeat rewrite FMap.M.subtractKV_empty_2; *)
    (*   try solve [ constructor ]. *)
    (* destruct (inv_rq x0) as [? [op [? ?]]]; destruct (inv_rs x1); subst; destruct op; try solve [ constructor ]. *)
    (* kinv_action_dest. *)
    (* match goal with *)
    (* | [ H : ?x = ?y |- _ ] => *)
    (*   let x' := fresh in *)
    (*   let y' := fresh in *)
    (*   remember x as x'; *)
    (*     remember y as y'; *)
    (*     assert (x' Fin.F1 = y' Fin.F1) by (rewrite H; reflexivity); *)
    (*     subst *)
    (* end. *)
    (* subst. *)
    (* constructor. *)
  Admitted.
  
End ThreeStageSingleModularHiding.

Module SCSingleHiding := SCHiding SCSingle SCSingleModularHiding.
Check SCSingleHiding.abstractToSCHiding.
