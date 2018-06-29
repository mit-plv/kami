Require Import Notations.
Require Import List.
Require Import Lib.Word Lib.Indexer Lib.FMap.
Require Import Kami.Syntax Kami.Semantics Kami.SymEvalTac Kami.Tactics Kami.ModularFacts Kami.SemFacts.
Require Import Ex.SC Ex.IsaRv32 Ex.ProcThreeStage Ex.OneEltFifo.
Require Import Ex.Timing.Specification.
Require Import Lib.CommonTactics.


Definition rv32iRq := RqFromProc rv32iAddrSize rv32iDataBytes.
Definition rv32iRs := RsToProc rv32iDataBytes.
  

Module Type ThreeStageInterface.

  Parameter p : Modules.
  Parameter m : Modules.

  Axiom pequiv : Wf.ModEquiv type typeUT p.
  Axiom mequiv : Wf.ModEquiv type typeUT m.
  Axiom reginits : FMap.DisjList (Struct.namesOf (getRegInits p))
                                 (Struct.namesOf (getRegInits m)).

  Axiom validRegs : Wf.ValidRegsModules type (p ++ m)%kami.

  Axiom defsDisj : FMap.DisjList (getDefs p) (getDefs m).
  Axiom callsDisj : FMap.DisjList (getCalls p) (getCalls m).

  Parameter ThreeStageProcRegs : regfile -> progMem -> address -> RegsT.
  Parameter ThreeStageMemRegs : memory -> data -> RegsT.

  Parameter fhMeth : String.string.
  Parameter thMeth : String.string.
  Parameter rqMeth : String.string.
  Parameter rsMeth : String.string.

  Axiom methsDistinct : fhMeth <> thMeth /\ thMeth <> rqMeth /\ rqMeth <> fhMeth /\ rqMeth <> rsMeth /\ thMeth <> rsMeth /\ rsMeth <> fhMeth.
  Axiom mdrq : In rqMeth (getDefs m).
  Axiom mdrs : In rsMeth (getDefs m).
  Axiom pcrq : In rqMeth (getCalls p).
  Axiom pcrs : In rsMeth (getCalls p).
  Axiom pcfh : In fhMeth (getCalls p).
  Axiom pcth : In thMeth (getCalls p).
  Axiom pndfh : ~ In fhMeth (getDefs p).
  Axiom mndfh : ~ In fhMeth (getDefs m).
  Axiom pndth : ~ In thMeth (getDefs p).
  Axiom mndth : ~ In thMeth (getDefs m).

  Axiom pRegs : forall rf pm pc, FMap.M.KeysSubset (ThreeStageProcRegs rf pm pc) (Struct.namesOf (getRegInits p)).
  Axiom mRegs : forall mem nextRs, FMap.M.KeysSubset (ThreeStageMemRegs mem nextRs) (Struct.namesOf (getRegInits m)).

  Axiom pRqRs : forall rf u l,
      Step p rf u l ->
      (FMap.M.find rqMeth (calls l) = None \/
       FMap.M.find rsMeth (calls l) = None).

  Axiom mRqRs : forall rp rm up um lp lm,
      Step p rp up lp ->
      Step m rm um lm ->
      WellHiddenConcat p m lp lm -> 
      (FMap.M.find rqMeth (defs lm) = None \/
       FMap.M.find rsMeth (defs lm) = None).


  
End ThreeStageInterface.

Module ThreeStageDefs (ThreeStage : ThreeStageInterface).
  Import ThreeStage.
  
  Definition censorThreeStageLabel (lastRq : option bool) censorMeth (l : LabelT) := censorLabel (censorMeth lastRq) l.
   
  Definition censorThreeStageMeth (lastRqOp : option bool) (n : String.string) (t : {x : SignatureT & SignT x}) : {x : SignatureT & SignT x} :=
    if String.string_dec n rqMeth
    then match t with
         | existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Bit 0 |}
                  (argV, retV) =>
           let op := evalExpr (#argV!rv32iRq@."op")%kami_expr in
           existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Bit 0 |}
                  (evalExpr (STRUCT {"addr" ::= #argV!rv32iRq@."addr";
                                       "op" ::=  #argV!rv32iRq@."op";
                                     "data" ::= if op
                                                then $0
                                                else #argV!rv32iRq@."data"})%kami_expr,
                   evalExpr ($$WO)%kami_expr)
         | _ => t
         end
    else if String.string_dec n rsMeth
         then match t with
         | existT _
                  {| arg := Bit 0;
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (argV, retV) =>
           existT _
                  {| arg := Bit 0;
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (evalExpr ($$WO)%kami_expr,
                   evalExpr (STRUCT {"data" ::= match lastRqOp with
                                                | Some op => if op
                                                           then #retV!rv32iRs@."data"
                                                           else $0
                                                | None => #retV!rv32iRs@."data"
                                                end})%kami_expr)
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

    Definition censorThreeStageMemDefs (lastRqOp : option bool) (n : String.string) (t : {x : SignatureT & SignT x}) : {x : SignatureT & SignT x} :=
    if String.string_dec n rqMeth
    then match t with
         | existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Bit 0 |}
                  (argV, retV) =>
           let op := evalExpr (#argV!rv32iRq@."op")%kami_expr in
           existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Bit 0 |}
                  (evalExpr (STRUCT {"addr" ::= #argV!rv32iRq@."addr";
                                     "op" ::=  #argV!rv32iRq@."op";
                                     "data" ::= if op
                                                then $0
                                                else #argV!rv32iRq@."data"})%kami_expr,
                   evalExpr ($$WO)%kami_expr)
         | _ => t
         end
    else if String.string_dec n rsMeth
         then match t with
         | existT _
                  {| arg := Bit 0;
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (argV, retV) =>
           existT _
                  {| arg := Bit 0;
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (evalExpr ($$WO)%kami_expr,
                   evalExpr (STRUCT {"data" ::= match lastRqOp with
                                                | Some op => if op
                                                            then #retV!rv32iRs@."data"
                                                            else $0
                                                | None => #retV!rv32iRs@."data"
                                                end})%kami_expr)
         | _ => t
              end
         else t.

  
  Definition getRqCall (lastRq : option bool) (l : LabelT) : option bool:=
    match FMap.M.find rqMeth (calls l) with
    | Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (argV, retV)) =>
      Some (evalExpr (#argV!rv32iRq@."op")%kami_expr)
    | _ => match FMap.M.find rsMeth (calls l) with
          | Some _ => None
          | None => lastRq  (* nothing memory-relevant happened this cycle *)
          end
    end.

  Definition getRqDef (lastRq : option bool) (l : LabelT) : option bool :=
    match FMap.M.find rqMeth (defs l) with
    | Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (argV, retV)) =>
      Some (evalExpr (#argV!rv32iRq@."op")%kami_expr)
    | _ => match FMap.M.find rsMeth (defs l) with
          | Some _ => None
          | None => lastRq
          end
    end.


  Fixpoint censorThreeStageLabelSeq (lastRq: option bool) getRqMeth censorMeth (ls : LabelSeqT) {struct ls} : LabelSeqT :=
    match ls with
    | nil => nil
    | l :: ls' => 
      (censorLabel (censorMeth lastRq) l) :: censorThreeStageLabelSeq (getRqMeth lastRq l) getRqMeth censorMeth ls'
    end.
      
  Inductive ThreeStageProcMemConsistent : LabelSeqT -> option (bool * address) -> memory -> Prop := (* unclear what this becomes if calls aren't well-balanced, or whether that matters *)
  | S3PMCnil : forall lastRq mem, ThreeStageProcMemConsistent nil lastRq mem
  | S3PMCrq : forall (lastRq :option(bool*address)) mem l last' mem' ls argV retV,
      (FMap.M.find rqMeth (calls l) = Some (existT _
                                                   {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                                                             "op" :: Bool;
                                                                             "data" :: Bit 32});
                                                      ret := Bit 0 |}
                                                   (argV, retV)) /\
       let addr := evalExpr (#argV!rv32iRq@."addr")%kami_expr in
       let argval := evalExpr (#argV!rv32iRq@."data")%kami_expr in
       let op := evalExpr (#argV!rv32iRq@."op")%kami_expr in
       last' = Some (op, addr) /\
       if op
       then mem' = (fun a => if weq a addr then argval else mem a) (* ST *)
       else mem' = mem (* LD *)) ->
      ThreeStageProcMemConsistent ls last' mem' ->
      ThreeStageProcMemConsistent (l :: ls) lastRq mem
  | S3PMCrs : forall (lastRq :option(bool*address)) mem l last' mem' ls argV retV,
      (FMap.M.find rsMeth (calls l) = Some (existT _
                                                   {| arg := Bit 0;
                                                      ret := Struct (STRUCT {"data" :: Bit 32})|}
                                                   (argV, retV)) /\
       last' = None /\ 
       match lastRq with
       | Some (op, addr) =>
         if op
         then (* previous request was a ST *)
           mem' = mem (* we already did the update immediately upon getting the request *)
         else (* previous request was "LD addr" *)
           let retval := evalExpr (#retV!rv32iRs@."data")%kami_expr in
           mem' = mem /\ mem addr = retval
       | _ => (* this is the non-well-balanced case, not sure what goes here *)
         mem' = mem 
       end) ->
      ThreeStageProcMemConsistent ls last' mem' ->
      ThreeStageProcMemConsistent (l :: ls) lastRq mem
  | S3PMCcons : forall (lastRq :option(bool*address)) mem l last' mem' ls, 
      (FMap.M.find rqMeth (calls l) = None
       /\ FMap.M.find rsMeth (calls l) = None
       /\ mem' = mem /\ last' = lastRq) -> 
      ThreeStageProcMemConsistent ls last' mem' ->
      ThreeStageProcMemConsistent (l :: ls) lastRq mem.
  
  Definition ThreeStageProcHiding m (lastRq : option (bool * address)) regs mem : Prop := 
    forall labels newRegs fhs,
      ForwardMultistep m regs newRegs labels ->
      ThreeStageProcMemConsistent labels lastRq mem ->
      extractFhLabelSeq fhMeth labels = fhs ->
      forall fhs',
        length fhs = length fhs' ->
        exists labels' newRegs',
          ForwardMultistep m regs newRegs' labels' /\
          ThreeStageProcMemConsistent labels' lastRq mem /\
          censorThreeStageLabelSeq (option_map fst lastRq) getRqCall censorThreeStageMeth labels = censorThreeStageLabelSeq (option_map fst lastRq) getRqCall censorThreeStageMeth labels' /\
          extractFhLabelSeq fhMeth labels' = fhs'.

  Definition ThreeStageProcLabelAirtight (l : LabelT) : Prop :=
    match FMap.M.find rqMeth (calls l) with
    | Some (existT _
                   {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                             "op" :: Bool; 
                                             "data" :: Bit 32});
                      ret := Bit 0 |}
                   (argV, _)) =>
      if evalExpr (#argV!rv32iRq@."op")%kami_expr
      then True (* ST *)
      else evalExpr (#argV!rv32iRq@."data")%kami_expr = $0 (* LD *)
    | _ => True
    end. (* Guarantees the _processor_ doesn't leak over the unused fields. *)
  
  Definition ThreeStageProcLabelSeqAirtight : LabelSeqT -> Prop := Forall ThreeStageProcLabelAirtight.


  Definition extractMethsWrVals (ms : MethsT) : list (word 32) :=
    match FMap.M.find rqMeth ms with
    | Some (existT _
                   {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                             "op" :: Bool;
                                             "data" :: Bit 32});
                      ret := Bit 0 |}
                   (argV, retV)) =>
      if evalExpr (#argV!rv32iRq@."op")%kami_expr
      then [evalExpr (#argV!rv32iRq@."data")%kami_expr]
      else nil
    | _ => nil
    end.

  Definition extractMethsRdVals (lastRq : option bool) (ms : MethsT) : list (word 32) :=
    match FMap.M.find rsMeth ms with
    | Some (existT _
                   {| arg := Bit 0;
                      ret := Struct (STRUCT {"data" :: Bit 32}) |}
                   (argV, retV)) =>
      match lastRq with
      | Some op => 
        if op
        then nil
        else [evalExpr (#retV!rv32iRs@."data")%kami_expr]
      | _ => nil
      end
    | _ => nil
    end.
  
  Definition extractProcWrValSeq : LabelSeqT -> list (word 32) :=
    flat_map (fun l => extractMethsWrVals (calls l)).
  
  Definition extractMemWrValSeq : LabelSeqT -> list (word 32) :=
    flat_map (fun l => extractMethsWrVals (defs l)).

  Fixpoint extractProcRdValSeq (lastRq : option bool) (ls :  LabelSeqT) : list (word 32) :=
    match ls with
    | nil => nil
    | l :: ls' => (extractMethsRdVals lastRq (calls l)) ++ extractProcRdValSeq (getRqCall lastRq l) ls' 
    end.


  Fixpoint extractMemRdValSeq (lastRq : option bool) (ls :  LabelSeqT) : list (word 32) :=
    match ls with
    | nil => nil
    | l :: ls' => (extractMethsRdVals lastRq (defs l)) ++ extractMemRdValSeq (getRqDef lastRq l) ls' 
    end.
  
  Inductive ThreeStageMemMemConsistent : LabelSeqT -> option (bool * address) -> memory -> Prop := 
  | S3MMCnil : forall lastRq mem, ThreeStageMemMemConsistent nil lastRq mem
  | S3MMCrq : forall (lastRq:option(bool*address)) mem l last' mem' ls argV retV,
      (FMap.M.find rqMeth (defs l) = Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (argV, retV)) /\
                    let addr := evalExpr (#argV!rv32iRq@."addr")%kami_expr in
                    let argval := evalExpr (#argV!rv32iRq@."data")%kami_expr in
                    let op := evalExpr (#argV!rv32iRq@."op")%kami_expr in
                    last' = Some (op, addr) /\
                    if op
                    then mem' = (fun a => if weq a addr then argval else mem a) (* ST *)
                    else mem' = mem (* LD *)
      ) ->
      ThreeStageMemMemConsistent ls last' mem' ->
      ThreeStageMemMemConsistent (l :: ls) lastRq mem
  | S3MMCrs : forall (lastRq:option(bool*address)) mem l last' mem' ls argV retV,
      (FMap.M.find rsMeth (defs l) = Some (existT _
                                                  {| arg := Bit 0;
                                                     ret := Struct (STRUCT {"data" :: Bit 32})|}
                                                  (argV, retV)) /\
       last' = None /\ match lastRq with
                      | Some (op, addr) =>
                        if op
                        then (* previous request was a ST *)
                          mem' = mem (* we already did the update immediately upon getting the request *)
                        else (* previous request was "LD addr" *)
                          let retval := evalExpr (#retV!rv32iRs@."data")%kami_expr in
                          mem' = mem /\ mem addr = retval
                      | _ => (* this is the non-well-balanced case, not sure what goes here *)
                        mem' = mem 
                      end)      ->
      ThreeStageMemMemConsistent ls last' mem' ->
      ThreeStageMemMemConsistent (l :: ls) lastRq mem
  | S3MMCcons : forall (lastRq :option(bool*address)) mem l last' mem' ls,
      (FMap.M.find rqMeth (defs l) = None /\ FMap.M.find rsMeth (defs l) = None /\
       mem' = mem /\ last' = lastRq)
      ->
      ThreeStageMemMemConsistent ls last' mem' ->
      ThreeStageMemMemConsistent (l :: ls) lastRq mem.

  Definition ThreeStageMemHiding m : Prop :=
    forall mem lastRq nextRs labels newRegs,
      ThreeStageMemMemConsistent labels lastRq mem ->
      (* compatibility between lastRq and nextRs? *)
      ForwardMultistep m (ThreeStageMemRegs mem nextRs) newRegs labels ->
      forall wrs,
        extractMemWrValSeq labels = wrs ->
        forall mem' nextRs' wrs',
          length wrs = length wrs' ->
          (* compatibility between lastRq and nextRs'? *)
          exists labels' newRegs',
            ForwardMultistep m (ThreeStageMemRegs mem' nextRs') newRegs' labels' /\
            ThreeStageMemMemConsistent labels' lastRq mem' /\
            censorThreeStageLabelSeq (option_map fst lastRq) getRqDef censorThreeStageMemDefs labels = censorThreeStageLabelSeq  (option_map fst lastRq) getRqDef censorThreeStageMemDefs labels' /\
            extractMemWrValSeq labels' = wrs'.

  Definition ThreeStageMemSpec m : Prop :=
    forall oldRegs newRegs labels,
      ForwardMultistep m oldRegs newRegs labels ->
      forall mem nextRs,
        oldRegs = ThreeStageMemRegs mem nextRs ->
        exists lastRq,  (* compatibility? *)
        ThreeStageMemMemConsistent labels lastRq mem.

  Inductive ThreeStageMemLabelSeqAirtight : LabelSeqT -> option bool -> Prop :=
  | S3MLSAnil : forall lastRq, ThreeStageMemLabelSeqAirtight nil lastRq
  | S3MLSAcons : forall l ls (lastRq :option bool) last', (
      (exists argV retV, FMap.M.find rqMeth (defs l) = Some (existT _
                                                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                                                            "op" :: Bool;
                                                                            "data" :: Bit 32});
                                                     ret := Bit 0 |}
                                                  (argV, retV))
                    /\ let op := evalExpr (#argV!rv32iRq@."op")%kami_expr in
                      last' = Some op
      ) \/ (
        exists argV retV, FMap.M.find rsMeth (defs l) = Some (existT _
                                                                {| arg := Bit 0;
                                                                   ret := Struct (STRUCT {"data" :: Bit 32})|}
                                                                (argV, retV))
                     /\ last' = None /\
                     match lastRq with
                     | Some op =>
                       if op then evalExpr (#retV!rv32iRs@."data")%kami_expr = $0 else True
                     | _ => evalExpr (#retV!rv32iRs@."data")%kami_expr = $0  (* being cautious *)
                     end
      ) \/ (
        FMap.M.find rqMeth (defs l) = None /\ FMap.M.find rsMeth (defs l) = None /\ last' = lastRq
      )) -> 
      ThreeStageMemLabelSeqAirtight ls last' ->
      ThreeStageMemLabelSeqAirtight (l :: ls) lastRq.
  
End ThreeStageDefs.

Module Type ThreeStageModularHiding (ThreeStage : ThreeStageInterface).
  Module Defs := ThreeStageDefs ThreeStage.
  Import ThreeStage Defs.

  Axiom abstractToProcHiding :
    forall lastRq rf pm pc mem,
      abstractHiding rf pm pc mem ->
      ThreeStageProcHiding p lastRq (ThreeStageProcRegs rf pm pc) mem.

  
  Axiom ProcAirtight : forall oldregs newregs labels,
      ForwardMultistep p oldregs newregs labels ->
      ThreeStageProcLabelSeqAirtight labels.
  
  Axiom MemHiding : ThreeStageMemHiding m.

  Axiom MemSpec : ThreeStageMemSpec m.

  Axiom MemAirtight : forall oldregs newregs labels,
      ForwardMultistep m oldregs newregs labels ->
      ThreeStageMemLabelSeqAirtight labels None.

End ThreeStageModularHiding.
