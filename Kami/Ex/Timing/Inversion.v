Require Import Notations.
Require Import List.
Require Import Lib.Word Lib.Indexer Lib.FMap.
Require Import Kami.Syntax Kami.Semantics Kami.SymEvalTac Kami.Tactics Kami.ModularFacts Kami.SemFacts.
Require Import Ex.SC Ex.IsaRv32 Ex.ProcThreeStage Ex.OneEltFifo.
Require Import Ex.Timing.Specification.
Require Import Lib.CommonTactics.



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
  Parameter ThreeStageMemRegs : memory -> RegsT.

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
  Axiom mRegs : forall mem, FMap.M.KeysSubset (ThreeStageMemRegs mem) (Struct.namesOf (getRegInits m)).

  Axiom pRqRs : forall rf u l,
      Step p rf u l ->
      (FMap.M.find rqMeth (calls l) = None \/
       FMap.M.find rsMeth (calls l) = None).

  Axiom mRqRs : forall rf u l,
      Step m rf u l ->
      (FMap.M.find rqMeth (defs l) = None \/
       FMap.M.find rsMeth (defs l) = None).

End ThreeStageInterface.

Module Inversions (ThreeStage : ThreeStageInterface).
  Import ThreeStage.
  Definition rv32iRq := RqFromProc rv32iAddrSize rv32iDataBytes.
  Definition rv32iRs := RsToProc rv32iDataBytes.

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

  Lemma inv_none :
    forall r : type (Bit 0),
      r = evalExpr ($$WO)%kami_expr.
  Proof.
    intros.
    simpl in *.
    apply word0.
  Qed.

  Lemma inv_some : forall A (x y : A), Some x = Some y -> x = y.
  Proof.
    intros; congruence.
  Qed.

  Ltac inv_some :=
    match goal with
    | [ H : Some _ = Some _ |- _ ] => apply inv_some in H
    end.

  Lemma inv_censor_rq_calls : forall lastRq l l',
      censorThreeStageLabel lastRq censorThreeStageMeth l = l' ->
      FMap.M.find rqMeth (calls l) = FMap.M.find rqMeth (calls l') \/
      exists adr op arg,
        FMap.M.find rqMeth (calls l) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (calls l') = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= if op then $0 else #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)).
  Proof.
    intros lastRq l l' H.
    destruct l. destruct l'.
    pose methsDistinct. shatter.
    unfold censorThreeStageLabel, censorLabel, censorThreeStageMeth in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f calls = calls0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find rqMeth (FMap.M.mapi f calls) = FMap.M.find rqMeth calls0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind
    end.
    unfold Semantics.calls, Semantics.defs in *.
    remember (FMap.M.find rqMeth calls0) as e' eqn:He'.
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
    pose (Hrs := inv_none t0).
    destruct Hrq as [adr [op [dat Heqq]]].
    exists adr, op, dat.
    subst.
    destruct op; tauto.
  Qed.

  
  Lemma inv_censor_rq_calls_as_defs : forall lastRq l l',
      censorThreeStageLabel lastRq censorThreeStageMeth l = l' ->
      FMap.M.find rqMeth (defs l) = FMap.M.find rqMeth (defs l') \/
      exists adr op arg,
        FMap.M.find rqMeth (defs l) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (defs l') = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= if op then $0 else #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)).
  Proof.
    intros lastRq l l' H.
    destruct l. destruct l'.
    pose methsDistinct. shatter.
    unfold censorThreeStageLabel, censorLabel, censorThreeStageMeth in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f defs = defs0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find rqMeth (FMap.M.mapi f defs) = FMap.M.find rqMeth defs0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind
    end.
    unfold Semantics.calls, Semantics.defs in *.
    remember (FMap.M.find rqMeth defs0) as e' eqn:He'.
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
    pose (Hrs := inv_none t0).
    destruct Hrq as [adr [op [dat Heqq]]].
    exists adr, op, dat.
    subst.
    destruct op; tauto.
  Qed.


  Lemma inv_censor_rs_calls : forall lastRq l l',
      censorThreeStageLabel lastRq censorThreeStageMeth l = l' ->
      FMap.M.find rsMeth (calls l) = FMap.M.find rsMeth (calls l') \/
      exists arg,
        FMap.M.find rsMeth (calls l) = 
        Some (existT _
                     {| arg := Bit 0;
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr ($$WO)%kami_expr,
                      evalExpr (STRUCT { "data" ::= #arg })%kami_expr)) /\
        FMap.M.find rsMeth (calls l') = 
        Some (existT _
                     {| arg := Bit 0;
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr ($$WO)%kami_expr,
                      evalExpr (STRUCT {"data" ::=
                                          match lastRq with
                                          | Some op => if op then #arg else $0
                                          | None => #arg
                                          end})%kami_expr)).
  Proof.
    intros lastRq l l' H.
    destruct l. destruct l'.
    pose methsDistinct. shatter.
    unfold censorThreeStageLabel, censorLabel, censorThreeStageMeth in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f calls = calls0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find rsMeth (FMap.M.mapi f calls) = FMap.M.find rsMeth calls0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind
    end.
    unfold Semantics.calls, Semantics.defs in *.
    remember (FMap.M.find rsMeth calls0) as e' eqn:He'.
    clear He'.
    match goal with
    | [ H : match ?x with | _ => _ end = _ |- _ ] => destruct x
    end; try solve [ left; assumption ].
    match goal with
    | [ H : Some _ = ?e |- _ ] => destruct e; [inv_some | discriminate]
    end.
    repeat (match goal with
    | [ H : (if ?x then _ else _) = _ |- _ ] => destruct x
    end; try solve [ pose methsDistinct; intuition congruence ]).
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
    pose (Hrq := inv_none t).
    pose (Hrs := inv_rs t0).
    destruct Hrs as [dat Heqq].
    exists dat.
    subst.
    split; [reflexivity|
            destruct lastRq; [|reflexivity]].    
    match goal with
    | [ |- context[(@existT SignatureT (fun x : SignatureT => SignT x))] ] => replace ((@existT SignatureT (fun x : SignatureT => SignT x))) with ((@existT SignatureT SignT)) by reflexivity
    end.
    destruct b; reflexivity.
  Qed.


  
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

  
  Lemma inv_censor_rq_memdefs : forall lastRq l l',
      censorThreeStageLabel lastRq censorThreeStageMemDefs l = l' ->
      FMap.M.find rqMeth (defs l) = FMap.M.find rqMeth (defs l') \/
      exists adr op arg,
        FMap.M.find rqMeth (defs l) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (defs l') = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= if op then $0 else #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)).
  Proof.
    intros lastRq l l' H.
    destruct l. destruct l'.
    pose methsDistinct. shatter.
    unfold censorThreeStageLabel, censorLabel, censorThreeStageMemDefs in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f defs = defs0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find rqMeth (FMap.M.mapi f defs) = FMap.M.find rqMeth defs0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind
    end.
    unfold Semantics.calls, Semantics.defs in *.
    remember (FMap.M.find rqMeth defs0) as e' eqn:He'.
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
    | [ x : SignT _ |- _ ] => destruct x
    end.
    unfold arg, ret in *.
    right.
    subst.
    pose (Hrq := inv_rq t).
    pose (Hrs := inv_none t0).
    destruct Hrq as [adr [op [dat Heqq]]].
    exists adr, op, dat.
    subst.
    destruct op; tauto.
  Qed.
  
  Lemma inv_censor_rs_memdefs : forall lastRq l l',
      censorThreeStageLabel lastRq censorThreeStageMemDefs l = l' ->
      FMap.M.find rsMeth (defs l) = FMap.M.find rsMeth (defs l') \/
      exists arg,
        FMap.M.find rsMeth (defs l) = 
        Some (existT _
                     {| arg := Bit 0;
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr ($$WO)%kami_expr,
                      evalExpr (STRUCT { "data" ::= #arg })%kami_expr)) /\
        FMap.M.find rsMeth (defs l') = 
        Some (existT _
                     {| arg := Bit 0;
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}                   (evalExpr ($$WO)%kami_expr,
                                                                                        evalExpr (STRUCT {"data" ::= match lastRq with
                                                                                                                     | Some op => if op then #arg else $0
                                                                                                                     | None => #arg
                                                                                                                     end})%kami_expr)).
  Proof.
    intros lastRq l l' H.
    destruct l. destruct l'.
    pose methsDistinct. shatter.
    unfold censorThreeStageLabel, censorLabel, censorThreeStageMemDefs in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f defs = defs0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find rsMeth (FMap.M.mapi f defs) = FMap.M.find rsMeth defs0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind
    end.
    unfold Semantics.calls, Semantics.defs in *.
    remember (FMap.M.find rsMeth defs0) as e' eqn:He'.
    clear He'.
    match goal with
    | [ H : match ?x with | _ => _ end = _ |- _ ] => destruct x
    end; try solve [ left; assumption ].
    match goal with
    | [ H : Some _ = ?e |- _ ] => destruct e; [inv_some | discriminate]
    end.
    repeat (match goal with
    | [ H : (if ?x then _ else _) = _ |- _ ] => destruct x
    end; try solve [ pose methsDistinct; intuition congruence ]).
    repeat match goal with
    | [ s : {_ : _ & _} |- _ ] => destruct s
    end.
    repeat (match goal with
            | [ H : match ?x with | _ => _ end _ = _ |- _ ] => destruct x
            end; try solve [ left; f_equal; assumption ]).
    match goal with
    | [ x : SignT _ |- _ ] => destruct x
    end.
    unfold arg, ret in *.
    right.
    subst.
    pose (Hrq := inv_none t).
    pose (Hrs := inv_rs t0).
    destruct Hrs as [dat Heqq].
    exists dat.
    subst.
        split; [reflexivity|
            destruct lastRq; [|reflexivity]].    
    match goal with
    | [ |- context[(@existT SignatureT (fun x : SignatureT => SignT x))] ] => replace ((@existT SignatureT (fun x : SignatureT => SignT x))) with ((@existT SignatureT SignT)) by reflexivity
    end.
    destruct b; reflexivity.
  Qed.


  Lemma inv_pair : forall A B (x1 x2 : A) (y1 y2 : B), (x1, y1) = (x2, y2) -> x1 = x2 /\ y1 = y2.
  Proof.
    intros.
    inv H.
    tauto.
  Qed.

  Ltac inv_rq_eq := 
    match goal with
    | [ H : Some (existT _ _ (?q1, ?s1)) = Some (existT _ _ (?q2, ?s2)) |- _ ] =>
      apply inv_some in H;
      apply Semantics.sigT_eq in H;
      let Heqa := fresh in
      let Heqo := fresh in
      let Heqd := fresh in
      let Hdiscard := fresh in
      assert (evalExpr (#(q1)!rv32iRq@."addr")%kami_expr = evalExpr (#(q2)!rv32iRq@."addr")%kami_expr) as Heqa by (apply inv_pair in H; destruct H as [Hdiscard _]; rewrite Hdiscard; reflexivity);
      assert (evalExpr (#(q1)!rv32iRq@."op")%kami_expr = evalExpr (#(q2)!rv32iRq@."op")%kami_expr) as Heqo by (apply inv_pair in H; destruct H as [Hdiscard _]; rewrite Hdiscard; reflexivity);
      assert (evalExpr (#(q1)!rv32iRq@."data")%kami_expr = evalExpr (#(q2)!rv32iRq@."data")%kami_expr) as Heqd by (apply inv_pair in H; destruct H as [Hdiscard _]; rewrite Hdiscard; reflexivity);
      simpl in Heqa;
      simpl in Heqo;
      simpl in Heqd;
      subst;
      clear H
    end.
  
  Ltac inv_rs_eq := 
    match goal with
    | [ H : Some (existT _ _ (?q1, ?s1)) = Some (existT _ _ (?q2, ?s2)) |- _ ] =>
      apply inv_some in H;
      apply Semantics.sigT_eq in H;
      let Heqd := fresh in
      let Hdiscard := fresh in
      assert (evalExpr (#(s1)!rv32iRs@."data")%kami_expr = evalExpr (#(s2)!rv32iRs@."data")%kami_expr) as Heqd by (apply inv_pair in H; destruct H as [_ Hdiscard]; rewrite Hdiscard; reflexivity);
      simpl in Heqd;
      subst;
      clear H
    end.

  Lemma inv_censoreq_rq_calls : forall lastRq la lb,
      censorThreeStageLabel lastRq censorThreeStageMeth la = censorThreeStageLabel lastRq censorThreeStageMeth lb ->
      FMap.M.find rqMeth (calls la) = FMap.M.find rqMeth (calls lb) \/
      exists adr op arg arg',
        FMap.M.find rqMeth (calls la) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (calls lb) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg' })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\ if op then True else arg = arg'. 
  Proof.
    intros lastRq la lb H.
    destruct (inv_censor_rq_calls lastRq la _ eq_refl) as [Haeq | [adra [opa [arga [Ha Hac]]]]];
      destruct (inv_censor_rq_calls lastRq lb _ eq_refl) as [Hbeq | [adrb [opb [argb [Hb Hbc]]]]].
    - left.
      congruence.
    - right.
      rewrite H in Haeq.
      rewrite Hbc in Haeq.
      exists adrb, opb.
      destruct opb.
      + exists $0, argb.
        eauto.
      + exists argb, argb.
        eauto.
    - right.
      rewrite <- H in Hbeq.
      rewrite Hac in Hbeq.
      exists adra, opa.
      destruct opa.
      + exists arga, $0. eauto.
      + exists arga, arga. eauto.
    - right.
      rewrite H in Hac.
      rewrite Hbc in Hac.
      inv_rq_eq.    
      exists adra, opa.
      destruct opa;
      repeat match goal with
             | [ H : evalExpr _ = evalExpr _ |- _ ] => simpl in H
             end;
      subst;
      repeat eexists;
      eauto.
  Qed.


  Lemma inv_censoreq_rq_calls_as_defs : forall lastRq la lb,
      censorThreeStageLabel lastRq censorThreeStageMeth la = censorThreeStageLabel lastRq censorThreeStageMeth lb ->
      FMap.M.find rqMeth (defs la) = FMap.M.find rqMeth (defs lb) \/
      exists adr op arg arg',
        FMap.M.find rqMeth (defs la) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (defs lb) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg' })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\ if op then True else arg = arg'. 
  Proof.
    intros lastRq la lb H.
    destruct (inv_censor_rq_calls_as_defs lastRq la _ eq_refl) as [Haeq | [adra [opa [arga [Ha Hac]]]]];
      destruct (inv_censor_rq_calls_as_defs lastRq lb _ eq_refl) as [Hbeq | [adrb [opb [argb [Hb Hbc]]]]].
    - left.
      congruence.
    - right.
      rewrite H in Haeq.
      rewrite Hbc in Haeq.
      exists adrb, opb.
      destruct opb.
      + exists $0, argb.
        eauto.
      + exists argb, argb.
        eauto.
    - right.
      rewrite <- H in Hbeq.
      rewrite Hac in Hbeq.
      exists adra, opa.
      destruct opa.
      + exists arga, $0. eauto.
      + exists arga, arga. eauto.
    - right.
      rewrite H in Hac.
      rewrite Hbc in Hac.
      inv_rq_eq.    
      exists adra, opa.
      destruct opa;
      repeat match goal with
             | [ H : evalExpr _ = evalExpr _ |- _ ] => simpl in H
             end;
      subst;
      repeat eexists;
      eauto.
  Qed.

  
    Lemma inv_censoreq_rs_calls : forall lastRq la lb,
      censorThreeStageLabel lastRq censorThreeStageMeth la = censorThreeStageLabel lastRq censorThreeStageMeth lb ->
      FMap.M.find rsMeth (calls la) = FMap.M.find rsMeth (calls lb) \/
      exists arg arg',
        FMap.M.find rsMeth (calls la) = 
        Some (existT _
                     {| arg := Bit 0;
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr ($$WO)%kami_expr,
                      evalExpr (STRUCT {"data" ::= #arg })%kami_expr)) /\
        FMap.M.find rsMeth (calls lb) = 
        Some (existT _
                     {| arg := Bit 0;
                        ret := Struct (STRUCT { "data" :: Bit 32}) |}
                     ((evalExpr ($$WO)%kami_expr),
                      evalExpr (STRUCT { "data" ::= #arg' })%kami_expr)) /\
              match lastRq with
                  | Some op => if op then arg = arg' else True
                  | None => arg = arg'
              end. 
  Proof.
    intros lastRq la lb H.
    destruct (inv_censor_rs_calls lastRq la _ eq_refl) as [Haeq | [arga [Ha Hac]]];
      destruct (inv_censor_rs_calls lastRq lb _ eq_refl) as [Hbeq | [argb [Hb Hbc]]].
    - left.
      congruence.
    - right.
      rewrite H in Haeq.
      rewrite Hbc in Haeq.
      destruct lastRq; [destruct b|].
      + exists argb, argb.
        eauto.
      + exists $0, argb.
        eauto.
      + exists argb, argb.
        eauto.
    - right.
      rewrite <- H in Hbeq.
      rewrite Hac in Hbeq.
      destruct lastRq; [destruct b|].
      + exists arga, arga. eauto.
      + exists arga, $0. eauto.
      + exists arga, arga. eauto.
    - right.
      rewrite H in Hac.
      rewrite Hbc in Hac.
      inv_rs_eq.    
      destruct lastRq; try match goal with
                           | [ b : bool |- _ ] => destruct b
                           end;
      repeat match goal with
             | [ H : evalExpr _ = evalExpr _ |- _ ] => simpl in H
             end;
      subst;
      repeat eexists;
      eauto.
  Qed.

  Lemma inv_censoreq_rq_memdefs : forall lastRq la lb,
      censorThreeStageLabel lastRq censorThreeStageMemDefs la = censorThreeStageLabel lastRq censorThreeStageMemDefs lb ->
      FMap.M.find rqMeth (defs la) = FMap.M.find rqMeth (defs lb) \/
      exists adr op arg arg',
        FMap.M.find rqMeth (defs la) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (defs lb) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg' })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\ if op then True else arg = arg'.
  Proof.
    intros lastRq la lb H.
    destruct (inv_censor_rq_memdefs lastRq la _ eq_refl) as [Haeq | [adra [opa [arga [Ha Hac]]]]];
      destruct (inv_censor_rq_memdefs lastRq lb _ eq_refl) as [Hbeq | [adrb [opb [argb [Hb Hbc]]]]].
    - left.
      congruence.
    - right.
      rewrite H in Haeq.
      rewrite Hbc in Haeq.
      exists adrb, opb.
      destruct opb.
      + exists $0, argb.
        eauto.
      + exists argb, argb.
        eauto.
    - right.
      rewrite <- H in Hbeq.
      rewrite Hac in Hbeq.
      exists adra, opa.
      destruct opa.
      + exists arga, $0. eauto.
      + exists arga, arga. eauto.
    - right.
      rewrite H in Hac.
      rewrite Hbc in Hac.
      inv_rq_eq.
      exists adra, opa.
      destruct opa;
      repeat match goal with
             | [ H : evalExpr _ = evalExpr _ |- _ ] => simpl in H
             end;
      subst;
      repeat eexists;
      eauto.
  Qed.
  
  
  Lemma inv_censoreq_rs_memdefs : forall lastRq la lb,
      censorThreeStageLabel lastRq censorThreeStageMemDefs la = censorThreeStageLabel lastRq censorThreeStageMemDefs lb ->
      FMap.M.find rsMeth (defs la) = FMap.M.find rsMeth (defs lb) \/
      exists arg arg',
        FMap.M.find rsMeth (defs la) = 
        Some (existT _
                     {| arg := Bit 0;
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr ($$WO)%kami_expr,
                      evalExpr (STRUCT {"data" ::= #arg })%kami_expr)) /\
        FMap.M.find rsMeth (defs lb) = 
        Some (existT _
                     {| arg := Bit 0;
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr ($$WO)%kami_expr,
                      evalExpr (STRUCT { "data" ::= #arg' })%kami_expr)) /\
        match lastRq with
        | Some op => if op then arg = arg' else True
        | None => arg = arg'
        end.
  Proof.
    intros lastRq la lb H.
    destruct (inv_censor_rs_memdefs lastRq la _ eq_refl) as [Haeq | [arga [Ha Hac]]];
      destruct (inv_censor_rs_memdefs lastRq lb _ eq_refl) as [Hbeq | [argb [Hb Hbc]]].
    - left.
      congruence.
    - right.
      rewrite H in Haeq.
      rewrite Hbc in Haeq.      
      destruct lastRq; [destruct b|].
      + exists argb, argb.
        eauto.
      + exists $0, argb.
        eauto.
      + exists argb, argb.
        eauto.
    - right.
      rewrite <- H in Hbeq.
      rewrite Hac in Hbeq.
      destruct lastRq; [destruct b|].
      + exists arga, arga. eauto.
      + exists arga, $0. eauto.
      + exists arga, arga. eauto.
    - right.
      rewrite H in Hac.
      rewrite Hbc in Hac.
      inv_rs_eq.
      destruct lastRq; [destruct b|];
      repeat match goal with
             | [ H : evalExpr _ = evalExpr _ |- _ ] => simpl in H
             end;
      subst;
      repeat eexists;
      eauto.
  Qed.
  
  Lemma inv_censor_rq_calls_with_mem : forall lastRq l l' mem mem',
      censorThreeStageLabel lastRq censorThreeStageMeth l = l' ->
      match FMap.M.find rqMeth (calls l) with
      | Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (argV, retV)) =>
        let addr := evalExpr (#argV!rv32iRq@."addr")%kami_expr in
        let argval := evalExpr (#argV!rv32iRq@."data")%kami_expr in
        if evalExpr (#argV!rv32iRq@."op")%kami_expr
        then mem' = (fun a => if weq a addr then argval else mem a)
        else mem' = mem
      | _ => mem' = mem
      end ->
      (FMap.M.find rqMeth (calls l) = FMap.M.find rqMeth (calls l') /\ mem' = mem) \/
      exists adr op arg,
        FMap.M.find rqMeth (calls l) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (calls l') = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= if op then $0 else #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)).
  Proof.
    intros lastRq l l' mem mem' H Hmem.
    destruct l. destruct l'.
    pose methsDistinct. shatter.
    unfold censorThreeStageMeth, censorThreeStageLabel, censorLabel in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f calls = calls0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find rqMeth (FMap.M.mapi f calls) = FMap.M.find rqMeth calls0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind Hmem
    end.
    unfold Semantics.calls, Semantics.defs in *.
    remember (FMap.M.find rqMeth calls0) as e' eqn:He'.
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
    pose (Hrs := inv_none t0).
    destruct Hrq as [adr [op [dat Heqq]]].
    exists adr, op, dat.
    subst.
    destruct op; tauto.
  Qed.

  Lemma inv_censor_rq_memdefs_with_mem : forall lastRq l l' mem mem',
      censorThreeStageLabel lastRq censorThreeStageMemDefs l = l' ->
      match FMap.M.find rqMeth (defs l) with
      | Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (argV, retV)) =>
        let addr := evalExpr (#argV!rv32iRq@."addr")%kami_expr in
        let argval := evalExpr (#argV!rv32iRq@."data")%kami_expr in
        if evalExpr (#argV!rv32iRq@."op")%kami_expr
        then mem' = (fun a => if weq a addr then argval else mem a)
        else mem' = mem
      | _ => mem' = mem
      end ->
      (FMap.M.find rqMeth (defs l) = FMap.M.find rqMeth (defs l') /\ mem' = mem) \/
      exists adr op arg,
        FMap.M.find rqMeth (defs l) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (defs l') = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= if op then $0 else #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)).
  Proof.
    intros lastRq l l' mem mem' H Hmem.
    destruct l. destruct l'.
    pose methsDistinct. shatter.
    unfold censorThreeStageLabel, censorLabel, censorThreeStageMemDefs in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f defs = defs0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find rqMeth (FMap.M.mapi f defs) = FMap.M.find rqMeth defs0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind Hmem
    end.
    unfold Semantics.calls, Semantics.defs in *.
    remember (FMap.M.find rqMeth defs0) as e' eqn:He'.
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
    pose (Hrs := inv_none t0).
    destruct Hrq as [adr [op [dat Heqq]]].
    exists adr, op, dat.
    subst.
    destruct op; tauto.
  Qed.

  Lemma inv_censor_other_calls : forall lastRq l l' meth,
      censorThreeStageLabel lastRq censorThreeStageMeth l = l' ->
      meth <> rqMeth ->
      meth <> rsMeth ->
      meth <> fhMeth ->
      meth <> thMeth ->
      FMap.M.find meth (calls l) = FMap.M.find meth (calls l').
  Proof.
    intros lastRq l l' meth H He Hs Hf Ht.
    destruct l. destruct l'.
    unfold censorThreeStageLabel, censorLabel, censorThreeStageMeth in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f calls = calls0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find meth (FMap.M.mapi f calls) = FMap.M.find meth calls0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind He Hs Hf Ht
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

  Lemma inv_censor_other_defs : forall lastRq l l' meth,
      censorThreeStageLabel lastRq censorThreeStageMeth l = l' ->
      meth <> rqMeth ->
      meth <> rsMeth ->
      meth <> fhMeth ->
      meth <> thMeth ->
      FMap.M.find meth (defs l) = FMap.M.find meth (defs l').
  Proof.
    intros lastRq l l' meth H He Hs Hf Ht.
    destruct l. destruct l'.
    unfold censorThreeStageLabel, censorLabel, censorThreeStageMeth in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f defs = defs0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find meth (FMap.M.mapi f defs) = FMap.M.find meth defs0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind He Hs Hf Ht
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

  Lemma inv_censor_other_mem_calls : forall lastRq l l' meth,
      censorThreeStageLabel lastRq censorThreeStageMemDefs l = l' ->
      meth <> rqMeth ->
      meth <> rsMeth ->
      FMap.M.find meth (calls l) = FMap.M.find meth (calls l').
  Proof.
    intros lastRq l l' meth H He Hs.
    destruct l. destruct l'.
    unfold censorThreeStageLabel, censorLabel, censorThreeStageMemDefs in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f calls = calls0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find meth (FMap.M.mapi f calls) = FMap.M.find meth calls0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind He Hs
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
    repeat match goal with
    | [ H : (if ?x then _ else _) = _ |- _ ] => destruct x
    end; try tauto.
    subst.
    reflexivity.
  Qed.

  Lemma inv_censor_other_mem_defs : forall lastRq l l' meth,
      censorThreeStageLabel lastRq censorThreeStageMemDefs l = l' ->
      meth <> rqMeth ->
      meth <> rsMeth ->
      FMap.M.find meth (defs l) = FMap.M.find meth (defs l').
  Proof.
    intros lastRq l l' meth H He Hs.
    destruct l. destruct l'.
    unfold censorThreeStageLabel, censorLabel, censorThreeStageMemDefs in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f defs = defs0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find meth (FMap.M.mapi f defs) = FMap.M.find meth defs0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind He Hs
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

  
End Inversions.
