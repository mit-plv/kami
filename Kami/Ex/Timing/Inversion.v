Require Import Notations.
Require Import List.
Require Import Lib.Word Lib.Indexer Lib.FMap.
Require Import Kami.Syntax Kami.Semantics Kami.SymEvalTac Kami.Tactics Kami.ModularFacts Kami.SemFacts.
Require Import Ex.SC Ex.IsaRv32 Ex.ProcThreeStage Ex.OneEltFifo.
Require Import Ex.Timing.Specification Ex.Timing.ThreeStageInterface.
Require Import Lib.CommonTactics.


Module Inversions (ThreeStage : ThreeStageInterface).
  Module Defs := (ThreeStageDefs ThreeStage).
  Import ThreeStage Defs.

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
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (calls l') = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
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
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (defs l') = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
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

  

  Lemma inv_censor_rs_calls_as_defs : forall lastRq l l',
      censorThreeStageLabel lastRq censorThreeStageMeth l = l' ->
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

  
  Lemma inv_censor_rq_memdefs : forall lastRq l l',
      censorThreeStageLabel lastRq censorThreeStageMemDefs l = l' ->
      FMap.M.find rqMeth (defs l) = FMap.M.find rqMeth (defs l') \/
      exists adr op arg,
        FMap.M.find rqMeth (defs l) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (defs l') = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
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

  Lemma inv_censor_rq_memdefs_as_calls : forall lastRq l l',
      censorThreeStageLabel lastRq censorThreeStageMemDefs l = l' ->
      FMap.M.find rqMeth (calls l) = FMap.M.find rqMeth (calls l') \/
      exists adr op arg,
        FMap.M.find rqMeth (calls l) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (calls l') = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
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
  
  Lemma inv_censor_rs_memdefs_as_calls : forall lastRq l l',
      censorThreeStageLabel lastRq censorThreeStageMemDefs l = l' ->
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
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (calls lb) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
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
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (defs lb) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
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

  Lemma inv_censoreq_rs_calls_as_defs : forall lastRq la lb,
      censorThreeStageLabel lastRq censorThreeStageMeth la = censorThreeStageLabel lastRq censorThreeStageMeth lb ->
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
                        ret := Struct (STRUCT { "data" :: Bit 32}) |}
                     ((evalExpr ($$WO)%kami_expr),
                      evalExpr (STRUCT { "data" ::= #arg' })%kami_expr)) /\
              match lastRq with
                  | Some op => if op then arg = arg' else True
                  | None => arg = arg'
              end. 
  Proof.
    intros lastRq la lb H.
    destruct (inv_censor_rs_calls_as_defs lastRq la _ eq_refl) as [Haeq | [arga [Ha Hac]]];
      destruct (inv_censor_rs_calls_as_defs lastRq lb _ eq_refl) as [Hbeq | [argb [Hb Hbc]]].
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
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (defs lb) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
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

  
  Lemma inv_censoreq_rq_memdefs_as_calls : forall lastRq la lb,
      censorThreeStageLabel lastRq censorThreeStageMemDefs la = censorThreeStageLabel lastRq censorThreeStageMemDefs lb ->
      FMap.M.find rqMeth (calls la) = FMap.M.find rqMeth (calls lb) \/
      exists adr op arg arg',
        FMap.M.find rqMeth (calls la) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (calls lb) = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg' })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\ if op then True else arg = arg'.
  Proof.
    intros lastRq la lb H.
    destruct (inv_censor_rq_memdefs_as_calls lastRq la _ eq_refl) as [Haeq | [adra [opa [arga [Ha Hac]]]]];
      destruct (inv_censor_rq_memdefs_as_calls lastRq lb _ eq_refl) as [Hbeq | [adrb [opb [argb [Hb Hbc]]]]].
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
  
  
  Lemma inv_censoreq_rs_memdefs_as_calls : forall lastRq la lb,
      censorThreeStageLabel lastRq censorThreeStageMemDefs la = censorThreeStageLabel lastRq censorThreeStageMemDefs lb ->
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
                        ret := Struct (STRUCT {"data" :: Bit 32}) |}
                     (evalExpr ($$WO)%kami_expr,
                      evalExpr (STRUCT { "data" ::= #arg' })%kami_expr)) /\
        match lastRq with
        | Some op => if op then arg = arg' else True
        | None => arg = arg'
        end.
  Proof.
    intros lastRq la lb H.
    destruct (inv_censor_rs_memdefs_as_calls lastRq la _ eq_refl) as [Haeq | [arga [Ha Hac]]];
      destruct (inv_censor_rs_memdefs_as_calls lastRq lb _ eq_refl) as [Hbeq | [argb [Hb Hbc]]].
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
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
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
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (calls l') = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
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
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
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
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (evalExpr (STRUCT { "addr" ::= #adr;
                                         "op" ::= #op;
                                         "data" ::= #arg })%kami_expr,
                      evalExpr ($$WO)%kami_expr)) /\
        FMap.M.find rqMeth (defs l') = 
        Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 11;
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

  
  Lemma inv_censor_fh_calls : forall lastRq l l',
      censorThreeStageLabel lastRq censorThreeStageMeth l = l' ->
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
    intros lastRq l l' H.
    destruct l. destruct l'.
    unfold censorThreeStageLabel, censorLabel, censorThreeStageMeth in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f calls = calls0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find fhMeth (FMap.M.mapi f calls) = FMap.M.find fhMeth calls0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind
    end.
    pose proof methsDistinct; shatter.
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
    match goal with
           | [ s : sigT _ |- _ ] => destruct s
           end. 
    repeat (match goal with
            | [ H : match ?x with | _ => _ end _ = _ |- _ ] => destruct x
            end; try solve [ left; f_equal; assumption ]).
    match goal with
    | [ x : SignT _ |- _ ] => destruct s
    end. subst.
    unfold arg, ret in *.
    right.
    match goal with
    | [ x : type (Bit 0) |- _ ] => pose proof (inv_none x)
    end.
    subst. 
    exists t0.
    tauto.
  Qed.

  Lemma inv_censor_th_calls : forall lastRq l l',
      censorThreeStageLabel lastRq censorThreeStageMeth l = l' ->
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
    intros lastRq l l' H.
    destruct l. destruct l'.
    unfold censorThreeStageLabel, censorLabel, censorThreeStageMeth in H.
    inv_label.
    match goal with
    | [ H : FMap.M.mapi ?f calls = calls0 |- _ ] =>
      let Hfind := fresh in
      assert (FMap.M.find thMeth (FMap.M.mapi f calls) = FMap.M.find thMeth calls0) as Hfind by (f_equal; assumption);
        rewrite FMap.M.F.P.F.mapi_o in Hfind by (intros; subst; reflexivity);
        unfold option_map in Hfind;
        clear - Hfind
    end.
    pose proof methsDistinct; shatter.
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
    match goal with
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
    match goal with
    | [ x : type (Bit 0) |- _ ] => pose proof (inv_none x)
    end.
    subst.
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

  Lemma inv_censor_host_fh : forall lastRq s s',
      censorHostMeth fhMeth thMeth fhMeth s = s' ->
      (s = s' /\ censorThreeStageMeth lastRq fhMeth s = s) \/
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
    intros lastRq s s' H.
    pose methsDistinct; shatter.
    unfold censorHostMeth in H.
    unfold censorThreeStageMeth.
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

  Lemma inv_censor_host_th : forall lastRq s s',
      censorHostMeth fhMeth thMeth thMeth s = s' ->
      (s = s' /\ censorThreeStageMeth lastRq thMeth s = s) \/
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
    intros lastRq s s' H.
    pose methsDistinct. shatter.
    unfold censorHostMeth in H.
    unfold censorThreeStageMeth.
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


  
  Lemma rqCall_from_censor : forall lastRq a b,
      censorThreeStageLabel lastRq censorThreeStageMeth a =
      censorThreeStageLabel lastRq censorThreeStageMeth b ->
      (getRqCall lastRq a) = (getRqCall lastRq b).
  Proof.
    intros.
    destruct (inv_censoreq_rq_calls lastRq a b H) as [Rqeq | [adra [opa [arga [argb ?]]]]];
    destruct (inv_censoreq_rs_calls lastRq a b H) as [Rseq | [arga' [argb' ?]]].
    - unfold getRqCall; repeat rewrite Rqeq, Rseq; reflexivity.
    - shatter. unfold getRqCall; repeat rewrite Rqeq, H0, H1;
                 reflexivity.
    - shatter. unfold getRqCall; repeat rewrite Rseq, H0, H1;
                 reflexivity.
    - shatter. unfold getRqCall;
      repeat match goal with
             | [H : (_ === calls _ .[ _ ])%fmap |- _ ] => rewrite H
             end.
      reflexivity.
  Qed.

  Lemma rqDef_from_censor : forall lastRq a b,
      censorThreeStageLabel lastRq censorThreeStageMemDefs a =
      censorThreeStageLabel lastRq censorThreeStageMemDefs b ->
      (getRqDef lastRq a) = (getRqDef lastRq b).
  Proof.
    intros.
    destruct (inv_censoreq_rq_memdefs lastRq a b H) as [Rqeq | [adra [opa [arga [argb ?]]]]];
    destruct (inv_censoreq_rs_memdefs lastRq a b H) as [Rseq | [arga' [argb' ?]]].
    - unfold getRqDef; repeat rewrite Rqeq, Rseq; reflexivity.
    - shatter. unfold getRqDef; repeat rewrite Rqeq, H0, H1;
                 reflexivity.
    - shatter. unfold getRqDef; repeat rewrite Rseq, H0, H1;
                 reflexivity.
    - shatter. unfold getRqDef;
      repeat match goal with
             | [H : (_ === defs _ .[ _ ])%fmap |- _ ] => rewrite H
             end.
      reflexivity.
  Qed.

End Inversions.
