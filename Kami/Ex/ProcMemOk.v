Require Import Kami.
Require Import Lib.FinNotations Lib.Struct Lib.Indexer.
Require Import Ex.OneEltFifo Ex.ProcMemSpec Ex.PipelinedProc
        Ex.DecExec Ex.DecExecOk Ex.ProcMemInterm.

Require Import Kami.Tactics Kami.ModuleBoundEx.

Set Implicit Arguments.

Section PipelinedProc.
  Variables (instK dataK: Kind)
            (addrSize rfSize: nat)
            (pgmSize: nat).

  Variables (dec: Decoder instK addrSize rfSize)
            (exec: Executer dataK).

  Variable (init: ProcInit instK dataK rfSize pgmSize).

  Local Definition procIntermInl := procIntermInl dec exec init.
  Local Definition RfWrite := RfWrite dataK rfSize.

  Definition procInterm_scoreboard_inv
             (sbFlagsv: fullType type (SyntaxKind (Vector Bool rfSize)))
             (e2wfullv: fullType type (SyntaxKind Bool))
             (e2weltv: fullType type (SyntaxKind (Struct RfWrite))) :=
    e2wfullv = true -> sbFlagsv (e2weltv F1) = true.

  Record procInterm_inv (o: RegsT): Prop :=
    { pcv: fullType type (SyntaxKind (Bit pgmSize));
      Hpcv: M.find "pc"%string o = Some (existT _ _ pcv);
      pgmv: fullType type (SyntaxKind (Vector instK pgmSize));
      Hpgmv: M.find "pgm"%string o = Some (existT _ _ pgmv);
      rfv: fullType type (SyntaxKind (Vector dataK rfSize));
      Hrfv: M.find "rf"%string o = Some (existT _ _ rfv);
      e2wfullv: fullType type (SyntaxKind Bool);
      He2wfullv: M.find "full.e2w"%string o = Some (existT _ _ e2wfullv);
      e2weltv: fullType type (SyntaxKind (Struct RfWrite));
      He2weltv: M.find "elt.e2w"%string o = Some (existT _ _ e2weltv);
      sbFlagsv: fullType type (SyntaxKind (Vector Bool rfSize));
      HsbFlagsv: M.find "sbFlags"%string o = Some (existT _ _ sbFlagsv);

      HsbInv: procInterm_scoreboard_inv sbFlagsv e2wfullv e2weltv;
    }.
  Hint Unfold procInterm_scoreboard_inv : InvDefs.

  Ltac procInterm_inv_dest_tac :=
    try match goal with
        | [H: procInterm_inv _ |- _] => destruct H
        end;
    kinv_red.

  Ltac procInterm_inv_constr_tac :=
    econstructor;
    repeat (intros; try findReify;
            kinv_eq; kinv_red; eauto).

  Ltac procInterm_inv_tac :=
    procInterm_inv_dest_tac; procInterm_inv_constr_tac.

  Lemma procInterm_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits (projT1 procIntermInl)) ->
      Multistep (projT1 procIntermInl) init n ll ->
      procInterm_inv n.
  Proof.
    induction 2.
    - unfold getRegInits, procIntermInl, projT1.
      procInterm_inv_tac; simpl in *; kinv_simpl.
    - kinvert.
      + mred.
      + mred.
      + kinv_dest_custom procInterm_inv_tac.
      + kinv_dest_custom procInterm_inv_tac.
      + kinv_dest_custom procInterm_inv_tac.
      + kinv_dest_custom procInterm_inv_tac.
      + kinv_dest_custom procInterm_inv_tac.
  Qed.

  Lemma procInterm_inv_ok:
    forall o,
      reachable o (projT1 procIntermInl) ->
      procInterm_inv o.
  Proof.
    intros; inv H; inv H0.
    eapply procInterm_inv_ok'; eauto.
  Qed.

  Definition procInterm_regMap (r: RegsT): RegsT :=
    (mlet pcv: (Bit pgmSize) <- r |> "pc";
       mlet pgmv: (Vector instK pgmSize) <- r |> "pgm";
       mlet rfv: (Vector dataK rfSize) <- r |> "rf";
       mlet e2wfullv: Bool <- r |> "e2w"--"full";
       mlet e2weltv: (Struct RfWrite) <- r |> "e2w"--"elt";
       mlet sbFlagsv: (Vector Bool rfSize) <- r |> "sbFlags";
       (["pgm" <- existT _ _ pgmv]
        +["rf" <- existT _ _
               (if e2wfullv
                then evalExpr (#rfv@[#e2weltv!RfWrite@."idx"
                               <- #e2weltv!RfWrite@."val"])%kami_expr
                else rfv)]
        +["pc" <- existT _ _ pcv])%fmap)%mapping.
  Hint Unfold procInterm_regMap: MapDefs.

  Definition procInterm_ruleMap (o: RegsT): string -> option string :=
    "decexecArith" |-> "doArith";
      "decexecLd" |-> "doLoad";
      "decexecSt" |-> "doStore";
      "decexecTh" |-> "doToHost"; ||.
  Hint Unfold procInterm_ruleMap: MethDefs.

  Theorem procImpl_ok_2:
    procInterm dec exec init <<== procSpec dec exec init.
  Proof.
    intros.

    (* 1) inlining *)
    kinline_refine_left procIntermInl.

    (* 2) decomposition *)
    kdecompose_nodefs procInterm_regMap procInterm_ruleMap.

    (* (* 3) simulation *) *)
    kinv_add procInterm_inv_ok.
    kinv_add_end.
    kinvert.
    - kinv_magic_with procInterm_inv_tac idtac.
    - kinv_magic_with procInterm_inv_tac idtac.
    - kinv_magic_with procInterm_inv_tac idtac.
    - kinv_magic_with procInterm_inv_tac idtac.
    - kinv_magic_with procInterm_inv_tac idtac.
  Qed.

  Theorem procImpl_ok:
    procImpl dec exec init <<== procSpec dec exec init.
  Proof.
    ketrans.
    - apply procImpl_ok_1.
    - apply procImpl_ok_2.
  Qed.

  Theorem procMemImpl_ok:
    procMemImpl dec exec init <<== procMemSpec dec exec init.
  Proof.
    kmodular.
    - apply procImpl_ok.
    - krefl.
  Qed.
  
End PipelinedProc.

