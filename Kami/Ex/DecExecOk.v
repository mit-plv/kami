Require Import Kami.
Require Import Lib.FinNotations Lib.Struct Lib.Indexer.
Require Import Ex.ProcMemSpec Ex.PipelinedProc Ex.DecExec.

Set Implicit Arguments.

Section DecExec.
  Variables (instK dataK: Kind)
            (addrSize rfSize: nat)
            (pgmSize: nat).

  Variables (dec: Decoder instK addrSize rfSize)
            (exec: Executer dataK)
            (pcInit : ConstT (Bit pgmSize))
            (pgmInit : ConstT (Vector instK pgmSize)).

  Local Notation D2E := (D2E addrSize rfSize pgmSize).
  Local Notation decexecSepInl := (decexecSepInl dec exec pcInit pgmInit).

  Definition decexec_regMap (r: RegsT): RegsT :=
    (mlet pcv : (Bit pgmSize) <- r |> "pc";
     mlet pgmv : (Vector instK pgmSize) <- r |> "pgm";
     mlet d2efullv : Bool <- r |> "d2e"--"full";
     mlet d2eeltv : (Struct D2E) <- r |> "d2e"--"elt";
     (["pgm" <- existT _ _ pgmv]
      +["pc" <- existT _ (SyntaxKind (Bit pgmSize))
             (if d2efullv then d2eeltv F7 else pcv)])%fmap)%mapping.
  Hint Unfold decexec_regMap: MapDefs.
  
  Definition decexec_ruleMap (o: RegsT): string -> option string :=
    "executeArith" |-> "decexecArith";
      "executeLd" |-> "decexecLd";
      "executeSt" |-> "decexecSt";
      "executeTh" |-> "decexecTh"; ||.
  Hint Unfold decexec_ruleMap: MethDefs.

  Definition decexec_d2e_inv
             (pgmv: fullType type (SyntaxKind (Vector instK pgmSize)))
             (d2efullv: fullType type (SyntaxKind Bool))
             (d2eeltv: fullType type (SyntaxKind (Struct D2E))) :=
    d2efullv = true ->
    let pc := d2eeltv F7 in
    let inst := evalExpr (#pgmv@[#pc])%kami_expr in
    d2eeltv F1 = evalExpr (getOp dec inst) /\
    d2eeltv F2 = evalExpr (getArithOp dec inst) /\
    d2eeltv F3 = evalExpr (getSrc1 dec inst) /\
    d2eeltv F4 = evalExpr (getSrc2 dec inst) /\
    d2eeltv F5 = evalExpr (getDst dec inst) /\
    d2eeltv F6 = evalExpr (getAddr dec inst).

  Record decexec_inv (o: RegsT): Prop :=
    { pcv: fullType type (SyntaxKind (Bit pgmSize));
      Hpcv: M.find "pc"%string o = Some (existT _ _ pcv);
      pgmv: fullType type (SyntaxKind (Vector instK pgmSize));
      Hpgmv: M.find "pgm"%string o = Some (existT _ _ pgmv);
      d2efullv: fullType type (SyntaxKind Bool);
      Hd2efullv: M.find "full.d2e"%string o = Some (existT _ _ d2efullv);
      d2eeltv: fullType type (SyntaxKind (Struct D2E));
      Hd2eeltv: M.find "elt.d2e"%string o = Some (existT _ _ d2eeltv);

      Hpcinv: d2efullv = true -> pcv = d2eeltv F7 ^+ $1;
      Hdeinv: decexec_d2e_inv pgmv d2efullv d2eeltv
    }.
  Hint Unfold decexec_d2e_inv : InvDefs.

  Ltac decexec_inv_dest_tac :=
    try match goal with
    | [H: decexec_inv _ |- _] => destruct H
    end;
    kinv_red.

  Ltac decexec_inv_constr_tac :=
    econstructor;
    repeat (intros; try findReify;
            kinv_eq; kinv_red; eauto).

  Ltac decexec_inv_tac :=
    decexec_inv_dest_tac; decexec_inv_constr_tac.

  Lemma decexec_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits (projT1 decexecSepInl)) ->
      Multistep (projT1 decexecSepInl) init n ll ->
      decexec_inv n.
  Proof.
    induction 2.
    - unfold getRegInits, decexecSepInl, projT1.
      decexec_inv_tac; simpl in *; kinv_simpl.
    - kinvert.
      + mred.
      + mred.
      + kinv_dest_custom decexec_inv_tac.
      + kinv_dest_custom decexec_inv_tac.
      + kinv_dest_custom decexec_inv_tac.
      + kinv_dest_custom decexec_inv_tac.
      + kinv_dest_custom decexec_inv_tac.
  Qed.

  Lemma decexec_inv_ok:
    forall o,
      reachable o (projT1 decexecSepInl) ->
      decexec_inv o.
  Proof.
    intros; inv H; inv H0.
    eapply decexec_inv_ok'; eauto.
  Qed.
  
  Theorem decexec_ok:
    decexecSep dec exec pcInit pgmInit <<== decexec dec exec pcInit pgmInit.
  Proof.
    intros.

    (* 1) inlining *)
    ketrans; [exact (projT2 decexecSepInl)|].

    (* 2) decomposition *)
    kdecompose_nodefs decexec_regMap decexec_ruleMap.

    (* 3) simulation *)
    kinv_add decexec_inv_ok.
    kinv_add_end.
    kinvert.
    - kinv_magic_with decexec_inv_dest_tac idtac.
    - kinv_magic_with decexec_inv_dest_tac idtac.
    - kinv_magic_with decexec_inv_dest_tac idtac.
    - kinv_magic_with decexec_inv_dest_tac idtac.
    - kinv_magic_with decexec_inv_dest_tac idtac.
  Qed.

End DecExec.

