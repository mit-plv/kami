Require Import Kami.
Require Import Lib.FinNotations Lib.Struct Lib.Indexer.
Require Import Ex.ProcMemSpec Ex.PipelinedProc.

Set Implicit Arguments.

Section DecExec.
  Variables (instK dataK: Kind)
            (addrSize rfSize: nat)
            (pgmSize: nat).

  Variables (dec: Decoder instK addrSize rfSize)
            (exec: Executer dataK)
            (pcInit : ConstT (Bit pgmSize))
            (pgmInit : ConstT (Vector instK pgmSize)).

  Local Notation doMem := (doMem dataK addrSize).
  Local Notation toHost := (toHost dataK).
  Local Notation D2E := (D2E addrSize rfSize pgmSize).
  Local Notation sbSearch1 := (sbSearch1 rfSize).
  Local Notation sbSearch2 := (sbSearch2 rfSize).
  Local Notation sbSearch3 := (sbSearch3 rfSize).
  Local Notation sbInsert := (sbInsert rfSize).
  Local Notation rfRead1 := (rfRead1 dataK rfSize).
  Local Notation rfRead2 := (rfRead2 dataK rfSize).
  Local Notation e2wEnq := (e2wEnq dataK rfSize).
  
  Definition decexec :=
    MODULE {
      Register "pc" : Bit pgmSize <- pcInit
      with Register "pgm" : Vector instK pgmSize <- pgmInit

      with Rule "decexecArith" :=
        Read pc: Bit pgmSize <- "pc";
        Read pgm <- "pgm";
        LET inst <- #pgm@[#pc];
        LET op <- getOp dec inst;
        Assert (#op == $$opArith);
      
        LET src1 <- getSrc1 dec inst;
        LET src2 <- getSrc2 dec inst;
        LET dst <- getDst dec inst;
        Call srcOk1 <- sbSearch1(#src1);
        Call srcOk2 <- sbSearch2(#src2);
        Call dstOk <- sbSearch3(#dst);
        Assert (#srcOk1 && #srcOk2 && #dstOk);

        LET arithOp <- getArithOp dec inst;
        Call val1 <- rfRead1(#src1);
        Call val2 <- rfRead2(#src2);
        LET execVal <- execArith exec arithOp val1 val2;
        Call sbInsert(#dst);
        Call e2wEnq (STRUCT { "idx" ::= #dst; "val" ::= #execVal });

        Write "pc" <- #pc + $1;
        Retv

      with Rule "decexecLd" :=
        Read pc: Bit pgmSize <- "pc";
        Read pgm <- "pgm";
        LET inst <- #pgm@[#pc];
        LET op <- getOp dec inst;
        Assert (#op == $$opLd);

        LET dst <- getDst dec inst;
        LET addr <- getAddr dec inst;
        Call val <- doMem(STRUCT { "isLoad" ::= $$true;
                                   "addr" ::= #addr;
                                   "data" ::= $$Default });
        Call dstOk <- sbSearch3(#dst);
        Assert #dstOk;

        Call sbInsert(#dst);
        Call e2wEnq (STRUCT { "idx" ::= #dst; "val" ::= #val });
        Write "pc" <- #pc + $1;
        Retv

      with Rule "decexecSt" :=
        Read pc: Bit pgmSize <- "pc";
        Read pgm <- "pgm";
        LET inst <- #pgm@[#pc];
        LET op <- getOp dec inst;
        Assert (#op == $$opSt);

        LET addr <- getAddr dec inst;
        LET src1 <- getSrc1 dec inst;
        Call srcOk1 <- sbSearch1(#src1);
        Assert #srcOk1;
          
        Call val <- rfRead1(#src1);
        Call doMem(STRUCT { "isLoad" ::= $$false;
                            "addr" ::= #addr;
                            "data" ::= $$Default });
        Write "pc" <- #pc + $1;
        Retv

      with Rule "decexecTh" :=
        Read pc: Bit pgmSize <- "pc";
        Read pgm <- "pgm";
        LET inst <- #pgm@[#pc];
        LET op <- getOp dec inst;
        Assert (#op == $$opTh);

        LET src1 <- getSrc1 dec inst;
        Call srcOk1 <- sbSearch1(#src1);
        Assert #srcOk1;

        Call val1 <- rfRead1(#src1);
        Call toHost(#val1);
        Write "pc" <- #pc + $1;
        Retv
    }.

  Definition decexecSep :=
    ((decoder dec pcInit pgmInit)
       ++ (d2e addrSize rfSize pgmSize)
       ++ (executer addrSize rfSize pgmSize exec))%kami.

  Hint Unfold decexecSep decexec: ModuleDefs.

  Lemma decexecSep_ModEquiv: ModEquiv type typeUT decexecSep.
  Proof.
    kequiv.
  Qed.
  Hint Resolve decexecSep_ModEquiv.

  (* Eval vm_compute in (namesOf (getRegInits decexecSep)). *)
  (* = ["pc"%string; "pgm"%string; "elt.d2e"%string; "full.d2e"%string] *)
  (*   : list string *)
  (* Eval vm_compute in (namesOf (getRegInits decexec)). *)
  (* = ["pc"%string; "pgm"%string] *)
  (*   : list string *)
  Definition decexec_regMap (r: RegsT): RegsT :=
    (mlet pcv : (Bit pgmSize) <- r |> "pc";
     mlet pgmv : (Vector instK pgmSize) <- r |> "pgm";
     mlet d2efullv : Bool <- r |> "d2e"--"full";
     mlet d2eeltv : (Struct D2E) <- r |> "d2e"--"elt";
     (["pgm" <- existT _ _ pgmv]
      +["pc" <- existT _ (SyntaxKind (Bit pgmSize))
             (if d2efullv then d2eeltv F7 else pcv)])%fmap)%mapping.
  Hint Unfold decexec_regMap: MapDefs.
  
  (* Definition decexec_regMap (ir sr: RegsT): Prop. *)
  (*   kexistv "pc"%string ipcv ir (Bit pgmSize). *)
  (*   kexistv "pgm"%string ipgmv ir (Vector instK pgmSize). *)
  (*   kexistv "d2e"--"full" id2efullv ir Bool. *)
  (*   kexistv "d2e"--"elt" id2eeltv ir (Struct D2E). *)
  (*   kexistv "pc"%string spcv sr (Bit pgmSize). *)
  (*   kexistv "pgm"%string spgmv sr (Vector instK pgmSize). *)
  (*   refine (_ /\ _). *)
  (*   - exact (ipgmv = spgmv). *)
  (*   - exact (ipcv = if id2efullv then spcv ^+ $1 else spcv). *)
  (* Defined. *)
  (* Hint Unfold decexec_regMap: MethDefs. *)

  Definition decexec_ruleMap (o: RegsT): string -> option string :=
    "executeArith" |-> "decexecArith";
      "executeLd" |-> "decexecLd";
      "executeSt" |-> "decexecSt";
      "executeTh" |-> "decexecTh"; ||.
  Hint Unfold decexec_ruleMap: MethDefs.

  Definition decexecSepInl: sigT (fun m: Modules => decexecSep <<== m).
  Proof.
    pose proof (inlineF_refines
                  decexecSep_ModEquiv
                  (Reflection.noDupStr_NoDup
                     (namesOf (getDefsBodies decexecSep))
                     eq_refl)) as Him.
    unfold MethsT in Him; rewrite <-SemFacts.idElementwiseId in Him.
    match goal with
    | [H: context[inlineF ?m] |- _] => set m as origm in H at 2
    end.
    kinline_compute_in Him.
    unfold origm in *.
    specialize (Him eq_refl).
    exact (existT _ _ Him).
  Defined.

  Definition decexec_inv_body
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
      Hdeinv: decexec_inv_body pgmv d2efullv d2eeltv
    }.
  Hint Unfold decexec_inv_body : InvDefs.

  Ltac decexec_inv_tac :=
    try match goal with
    | [H: decexec_inv _ |- _] => destruct H
    end;
    kinv_red;
    econstructor; (* let's prove that the invariant holds for the next state *)
    try (findReify; (reflexivity || eassumption); fail);
    kinv_red; (* unfolding invariant definitions *)
    repeat (* cheaper than "intuition" *)
      (match goal with
       | [ |- _ /\ _ ] => split
       end);
    try eassumption; intros; try reflexivity;
    intuition kinv_simpl; intuition idtac.

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
  
  Theorem decexec_ok: decexecSep <<== decexec.
  Proof.
    intros.

    (* 1) inlining *)
    ketrans; [exact (projT2 decexecSepInl)|].

    (* 2) decomposition *)
    kdecompose_nodefs decexec_regMap decexec_ruleMap.

    (* 3) simulation *)
    (* let invs := (eval hnf in (invariants cfg)) in *)
    (* kinv_add_rep invs; *)
    kinv_add decexec_inv_ok.
    kinv_add_end.
    kinvert.
    - kinv_action_dest.
      kinv_custom decexec_inv_tac.
      + kinv_regmap_red.
        kinv_constr.
      + kinv_regmap_red.
        kinv_constr.
    - kinv_action_dest.
      kinv_custom decexec_inv_tac.
      + kinv_regmap_red.
        kinv_constr; kinv_eq; kinv_finish.
      + kinv_regmap_red.
        kinv_constr; kinv_eq.
    - kinv_action_dest.
      kinv_custom decexec_inv_tac.
      + kinv_regmap_red.
        kinv_constr; kinv_eq; kinv_finish.
      + kinv_regmap_red.
        kinv_constr; kinv_eq.
    - kinv_action_dest.
      kinv_custom decexec_inv_tac.
      + kinv_regmap_red.
        kinv_constr; kinv_eq; kinv_finish.
      + kinv_regmap_red.
        kinv_constr; kinv_eq.
    - kinv_action_dest.
      kinv_custom decexec_inv_tac.
      + kinv_regmap_red.
        kinv_constr; kinv_eq; kinv_finish.
      + kinv_regmap_red.
        kinv_constr; kinv_eq.
  Qed.
  
End DecExec.

