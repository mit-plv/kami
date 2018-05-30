Require Import Kami.
Require Import Lib.FinNotations Lib.Struct Lib.Indexer.
Require Import Ex.OneEltFifo Ex.ProcMemSpec Ex.PipelinedProc Ex.DecExec.

Require Import Kami.Tactics Kami.ModuleBoundEx.

Section PipelinedProc.
  Variables (instK dataK: Kind)
            (addrSize rfSize: nat)
            (pgmSize: nat).

  Variables (dec: Decoder instK addrSize rfSize)
            (exec: Executer dataK).

  Variable (init: ProcInit instK dataK rfSize pgmSize).
  
  Definition procImpl2 :=
    ((decexec dec exec (pcInit init) (pgmInit init))
       ++ (regFile (rfInit init))
       ++ (e2w dataK rfSize)
       ++ (scoreboard rfSize)
       ++ (writeback dataK rfSize))%kami.
  Lemma procImpl2_PhoasWf: ModPhoasWf procImpl2.
  Proof. kequiv. Qed.
  Lemma procImpl2_RegsWf: ModRegsWf procImpl2.
  Proof. kvr. Qed.
  Hint Resolve procImpl2_PhoasWf procImpl2_RegsWf.

  Hint Unfold procImpl2: ModuleDefs.
  
  Theorem procImpl_ok_1:
    procImpl dec exec init <<== procImpl2.
  Proof.
    kmodular.
    - apply decexec_ok.
    - krefl.
  Qed.

  Local Notation RfWrite := (RfWrite dataK rfSize).

  Definition procImpl2_regMap (r: RegsT): RegsT :=
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
  Hint Unfold procImpl2_regMap: MapDefs.

  Definition procImpl2_ruleMap (o: RegsT): string -> option string :=
    "decexecArith" |-> "doArith";
      "decexecLd" |-> "doLoad";
      "decexecSt" |-> "doStore";
      "decexecTh" |-> "doToHost"; ||.
  Hint Unfold procImpl2_ruleMap: MethDefs.

  Definition procImpl2Inl: sigT (fun m: Modules => procImpl2 <<== m).
  Proof.
    pose proof (inlineF_refines
                  (procImpl2_PhoasWf type typeUT)
                  (Reflection.noDupStr_NoDup
                     (namesOf (getDefsBodies procImpl2))
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

  Record procImpl2_inv (o: RegsT): Prop :=
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
      HsbFlagsv: M.find "sbFlags"%string o = Some (existT _ _ sbFlagsv)
    }.
  (* Hint Unfold procImpl2_inv_body : InvDefs. *)

  Ltac procImpl2_inv_dest_tac :=
    try match goal with
        | [H: procImpl2_inv _ |- _] => destruct H
        end;
    kinv_red.

  Ltac procImpl2_inv_constr_tac :=
    econstructor; (* let's prove that the invariant holds for the next state *)
    try (findReify; (reflexivity || eassumption); fail);
    kinv_red; (* unfolding invariant definitions *)
    repeat (* cheaper than "intuition" *)
      (match goal with
       | [ |- _ /\ _ ] => split
       end);
    try eassumption; intros; try reflexivity;
    intuition kinv_simpl; intuition idtac.

  Ltac procImpl2_inv_tac :=
    procImpl2_inv_dest_tac; procImpl2_inv_constr_tac.

  Lemma procImpl2_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits (projT1 procImpl2Inl)) ->
      Multistep (projT1 procImpl2Inl) init n ll ->
      procImpl2_inv n.
  Proof.
    induction 2.
    - unfold getRegInits, procImpl2Inl, projT1.
      procImpl2_inv_tac; simpl in *; kinv_simpl.
    - kinvert.
      + mred.
      + mred.
      + kinv_dest_custom procImpl2_inv_tac.
      + kinv_dest_custom procImpl2_inv_tac.
      + kinv_dest_custom procImpl2_inv_tac.
      + kinv_dest_custom procImpl2_inv_tac.
      + kinv_dest_custom procImpl2_inv_tac.
  Qed.

  Lemma procImpl2_inv_ok:
    forall o,
      reachable o (projT1 procImpl2Inl) ->
      procImpl2_inv o.
  Proof.
    intros; inv H; inv H0.
    eapply procImpl2_inv_ok'; eauto.
  Qed.

  Theorem procImpl_ok_2: procImpl2 <<== procSpec dec exec init.
  Proof.
    (* intros. *)

    (* (* 1) inlining *) *)
    (* ketrans; [exact (projT2 procImpl2Inl)|]. *)

    (* (* 2) decomposition *) *)
    (* kdecompose_nodefs procImpl2_regMap procImpl2_ruleMap. *)

    (* (* (* 3) simulation *) *) *)
    (* kinv_add procImpl2_inv_ok. *)
    (* kinv_add_end. *)
    (* kinvert. *)
    (* - kinv_action_dest. *)
    (*   kinv_custom procImpl2_inv_dest_tac. *)
    (*   kinv_regmap_red. *)
    (*   kinv_constr; kinv_eq; kinv_finish. *)
    (* - kinv_action_dest. *)
    (*   kinv_custom procImpl2_inv_dest_tac. *)
    (*   kinv_regmap_red. *)
    (*   kinv_constr; kinv_eq; kinv_finish. *)
    (* - kinv_action_dest. *)
    (*   kinv_custom procImpl2_inv_dest_tac. *)
    (*   kinv_regmap_red. *)
    (*   kinv_constr; kinv_eq; kinv_finish. *)
    (*   admit. (* about rf and scoreboard *) *)
    (* - kinv_action_dest. *)
    (*   kinv_custom procImpl2_inv_dest_tac. *)
    (*   kinv_regmap_red. *)
    (*   kinv_constr; kinv_eq; kinv_finish. *)
    (*   admit. (* about rf and scoreboard *) *)
    (* - kinv_action_dest. *)
    (*   kinv_custom procImpl2_inv_dest_tac. *)
    (*   kinv_regmap_red. *)
    (*   kinv_constr; kinv_eq; kinv_finish. *)
  Admitted.

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

