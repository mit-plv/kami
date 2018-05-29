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
  
  Theorem procImpl2_ok:
    procImpl dec exec init <<== procImpl2.
  Proof.
    kmodular.
    - apply decexec_ok.
    - krefl.
  Qed.

  (* Eval vm_compute in (namesOf (getRegInits procImpl2)). *)
  (* = ["pc"%string; "pgm"%string; "rf"%string; "elt.e2w"%string; *)
  (*    "full.e2w"%string; "sbFlags"%string] *)
  (*   : list string *)
  (* Eval vm_compute in (namesOf (getRegInits (procSpec dec exec init))). *)
  (* = ["pc"%string; "rf"%string; "pgm"%string] *)
  (*   : list string *)
  (** FIXME *)
  Definition procImpl2_regMap (r: RegsT): RegsT :=
    (mlet pcv: (Bit pgmSize) <- r |> "pc";
       mlet pgmv: (Vector instK pgmSize) <- r |> "pgm";
       mlet rfv: (Vector dataK rfSize) <- r |> "rf";
       mlet e2wfullv: Bool <- r |> "e2w"--"full";
       mlet e2weltv: (Struct (RfWrite dataK rfSize)) <- r |> "e2w"--"elt";
       mlet sbFlagsv: (Vector Bool rfSize) <- r |> "sbFlags";
       (["pgm" <- existT _ _ pgmv]
        +["rf" <- existT _ _ rfv]
        +["pc" <- existT _ _ pcv])%fmap)%mapping.
  Hint Unfold procImpl2_regMap: MapDefs.

  (* Eval vm_compute in (namesOf (getRules procImpl2)). *)
  (* = ["decexecArith"%string; "decexecLd"%string; *)
  (*    "decexecSt"%string; "decexecTh"%string; *)
  (*    "writeback"%string] *)
  (*   : list string *)
  (* Eval vm_compute in (namesOf (getRules (procSpec dec exec init))). *)
  (* = ["doArith"%string; "doLoad"%string; "doStore"%string; *)
  (*    "doToHost"%string] *)
  (*   : list string *)
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

  (* Eval vm_compute in (namesOf (getRegInits procImpl2)). *)
  (* = ["pc"%string; "pgm"%string; "rf"%string; "elt.e2w"%string; *)
  (*    "full.e2w"%string; "sbFlags"%string] *)
  (*   : list string *)
  Record procImpl2_inv (o: RegsT): Prop :=
    { pcv: fullType type (SyntaxKind (Bit pgmSize));
      Hpcv: M.find "pc"%string o = Some (existT _ _ pcv);
      pgmv: fullType type (SyntaxKind (Vector instK pgmSize));
      Hpgmv: M.find "pgm"%string o = Some (existT _ _ pgmv);
      e2wfullv: fullType type (SyntaxKind Bool);
      He2wfullv: M.find "full.e2w"%string o = Some (existT _ _ e2wfullv);
      e2weltv: fullType type (SyntaxKind (Struct (RfWrite dataK rfSize)));
      He2weltv: M.find "elt.e2w"%string o = Some (existT _ _ e2weltv);
      sbFlagsv: fullType type (SyntaxKind (Vector Bool rfSize));
      HsbFlagsv: M.find "sbFlags"%string o = Some (existT _ _ sbFlagsv)
    }.
  (* Hint Unfold procImpl2_inv_body : InvDefs. *)

  Ltac procImpl2_inv_tac :=
    try match goal with
        | [H: procImpl2_inv _ |- _] => destruct H
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

  Theorem procImpl_ok: procImpl2 <<== procSpec dec exec init.
  Proof.
    intros.

    (* 1) inlining *)
    ketrans; [exact (projT2 procImpl2Inl)|].

    (* 2) decomposition *)
    kdecompose_nodefs procImpl2_regMap procImpl2_ruleMap.

    (* (* 3) simulation *) *)
    kinv_add procImpl2_inv_ok.
    kinv_add_end.
    kinvert.
  Admitted.
  
End PipelinedProc.

