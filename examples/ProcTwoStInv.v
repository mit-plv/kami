Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StructNotation Lib.StringBound Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Specialize Kami.Inline Kami.InlineFacts Kami.Decomposition.
Require Import Kami.Tactics Kami.Notations.
Require Import Ex.MemTypes Ex.SC Ex.NativeFifo Ex.MemAtomic Ex.ProcTwoStage Ex.ProcTwoStInl.
Require Import Eqdep ProofIrrelevance.

Set Implicit Arguments.

Section Invariants.
  Variables opIdx addrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT opIdx addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize lgDataBytes rfIdx.

  Variables opLd opSt opTh: ConstT (Bit opIdx).
  Hypothesis (HldSt: (if weq (evalConstT opLd) (evalConstT opSt) then true else false) = false).

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  Definition p2stInl := p2stInl dec execState execNextPc opLd opSt opTh.

  Record p2st_inv (o: RegsT) : Prop :=
    { pcv : fullType type (SyntaxKind (Bit addrSize));
      Hpcv : M.find "pc"%string o = Some (existT _ _ pcv);
      pgmv : fullType type (SyntaxKind (Vector (Data lgDataBytes) addrSize));
      Hpgmv : M.find "pgm"%string o = Some (existT _ _ pgmv);
      fepochv : fullType type (SyntaxKind Bool);
      Hfepochv : M.find "fEpoch"%string o = Some (existT _ _ fepochv);
      rfv : fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx));
      Hrfv : M.find "rf"%string o = Some (existT _ _ rfv);

      d2eeltv : fullType type (SyntaxKind (d2eElt opIdx addrSize lgDataBytes rfIdx));
      Hd2eeltv : M.find "d2e"--"elt"%string o = Some (existT _ _ d2eeltv);
      d2efullv : fullType type (SyntaxKind Bool);
      Hd2efullv : M.find "d2e"--"full"%string o = Some (existT _ _ d2efullv);

      e2deltv : fullType type (SyntaxKind (Bit addrSize));
      He2deltv : M.find "e2d"--"elt"%string o = Some (existT _ _ e2deltv);
      e2dfullv : fullType type (SyntaxKind Bool);
      He2dfullv : M.find "e2d"--"full"%string o = Some (existT _ _ e2dfullv);

      stallv : fullType type (SyntaxKind Bool);
      Hstallv : M.find "stall"%string o = Some (existT _ _ stallv);
      eepochv : fullType type (SyntaxKind Bool);
      Heepochv : M.find "eEpoch"%string o = Some (existT _ _ eepochv);

      Hinv :
        (fepochv = eepochv -> e2dfullv = false) /\ (e2dfullv = false -> fepochv = eepochv) /\
        (fepochv <> eepochv -> e2dfullv = true) /\ (e2dfullv = true -> fepochv <> eepochv) /\

        (e2dfullv = true -> d2efullv = false) /\ (d2efullv = true -> e2dfullv = false) /\

        (stallv = true -> d2efullv = true) /\
        
        (d2efullv = true ->
         (fepochv = d2eeltv ``"epoch" /\
          pcv = d2eeltv ``"nextPc" /\
          evalExpr (dec _ rfv (pgmv (d2eeltv ``"curPc"))) = d2eeltv ``"instDec"))
    }.

  Ltac p2st_inv_old :=
    try match goal with
        | [H: p2st_inv _ |- _] => destruct H
        end;
    kinv_red.
  
  Ltac p2st_inv_new :=
    econstructor; (* let's prove that the invariant holds for the next state *)
    try (findReify; (reflexivity || eassumption); fail);
    kregmap_clear. (* for improving performance *)

  Ltac p2st_inv_tac := p2st_inv_old; p2st_inv_new.

  Lemma p2st_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits (fst p2stInl)) ->
      Multistep (fst p2stInl) init n ll ->
      p2st_inv n.
  Proof.
    admit.
    
    (* induction 2. *)

    (* - kinv_dest_custom p2st_inv_tac. *)
    (*   intuition idtac. *)
    (*   + inv H. *)
    (*   + inv H. *)

    (* - kinvert. *)
    (*   + mred. *)
    (*   + mred. *)
    (*   + kinv_dest_custom p2st_inv_tac. *)
    (*     destruct x0, eepochv; intuition idtac. *)
    (*   + kinv_dest_custom p2st_inv_tac. *)
    (*     intuition idtac. *)
    (*   + kinv_dest_custom p2st_inv_tac. *)
    (*     intuition idtac. *)
    (*   + kinv_dest_custom p2st_inv_tac. *)
    (*     intuition idtac. *)
    (*   + kinv_dest_custom p2st_inv_tac. *)
    (*     * unfold BoundedIndexFull, IndexBound_head, IndexBound_tail, *)
    (*       mapAttr, addFirstBoundedIndex, bindex in *; simpl in *. *)
    (*       match goal with *)
    (*       | [ |- context[x1 ?e] ] => destruct (x1 e) *)
    (*       end; intuition idtac. *)
    (*       { inv H3. } *)
    (*       { inv H2. } *)
    (*     * unfold BoundedIndexFull, IndexBound_head, IndexBound_tail, *)
    (*       mapAttr, addFirstBoundedIndex, bindex in *; simpl in *. *)
    (*       match goal with *)
    (*       | [ |- context[x1 ?e] ] => destruct (x1 e) *)
    (*       end; intuition idtac. *)
        
    (*   + kinv_dest_custom p2st_inv_tac. *)
    (*     unfold BoundedIndexFull, IndexBound_head, IndexBound_tail, *)
    (*     mapAttr, addFirstBoundedIndex, bindex in *; simpl in *. *)
    (*     match goal with *)
    (*     | [ |- context[x1 ?e] ] => destruct (x1 e) *)
    (*     end; intuition idtac. *)

    (*   + kinv_dest_custom p2st_inv_tac. *)
    (*     * match goal with *)
    (*       | [ |- context[x2 ?e] ] => destruct (x2 e) *)
    (*       end; intuition idtac. *)
    (*       { inv H2. } *)
    (*       { inv H. } *)
    (*     * match goal with *)
    (*       | [ |- context[x2 ?e] ] => destruct (x2 e) *)
    (*       end; intuition idtac. *)

    (*   + kinv_dest_custom p2st_inv_tac. *)
    (*     * match goal with *)
    (*       | [ |- context[x2 ?e] ] => destruct (x2 e) *)
    (*       end; intuition idtac. *)
    (*       { inv H2. } *)
    (*       { inv H. } *)
    (*     * match goal with *)
    (*       | [ |- context[x2 ?e] ] => destruct (x2 e) *)
    (*       end; intuition idtac. *)

    (*   + kinv_dest_custom p2st_inv_tac. *)
    (*     * unfold BoundedIndexFull, IndexBound_head, IndexBound_tail, *)
    (*       mapAttr, addFirstBoundedIndex, bindex in *; simpl in *. *)
    (*       match goal with *)
    (*       | [ |- context[x1 ?e] ] => destruct (x1 e) *)
    (*       end; intuition idtac. *)
    (*       { inv H3. } *)
    (*       { inv H2. } *)
    (*     * unfold BoundedIndexFull, IndexBound_head, IndexBound_tail, *)
    (*       mapAttr, addFirstBoundedIndex, bindex in *; simpl in *. *)
    (*       match goal with *)
    (*       | [ |- context[x1 ?e] ] => destruct (x1 e) *)
    (*       end; intuition idtac. *)

    (*   + kinv_dest_custom p2st_inv_tac. *)
    (*     * unfold BoundedIndexFull, IndexBound_head, IndexBound_tail, *)
    (*       mapAttr, addFirstBoundedIndex, bindex in *; simpl in *. *)
    (*       match goal with *)
    (*       | [ |- context[x1 ?e] ] => destruct (x1 e) *)
    (*       end; intuition idtac. *)
    (*       { inv H3. } *)
    (*       { inv H2. } *)
    (*     * unfold BoundedIndexFull, IndexBound_head, IndexBound_tail, *)
    (*       mapAttr, addFirstBoundedIndex, bindex in *; simpl in *. *)
    (*       match goal with *)
    (*       | [ |- context[x1 ?e] ] => destruct (x1 e) *)
    (*       end; intuition idtac. *)

  Qed.
  
  Lemma p2st_inv_ok:
    forall o,
      reachable o (fst p2stInl) ->
      p2st_inv o.
  Proof.
    intros; inv H; inv H0.
    eapply p2st_inv_ok'; eauto.
  Qed.

End Invariants.

Hint Unfold RqFromProc RsToProc: MethDefs.

