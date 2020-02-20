Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Specialize Kami.Inline Kami.InlineFacts Kami.Decomposition.
Require Import Kami.Tactics Kami.Notations Kami.PrimBram.
Require Import Ex.MemTypes Ex.SC Ex.NativeFifo Ex.MemAsync Ex.ProcFetch Ex.ProcFInl.
Require Import Eqdep ProofIrrelevance.

Set Implicit Arguments.

Section Invariants.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes).

  Variable (f2dElt: Kind).
  Variable (f2dPack:
              forall ty,
                Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind f2dElt)).
  Variables
    (f2dRawInst: forall ty, fullType ty (SyntaxKind f2dElt) ->
                            Expr ty (SyntaxKind (Data instBytes)))
    (f2dCurPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind (Pc addrSize)))
    (f2dNextPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                           Expr ty (SyntaxKind (Pc addrSize)))
    (f2dEpoch: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind Bool)).

  Context {indexSize tagSize: nat}.
  Variables (getIndex: forall ty, fullType ty (SyntaxKind (Bit addrSize)) ->
                                  Expr ty (SyntaxKind (Bit indexSize)))
            (getTag: forall ty, fullType ty (SyntaxKind (Bit addrSize)) ->
                                Expr ty (SyntaxKind (Bit tagSize))).

  Variables (pcInit : ConstT (Pc addrSize)).
  
  Definition fetchICacheInl :=
    projT1 (fetchICacheInl fetch f2dPack getIndex getTag pcInit).

  Record fetchICache_inv (o: RegsT) : Prop :=
    { pcv : fullType type (SyntaxKind (Pc addrSize));
      Hpcv : M.find "pc"%string o = Some (existT _ _ pcv);
      pinitv : fullType type (SyntaxKind Bool);
      Hpinitv : M.find "pinit"%string o = Some (existT _ _ pinitv);
      pinitRqv : fullType type (SyntaxKind Bool);
      HpinitRqv : M.find "pinitRq"%string o = Some (existT _ _ pinitRqv);
      pinitRqOfsv : fullType type (SyntaxKind (Bit iaddrSize));
      HpinitRqOfsv : M.find "pinitRqOfs"%string o = Some (existT _ _ pinitRqOfsv);
      pinitRsOfsv : fullType type (SyntaxKind (Bit iaddrSize));
      HpinitRsOfsv : M.find "pinitRsOfs"%string o = Some (existT _ _ pinitRsOfsv);
      fepochv : fullType type (SyntaxKind Bool);
      Hfepochv : M.find "fEpoch"%string o = Some (existT _ _ fepochv);
      pcuv : fullType type (SyntaxKind Bool);
      Hpcuv : M.find "pcUpdated"%string o = Some (existT _ _ pcuv);
            
      bramv : fullType type (SyntaxKind (Vector (Data instBytes) iaddrSize));
      Hbramv : M.find "pgm"--"bram" o = Some (existT _ _ bramv);
      breadv : fullType type (bramReadValK (Data instBytes) type);
      Hbreadv : M.find "pgm"--"readVal" o = Some (existT _ _ breadv);

      Hinv0 : pinitv = false -> breadv = None;
      Hinv1 : pinitv = true -> pcuv = false ->
              match breadv with
              | Some val => val = bramv (evalExpr (toIAddr _ pcv))
              | None => True
              end
    }.

  Ltac fetchICache_inv_old :=
    repeat match goal with
           | [H: fetchICache_inv _ |- _] => destruct H
           end;
    kinv_red.

  Ltac fetchICache_inv_new :=
    econstructor; (* let's prove that the invariant holds for the next state *)
    try (findReify; (reflexivity || eassumption); fail);
    kinv_red; (* unfolding invariant definitions *)
    try eassumption; intros; try reflexivity.
    (* intuition kinv_simpl; intuition idtac. *)

  Ltac fetchICache_inv_tac := fetchICache_inv_old; fetchICache_inv_new.

  Lemma fetchICache_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits fetchICacheInl) ->
      Multistep fetchICacheInl init n ll ->
      fetchICache_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2.

    - fetchICache_inv_old.
      unfold getRegInits, fetchICacheInl, ProcFInl.fetchICacheInl, projT1.
      fetchICache_inv_new.

    - kinvert.
      + mred.
      + mred.
      + kinv_dest_custom fetchICache_inv_tac.
      + kinv_dest_custom fetchICache_inv_tac.
      + kinv_dest_custom fetchICache_inv_tac.
      + kinv_dest_custom fetchICache_inv_tac.
      + kinv_dest_custom fetchICache_inv_tac.
      + kinv_dest_custom fetchICache_inv_tac.
      + kinv_dest_custom fetchICache_inv_tac.
      + kinv_dest_custom fetchICache_inv_tac.
        END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma fetchICache_inv_ok:
    forall o,
      reachable o fetchICacheInl ->
      fetchICache_inv o.
  Proof.
    intros; inv H; inv H0.
    eapply fetchICache_inv_ok'; eauto.
  Qed.

End Invariants.

