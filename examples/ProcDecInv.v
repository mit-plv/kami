Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Inline Lts.InlineFacts_2 Lts.DecompositionZero.
Require Import Lts.Tactics Lts.Notations.
Require Import Ex.MemTypes Ex.SC Ex.NativeFifo Ex.MemAtomic Ex.ProcDec Ex.ProcDecInl.
Require Import Eqdep ProofIrrelevance.

Set Implicit Arguments.

Section Invariants.
  Variables addrSize lgDataBytes rfIdx: nat.

  Variable dec: DecT 2 addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT 2 addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT 2 addrSize lgDataBytes rfIdx.

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  Definition pdecInl := pdecInl dec execState execNextPc.

  Definition procDec_inv_0 (o: RegsT): Prop.
  Proof.
    kexistv "pc"%string pcv o (Bit addrSize).
    kexistv "rf"%string rfv o (Vector (Data lgDataBytes) rfIdx).
    kexistv "stall"%string stallv o Bool.
    kexistnv "rqFromProc"--"elt" ieltv o (listEltK RqFromProc type).
    kexistnv "rsToProc"--"elt" oeltv o (listEltK RsToProc type).
    exact True.
  Defined.
  Hint Unfold procDec_inv_0: InvDefs.

  Definition fifo_empty_inv {A} (elt: list A) :=
    elt = nil.
  
  Definition fifo_not_empty_inv {A} (elt: list A) :=
    exists e, elt = e :: nil.
    (* length elt = 1. *)

  Definition mem_request_inv
             (pc: fullType type (SyntaxKind (Bit addrSize)))
             (rf: fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx)))
             (insElt: list (type RqFromProc)): Prop.
  Proof.
    refine (match insElt with nil => True | _ => _ end).
    refine (_ /\ _ /\ _).
    - refine (_ /\ _).
      + exact ((if weq (evalExpr (dec _ rf pc) ``"opcode") (evalConstT opLd)
                then false else true) = hd (evalConstT Default) insElt ``"op").
      + exact ((if weq (evalExpr (dec _ rf pc) ``"opcode") (evalConstT opSt)
                then true else false) = hd (evalConstT Default) insElt ``"op").
    - exact (hd (evalConstT Default) insElt ``"addr" = evalExpr (dec _ rf pc) ``"addr").
    - refine (if (hd (evalConstT Default) insElt ``"op") : bool then _ else _).
      + exact (hd (evalConstT Default) insElt ``"data" = evalExpr (dec _ rf pc) ``"value").
      + exact (hd (evalConstT Default) insElt ``"data" =
               evalConstT (getDefaultConst (Data lgDataBytes))).
  Defined.
  Hint Unfold fifo_empty_inv fifo_not_empty_inv mem_request_inv: InvDefs.
  Hint Unfold evalConstT: MethDefs.

  Definition procDec_inv_1 (o: RegsT): Prop.
  Proof.
    kexistv "pc"%string pcv o (Bit addrSize).
    kexistv "rf"%string rfv o (Vector (Data lgDataBytes) rfIdx).
    kexistv "stall"%string stallv o Bool.
    kexistnv "rqFromProc"--"elt" ieltv o (listEltK RqFromProc type).
    kexistnv "rsToProc"--"elt" oeltv o (listEltK RsToProc type).
    refine (or3 _ _ _).
    - exact (v1 = false /\ fifo_empty_inv v2 /\ fifo_empty_inv v3).
    - refine (_ /\ _).
      + exact (v1 = true /\ fifo_not_empty_inv v2 /\ fifo_empty_inv v3).
      + exact (mem_request_inv v v0 v2).
    - exact (v1 = true /\ fifo_empty_inv v2 /\ fifo_not_empty_inv v3).
  Defined.
  Hint Unfold procDec_inv_1: InvDefs.

  Lemma procDec_inv_0_ok':
    forall init n ll,
      init = initRegs (getRegInits (fst pdecInl)) ->
      Multistep (fst pdecInl) init n ll ->
      procDec_inv_0 n.
  Proof. (* SKIP_PROOF_ON
    induction 2.

    - kinv_magic_light.

    - kinvert.
      + kinv_magic_light.
      + kinv_magic_light.
      + kinv_magic_light.
      + kinv_magic_light.
      + kinv_magic_light.
      + kinv_magic_light.
      + kinv_magic_light.
      + kinv_magic_light.
      + kinv_magic_light.
      + kinv_magic_light.
        END_SKIP_PROOF_ON *) admit.
  Qed.

  Lemma procDec_inv_0_ok:
    forall o,
      reachable o (fst pdecInl) ->
      procDec_inv_0 o.
  Proof.
    intros; inv H; inv H0.
    eapply procDec_inv_0_ok'; eauto.
  Qed.

  Ltac procDec_inv_1_tac :=
    kinv_or3;
    repeat
      match goal with
      | [ |- _ /\ _ ] => split
      | [ |- exists _, _ ] => eexists
      end.

  Lemma procDec_inv_1_ok':
    forall init n ll,
      init = initRegs (getRegInits (fst pdecInl)) ->
      Multistep (fst pdecInl) init n ll ->
      procDec_inv_1 n.
  Proof. (* SKIP_PROOF_ON
    induction 2.

    - kinv_magic_light_with procDec_inv_1_tac.
      or3_fst; kinv_magic_light_with procDec_inv_1_tac.

    - kinvert.
      + mred.
      + mred.
      + kinv_magic_light_with kinv_or3.
        or3_snd; kinv_magic_light_with procDec_inv_1_tac.
        * kinv_finish.
        * kinv_finish.
      + kinv_magic_light_with kinv_or3.
        or3_snd; kinv_magic_light_with procDec_inv_1_tac.
        * kinv_finish.
        * kinv_finish.
      + kinv_magic_light_with kinv_or3.
        or3_fst; kinv_magic_light_with procDec_inv_1_tac.
      + kinv_magic_light_with kinv_or3.
        or3_fst; kinv_magic_light_with procDec_inv_1_tac.
      + kinv_magic_light_with kinv_or3.
        or3_fst; kinv_magic_light_with procDec_inv_1_tac.
      + kinv_magic_light_with kinv_or3.
        or3_fst; kinv_magic_light_with procDec_inv_1_tac.
      + kinv_magic_light_with kinv_or3.
        or3_thd; kinv_magic_light_with procDec_inv_1_tac.
      + kinv_magic_light_with kinv_or3.
        or3_thd; kinv_magic_light_with procDec_inv_1_tac.
        END_SKIP_PROOF_ON *) admit.
  Qed.

  Lemma procDec_inv_1_ok:
    forall o,
      reachable o (fst pdecInl) ->
      procDec_inv_1 o.
  Proof.
    intros; inv H; inv H0.
    eapply procDec_inv_1_ok'; eauto.
  Qed.

End Invariants.

Hint Unfold RqFromProc RsToProc: MethDefs.
Hint Unfold procDec_inv_0 procDec_inv_1
     fifo_empty_inv fifo_not_empty_inv mem_request_inv: InvDefs.

