Require Import Arith.Peano_dec Bool String List.
Require Import Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics.
Require Import Kami.Wf Kami.Tactics.

Import ListNotations.

Set Implicit Arguments.

Definition primNormalFifoName: string := "FIFO".
Definition primPipelineFifoName: string := "PipelineFIFO".
Definition primBypassFifoName: string := "BypassFIFO".

Section PrimFifo.
  Variables (primFifoName fifoName: string)
            (sz: nat)
            (dType: Kind).

  Local Notation "^ s" := (fifoName -- s) (at level 0).

  Definition fifoEnq: MethodT {| arg := dType; ret := Void |} :=
    fun _ d =>
      (Read isFull <- ^"full";
       Assert !#isFull;
       Write ^"elt" <- #d;
       Write ^"full" <- $$true;
       Retv)%kami_action.

  Definition fifoDeq: MethodT {| arg := Void; ret := dType |} :=
    fun _ _ =>
      (Read isFull <- ^"full";
       Assert #isFull;
       Read elt <- ^"elt";
       Write ^"full" <- $$false;
       Ret #elt)%kami_action.

  Definition fifoFirstElt: MethodT {| arg := Void; ret := dType |} :=
    fun _ _ =>
      (Read isFull <- ^"full";
       Assert #isFull;
       Read elt <- ^"elt";
       Ret #elt)%kami_action.

  Definition fifoIsFull: MethodT {| arg := Void; ret := Bool |} :=
    fun _ _ =>
      (Read isFull <- ^"full";
       Ret #isFull)%kami_action.

  Definition fifoClear: MethodT {| arg := Void; ret := Void |} :=
    fun _ _ =>
      (Write ^"full" <- $$false;
       Retv)%kami_action.

  Definition fifo: Modules :=
    PrimMod
      {| pm_name := primFifoName;
         pm_regInits :=
           [^"elt" :: (RegInitDefault (SyntaxKind dType));
              ^"full" :: (RegInitDefault (SyntaxKind Bool))]%struct;
         pm_rules := nil;
         pm_methods :=
           [^"enq" :: (existT _ _ fifoEnq);
              ^"deq" :: (existT _ _ fifoDeq)]%struct
      |}.

  Definition fifoF: Modules :=
    PrimMod
      {| pm_name := primFifoName;
         pm_regInits :=
           [^"elt" :: (RegInitDefault (SyntaxKind dType));
              ^"full" :: (RegInitDefault (SyntaxKind Bool))]%struct;
         pm_rules := nil;
         pm_methods :=
           [^"enq" :: (existT _ _ fifoEnq);
              ^"deq" :: (existT _ _ fifoDeq);
              ^"isFull" :: (existT _ _ fifoIsFull)]%struct
      |}.

  Definition fifoC: Modules :=
    PrimMod
      {| pm_name := primFifoName;
         pm_regInits :=
           [^"elt" :: (RegInitDefault (SyntaxKind dType));
              ^"full" :: (RegInitDefault (SyntaxKind Bool))]%struct;
         pm_rules := nil;
         pm_methods :=
           [^"enq" :: (existT _ _ fifoEnq);
              ^"deq" :: (existT _ _ fifoDeq);
              ^"clear" :: (existT _ _ fifoClear)]%struct
      |}.

End PrimFifo.

#[global] Hint Unfold fifo fifoF fifoC: ModuleDefs.
#[global] Hint Unfold primPipelineFifoName primBypassFifoName
     fifoEnq fifoDeq fifoFirstElt fifoIsFull fifoClear: MethDefs.

Section Facts.
  Variables (primFifoName fifoName: string)
            (dType: Kind).

  Lemma fifo_ModEquiv:
    ModPhoasWf (fifo primFifoName fifoName dType).
  Proof.
    kequiv.
  Qed.
  #[local] Hint Resolve fifo_ModEquiv.

  Lemma fifoF_ModEquiv:
    ModPhoasWf (fifoF primFifoName fifoName dType).
  Proof.
    kequiv.
  Qed.
  #[local] Hint Resolve fifoF_ModEquiv.

  Lemma fifoC_ModEquiv:
    ModPhoasWf (fifoC primFifoName fifoName dType).
  Proof.
    kequiv.
  Qed.
  #[local] Hint Resolve fifoC_ModEquiv.

  Lemma fifo_ValidRegs:
    ModRegsWf (fifo primFifoName fifoName dType).
  Proof.
    kvr.
  Qed.
  #[local] Hint Resolve fifo_ValidRegs.

  Lemma fifoF_ValidRegs:
    ModRegsWf (fifoF primFifoName fifoName dType).
  Proof.
    kvr.
  Qed.
  #[local] Hint Resolve fifoF_ValidRegs.

  Lemma fifoC_ValidRegs:
    ModRegsWf (fifoC primFifoName fifoName dType).
  Proof.
    kvr.
  Qed.
  #[local] Hint Resolve fifoC_ValidRegs.

End Facts.

#[global] Hint Resolve fifo_ModEquiv fifoF_ModEquiv fifoC_ModEquiv.
#[global] Hint Resolve fifo_ValidRegs fifoF_ValidRegs fifoC_ValidRegs.

