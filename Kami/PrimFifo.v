Require Import Arith.Peano_dec Bool String List.
Require Import Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics.
Require Import Kami.Wf Kami.Tactics.

Set Implicit Arguments.

Definition primFifoName: string := "FIFO".

Section ListAsFifo.
  Variable (sz: nat).
  Context {dType: Kind}.

  Definition listIsEmpty {ty} (l: list (ty dType)) :=
    match l with
    | nil => ConstBool true
    | _ => ConstBool false
    end.
  
  Definition listIsFull {ty} (l: list (ty dType)) :=
    if eq_nat_dec (List.length l) sz
    then ConstBool true
    else ConstBool false.
  
  Definition listEnq {ty} (a: ty dType) (l: list (ty dType)) :=
    l ++ [a].

  Definition listDeq {ty} (l: list (ty dType)) :=
    match l with
    | nil => nil
    | h :: t => t
    end.
  
  Definition listFirstElt {ty} (l: list (ty dType)): Expr ty (SyntaxKind dType) :=
    match l with
    | nil => ($$Default)%kami_expr
    | h :: t => (#h)%kami_expr
    end.

End ListAsFifo.

Section PrimFifo.
  Variables (fifoName: string)
            (sz: nat)
            (dType: Kind).

  Local Notation "^ s" := (fifoName -- s) (at level 0).

  Definition fifoEltT ty := list (ty dType).
  Definition fifoEltK ty := @NativeKind (fifoEltT ty) nil.
  Definition fifoElt ty := (^"elt" :: (@NativeConst (fifoEltT ty) nil nil))%struct.

  Definition fifoEnq: forall ty (d: ty dType), ActionT ty Void :=
    fun ty d =>
      (ReadN eltT : fifoEltK ty <- ^"elt";
       Assert !$$(listIsFull sz eltT);
       Write ^"elt" <- (Var _ (fifoEltK ty) (listEnq d eltT));
       Retv)%kami_action.

  Definition fifoDeq: forall ty (_: ty Void), ActionT ty dType :=
    fun ty _ =>
      (ReadN eltT : fifoEltK ty <- ^"elt";
       Assert !$$(listIsEmpty eltT);
       Write ^"elt" <- (Var _ (fifoEltK ty) (listDeq eltT));
       Ret (listFirstElt eltT))%kami_action.

  Definition fifoFirstElt: forall ty (_: ty Void), ActionT ty dType :=
    fun ty _ =>
      (ReadN elt : fifoEltK ty <- ^"elt";
       Assert !$$(listIsEmpty elt);
       Ret (listFirstElt elt))%kami_action.

  Definition fifo: Modules :=
    PrimMod
      {| pm_name := primFifoName;
         pm_regInits :=
           [(^"elt" :: (RegInitCustom (existT ConstFullT (fifoEltK type)
                                              (NativeConst nil nil))))%struct];
         pm_rules := nil;
         pm_methods :=
           [(^"enq" :: (existT _ {| arg:= _; ret:= _ |} fifoEnq))%struct;
              (^"deq" :: (existT _ {| arg:= _; ret:= _ |} fifoDeq))%struct;
              (^"firstElt" :: (existT _ {| arg:= _; ret:= _ |} fifoFirstElt))%struct]
      |}.

  Definition simpleFifo: Modules :=
    PrimMod
      {| pm_name := primFifoName;
         pm_regInits :=
           [(^"elt" :: (RegInitCustom (existT ConstFullT (fifoEltK type)
                                              (NativeConst nil nil))))%struct];
         pm_rules := nil;
         pm_methods :=
           [(^"enq" :: (existT _ {| arg:= _; ret:= _ |} fifoEnq))%struct;
              (^"deq" :: (existT _ {| arg:= _; ret:= _ |} fifoDeq))%struct]
      |}.

End PrimFifo.

Hint Unfold fifo simpleFifo : ModuleDefs.
Hint Unfold listIsEmpty listIsFull listEnq listDeq listFirstElt
     primFifoName fifoEltT fifoEltK fifoElt
     fifoEnq fifoDeq fifoFirstElt: MethDefs.

Section Facts.
  Variables (fifoName: string)
            (sz: nat)
            (dType: Kind).

  Lemma fifo_ModEquiv:
    ModPhoasWf (fifo fifoName sz dType).
  Proof.
    kequiv.
  Qed.
  Hint Resolve fifo_ModEquiv.

  Lemma simpleFifo_ModEquiv:
    ModPhoasWf (simpleFifo fifoName sz dType).
  Proof.
    kequiv.
  Qed.
  Hint Resolve simpleFifo_ModEquiv.

  Lemma fifo_ValidRegs:
    ModRegsWf (fifo fifoName sz dType).
  Proof.
    kvr.
  Qed.
  Hint Resolve fifo_ValidRegs.

  Lemma simpleFifo_ValidRegs:
    ModRegsWf (simpleFifo fifoName sz dType).
  Proof.
    kvr.
  Qed.
  Hint Resolve simpleFifo_ValidRegs.

End Facts.

Hint Resolve fifo_ModEquiv simpleFifo_ModEquiv.
Hint Resolve fifo_ValidRegs simpleFifo_ValidRegs.

