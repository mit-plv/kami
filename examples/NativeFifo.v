Require Import Arith.Peano_dec Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv.
Require Import Ex.Fifo.

Set Implicit Arguments.

Section NativeFifo.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.
  Variable default: ConstT dType.

  Notation "^ s" := (fifoName .. s) (at level 0).

  Definition listEltT ty := list (ty dType).
  Definition listEltK ty := @NativeKind (listEltT ty) nil.
  Definition listElt ty := (^"elt" :: (@NativeConst (listEltT ty) nil nil))%struct.

  Definition listIsFull {ty} (l: fullType ty (listEltK ty)) :=
    if eq_nat_dec (length l) sz then ConstBool true else ConstBool false.
  Definition listIsEmpty {ty} (l: fullType ty (listEltK ty)) :=
    if eq_nat_dec (length l) 0 then ConstBool true else ConstBool false.
  Definition listEnq {ty} (a: ty dType) (l: fullType ty (listEltK ty)) :=
    a :: l.
  Definition listDeq {ty} (l: fullType ty (listEltK ty)) :=
    match l with
    | nil => nil
    | h :: t => t
    end.
  Definition listFirstElt {ty} (l: fullType ty (listEltK ty)): Expr ty (SyntaxKind dType) :=
    match l with
    | nil => ($$default)%kami
    | h :: t => (#h)%kami
    end.

  (* defined methods *)
  Definition enq {ty} : forall (d: ty dType), ActionT ty Void := fun d =>
    (ReadN elt : listEltK ty <- ^"elt";
     Assert !$$(listIsFull elt);
     Write ^"elt" <- (Var _ (listEltK ty) (listEnq d elt));
     Retv)%kami.

  Definition deq {ty} : ActionT ty dType :=
    (ReadN elt : listEltK ty <- ^"elt";
     Assert !$$(listIsEmpty elt);
     Write ^"elt" <- (Var _ (listEltK ty) (listDeq elt));
     Ret (listFirstElt elt))%kami.

  Definition firstElt {ty} : ActionT ty dType :=
    (ReadN elt : listEltK ty <- ^"elt";
     Assert !$$(listIsEmpty elt);
     Ret (listFirstElt elt))%kami.

  Definition fifo := MODULE {
    RegisterN ^"elt" : listEltK type <- (NativeConst nil nil)

    with Method ^"enq"(d : dType) : Void := (enq d)
    with Method ^"deq"() : dType := deq
    with Method ^"firstElt"() : dType := firstElt
  }.

  Definition simpleFifo := MODULE {
    RegisterN ^"elt" : listEltK type <- (NativeConst nil nil)

    with Method ^"enq"(d : dType) : Void := (enq d)
    with Method ^"deq"() : dType := deq
  }.

End NativeFifo.

Hint Unfold fifo simpleFifo : ModuleDefs.
Hint Unfold enq deq : MethDefs.

Require Import Refinement.

Section Facts.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.
  Variable default: ConstT dType.

  Definition realFifo := Fifo.fifo fifoName sz dType.
  Definition nativeFifo := @fifo fifoName sz dType default.

  Lemma fifo_refines_nativefifo: realFifo <<== nativeFifo.
  Proof.
    admit.
  Qed.

End Facts.

