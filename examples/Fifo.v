Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Tactics.

Require Import FunctionalExtensionality Eqdep Eqdep_dec.

Set Implicit Arguments.
  
Section Fifo.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.

  Notation "^ s" := (fifoName .. s) (at level 0).

  Definition enq {ty} : forall (d: ty dType), ActionT ty Void := fun d =>
    (Read isFull <- ^"full";
     Assert !#isFull;
     Read elt <- ^"elt";
     Read enqP <- ^"enqP";
     Read deqP <- ^"deqP";
     Write ^"elt" <- #elt@[#enqP <- #d];
     Write ^"empty" <- $$false;
     LET next_enqP <- (#enqP + $1) :: Bit sz;
     Write ^"full" <- (#deqP == #next_enqP);
     Write ^"enqP" <- #next_enqP;
     Retv)%kami.

  Definition deq {ty} : ActionT ty dType :=
    (Read isEmpty <- ^"empty";
     Assert !#isEmpty;
     Read elt <- ^"elt";
     Read enqP <- ^"enqP";
     Read deqP <- ^"deqP";
     Write ^"full" <- $$false;
     LET next_deqP <- (#deqP + $1) :: Bit sz;
     Write ^"empty" <- (#enqP == #next_deqP);
     Write ^"deqP" <- #next_deqP;
     Ret #elt@[#deqP])%kami.

  Definition fifo := MODULE {
    Register ^"elt" : Vector dType sz <- Default
    with Register ^"enqP" : Bit sz <- Default
    with Register ^"deqP" : Bit sz <- Default
    with Register ^"empty" : Bool <- true
    with Register ^"full" : Bool <- Default

    (* with Method ^"notFull"() : Bool := *)
    (*   Read isFull <- ^"full"; *)
    (*   Ret !#isFull *)

    (* with Method ^"notEmpty"() : Bool := *)
    (*   Read isEmpty <- ^"empty"; *)
    (*   Ret !#isEmpty *)

    with Method ^"enq"(d : dType) : Void := (enq d)
    with Method ^"deq"() : dType := deq

    with Method ^"firstElt"() : dType :=
      Read isEmpty <- ^"empty";
      Assert !#isEmpty;
      Read elt : Vector dType sz <- ^"elt";
      Read deqP <- ^"deqP";
      Ret #elt@[#deqP]
  }.

  Definition simpleFifo := MODULE {
    Register ^"elt" : Vector dType sz <- Default
    with Register ^"enqP" : Bit sz <- Default
    with Register ^"deqP" : Bit sz <- Default
    with Register ^"empty" : Bool <- true
    with Register ^"full" : Bool <- Default

    with Method ^"enq"(d : dType) : Void := (enq d)
    with Method ^"deq"() : dType := deq
  }.

End Fifo.

Hint Unfold fifo simpleFifo : ModuleDefs.
Hint Unfold enq deq : MethDefs.

Section Facts.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.

  Lemma fifo_ModEquiv:
    forall m,
      m = fifo fifoName sz dType ->
      ModEquiv type typeUT m.
  Proof.
    kequiv.
  Qed.

  Lemma simpleFifo_ModEquiv:
    forall m,
      m = simpleFifo fifoName sz dType ->
      ModEquiv type typeUT m.
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve fifo_ModEquiv simpleFifo_ModEquiv.

