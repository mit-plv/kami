Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Notations Lts.Semantics Lts.Equiv Lts.Tactics.

Require Import FunctionalExtensionality Eqdep Eqdep_dec.

Set Implicit Arguments.
  
Section Fifo.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.

  Notation "^ s" := (fifoName -- s) (at level 0).

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
     Retv)%kami_action.

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
     Ret #elt@[#deqP])%kami_action.

  Definition firstElt {ty} : ActionT ty dType :=
    (Read isEmpty <- ^"empty";
     Assert !#isEmpty;
     Read elt : Vector dType sz <- ^"elt";
     Read deqP <- ^"deqP";
     Ret #elt@[#deqP])%kami_action.
  
  Definition fifo := MODULE {
    Register ^"elt" : Vector dType sz <- Default
    with Register ^"enqP" : Bit sz <- Default
    with Register ^"deqP" : Bit sz <- Default
    with Register ^"empty" : Bool <- true
    with Register ^"full" : Bool <- Default

    with Method ^"enq"(d : dType) : Void := (enq d)
    with Method ^"deq"() : dType := deq
    with Method ^"firstElt"() : dType := firstElt
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

  (** SinAction version *)
  Hypothesis HfifoName: index 0 indexSymbol fifoName = None.
  Lemma fgn:
    forall s, index 0 indexSymbol s = None -> index 0 indexSymbol (^s) = None.
  Proof.
    pose proof HfifoName.
    admit.
  Qed.

  Definition enqS {ty} : forall (d: ty dType), SinActionT ty Void := fun d =>
    (Read isFull <- { ^"full" | fgn "full" eq_refl };
     Assert !#isFull;
     Read elt <- { ^"elt" | fgn "elt" eq_refl };
     Read enqP <- { ^"enqP" | fgn "enqP" eq_refl };
     Read deqP <- { ^"deqP" | fgn "deqP" eq_refl };
     Write { ^"elt" | fgn "elt" eq_refl } <- #elt@[#enqP <- #d];
     Write { ^"empty" | fgn "empty" eq_refl } <- $$false;
     LET next_enqP <- (#enqP + $1) :: Bit sz;
     Write { ^"full" | fgn "full" eq_refl } <- (#deqP == #next_enqP);
     Write { ^"enqP" | fgn "enqP" eq_refl } <- #next_enqP;
     Retv)%kami_sin.

  Definition deqS {ty} : SinActionT ty dType :=
    (Read isEmpty <- { ^"empty" | fgn "empty" eq_refl };
     Assert !#isEmpty;
     Read elt <- { ^"elt" | fgn "elt" eq_refl };
     Read enqP <- { ^"enqP" | fgn "enqP" eq_refl };
     Read deqP <- { ^"deqP" | fgn "deqP" eq_refl };
     Write { ^"full" | fgn "full" eq_refl } <- $$false;
     LET next_deqP <- (#deqP + $1) :: Bit sz;
     Write { ^"empty" | fgn "empty" eq_refl } <- (#enqP == #next_deqP);
     Write { ^"deqP" | fgn "deqP" eq_refl } <- #next_deqP;
     Ret #elt@[#deqP])%kami_sin.

  Definition firstEltS {ty} : SinActionT ty dType :=
    (Read isEmpty <- { ^"empty" | fgn "empty" eq_refl };
     Assert !#isEmpty;
     Read elt : Vector dType sz <- { ^"elt" | fgn "elt" eq_refl };
     Read deqP <- { ^"deqP" | fgn "deqP" eq_refl };
     Ret #elt@[#deqP])%kami_sin.
  
  Definition fifoS := SIN {
    Register { ^"elt" | fgn "elt" eq_refl } : Vector dType sz <- Default
    with Register { ^"enqP" | fgn "enqP" eq_refl } : Bit sz <- Default
    with Register { ^"deqP" | fgn "deqP" eq_refl } : Bit sz <- Default
    with Register { ^"empty" | fgn "empty" eq_refl } : Bool <- true
    with Register { ^"full" | fgn "full" eq_refl } : Bool <- Default

    with Method { ^"enq" | fgn "enq" eq_refl }(d : dType) : Void := (enqS d)
    with Method { ^"deq" | fgn "deq" eq_refl }() : dType := deqS
    with Method { ^"firstElt" | fgn "firstElt" eq_refl }() : dType := firstEltS
  }.

  Definition simpleFifoS := SIN {
    Register { ^"elt" | fgn "elt" eq_refl } : Vector dType sz <- Default
    with Register { ^"enqP" | fgn "enqP" eq_refl } : Bit sz <- Default
    with Register { ^"deqP" | fgn "deqP" eq_refl } : Bit sz <- Default
    with Register { ^"empty" | fgn "empty" eq_refl } : Bool <- true
    with Register { ^"full" | fgn "full" eq_refl } : Bool <- Default

    with Method { ^"enq" | fgn "enq" eq_refl }(d : dType) : Void := (enqS d)
    with Method { ^"deq" | fgn "deq" eq_refl }() : dType := deqS
  }.
  
End Fifo.

Hint Unfold fifo simpleFifo : ModuleDefs.
Hint Unfold enq deq firstElt : MethDefs.

Hint Unfold fifoS simpleFifoS : ModuleDefs.
Hint Unfold enqS deqS firstEltS : MethDefs.

Section Facts.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.

  Hypothesis HfifoName: index 0 indexSymbol fifoName = None.

  (*
  Lemma fifo_fifoS:
    fifo fifoName sz dType = ParametricSyntax.makeModule (fifoS fifoName sz dType HfifoName).
  Proof. reflexivity. Qed.

  Lemma simpleFifo_simpleFifoS:
    simpleFifo fifoName sz dType =
    ParametricSyntax.makeModule (simpleFifoS fifoName sz dType HfifoName).
  Proof. reflexivity. Qed.
   *)

  Lemma fifo_ModEquiv:
    forall m,
      m = fifo fifoName sz dType ->
      (forall ty1 ty2, ModEquiv ty1 ty2 m).
  Proof.
    kequiv.
  Qed.

  Lemma simpleFifo_ModEquiv:
    forall m,
      m = simpleFifo fifoName sz dType ->
      (forall ty1 ty2, ModEquiv ty1 ty2 m).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve fifo_ModEquiv simpleFifo_ModEquiv.

