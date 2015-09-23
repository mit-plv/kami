Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FnMap.
Require Import Lts.Syntax Lts.Semantics.

Require Import FunctionalExtensionality Eqdep Eqdep_dec.

Set Implicit Arguments.

Section Fifo.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.

  Notation "^ s" := (fifoName -n- s) (at level 0).

  Definition max_index : ConstT (Bit sz) := ^~ $1.

  Definition fifo := MODULE {{
    Register ^"elt" : Vector dType sz <- Default
    with Register ^"enqP" : Bit sz <- Default
    with Register ^"deqP" : Bit sz <- Default
    with Register ^"empty" : Bool <- true
    with Register ^"full" : Bool <- Default

    with Method ^"notFull"() : Bool :=
      Read isFull <- ^"full";
      Ret !#isFull

    with Method ^"notEmpty"() : Bool :=
      Read isEmpty <- ^"empty";
      Ret !#isEmpty

    with Method ^"enq"(d : dType) : Void :=
      Read isFull <- ^"full";
      Assert !#isFull;
      Read elt <- ^"elt";
      Read enqP <- ^"enqP";
      Read deqP <- ^"deqP";
      Write ^"elt" <- #elt@[#enqP <- #d];
      Write ^"empty" <- $$false;
      Let next_enqP <- IF #enqP == $$max_index then $0 else #enqP + $1;
      Write ^"full" <- (#deqP == #next_enqP);
      Write ^"enqP" <- #next_enqP;
      Retv

    with Method ^"deq"() : dType :=
      Read isEmpty <- ^"empty";
      Assert !#isEmpty;
      Read elt <- ^"elt";
      Read enqP <- ^"enqP";
      Read deqP <- ^"deqP";
      Write ^"full" <- $$false;
      Let next_deqP : Bit sz <- IF #deqP == $$max_index then $0 else #enqP + $1;
      Write ^"empty" <- (#enqP == #next_deqP);
      Write ^"deqP" <- #next_deqP;
      Ret #elt@[#deqP]

    with Method ^"firstElt"() : dType :=
      Read isEmpty <- ^"empty";
      Assert !#isEmpty;
      Read elt : Vector dType sz <- ^"elt";
      Read deqP <- ^"deqP";
      Ret #elt@[#deqP]
  }}.

  Definition simpleFifo := MODULE {{
    Register ^"elt" : Vector dType sz <- Default
    with Register ^"enqP" : Bit sz <- Default
    with Register ^"deqP" : Bit sz <- Default
    with Register ^"empty" : Bool <- true
    with Register ^"full" : Bool <- Default

    with Method ^"enq"(d : dType) : Void :=
      Read isFull <- ^"full";
      Assert !#isFull;
      Read elt <- ^"elt";
      Read enqP <- ^"enqP";
      Read deqP <- ^"deqP";
      Write ^"elt" <- #elt@[#enqP <- #d];
      Write ^"empty" <- $$false;
      Let next_enqP <- IF #enqP == $$max_index then $0 else #enqP + $1;
      Write ^"full" <- (#deqP == #next_enqP);
      Write ^"enqP" <- #next_enqP;
      Retv

    with Method ^"deq"() : dType :=
      Read isEmpty <- ^"empty";
      Assert !#isEmpty;
      Read elt <- ^"elt";
      Read enqP <- ^"enqP";
      Read deqP <- ^"deqP";
      Write ^"full" <- $$false;
      Let next_deqP : Bit sz <- IF #deqP == $$max_index then $0 else #enqP + $1;
      Write ^"empty" <- (#enqP == #next_deqP);
      Write ^"deqP" <- #next_deqP;
      Ret #elt@[#deqP]
  }}.

  Section Spec.
    Lemma regsInDomain_simpleFifo: RegsInDomain simpleFifo.
    Proof.
      unfold RegsInDomain; intros; inv H.
      destruct rm; [inv Hltsmod; inv HInRule|].
      invertSemModRep; invertActionRep; inDomain_tac.
    Qed.
  End Spec.

End Fifo.

Hint Unfold fifo simpleFifo : ModuleDefs.
