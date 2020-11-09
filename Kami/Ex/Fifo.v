Require Import Bool String List.
Require Import Numbers.DecimalString.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringAsList.
Require Import Kami.Syntax Kami.Notations Kami.Semantics.
Require Import Kami.Wf Kami.Tactics.
Require Import FunctionalExtensionality Eqdep Eqdep_dec.

Set Implicit Arguments.

Section Fifo.
  Variables (fifoName: string)
            (sz: nat)
            (dType: Kind).

  Local Notation "^ s" := (fifoName -- s) (at level 0).

  Definition enq {ty} : forall (d: ty dType), ActionT ty Void :=
    fun d =>
      (Read isFull <- ^"full";
      Assert !#isFull;
      Read eltT <- ^"elt";
      Read enqPT <- ^"enqP";
      Read deqPT <- ^"deqP";
      Write ^"elt" <- #eltT@[#enqPT <- #d];
      Write ^"empty" <- $$false;
      LET next_enqP <- (#enqPT + $1) :: Bit sz;
      Write ^"full" <- (#deqPT == #next_enqP);
      Write ^"enqP" <- #next_enqP;
      Retv)%kami_action.

  Definition deq {ty} : ActionT ty dType :=
    (Read isEmpty <- ^"empty";
    Assert !#isEmpty;
    Read eltT <- ^"elt";
    Read enqPT <- ^"enqP";
    Read deqPT <- ^"deqP";
    Write ^"full" <- $$false;
    LET next_deqP <- (#deqPT + $1) :: Bit sz;
    Write ^"empty" <- (#enqPT == #next_deqP);
    Write ^"deqP" <- #next_deqP;
    Ret #eltT@[#deqPT])%kami_action.

  Definition firstElt {ty} : ActionT ty dType :=
    (Read isEmpty <- ^"empty";
    Assert !#isEmpty;
    Read eltT : Vector dType sz <- ^"elt";
    Read deqPT <- ^"deqP";
    Ret #eltT@[#deqPT])%kami_action.

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

End Fifo.

Hint Unfold fifo simpleFifo: ModuleDefs.
Hint Unfold enq deq firstElt: MethDefs.

Section DebugFifo.
  Variables (fifoName: string)
            (dType: Kind)
            (cntSz: nat).

  Local Notation "^ s" := (fifoName -- s) (at level 0).

  Variables (dmsg: string) (disp: forall ty, ty dType -> list (Disp ty)).

  Definition debugEnq {ty}: forall (d: ty dType), ActionT ty Void :=
    fun d =>
      (Read isFull <- ^"full";
      Assert !#isFull;
      Write ^"elt" <- #d;
      Write ^"full" <- $$true;
      Retv)%kami_action.

  Definition debugDeq {ty}: ActionT ty dType :=
    (Read isFull <- ^"full";
    Assert #isFull;
    Read delt <- ^"elt";
    Write ^"full" <- $$false;
    Ret #delt)%kami_action.

  Definition debugCount {ty}: ActionT ty Void :=
    (Read countDone <- ^"countDone";
    Assert !#countDone;
    Read count: Bit cntSz <- ^"counter";
    Write ^"counter" <- #count + $1;
    Read isFull <- ^"full";
    If (#count == $(Nat.pow 2 cntSz - 1) && #isFull)
     then (Read elt: dType <- ^"elt";
          Display dmsg (disp _ elt) (Write ^"countDone" <- $$true; Retv));
     Retv)%kami_action.

  Definition debugFifo := MODULE {
    Register ^"elt" : dType <- Default
    with Register ^"full" : Bool <- Default
    with Register ^"countDone" : Bool <- Default
    with Register ^"counter" : Bit cntSz <- Default
    with Rule ^"count" := debugCount
    with Method ^"enq"(d : dType) : Void := (debugEnq d)
    with Method ^"deq"() : dType := debugDeq
  }.

End DebugFifo.

Hint Unfold debugFifo: ModuleDefs.
Hint Unfold debugEnq debugDeq: MethDefs.

Section DebugFifoN.
  Variables (fifoName: string)
            (sz: nat)
            (dType: Kind)
            (cntSz: nat).

  Local Notation "^ s" := (fifoName -- s) (at level 0).

  Variables (dmsg: string) (disp: forall ty, ty dType -> list (Disp ty)).

  Definition debugEnqN {ty} : forall (d: ty dType), ActionT ty Void :=
    fun d =>
      (Read isFull <- ^"full";
      Assert !#isFull;
      Read eltT <- ^"elt";
      Read enqPT <- ^"enqP";
      Read deqPT <- ^"deqP";
      Write ^"elt" <- #eltT@[#enqPT <- #d];
      Write ^"empty" <- $$false;
      LET next_enqP <- (#enqPT + $1) :: Bit sz;
      Write ^"full" <- (#deqPT == #next_enqP);
      Write ^"enqP" <- #next_enqP;
      Retv)%kami_action.

  Definition debugDeqN {ty} : ActionT ty dType :=
    (Read isEmpty <- ^"empty";
    Assert !#isEmpty;
    Read eltT <- ^"elt";
    Read enqPT <- ^"enqP";
    Read deqPT <- ^"deqP";
    Write ^"full" <- $$false;
    LET next_deqP <- (#deqPT + $1) :: Bit sz;
    Write ^"empty" <- (#enqPT == #next_deqP);
    Write ^"deqP" <- #next_deqP;
    Ret #eltT@[#deqPT])%kami_action.

  Local Definition nat_to_string (n: nat): string :=
    NilEmpty.string_of_uint (Nat.to_uint n).

  Fixpoint displayN {ty} (elts: ty (Vector dType sz))
           (n: nat) (cont: ActionT ty Void): ActionT ty Void :=
    match n with
    | O => cont
    | S n' => (LET elt <- #elts@[$n'];
              Display (dmsg ++ nat_to_string n')
                      (disp _ elt) (displayN elts n' cont))%kami_action
    end.

  Definition debugCountN {ty}: ActionT ty Void :=
    (Read countDone <- ^"countDone";
    Assert !#countDone;
    Read count: Bit cntSz <- ^"counter";
    Write ^"counter" <- #count + $1;
    Read isFull <- ^"full";
    If (#count == $(Nat.pow 2 cntSz - 1) && #isFull)
     then (Read elt: Vector dType sz <- ^"elt";
          displayN elt (Nat.pow 2 sz) (Write ^"countDone" <- $$true; Retv));
     Retv)%kami_action.

  Definition debugFifoN := MODULE {
    Register ^"elt" : Vector dType sz <- Default
    with Register ^"enqP" : Bit sz <- Default
    with Register ^"deqP" : Bit sz <- Default
    with Register ^"empty" : Bool <- true
    with Register ^"full" : Bool <- Default
    with Register ^"countDone" : Bool <- Default
    with Register ^"counter" : Bit cntSz <- Default
    with Rule ^"count" := debugCountN
    with Method ^"enq"(d : dType) : Void := (debugEnqN d)
    with Method ^"deq"() : dType := debugDeqN
  }.

End DebugFifoN.

Hint Unfold debugFifoN: ModuleDefs.
Hint Unfold displayN debugEnqN debugDeqN: MethDefs.

Section Facts.
  Variables (fifoName: string)
            (sz: nat)
            (dType: Kind).

  Lemma fifo_ModEquiv:
    ModPhoasWf (fifo fifoName sz dType).
  Proof. kequiv. Qed.
  Hint Resolve fifo_ModEquiv.

  Lemma simpleFifo_ModEquiv:
    ModPhoasWf (simpleFifo fifoName sz dType).
  Proof. kequiv. Qed.
  Hint Resolve simpleFifo_ModEquiv.

  Lemma fifo_ValidRegs:
    ModRegsWf (fifo fifoName sz dType).
  Proof. kvr. Qed.
  Hint Resolve fifo_ValidRegs.

  Lemma simpleFifo_ValidRegs:
    ModRegsWf (simpleFifo fifoName sz dType).
  Proof. kvr. Qed.
  Hint Resolve simpleFifo_ValidRegs.

  Variables (cntSz: nat)
            (dmsg: string)
            (disp: forall ty, ty dType -> list (Disp ty)).

  Lemma debugFifo_ModEquiv:
    ModPhoasWf (debugFifo fifoName cntSz dmsg disp).
  Proof. kequiv. Qed.
  Hint Resolve debugFifo_ModEquiv.

  Lemma debugFifoN_ModEquiv:
    ModPhoasWf (debugFifoN fifoName sz cntSz dmsg disp).
  Proof.
    kequiv.
    induction (Nat.pow 2 sz); simpl; kequiv.
    assumption.
  Qed.
  Hint Resolve debugFifoN_ModEquiv.

  Lemma debugFifo_ValidRegs:
    ModRegsWf (debugFifo fifoName cntSz dmsg disp).
  Proof. kvr. Qed.
  Hint Resolve debugFifo_ValidRegs.

  Lemma debugFifoN_ValidRegs:
    ModRegsWf (debugFifoN fifoName sz cntSz dmsg disp).
  Proof.
    kvr.
    induction (Nat.pow 2 sz); simpl; kvr.
    assumption.
  Qed.
  Hint Resolve debugFifoN_ValidRegs.

End Facts.

Hint Resolve fifo_ModEquiv simpleFifo_ModEquiv
     debugFifo_ModEquiv debugFifoN_ModEquiv.
Hint Resolve fifo_ValidRegs simpleFifo_ValidRegs
     debugFifo_ValidRegs debugFifoN_ValidRegs.
