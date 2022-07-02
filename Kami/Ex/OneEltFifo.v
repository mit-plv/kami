Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Wf Kami.Tactics.

(* A fifo containing only one element.
 * Implementation is much simpler than the general fifo, implemented in Fifo.v
 *)
Section OneEltFifo.
  Variable fifoName: string.
  Variable dType: Kind.

  Local Notation "^ s" := (fifoName -- s) (at level 0).

  Definition enq {ty} : forall (d: ty dType), ActionT ty Void := fun d =>
    (Read isFull <- ^"full";
     Assert !#isFull;
     Write ^"elt" <- #d;
     Write ^"full" <- $$true;
     Retv)%kami_action.

  Definition deq {ty} : ActionT ty dType :=
    (Read isFull <- ^"full";
     Assert #isFull;
     Read elt <- ^"elt";
     Write ^"full" <- $$false;
     Ret #elt)%kami_action.

  Definition firstElt {ty} : ActionT ty dType :=
    (Read isFull <- ^"full";
     Assert #isFull;
     Read elt <- ^"elt";
     Ret #elt)%kami_action.

  Definition isFull {ty} : ActionT ty Bool :=
    (Read isFull <- ^"full";
     Ret #isFull)%kami_action.

  Definition flush {ty} : ActionT ty Void :=
    (Write ^"full" <- $$false;
     Retv)%kami_action.
  
  Definition oneEltFifo := MODULE {
    Register ^"elt" : dType <- Default
    with Register ^"full" : Bool <- Default

    with Method ^"enq"(d : dType) : Void := (enq d)
    with Method ^"deq"() : dType := deq
  }.

  Definition oneEltFifoEx1 := MODULE {
    Register ^"elt" : dType <- Default
    with Register ^"full" : Bool <- Default

    with Method ^"enq"(d : dType) : Void := (enq d)
    with Method ^"deq"() : dType := deq
    with Method ^"isFull"() : Bool := isFull
  }.

  Definition oneEltFifoEx2 := MODULE {
    Register ^"elt" : dType <- Default
    with Register ^"full" : Bool <- Default

    with Method ^"enq"(d : dType) : Void := (enq d)
    with Method ^"deq"() : dType := deq
    with Method ^"flush"() : Void := flush
  }.

  Lemma oneEltFifo_PhoasWf: ModPhoasWf oneEltFifo.
  Proof. kequiv. Qed.
  Lemma oneEltFifo_RegsWf: ModRegsWf oneEltFifo.
  Proof. kvr. Qed.

  Lemma oneEltFifoEx1_PhoasWf: ModPhoasWf oneEltFifoEx1.
  Proof. kequiv. Qed.
  Lemma oneEltFifoEx1_RegsWf: ModRegsWf oneEltFifoEx1.
  Proof. kvr. Qed.

  Lemma oneEltFifoEx2_PhoasWf: ModPhoasWf oneEltFifoEx2.
  Proof. kequiv. Qed.
  Lemma oneEltFifoEx2_RegsWf: ModRegsWf oneEltFifo.
  Proof. kvr. Qed.
  
End OneEltFifo.

#[global] Hint Resolve oneEltFifo_PhoasWf oneEltFifo_RegsWf.
#[global] Hint Resolve oneEltFifoEx1_PhoasWf oneEltFifoEx1_RegsWf.
#[global] Hint Resolve oneEltFifoEx2_PhoasWf oneEltFifoEx2_RegsWf.

#[global] Hint Unfold oneEltFifo oneEltFifoEx1 oneEltFifoEx2 : ModuleDefs.
#[global] Hint Unfold enq deq firstElt isFull flush : MethDefs.

