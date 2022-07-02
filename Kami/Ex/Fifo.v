Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringAsList.
Require Import Kami.Syntax Kami.Notations Kami.Semantics.
Require Import Kami.Wf Kami.Tactics.
Require Import FunctionalExtensionality Eqdep Eqdep_dec.

Set Implicit Arguments.
  
Section Fifo.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.

  Local Notation "^ s" := (fifoName -- s) (at level 0).

  Definition enq {ty} : forall (d: ty dType), ActionT ty Void := fun d =>
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

#[global] Hint Unfold fifo simpleFifo : ModuleDefs.
#[global] Hint Unfold enq deq firstElt : MethDefs.

Section Facts.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.

  Hypothesis HfifoName: index 0 indexSymbol fifoName = None.

  Lemma fifo_ModEquiv:
    ModPhoasWf (fifo fifoName sz dType).
  Proof. kequiv. Qed.
  #[local] Hint Resolve fifo_ModEquiv.

  Lemma simpleFifo_ModEquiv:
    ModPhoasWf (simpleFifo fifoName sz dType).
  Proof. kequiv. Qed.
  #[local] Hint Resolve simpleFifo_ModEquiv.

  Lemma fifo_ValidRegs:
    ModRegsWf (fifo fifoName sz dType).
  Proof. kvr. Qed.
  #[local] Hint Resolve fifo_ValidRegs.

  Lemma simpleFifo_ValidRegs:
    ModRegsWf (simpleFifo fifoName sz dType).
  Proof. kvr. Qed.
  #[local] Hint Resolve simpleFifo_ValidRegs.

End Facts.

#[global] Hint Resolve fifo_ModEquiv simpleFifo_ModEquiv.
#[global] Hint Resolve fifo_ValidRegs simpleFifo_ValidRegs.

