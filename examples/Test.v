Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq Lib.Indexer.

Require Import Lts.Syntax Lts.Notations Lts.Semantics Lts.Wf.
Require Import Lts.Inline Lts.InlineFacts.
Require Import Lts.RefinementFacts Lts.Decomposition.
Require Import Lts.Tactics.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

Definition fbCm := MethodSig "fb"() : Bool.

Definition ma := MODULE {
  Register "a" : Bool <- Default

  with Rule "ra" :=
    Call vb <- fbCm();
    Write "a" <- #vb;
    Retv
}.

Definition mb := MODULE {
  Register "b" : Bool <- true

  with Method "fb"() : Bool :=
    Write "b" <- $$true;
    Read rb <- "b";
    Ret #rb
}.

Definition mc := MODULE {
  Register "a" : Bool <- Default
  with Register "b" : Bool <- true

  with Rule "ra" :=                           
    Write "b" <- $$true;
    Read rb : Bool <- "b";
    Write "a" <- #rb;
    Retv
}.


