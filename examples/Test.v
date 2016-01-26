Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FMap.
Require Import Lts.Syntax Lts.Semantics.

Set Implicit Arguments.

Parameter i: nat.

Definition fbCm := MethodSig ("fb"__ i)() : Bool.

Definition ma := MODULE {
  Register "a" : Bool <- Default

  with Rule "ra" :=
    Call vb <- fbCm();
    Write "a" <- #vb;
    Retv
}.

Definition mb := MODULE {
  Register "b" : Bool <- true

  with Method ("fb"__ i)() : Bool :=
    Write "b" <- $$true;
    Read rb <- "b";
    Ret #rb
}.

Section Tests.

  Definition mab := ConcatMod ma mb.

End Tests.
