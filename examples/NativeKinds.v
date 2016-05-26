Require Import String Streams.
Require Import Lib.Indexer List.
Require Import Lts.Syntax Lts.Notations Lts.Semantics.

Set Implicit Arguments.

Section StreamMod.
  Variable modName: string.
  Variable A : Kind.
  Variable default : ConstT A.
  Variable stream : Stream (ConstT A).

  Definition nk := NativeKind (const default).

  Notation "^ s" := (modName -- s) (at level 0).

  Definition streamMod := MODULE {
    RegisterN ^"stream" : nk <- (NativeConst _ stream)

    with Method ^"get"() : A :=
    (ReadReg (^"stream") nk (fun s => 
    WriteReg (^"stream") (Var _ nk (Streams.tl s))
     (Ret $$(Streams.hd s))))%kami
  }.

End StreamMod.

