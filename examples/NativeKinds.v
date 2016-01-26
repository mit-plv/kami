Require Import String Streams.
Require Import Lib.Struct.
Require Import Lts.Syntax Lts.Semantics.

Set Implicit Arguments.

Section StreamMod.
  Variable modName: string.
  Variable A : Kind.
  Variable default : ConstT A.
  Variable stream : Stream (ConstT A).

  Definition nk := NativeKind (const default).

  Notation "^ s" := (modName -n- s) (at level 0).

  Definition streamMod := MODULE {
    RegisterN ^"stream" : nk <- (NativeConst _ stream)

    with Method ^"get"() : A :=
    (ReadReg (^"stream") nk (fun s => 
    WriteReg (^"stream") (Var _ nk (tl s))
     (Ret $$(hd s))))%kami
  }.

  (* Section Spec. *)
  (*   Lemma regsInDomain_streamMod: RegsInDomain streamMod. *)
  (*   Proof. *)
  (*     regsInDomain_tac. *)
  (*   Qed. *)
  (* End Spec. *)

End StreamMod.
