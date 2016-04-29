Require Import String Streams.
Require Import Lib.Indexer List.
Require Import Lts.Syntax Lts.Semantics.

Set Implicit Arguments.

Section StreamMod.
  Variable modName: string.
  Variable A : Kind.
  Variable default : ConstT A.
  Variable stream : Stream (ConstT A).

  Definition nk := NativeKind (const default).

  Notation "^ s" := (modName .. s) (at level 0).

  Definition streamMod := MODULE {
    RegisterN ^"stream" : nk <- (NativeConst _ stream)

    with Method ^"get"() : A :=
    (ReadReg (^"stream") nk (fun s => 
    WriteReg (^"stream") (Var _ nk (Streams.tl s))
     (Ret $$(Streams.hd s))))%kami
  }.

  (* Section Spec. *)
  (*   Lemma regsInDomain_streamMod: RegsInDomain streamMod. *)
  (*   Proof. *)
  (*     regsInDomain_tac. *)
  (*   Qed. *)
  (* End Spec. *)

End StreamMod.

Section Fifo.
  Variable A: Kind.
  Definition f :=
    MODULE {
        RegisterN "x": NativeKind nil <-
                         (@NativeConst (list (sigT (fun ty => ty A))) nil nil)
        with Method "enq"(d: A): Void :=
          ReadN old : (list (sigT (fun ty => ty A))) #< nil <- "x";
          Write "x" <-
                Var _ ((list (sigT (fun ty => ty A))) #< nil) ((existT (fun ty => ty A) _ d) :: old)%list;
          Retv
      }.
End Fifo.