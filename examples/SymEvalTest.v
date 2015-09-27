Require Import FunctionalExtensionality List String.
Require Import Lib.Word Lib.Struct Lib.FnMap.
Require Import Lts.Syntax Lts.Semantics Lts.Refinement Lts.SymEval Lts.SymEvalTac.

Definition bar := MethodSig "bar"(Bit 1) : Bit 1.

Theorem call_me : forall rm o n dm cm, LtsStep (ConcatMod (MODULE {
                                                               Method "foo"() : Bit 1 :=
                                                                 Call x <- bar($1);
                                                                 Ret #x
                                                          })
                                                          (MODULE {
                                                               Method "bar"(x : Bit 1) : Bit 1 :=
                                                                 Ret #x
                                                          }))
                                               rm o n dm cm
                                       -> forall r : Typed SignT, find "foo" dm = Some r
                                         -> exists w, r = {| objType := Build_SignatureT (Bit 0) (Bit 1);
                                                             objVal := (w, WO~1) |}.
Proof.
  do 6 intro.
  SymEval.
  eauto.
Qed.

Definition inc := MethodSig "inc"() : Void.
Definition inc2 := MethodSig "inc2"() : Void.

Theorem really_atomic : forall rm o n dm cm, LtsStep (ConcatMod (MODULE {
                                                                     Register "r" : Bit 2 <- Default

                                                                     with Method "inc"() : Void :=
                                                                       Read r : Bit 2 <- "r";
                                                                       Write "r" <- #r + $1;
                                                                       Retv

                                                                     with Method "inc2"() : Void :=
                                                                       Read r : Bit 2 <- "r";
                                                                       Write "r" <- #r + $2;
                                                                       Retv
                                                                })
                                                                (MODULE {
                                                                     Method "either"(b : Bool) : Void :=
                                                                       If (#b) then
                                                                         Call inc();
                                                                         Retv
                                                                       else
                                                                         Call inc2();
                                                                         Retv
                                                                       as _;
                                                                       Retv
                                                                }))
                                               rm o n dm cm
                                       -> ($0 : type (Bit 2)) === o.["r"]
                                       -> _=== n.["r"]
                                          \/ ($1 : type (Bit 2)) === n.["r"]
                                          \/ ($2 : type (Bit 2)) === n.["r"].
Proof.
  intros.
  SymEval;
    repeat match goal with
           | [ |- context[if ?argV then _ else _] ] => destruct argV; SymEval_simpl
           | [ |- exists x, _ = _ /\ _ ] => eexists; split; [ solve [ eauto ] | intuition idtac ]
           end.
Qed.
