Require Import FunctionalExtensionality List String.
Require Import Lib.Word Lib.Struct Lib.FMap.
Require Import Lts.Syntax Lts.Semantics Lts.Refinement Lts.SymEval Lts.SymEvalTac.

(** * Let's start with a basic example of symbolic evaluation, just inverting an action step. *)

(* Huh... the old [ACTION] notation isn't working here. *)
Definition incrementer : Action Void := (fun var =>
  Read r : Bit 2 <- "r";
  Write "r" <- #r + $1;
  Retv
)%kami.

Local Open Scope string.

Theorem increment_increments : forall regsIn regsOut calls ret v,
  SemAction regsIn (incrementer _) regsOut calls ret
  -> M.find "r"%string regsIn = Some {| objType := SyntaxKind (Bit 2); objVal := v |}
  -> regsOut = M.add "r" {| objType := SyntaxKind (Bit 2); objVal := v ^+ $1 |} (M.empty _).
Proof.
  intros.
Admitted.
(* BROKEN
  SymEval_Action H.
  eauto.
  hnf; eauto.
Qed.
*)


(** * Now some whole-module examples: *)

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
                                       -> forall r : Typed SignT, M.find "foo" dm = Some r
                                         -> exists w, r = {| objType := Build_SignatureT (Bit 0) (Bit 1);
                                                             objVal := (w, WO~1) |}.
Proof.
  admit.
  (* do 6 intro. *)
  (* SymEval. *)
  (* eauto. *)
Qed.


Definition inc := MethodSig "inc"() : Void.
Definition inc2 := MethodSig "inc2"() : Void.

Notation SyntaxType k := (fullType type (SyntaxKind k)).

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
                                                                       If #b then
                                                                         Call inc();
                                                                         Retv
                                                                       else
                                                                         Call inc2();
                                                                         Retv
                                                                       as _;
                                                                       Retv
                                                                }))
                                               rm o n dm cm
                                       -> ($0 : SyntaxType (Bit 2)) === o.["r"]
                                       -> _=== n.["r"]
                                          \/ ($1 : SyntaxType (Bit 2)) === n.["r"]
                                          \/ ($2 : SyntaxType (Bit 2)) === n.["r"].
Proof.
  admit.
  (* intros. *)
  (* SymEval; *)
  (*   repeat match goal with *)
  (*          | [ |- context[if ?argV then _ else _] ] => destruct argV; SymEval_simpl *)
  (*          | [ |- exists x, _ = _ /\ _ ] => eexists; split; [ solve [ eauto ] | intuition idtac ] *)
  (*          end. *)
Qed.

Definition larry := MethodSig "larry"(Bit 3) : Bit 3.
Definition curly := MethodSig "curly"(Bit 3) : Bit 3.

Theorem stooges : forall rm o n dm cm, LtsStep (ConcatMod (MODULE {
                                                               Register "a" : Bit 3 <- Default
                                                               with Register "b" : Bit 3 <- Default
                                                               with Register "c" : Bit 3 <- Default

                                                               with Method "larry"(x : Bit 3) : Bit 3 :=
                                                                 Read a : Bit 3 <- "a";
                                                                 Write "b" <- #x;
                                                                 Ret (#x + #a)

                                                               with Method "curly"(x : Bit 3) : Bit 3 :=
                                                                 Read b : Bit 3 <- "b";
                                                                 Write "a" <- #x;
                                                                 Ret (#x + #b)

                                                               with Rule "add" :=
                                                                 Read a : Bit 3 <- "a";
                                                                 Read b : Bit 3 <- "b";
                                                                 Write "b" <- #a + #b;
                                                                 Retv

                                                               with Rule "distraction" :=
                                                                 Read c : Bit 3 <- "c";
                                                                 Write "c" <- #c + #c;
                                                                 Retv
                                                          })
                                                          (MODULE {
                                                               Method "moe"(x : Bit 3) : Bit 3 :=
                                                                 Call l <- larry(#x);
                                                                 Call c <- curly(#l);
                                                                 Ret (#c)
                                                          }))
                                               rm o n dm cm
                                       -> forall a b c,
                                         (a : SyntaxType (Bit 3)) === o.["a"]
                                         -> (b : SyntaxType (Bit 3)) === o.["b"]
                                         -> (c : SyntaxType (Bit 3)) === o.["c"]
                                         -> match M.find "moe" dm with
                                            | None => True
                                            | Some r =>
                                              exists w, r = {| objType := Build_SignatureT (Bit 3) (Bit 3);
                                                               objVal := (w, w ^+ a ^+ b) |}
                                            end.
Proof.
  admit.
  (* intros. *)
  (* SymEval; *)
  (*   repeat (match goal with *)
  (*           | [ |- context[if ?argV then _ else _] ] => destruct argV *)
  (*           | [ |- exists x, _ = _ /\ _ ] => eexists; split; [ solve [ eauto ] | intuition idtac ] *)
  (*           end; SymEval_simpl; eauto). *)
Qed.

Definition rand := MethodSig "rand"() : Bool.

Theorem rando : forall rm o n dm cm, LtsStep (ConcatMod (MODULE {
                                                             Register "a" : Bit 3 <- Default
                                                             with Register "b" : Bit 3 <- Default
                                                             with Register "larryReceived" : Bit 3 <- Default

                                                             with Method "larry"(x : Bit 3) : Bit 3 :=
                                                               Read a : Bit 3 <- "a";
                                                               Write "b" <- (#x);
                                                               Write "larryReceived" <- (#x);
                                                               Ret (#x + #a)

                                                             with Method "curly"(x : Bit 3) : Bit 3 :=
                                                               Read b : Bit 3 <- "b";
                                                               Write "a" <- #x;
                                                               Ret (#x + #b)

                                                             with Rule "add" :=
                                                               Read a : Bit 3 <- "a";
                                                               Read b : Bit 3 <- "b";
                                                               Write "b" <- #a + #b;
                                                               Retv
                                                        })
                                                        (MODULE {
                                                             Method "moe"(x : Bit 3) : Bit 3 :=
                                                               Call b <- rand();
                                                               If #b then
                                                                 Call l <- larry(#x);
                                                                 Ret (#l)
                                                               else
                                                                 Call c <- curly(#x);
                                                                 Ret (#c)
                                                               as v;
                                                               Ret (#v)
                                             }))
                                             rm o n dm cm
                                     -> forall a b,
                                       (a : SyntaxType (Bit 3)) === o.["a"]
                                       -> (b : SyntaxType (Bit 3)) === o.["b"]
                                       -> match M.find "moe" dm with
                                          | None => True
                                          | Some r =>
                                            exists w, (r = {| objType := Build_SignatureT (Bit 3) (Bit 3);
                                                              objVal := (w, w ^+ a) |}
                                                       \/ r = {| objType := Build_SignatureT (Bit 3) (Bit 3);
                                                                 objVal := (w, w ^+ b) |})
                                                      /\ (_=== n.["b"]
                                                          \/ (w : SyntaxType (Bit 3)) === n.["b"]
                                                          \/ (a ^+ b : SyntaxType (Bit 3)) === n.["b"]
                                                          \/ exists w', w' <> w
                                                                        /\ (w' : SyntaxType (Bit 3)) === n.["larryReceived"]
                                                                        /\ (w' : SyntaxType (Bit 3)) === n.["b"])
                                          end.
Proof.
  
  admit.
  (* intros. *)
  (* SymEval; *)
  (*   repeat (match goal with *)
  (*             | [ |- context[if ?v then _ else _] ] => destruct v *)
  (*             | [ |- exists x, _ = _ /\ _ ] => eexists; split; [ solve [ eauto 10 ] | intuition idtac ] *)
  (*           end; SymEval_simpl; eauto 10). *)
  (* destruct (weq argV argV0); subst; eexists; split; eauto 6. *)
Qed.
