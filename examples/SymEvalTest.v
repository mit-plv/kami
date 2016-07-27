Require Import FunctionalExtensionality List String.
Require Import Lib.Word Lib.Struct Lib.FMap.
Require Import Lts.Syntax Lts.Semantics Lts.Refinement Lts.SymEval Lts.SymEvalTac
        Lts.Notations.

Set Implicit Arguments.

Definition bar := MethodSig "bar"(Bit 1) : Bit 1.

Theorem call_me : forall o u cm ret,
                    SemAction o (LET y: Bit 1 <- $ 0;
                                 Call x <- bar(#y);
                                 Write "w" : Bit 1 <- #y;
                                 Retv)%kami_action u cm ret ->
                    forall v, M.find "w"%string u = Some (existT (fullType type)
                                                                 (SyntaxKind (Bit 1)) v) ->
                              WO~0 = v.
Proof.
  do 5 intro.
  SymEval; auto.
Qed.
(*
forall r,
                         find "foo" dm = Some r
                         -> exists w, r = {| objType := Build_SignatureT (Bit 0) (Bit 1);
                                             objVal := (w, WO~1) |}.
Proof.
  do 6 intro.
  SymEval'' H; simpl.
  split.
  intros; assumption.
  split; intros.
  split; intros.
  eexists; eauto.
  autorewrite with SymEval in *.
  intros.
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
                                                                 Ret #c
                                                          }))
                                               rm o n dm cm
                                       -> forall a b c,
                                         (a : type (Bit 3)) === o.["a"]
                                         -> (b : type (Bit 3)) === o.["b"]
                                         -> (c : type (Bit 3)) === o.["c"]
                                         -> match find "moe" dm with
                                            | None => True
                                            | Some r =>
                                              exists w, r = {| objType := Build_SignatureT (Bit 3) (Bit 3);
                                                               objVal := (w, w ^+ a ^+ b) |}
                                            end.
Proof.
  intros.
  SymEval;
    repeat (match goal with
            | [ |- context[if ?argV then _ else _] ] => destruct argV
            | [ |- exists x, _ = _ /\ _ ] => eexists; split; [ solve [ eauto ] | intuition idtac ]
            end; SymEval_simpl; eauto).
Qed.

Definition rand := MethodSig "rand"() : Bool.

Theorem rando : forall rm o n dm cm, LtsStep (ConcatMod (MODULE {
                                                             Register "a" : Bit 3 <- Default
                                                             with Register "b" : Bit 3 <- Default
                                                             with Register "larryReceived" : Bit 3 <- Default

                                                             with Method "larry"(x : Bit 3) : Bit 3 :=
                                                               Read a : Bit 3 <- "a";
                                                               Write "b" <- #x;
                                                               Write "larryReceived" <- #x;
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
                                                                 Ret #l
                                                               else
                                                                 Call c <- curly(#x);
                                                                 Ret #c
                                                               as v;
                                                               Ret #v
                                             }))
                                             rm o n dm cm
                                     -> forall a b,
                                       (a : type (Bit 3)) === o.["a"]
                                       -> (b : type (Bit 3)) === o.["b"]
                                       -> match find "moe" dm with
                                          | None => True
                                          | Some r =>
                                            exists w, (r = {| objType := Build_SignatureT (Bit 3) (Bit 3);
                                                              objVal := (w, w ^+ a) |}
                                                       \/ r = {| objType := Build_SignatureT (Bit 3) (Bit 3);
                                                                 objVal := (w, w ^+ b) |})
                                                      /\ (_=== n.["b"]
                                                          \/ (w : type (Bit 3)) === n.["b"]
                                                          \/ (a ^+ b : type (Bit 3)) === n.["b"]
                                                          \/ exists w', w' <> w
                                                                        /\ (w' : type (Bit 3)) === n.["larryReceived"]
                                                                        /\ (w' : type (Bit 3)) === n.["b"])
                                          end.
Proof.
  intros.
  SymEval;
    repeat (match goal with
            | [ |- context[if ?argV then _ else _] ] => destruct argV
            | [ |- exists x, _ = _ /\ _ ] => eexists; split; [ solve [ eauto ] | intuition idtac ]
            end; SymEval_simpl; eauto 7).
  destruct (weq argV argV0); subst; eexists; split; eauto 6.
Qed.
*)