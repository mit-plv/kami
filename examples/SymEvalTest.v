Require Import FunctionalExtensionality List String.
Require Import Lib.Word Lib.Struct Lib.FnMap.
Require Import Lts.Syntax Lts.Semantics Lts.Refinement Lts.SymEval Lts.SymEvalTac.

Definition bar := MethodSig "bar"(Bit 1) : Bit 1.

Theorem call_me : forall rm o n dm cm, LtsStep (ConcatMod (MODULE {
                                                               Method "foo"() : Bit 1 :=
                                                                 Call x <- bar($1);
                                                                 Ret (Var _ (SyntaxKind (Bit 1)) x)
                                                          })
                                                          (MODULE {
                                                               Method "bar"(x : Bit 1) : Bit 1 :=
                                                                 Ret (Var type (SyntaxKind (Bit 1)) x)
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
                                                                     Register "r" : SyntaxKind (Bit 2) <-
                                                                                               (makeConst Default)

                                                                     with Method "inc"() : Void :=
                                                                       Read r : SyntaxKind (Bit 2) <- "r";
                                                                       Write "r" <- #r + $1;
                                                                       Retv

                                                                     with Method "inc2"() : Void :=
                                                                       Read r : SyntaxKind (Bit 2) <- "r";
                                                                       Write "r" <- #r + $2;
                                                                       Retv
                                                                })
                                                                (MODULE {
                                                                     Method "either"(b : Bool) : Void :=
                                                                       If (Var _ (SyntaxKind Bool) b) then
                                                                         Call inc();
                                                                         Retv
                                                                       else
                                                                         Call inc2();
                                                                         Retv
                                                                       as _;
                                                                       Retv
                                                                }))
                                               rm o n dm cm
                                       -> ($0 : (fullType type) (SyntaxKind (Bit 2))) === o.["r"]
                                       -> _=== n.["r"]
                                          \/ ($1 : (fullType type) (SyntaxKind (Bit 2))) === n.["r"]
                                          \/ ($2 : (fullType type) (SyntaxKind (Bit 2))) === n.["r"].
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
                                                               Register "a" : SyntaxKind (Bit 3) <- (makeConst Default)
                                                               with Register "b" : SyntaxKind (Bit 3) <- (makeConst Default)
                                                               with Register "c" : SyntaxKind (Bit 3) <- (makeConst Default)

                                                               with Method "larry"(x : Bit 3) : Bit 3 :=
                                                                 Read a : SyntaxKind (Bit 3) <- "a";
                                                                 Write "b" <- (Var _ (SyntaxKind (Bit 3)) x);
                                                                 Ret ((Var _ (SyntaxKind (Bit 3)) x) + #a)

                                                               with Method "curly"(x : Bit 3) : Bit 3 :=
                                                                 Read b : SyntaxKind (Bit 3) <- "b";
                                                                 Write "a" <- (Var _ (SyntaxKind (Bit 3)) x);
                                                                 Ret ((Var _ (SyntaxKind (Bit 3)) x) + #b)

                                                               with Rule "add" :=
                                                                 Read a : SyntaxKind (Bit 3) <- "a";
                                                                 Read b : SyntaxKind (Bit 3) <- "b";
                                                                 Write "b" <- #a + #b;
                                                                 Retv

                                                               with Rule "distraction" :=
                                                                 Read c : SyntaxKind (Bit 3) <- "c";
                                                                 Write "c" <- #c + #c;
                                                                 Retv
                                                          })
                                                          (MODULE {
                                                               Method "moe"(x : Bit 3) : Bit 3 :=
                                                                 Call l <- larry(Var _ (SyntaxKind (Bit 3)) x);
                                                                 Call c <- curly(Var _ (SyntaxKind _) l);
                                                                 Ret (Var _ (SyntaxKind _) c)
                                                          }))
                                               rm o n dm cm
                                       -> forall a b c,
                                         (a : fullType type (SyntaxKind (Bit 3))) === o.["a"]
                                         -> (b : fullType type (SyntaxKind (Bit 3))) === o.["b"]
                                         -> (c : fullType type (SyntaxKind (Bit 3))) === o.["c"]
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
                                                             Register "a" : SyntaxKind (Bit 3) <- (makeConst Default)
                                                             with Register "b" : SyntaxKind (Bit 3) <- (makeConst Default)
                                                             with Register "larryReceived" : SyntaxKind (Bit 3) <- (makeConst Default)

                                                             with Method "larry"(x : Bit 3) : Bit 3 :=
                                                               Read a : SyntaxKind (Bit 3) <- "a";
                                                               Write "b" <- (Var _ (SyntaxKind _) x);
                                                               Write "larryReceived" <- (Var _ (SyntaxKind _) x);
                                                               Ret ((Var _ (SyntaxKind _) x) + #a)

                                                             with Method "curly"(x : Bit 3) : Bit 3 :=
                                                               Read b : SyntaxKind (Bit 3) <- "b";
                                                               Write "a" <- (Var _ (SyntaxKind _) x);
                                                               Ret ((Var _ (SyntaxKind _) x) + #b)

                                                             with Rule "add" :=
                                                               Read a : SyntaxKind (Bit 3) <- "a";
                                                               Read b : SyntaxKind (Bit 3) <- "b";
                                                               Write "b" <- #a + #b;
                                                               Retv
                                                        })
                                                        (MODULE {
                                                             Method "moe"(x : Bit 3) : Bit 3 :=
                                                               Call b <- rand();
                                                               If (Var _ (SyntaxKind _) b) then
                                                                 Call l <- larry(Var _ (SyntaxKind _) x);
                                                                 Ret (Var _ (SyntaxKind _) l)
                                                               else
                                                                 Call c <- curly(Var _ (SyntaxKind _) x);
                                                                 Ret (Var _ (SyntaxKind _) c)
                                                               as v;
                                                               Ret (Var _ (SyntaxKind _) v)
                                             }))
                                             rm o n dm cm
                                     -> forall a b,
                                       (a : fullType type (SyntaxKind (Bit 3))) === o.["a"]
                                       -> (b : fullType type (SyntaxKind (Bit 3))) === o.["b"]
                                       -> match find "moe" dm with
                                          | None => True
                                          | Some r =>
                                            exists w, (r = {| objType := Build_SignatureT (Bit 3) (Bit 3);
                                                              objVal := (w, w ^+ a) |}
                                                       \/ r = {| objType := Build_SignatureT (Bit 3) (Bit 3);
                                                                 objVal := (w, w ^+ b) |})
                                                      /\ (_=== n.["b"]
                                                          \/ (w : fullType type (SyntaxKind (Bit 3))) === n.["b"]
                                                          \/ (a ^+ b : fullType type (SyntaxKind (Bit 3))) === n.["b"]
                                                          \/ exists w', w' <> w
                                                                        /\ (w' : fullType type (SyntaxKind (Bit 3))) === n.["larryReceived"]
                                                                        /\ (w' : fullType type (SyntaxKind (Bit 3))) === n.["b"])
                                          end.
Proof.
  intros.
  SymEval;
    repeat (match goal with
              | [ |- context[if ?v then _ else _] ] => destruct v
              | [ |- exists x, _ = _ /\ _ ] => eexists; split; [ solve [ eauto 10 ] | intuition idtac ]
            end; SymEval_simpl; eauto 10).
  destruct (weq argV argV0); subst; eexists; split; eauto 6.
Qed.
