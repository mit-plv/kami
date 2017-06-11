Require Import FunctionalExtensionality List String.
Require Import Lib.Word Lib.Struct Lib.FMap.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.SymEval Kami.SymEvalTac
        Kami.Notations.

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

