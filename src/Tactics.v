Require Import Bool String List.
Require Import Lib.Struct Lib.StringEq Lib.FMap.
Require Import Lts.Syntax Lts.Semantics Lts.Wf Lts.Equiv Lts.Refinement.
Require Import Lts.Inline Lts.InlineFacts_2 Lts.Specialize.
Require Import Lts.Decomposition Lts.DecompositionZero.

Set Implicit Arguments.

(**
Kami Tactics
- kequiv : prove any PHOAS equivalences defined in src/Equiv.v
- kequiv_with _tactic_ : also try to apply _tactic_ alternately
- kinline_compute : compute terms with _inlineF_
- kinline_compute_in _term_ : compute terms with _inlineF_ in _term_
- kinline_left : convert (a <<== b) to (inlineF a <<== b), where (inlineF a) is computed
- kdecompose : apply the decomposition theorem
- kdecompose_nodefs : apply the decompositionZero theorem, for modules with no defined methods.
- kspecializable : prove the Specializable predicate
- kduplicated : convert (duplicate a <<== duplicate b) to (a <<== b)
- kgetv/kexistv : used to construct register or label mappings
*)

Ltac kequiv_with tac :=
  repeat
    (repeat autounfold with MethDefs;
     try tac;
     match goal with
     | [ |- ModEquiv _ _ _ ] => constructor; intros
     | [ |- RulesEquiv _ _ _ ] => constructor; intros
     | [ |- MethsEquiv _ _ _ ] => constructor; intros
     | [ |- ActionEquiv _ _ _ ] => constructor; intros
     | [ |- ExprEquiv _ _ _ ] => constructor; intros
     | [ |- @ExprEquiv _ _ _ ?fk (ReadField ?a _) (ReadField ?a _) ] =>
       change fk with (SyntaxKind (GetAttrType a)); constructor; intros
     | [ |- In _ _] => simpl; tauto
     end).

Ltac kequiv := kequiv_with idtac.

Ltac kinline_compute :=
  repeat autounfold with ModuleDefs;
  repeat autounfold with MethDefs;
  cbv [inlineF inline inlineDms inlineDms'
               inlineDmToMod inlineDmToRules inlineDmToRule
               inlineDmToDms inlineDmToDm inlineDm
               filterDms filter
               noInternalCalls noCalls
               noCallsRules noCallsDms noCallDm isLeaf
               getBody inlineArg
               appendAction getAttribute
               makeModule makeModule'
               wfModules wfRules wfDms wfAction wfActionC maxPathLength
               getRegInits getDefs getDefsBodies getRules namesOf
               map app attrName attrType
               getCalls getCallsR getCallsM getCallsA
               appendName append
               ret arg fst snd projT1 projT2
               string_in string_eq ascii_eq
               eqb existsb andb orb negb];
  repeat
    match goal with
    | [ |- context[SignatureT_dec ?s ?s] ] =>
      rewrite (signature_eq s); unfold eq_rect
    end.

Ltac kinline_compute_in H :=
  repeat autounfold with ModuleDefs in H;
  repeat autounfold with MethDefs in H;
  cbv [inlineF inline inlineDms inlineDms'
               inlineDmToMod inlineDmToRules inlineDmToRule
               inlineDmToDms inlineDmToDm inlineDm
               filterDms filter
               noInternalCalls noCalls
               noCallsRules noCallsDms noCallDm isLeaf
               getBody inlineArg
               appendAction getAttribute
               makeModule makeModule'
               wfModules wfRules wfDms wfAction wfActionC maxPathLength
               getRegInits getDefs getDefsBodies getRules namesOf
               map app attrName attrType
               getCalls getCallsR getCallsM getCallsA
               appendName append
               ret arg fst snd projT1 projT2
               string_in string_eq ascii_eq
               eqb existsb andb orb negb] in H;
  repeat
    match type of H with
    | context[SignatureT_dec ?s ?s] =>
      rewrite (signature_eq s) in H; unfold eq_rect in H
    end.

Ltac kinline_left im :=
  match goal with
  | [ |- traceRefines _ ?lm _ ] =>
    apply traceRefines_inlining_left; auto;
    let Heq := fresh "Heq" in
    remember (inlineF lm) as im eqn:Heq;
    kinline_compute_in Heq;
    split; [|subst; reflexivity]
  end.

Ltac kdecompose t r Hrm Hmm :=
  eapply decomposition with (theta:= t)
                              (ruleMap:= r)
                              (substepRuleMap:= Hrm)
                              (substepMethMap:= Hmm); auto; intros.

Ltac kdecompose_nodefs t r :=
  apply decompositionZero with (theta:= t) (ruleMap:= r).

Ltac kspecializable := vm_compute; reflexivity.

Ltac kduplicated := apply duplicate_traceRefines; auto.

Ltac kgetv k v m t f :=
  destruct (M.find k m) as [[[kind|] v]|]; [|exact f|exact f];
  destruct (decKind kind t); [subst|exact f].

(* TODO: "v" is not working *)
Ltac kexistv k v m t :=
  refine (exists v: fullType type (SyntaxKind t),
             M.find k m = Some (existT _ _ v) /\ _).

