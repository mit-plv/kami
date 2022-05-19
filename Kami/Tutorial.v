Require Import Kami.Kami.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** Welcome to the Kami tutorial!  This tutorial gives a demo of implementing and verifying very simple producer-consumer components. *)

(** Kami has its own syntax, which is very similar to Bluespec.  Syntax is built with "Notation" in Coq, so module definitions are automatically type-checked internally by the Gallina type-checker. *)

(** Let's design a producer module first.  A module consists of registers, rules, and methods.  A rule or a method is defined as a sequence of actions.  Semantically, rules are executed by a global rule scheduler. Methods are executed by method calls, which can be called by other modules once they are composed. *)

(** Producer has a data register and a rule to send the data to Consumer. *)
Definition producer :=
  MODULE {
    Register "data" : Bit 32 (* type *) <- Default (* initial value *)

    with Rule "produce" :=
      Read data <- "data";
        (* Explicit actions are required to read values of registers into local variables. *)
      Call (MethodSig "send" (Bit 32 (* parameter type *)): Void (* return type*)) (#data) (* using [#] to read from variables *);
        (* Note embedding of a type assumption for the function being called, not just its name. *)
      Write "data" <- #data + $1 (* using [$] for a literal expression *);
      Retv
  }.

(** For proof automation, it is recommended to register module definitions to "ModuleDefs". *)
#[global] Hint Unfold producer : ModuleDefs.

(** Consumer only has one method, which takes the data sent by Producer and calls an external function with the data. *)
Definition consumer :=
  MODULE {
    Method "send" (data: Bit 32): Void :=
      Call (MethodSig "extCall" (Bit 32): Void) (#data);
      Retv
  }.
#[global] Hint Unfold consumer : ModuleDefs.

(** Now we compose Producer and Consumer to make the complete implementation. *)
Definition producerConsumerImpl := (producer ++ consumer)%kami.
#[global] Hint Unfold producerConsumerImpl : ModuleDefs.

(** What is a specification of the Producer-Consumer module?  We define specifications also as modules in Kami.  A specification is usually defined as a single module.  In this case, we define the specification simply by calling the external call with the current data and update it as Producer does. *)
Definition producerConsumerSpec :=
  MODULE {
    Register "data" : Bit 32 <- Default

    with Rule "produce_consume" :=
      Read data <- "data";
      Call (MethodSig "extCall" (Bit 32): Void) (#data);
      Write "data" <- #data + $1;
      Retv
  }.

(** Inlining and Decomposition are mostly used to prove refinement between [impl] and [spec].  Inlining collapses all internal method calls in [impl], which enables us only to consider external calls.  Decomposition allows us to relate each fine-grained state transition (by a rule or a method) in [impl] to one in [spec]. *)

(** In order to use the decomposition theorem, we have to define two maps, one for rules and the other for internal states.  See "src/Notations.v" for detailed notations for mapping. *)
Definition producer_consumer_ruleMap (_: RegsT): string -> option string :=
  "produce" |-> "produce_consume"; ||.
Definition producer_consumer_regMap (r: RegsT): RegsT.
  (* We are using tactics to build a map from register valuations in [impl] to register valuations in [spec]. *)
  kgetv "data"%string datav r (Bit 32) (M.empty _: RegsT).
  (* First, extract the value of [impl] register ["data"]. *)
  exact (M.add "data"%string (existT _ _ datav) (M.empty _)).
  (* Then, give the corresponding values of all registers for [spec]. *)
Defined.
#[global] Hint Unfold producer_consumer_regMap: MethDefs. (* for kdecompose_regMap_init *)

(** The Kami syntax is built by PHOAS, so sometimes we need to prove a PHOAS equivalence for any two variable mappings.  Adding the equivalence lemma to the Coq hint database will allow related features to use it automatically. *)
Lemma impl_ModEquiv:
  ModPhoasWf producerConsumerImpl.
Proof. kequiv. Qed.
#[global] Hint Resolve impl_ModEquiv.

(** Now we are ready to prove the refinement! *)
Theorem producer_consumer_refinement:
  producerConsumerImpl <<== producerConsumerSpec.
Proof.
  kinline_left implInlined.
  (* Inlining: replace internal function calls in [impl]. *)
  kdecompose_nodefs producer_consumer_regMap producer_consumer_ruleMap.
  (* Decomposition: consider all steps [impl] could take, requiring that each be matched appropriately in [spec]. *)

  kinvert.
  (* Inversion on the took-a-step hypothesis, to produce one new subgoal per [impl] rule, etc. *)
  kinv_magic_light.
  (* We have only one case for this example (for the one rule), and it's easy. *)
Qed.

(** We can also build refinement proofs by the one-line tactic with a proof configuration. *)
Definition producer_consumer_refinement_config :=
  {| inlining := ITManual;
     decomposition := DTFunctional producer_consumer_regMap producer_consumer_ruleMap;
     invariants := IVNil
  |}.

(** Here is the shortest proof of the refinement. *)
Theorem producer_consumer_refinement_again:
  producerConsumerImpl <<== producerConsumerSpec.
Proof.
  kami_ok producer_consumer_refinement_config idtac idtac.
Qed.
