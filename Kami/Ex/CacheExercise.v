Require Import Logic.FunctionalExtensionality.
Require Import Kami ProcMemSpec PipelinedProc ProcMemOk.
Open Scope string_scope.


(* In class, we worked through optimized implementations of processors, using
 * modular reasoning to substitute them into the processor part of a spec.
 * Let's now also add a modest optimization to the memory, which we'll be able
 * to combine with the processor optimizations. *)


(* These lemmas might come in handy, if your solution is like ours.... *)

Lemma mapVec_replicate : forall A B (v : A) (f : A ->B) n,
    mapVec f (replicate v n) = replicate (f v) n.
Proof.
  induction n; simpl; intuition congruence.
Qed.

Lemma evalVec_replicate : forall A (v : A) n (w : word n),
    evalVec (replicate v n) w = v.
Proof.
  induction w; simpl; intuition.
  destruct b; assumption.
Qed.      

Hint Rewrite mapVec_replicate evalVec_replicate : maps.


(* The basic prompt in this exercise is to implement and verify memories that
 * keep simple caches: the most recent memory read or write should be cached in
 * special registers.  Here we save the most recent address in one register and
 * the value associated with that address in another register.  Of course,
 * realistic memory systems go further and cache values of multiple addresses at
 * once. *)

Module WriteThrough.
  (* A write-through cache always keeps the underlying memory up-to-date.
   * The cache is just some extra state that we expect to be able to consult
   * more efficiently than the memory vector itself. *)
  
  Section Spec.
    Variables (instK dataK: Kind)
              (addrSize rfSize: nat).

    Definition MemRq := MemRq dataK addrSize.
    Definition MemRs := MemRs dataK.

    (* Here's a copy of the memory definition in the spec.
     * Extend it to do write-through caching. *)
    Definition memory :=
      MODULE {
        Register "mem" : Vector dataK addrSize <- Default

        with Method "doMem" (rq: Struct MemRq): MemRs :=
          Read memv <- "mem";
          If #rq!MemRq@."isLoad" then
            LET ldval <- #memv@[#rq!MemRq@."addr"];
            Ret #ldval
          else
            Write "mem" <- #memv@[ #rq!MemRq@."addr" <- #rq!MemRq@."data" ];
            Ret $$Default
          as rs;
          Ret #rs
        }.

    Lemma memory_PhoasWf: ModPhoasWf memory.
    Proof. kequiv. Qed.
    Lemma memory_RegsWf: ModRegsWf memory.
    Proof. kvr. Qed.

    Hint Resolve memory_PhoasWf memory_RegsWf.

    Definition doMem := MethodSig "doMem"(Struct MemRq): MemRs.

    Definition spec := ProcMemSpec.memory dataK addrSize.

    (* Now fill in this proof, probably following the methods demonstrated in
     * our proofs of processors in class. *)
    Theorem memory_ok : memory <<== spec.
    Proof.
    Admitted.

    (* A few hints and pointers to alternative tactics more suited to memories:
     *
     * - A crucial step will be defining an invariant.  It isn't necessary to
     *   use a very fancy one here.  Follow the pattern used for e.g.
     *   [procInterm_inv] in class.
     * - A register map is also good to define, along the lines of
     *   [procInterm_regMap] from class.
     * - Similar tactics (for forward and backward simplification) are useful to
     *   define (following e.g. [procInterm_inv_dest_tac],
     *   [procInterm_inv_constr_tac], [procInterm_inv_tac]).
     * - Then, in the key lemma to establish the invariant, use them with a new
     *   tactic [kinv_one_method], which can be called at the top level of a 
     *   lemma, with the same arguments taken by [kdecompose_nodefs] in the
     *   examples from class.  Basically, this machinery is specialized to
     *   modules with single methods that make no method calls of their own,
     *   where there are also no rules.
     * - In case your lemma statements wind up slightly different from ours, you
     *   might find it useful to call some more primitive tactics used by
     *   [kinv_one_method].  Try [kinvert_step_one_method] to invert a [Step]
     *   hypothesis effectively, and try the same [kinv_magic_with] tactic from
     *   class for further simplification afterward.
     * - When you get to proving the main refinement fact, try
     *   [kdecompose_oneMethod], which takes your register map as argument.  Now
     *   there is no need to pass a rulemap, because the tactics are specialized
     *   to modules without rules!
     * - Another tactic [kdecompose_oneMethod_invert] (taking no arguments) is
     *   also handy to invert facts about steps effectively.
     * - The [autorewrite with maps] tactic may be helpful throughout.  We
     *   already seeded this hint database with a few handy facts at the top of
     *   this file, and you may want to add more hints. *)


    (* Let's also see how easy it is to reuse old results modularly, by proving
     * that the optimized processor and optimized memory together implement the
     * original spec. *)
    
    Variable dec: Decoder instK addrSize rfSize.
    Variable exec: Executer dataK.
    Variable pgmSize: nat.
    Variable procInit: ProcInit instK dataK rfSize pgmSize.

    Definition procMemSpec := procMemSpec dec exec procInit.

    Definition procMemImpl :=
      (procImpl dec exec procInit ++ memory)%kami.

    Theorem procMem_ok : procMemImpl <<== procMemSpec.
    Proof.
    Admitted.
  End Spec.
End WriteThrough.


Module WriteBack.
  (* A write-back cache tries to delay updating the underlying memory, hoping to
   * coalesce multiple writes before touching the memory. *)
  
  Section Spec.
    Variables (instK dataK: Kind)
              (addrSize rfSize: nat).

    Definition MemRq := MemRq dataK addrSize.
    Definition MemRs := MemRs dataK.

    (* Extend this memory similarly to above, but following the write-back
     * strategy. *)
    Definition memory :=
      MODULE {
        Register "mem" : Vector dataK addrSize <- Default

        with Method "doMem" (rq: Struct MemRq): MemRs :=
          Read memv <- "mem";
          If #rq!MemRq@."isLoad" then
            LET ldval <- #memv@[#rq!MemRq@."addr"];
            Ret #ldval
          else
            Write "mem" <- #memv@[ #rq!MemRq@."addr" <- #rq!MemRq@."data" ];
            Ret $$Default
          as rs;
          Ret #rs
        }.

    Lemma memory_PhoasWf: ModPhoasWf memory.
    Proof. kequiv. Qed.
    Lemma memory_RegsWf: ModRegsWf memory.
    Proof. kvr. Qed.

    Hint Resolve memory_PhoasWf memory_RegsWf.

    Definition doMem := MethodSig "doMem"(Struct MemRq): MemRs.

    Definition spec := ProcMemSpec.memory dataK addrSize.

    (* Here is the same main theorem from the last cache strategy. *)
    Theorem memory_ok : memory <<== spec.
    Proof.
    Admitted.

    (* New hints:
     *
     * - The invariant gets simpler in this version.  In fact, you might think
     *   at first that no invariant is required, but it will be helpful to use
     *   an invariant to record that the registers store values of the expected
     *   types.  (The semantics in principle allows registers to store values of
     *   the wrong types.)
     * - Your register map probably needs to use an operation to overwrite one
     *   address [a] of a memory [mem] with value [v].  A natural way to write
     *   such an update is:
     *     [fun w => if weq w a then v else mem w]
     * - The refinement is probably a bit more work to prove.
     * - You will likely find yourself needing to prove equalities between
     *   functions that represent memories.  (A memory maps addresses to
     *   values.)  Consider using the tactic [extensionality w], to prove a
     *   function equality by proving that the two functions return equal values
     *   for an arbitrary argument [w]. *)


    (* The final corollary should now be provable with the same proof script as
     * before. *)
    
    Variable dec: Decoder instK addrSize rfSize.
    Variable exec: Executer dataK.
    Variable pgmSize: nat.
    Variable procInit: ProcInit instK dataK rfSize pgmSize.

    Definition procMemSpec := procMemSpec dec exec procInit.

    Definition procMemImpl :=
      (procImpl dec exec procInit ++ memory)%kami.

    Theorem procMem_ok : procMemImpl <<== procMemSpec.
    Proof.
    Admitted.
  End Spec.
End WriteBack.
