Require Import Kami.

Set Implicit Arguments.

(*! Specifying, implementing, and verifying a very simple processor !*)

(** Processors and memory systems are one of typical hardware that involves
 * nontrivial optimizations so it is worth verifying them. In this case study,
 * we will 1) define a spec processor and a memory system with a very simple
 * ISA, 2) implement an optimized processor using pipelining and scoreboarding,
 * and 3) prove the refinement between the implementation and the spec.
 *
 * You may want to take a look at the code in the following order:
 * - ProcMemSpec.v (you are here!): the spec processor and memory system
 * - PipelinedProc.v: a 3-stage pipelined processor implementation
 * - DecExec.v: a pipeline stage that merges the first two stages,
     [decoder] and [executer].
 * - DecExecOk.v: correctness of [decexec] in DecExec.v
 * - ProcMemInterm.v: an intermediate 2-stage pipelined processor 
 * - ProcMemOk.v: a complete refinement proof
 *)

Section Spec.
  (* Specification is parametrized by several variables. *)
  Variables (instK dataK: Kind)
            (addrSize rfSize: nat).
  
  (* An abstract ISA, used by both the spec and implementations. *)
  Section AbstractISA.

    (* There are only four kinds of operations: arithmetic, load, store, 
     * and tohost. *)
    Definition opArith := WO~0~0.
    Definition opLd := WO~0~1.
    Definition opSt := WO~1~0.
    Definition opTh := WO~1~1.

    Definition opK := Bit 2.

    Definition opArithAdd := WO~0~0.
    Definition opArithSub := WO~0~1.
    Definition opArithMul := WO~1~0.
    Definition opArithDiv := WO~1~1.

    Definition opArithK := Bit 2.

    Record Decoder :=
      { getOp: forall ty, ty instK -> Expr ty (SyntaxKind opK);
        getArithOp: forall ty, ty instK -> Expr ty (SyntaxKind opArithK);
        getSrc1: forall ty, ty instK -> Expr ty (SyntaxKind (Bit rfSize));
        getSrc2: forall ty, ty instK -> Expr ty (SyntaxKind (Bit rfSize));
        getDst: forall ty, ty instK -> Expr ty (SyntaxKind (Bit rfSize));
        getAddr: forall ty, ty instK -> Expr ty (SyntaxKind (Bit addrSize))
      }.

    Record Executer :=
      { execArith: forall ty, ty opArithK -> ty dataK -> ty dataK ->
                              Expr ty (SyntaxKind dataK);
      }.

    (* We don't want to provide an implicit argument (as an underscore) for the
     * PHOAS type instantiation function every time we use one of decoder or
     * executer interfaces. *)
    Global Arguments getOp _ [ty].
    Global Arguments getArithOp _ [ty].
    Global Arguments getSrc1 _ [ty].
    Global Arguments getSrc2 _ [ty].
    Global Arguments getDst _ [ty].
    Global Arguments getAddr _ [ty].
    Global Arguments execArith _ [ty].

  End AbstractISA.

  (* A memory specification that instantaneously responds to any requests *)
  Section Memory.

    (* When "isLoad" is [true], we don't care the "data" value. *)
    Definition MemRq :=
      STRUCT { "isLoad" :: Bool;
               "addr" :: Bit addrSize;
               "data" :: dataK
             }.

    (* If the response is for a store operation, 
     * the response value has no meanings. *)
    Definition MemRs := dataK.

    (* The memory spec has only one method ("doMem"), which takes a request and
     * instantaneously returns an appropriate response. *)
    Definition memory :=
      MODULE {
        Register "mem" : Vector dataK addrSize <- Default

        with Method "doMem" (rq: Struct MemRq): MemRs :=
          Read memv <- "mem";
          If !#rq!MemRq@."isLoad" then
            LET ldval <- #memv@[#rq!MemRq@."addr"];
            Ret #ldval
          else
            Write "mem" <- #memv@[ #rq!MemRq@."addr" <- #rq!MemRq@."data" ];
            Ret $$Default
          as rs;
          Ret #rs
      }.

    (* Whenever we define a Kami module, we should prove well-formedness
     * conditions about the module. One is about the PHOAS equivalence, and the
     * other is about valid register uses. These lemmas are always proven
     * by a single-line tactic [kequiv] or [kvr], respectively. *)
    Lemma memory_PhoasWf: ModPhoasWf memory.
    Proof. kequiv. Qed.
    Lemma memory_RegsWf: ModRegsWf memory.
    Proof. kvr. Qed.

    (* It is convenient to provide a definition of every signature of a method
     * in a module, in order for other modules to call the method using this
     * definition. *)
    Definition doMem := MethodSig "doMem"(Struct MemRq): MemRs.

  End Memory.

  (* A processor specification that handles one instruction at a time *)
  Section ProcSpec.
    Variables (pgmSize: nat)
              (dec: Decoder)
              (exec: Executer).

    Definition toHost := MethodSig "toHost"(dataK): Void.

    (* Initial values of a processor are parametrized. *)
    Record ProcInit :=
      { pcInit : ConstT (Bit pgmSize);
        rfInit : ConstT (Vector dataK rfSize);
        pgmInit : ConstT (Vector instK pgmSize)
      }.
    Variable (procInit: ProcInit).

    (* The processor spec has several rules, where each rule handles a single
     * instruction at a time. *)
    Definition procSpec :=
      MODULE {
        Register "pc" : Bit pgmSize <- (pcInit procInit)
        with Register "rf" : Vector dataK rfSize <- (rfInit procInit)
        with Register "pgm" : Vector instK pgmSize <- (pgmInit procInit)

        (* The "doArith" rule handles arithmetic operations. *)
        with Rule "doArith" :=
          Read pc: Bit pgmSize <- "pc";
          Read rf <- "rf";
          Read pgm <- "pgm";

          LET inst <- #pgm@[#pc];

          (* Below assertion ensures that this rule only handles 
           * arithmetic operations. *)
          Assert (getOp dec inst == $$opArith);

          LET op <- getArithOp dec inst;
          LET src1 <- getSrc1 dec inst;
          LET val1 <- #rf@[#src1];
          LET src2 <- getSrc2 dec inst;
          LET val2 <- #rf@[#src2];
          LET dst <- getDst dec inst;
          LET dval <- execArith exec op val1 val2;
          Write "rf" <- #rf@[#dst <- #dval];
          Write "pc" <- #pc + $1;
          Retv
            
        with Rule "doLoad" :=
          Read pc: Bit pgmSize <- "pc";
          Read rf <- "rf";
          Read pgm <- "pgm";

          LET inst <- #pgm@[#pc];
          Assert (getOp dec inst == $$opLd);

          LET dst <- getDst dec inst;
          LET addr <- getAddr dec inst;

          (* The processor spec is using the [doMem] signature we provided 
           * above; the final spec will be a composition of [procSpec] and 
           * [memory]. *)
          Call val <- doMem(STRUCT { "isLoad" ::= $$true;
                                     "addr" ::= #addr;
                                     "data" ::= $$Default });
          Write "rf" <- #rf@[#dst <- #val];
          Write "pc" <- #pc + $1;
          Retv

        with Rule "doStore" :=
          Read pc: Bit pgmSize <- "pc";
          Read rf <- "rf";
          Read pgm <- "pgm";

          LET inst <- #pgm@[#pc];
          Assert (getOp dec inst == $$opSt);

          LET addr <- getAddr dec inst;
          LET src <- getSrc1 dec inst;
          LET val <- #rf@[#src];
          
          Call doMem(STRUCT { "isLoad" ::= $$false;
                              "addr" ::= #addr;
                              "data" ::= #val });
          Write "pc" <- #pc + $1;
          Retv

        with Rule "doToHost" :=
          Read pc: Bit pgmSize <- "pc";
          Read rf <- "rf";
          Read pgm <- "pgm";
          
          LET inst <- #pgm@[#pc];
          Assert (getOp dec inst == $$opTh);

          LET src1 <- getSrc1 dec inst;
          LET val1 <- #rf@[#src1];

          (* [toHost] is the only external method call that generates observable
           * behaviors. *)
          Call toHost(#val1);
          Write "pc" <- #pc + $1;
          Retv
      }.
    Lemma procSpec_PhoasWf: ModPhoasWf procSpec.
    Proof. kequiv. Qed.
    Lemma procSpec_RegsWf: ModRegsWf procSpec.
    Proof. kvr. Qed.
    
  End ProcSpec.

  (* The final spec is simply a composition of [procSpec] and [memory]. *)
  Definition procMemSpec (dec: Decoder) (exec: Executer)
             (pgmSize: nat) (procInit: ProcInit pgmSize) :=
    (procSpec dec exec procInit ++ memory)%kami.

End Spec.

(* It is recommended to register well-formedness proofs to the Coq's core hint
 * database. [kequiv] and [kvr] take advantage of them to provide faster proofs.
 *)
Hint Resolve memory_PhoasWf memory_RegsWf.
Hint Resolve procSpec_PhoasWf procSpec_RegsWf.

(* It is highly recommended (almost mandatory) to register all module 
 * definitions and method-related definitions to specific hint databases.
 * This is only for the purpose of inlining. Inlining may fail when some
 * definitions are not registered to a proper database. *)
Hint Unfold memory procSpec procMemSpec: ModuleDefs.
Hint Unfold opArith opLd opSt opTh opK
     opArithAdd opArithSub opArithMul opArithDiv opArithK
     MemRq MemRs doMem toHost: MethDefs.

