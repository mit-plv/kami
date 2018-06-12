Require Import Kami.
Require Import Ex.ProcMemSpec Ex.PipelinedProc.

Set Implicit Arguments.

(*! Specifying, implementing, and verifying a very simple processor !*)

(** You may want to take a look at the code in the following order:
 * - ProcMemSpec.v: the spec of processors and memory systems
 * - PipelinedProc.v: a 3-stage pipelined processor implementation
 * - DecExec.v (you are here!): a pipeline stage that merges the first two 
 *   stages, [decoder] and [executer].
 * - DecExecOk.v: correctness of [decexec] in DecExec.v
 * - ProcMemInterm.v: an intermediate 2-stage pipelined processor 
 * - ProcMemOk.v: a complete refinement proof
 *)

(* How can we verify a pipelined processor? One of intuitive and efficient ways
 * is called "stage merging." As the name says, we prove a refinement, where
 * specification is also possibly staged but has less stages since some stages
 * are merged into one in the spec. We will eventually have a refinement where
 * the spec has a single stage by applying stage merging repeatedly.
 *
 * Here we first provide [decexec], a merged stage between [decoder] and
 * [executer] in PipelinedProc.v
 *)
Section DecExec.
  Variables (instK dataK: Kind)
            (addrSize rfSize: nat)
            (pgmSize: nat).

  Variables (dec: Decoder instK addrSize rfSize)
            (exec: Executer dataK)
            (pcInit : ConstT (Bit pgmSize))
            (pgmInit : ConstT (Vector instK pgmSize)).

  Local Definition doMem := doMem dataK addrSize.
  Local Definition toHost := toHost dataK.
  Local Definition D2E := D2E addrSize rfSize pgmSize.
  Local Definition sbSearch1 := sbSearch1 rfSize.
  Local Definition sbSearch2 := sbSearch2 rfSize.
  Local Definition sbInsert := sbInsert rfSize.
  Local Definition rfRead1 := rfRead1 dataK rfSize.
  Local Definition rfRead2 := rfRead2 dataK rfSize.
  Local Definition e2wEnq := e2wEnq dataK rfSize.
  
  Definition decexec :=
    MODULE {
      Register "pc" : Bit pgmSize <- pcInit
      with Register "pgm" : Vector instK pgmSize <- pgmInit

      with Rule "decexecArith" :=
        Read pc: Bit pgmSize <- "pc";
        Read pgm <- "pgm";
        LET inst <- #pgm@[#pc];
        LET op <- getOp dec inst;
        Assert (#op == $$opArith);
      
        LET src1 <- getSrc1 dec inst;
        LET src2 <- getSrc2 dec inst;
        LET dst <- getDst dec inst;
        Call srcOk1 <- sbSearch1(#src1);
        Call srcOk2 <- sbSearch2(#src2);
        Assert (!#srcOk1 && !#srcOk2);

        LET arithOp <- getArithOp dec inst;
        Call val1 <- rfRead1(#src1);
        Call val2 <- rfRead2(#src2);
        LET execVal <- execArith exec arithOp val1 val2;
        Call sbInsert(#dst);
        Call e2wEnq (STRUCT { "idx" ::= #dst; "val" ::= #execVal });

        Write "pc" <- #pc + $1;
        Retv

      with Rule "decexecLd" :=
        Read pc: Bit pgmSize <- "pc";
        Read pgm <- "pgm";
        LET inst <- #pgm@[#pc];
        LET op <- getOp dec inst;
        Assert (#op == $$opLd);

        LET dst <- getDst dec inst;
        LET addr <- getAddr dec inst;
        Call val <- doMem(STRUCT { "isLoad" ::= $$true;
                                   "addr" ::= #addr;
                                   "data" ::= $$Default });
        Call dstOk <- sbSearch1(#dst);
        Assert !#dstOk;

        Call sbInsert(#dst);
        Call e2wEnq (STRUCT { "idx" ::= #dst; "val" ::= #val });
        Write "pc" <- #pc + $1;
        Retv

      with Rule "decexecSt" :=
        Read pc: Bit pgmSize <- "pc";
        Read pgm <- "pgm";
        LET inst <- #pgm@[#pc];
        LET op <- getOp dec inst;
        Assert (#op == $$opSt);

        LET addr <- getAddr dec inst;
        LET src1 <- getSrc1 dec inst;
        Call srcOk1 <- sbSearch1(#src1);
        Assert !#srcOk1;
          
        Call val <- rfRead1(#src1);
        Call doMem(STRUCT { "isLoad" ::= $$false;
                            "addr" ::= #addr;
                            "data" ::= #val });
        Write "pc" <- #pc + $1;
        Retv

      with Rule "decexecTh" :=
        Read pc: Bit pgmSize <- "pc";
        Read pgm <- "pgm";
        LET inst <- #pgm@[#pc];
        LET op <- getOp dec inst;
        Assert (#op == $$opTh);

        LET src1 <- getSrc1 dec inst;
        Call srcOk1 <- sbSearch1(#src1);
        Assert !#srcOk1;

        Call val1 <- rfRead1(#src1);
        Call toHost(#val1);
        Write "pc" <- #pc + $1;
        Retv
    }.
  Lemma decexec_PhoasWf: ModPhoasWf decexec.
  Proof. kequiv. Qed.
  Lemma decexec_RegsWf: ModRegsWf decexec.
  Proof. kvr. Qed.

  (* [decexecSep] is a combined module that contains [decoder] and [executer]
   * separately. We will prove the refinement between [decexec] and [decexecSep]
   * soon, but before that we need to inline [decexecSep] first, following a
   * typical Kami verification flow. See DecExecOk.v to see how this inlined
   * module is used for a correctness proof. *)
  Definition decexecSep :=
    ((decoder dec pcInit pgmInit)
       ++ (d2e addrSize rfSize pgmSize)
       ++ (executer addrSize rfSize pgmSize exec))%kami.
  Lemma decexecSep_PhoasWf: ModPhoasWf decexecSep.
  Proof. kequiv. Qed.
  Lemma decexecSep_RegsWf: ModRegsWf decexecSep.
  Proof. kvr. Qed.
  Hint Resolve decexecSep_PhoasWf decexecSep_RegsWf.

  Hint Unfold decexecSep: ModuleDefs.

  Definition decexecSepInl: {m: Modules & decexecSep <<== m}.
  Proof.
    kinline_refine decexecSep.
  Defined.
  
End DecExec.

Hint Resolve decexec_PhoasWf decexec_RegsWf.
Hint Resolve decexecSep_PhoasWf decexecSep_RegsWf.
Hint Unfold decexec decexecSep: ModuleDefs.
Hint Unfold doMem toHost D2E sbSearch1 sbSearch2 sbInsert
     rfRead1 rfRead2 e2wEnq: MethDefs.

