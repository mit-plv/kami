Require Import Kami.
Require Import Lib.FinNotations Lib.Struct Lib.Indexer.
Require Import Ex.ProcMemSpec Ex.PipelinedProc.

Set Implicit Arguments.

Section DecExec.
  Variables (instK dataK: Kind)
            (addrSize rfSize: nat)
            (pgmSize: nat).

  Variables (dec: Decoder instK addrSize rfSize)
            (exec: Executer dataK)
            (pcInit : ConstT (Bit pgmSize))
            (pgmInit : ConstT (Vector instK pgmSize)).

  Local Notation doMem := (doMem dataK addrSize).
  Local Notation toHost := (toHost dataK).
  Local Notation D2E := (D2E addrSize rfSize pgmSize).
  Local Notation sbSearch1 := (sbSearch1 rfSize).
  Local Notation sbSearch2 := (sbSearch2 rfSize).
  Local Notation sbInsert := (sbInsert rfSize).
  Local Notation rfRead1 := (rfRead1 dataK rfSize).
  Local Notation rfRead2 := (rfRead2 dataK rfSize).
  Local Notation e2wEnq := (e2wEnq dataK rfSize).
  
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

  Definition decexecSepInl: sigT (fun m: Modules => decexecSep <<== m).
  Proof.
    pose proof (inlineF_refines
                  (decexecSep_PhoasWf type typeUT)
                  (Reflection.noDupStr_NoDup
                     (namesOf (getDefsBodies decexecSep))
                     eq_refl)) as Him.
    unfold MethsT in Him; rewrite <-SemFacts.idElementwiseId in Him.
    match goal with
    | [H: context[inlineF ?m] |- _] => set m as origm in H at 2
    end.
    kinline_compute_in Him.
    unfold origm in *.
    specialize (Him eq_refl).
    exact (existT _ _ Him).
  Defined.
  
End DecExec.

Hint Resolve decexec_PhoasWf decexec_RegsWf.
Hint Resolve decexecSep_PhoasWf decexecSep_RegsWf.
Hint Unfold decexec decexecSep: ModuleDefs.

