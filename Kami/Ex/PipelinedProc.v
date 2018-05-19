Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.Fifo Ex.ProcMemSpec.

Section PipelinedProc.
  Variables (instK dataK: Kind)
            (addrSize rfSize: nat)
            (pgmSize: nat).
    
  Variable (procInit: ProcInit instK dataK addrSize rfSize pgmSize).
  Variable (dec: Decoder instK addrSize rfSize).

  Definition d2e :=
    STRUCT { "op" :: opK;
             "arithOp" :: opArithK;
             "src1" :: Bit rfSize;
             "src2" :: Bit rfSize;
             "dst" :: Bit rfSize;
             "addr" :: Bit addrSize
           }.

  Definition d2eEnq := MethodSig ("d2e" -- "enq")(Struct d2e): Void.
  
  Definition decoder :=
    MODULE {
      Register "pc" : Bit addrSize <- (pcInit procInit)
      with Register "pgm" : Vector instK pgmSize <- (pgmInit procInit)

      with Rule "decode" :=
        Read pc: Bit addrSize <- "pc";
        Read pgm <- "pgm";
        LET inst <- #pgm@[#pc];
        LET decoded <- STRUCT { "op" ::= getOp dec inst;
                                "arithOp" ::= getArithOp dec inst;
                                "src1" ::= getSrc1 dec inst;
                                "src2" ::= getSrc2 dec inst;
                                "dst" ::= getDst dec inst;
                                "addr" ::= getAddr dec inst };
        Call d2eEnq(#decoded);
        Retv
    }.

  Variable (exec: Executer dataK).

End PipelinedProc.

