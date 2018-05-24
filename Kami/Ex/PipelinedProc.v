Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.Fifo Ex.ProcMemSpec.

Section PipelinedProc.
  Variables (instK dataK: Kind)
            (addrSize rfSize: nat)
            (pgmSize: nat).

  Variables (dec: Decoder instK addrSize rfSize)
            (exec: Executer dataK).
  
  Section RegFile.
    Variable rfInit: ConstT (Vector dataK rfSize).

    Definition RfWrite :=
      STRUCT { "idx" :: Bit rfSize;
               "val" :: dataK
             }.
    
    Definition regFile := MODULE {
      Register "rf" : Vector dataK rfSize <- rfInit

      with Method "rfRead1" (idx: Bit rfSize): Vector dataK rfSize :=
        Read rf <- "rf";
        Ret #rf@[#idx]

      with Method "rfRead2" (idx: Bit rfSize): Vector dataK rfSize :=
        Read rf <- "rf";
        Ret #rf@[#idx]

      with Method "rfWrite" (wr: Struct RfWrite): Void :=
        Read rf <- "rf";
        Write "rf" <- #rf@[#wr!RfWrite@."idx" <- #wr!RfWrite@."val"];
        Retv
    }.
      
    Definition rfRead1 := MethodSig "rfRead1"(Bit rfSize): dataK.
    Definition rfRead2 := MethodSig "rfRead2"(Bit rfSize): dataK.
    Definition rfWrite := MethodSig "rfWrite"(Struct RfWrite): Void.

  End RegFile.

  Definition D2E :=
    STRUCT { "op" :: opK;
             "arithOp" :: opArithK;
             "src1" :: Bit rfSize;
             "src2" :: Bit rfSize;
             "dst" :: Bit rfSize;
             "addr" :: Bit addrSize
           }.

  Definition d2eEnq := MethodSig ("d2e" -- "enq")(Struct D2E): Void.
  Definition d2eDeq := MethodSig ("d2e" -- "deq")(Void): Struct D2E.

  Section Decoder.
    Variables (pcInit : ConstT (Bit addrSize))
              (pgmInit : ConstT (Vector instK pgmSize)).
    
    Definition decoder :=
      MODULE {
        Register "pc" : Bit addrSize <- pcInit
        with Register "pgm" : Vector instK pgmSize <- pgmInit

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
          Write "pc" <- #pc + $1;
          Retv
        }.

  End Decoder.
    
  Definition scoreboard :=
    MODULE {
      Register "sbFlags" : Vector Bool rfSize <- Default
                                 
      with Method "sbSearch1" (sidx: Bit rfSize) : Bool :=
        Read flags <- "sbFlags";
        Ret #flags@[#sidx]

      with Method "sbSearch2" (sidx: Bit rfSize) : Bool :=
        Read flags <- "sbFlags";
        Ret #flags@[#sidx]

      with Method "sbSearch3" (sidx: Bit rfSize) : Bool :=
        Read flags <- "sbFlags";
        Ret #flags@[#sidx]
            
      with Method "sbInsert" (nidx: Bit rfSize) : Void :=
        Read flags <- "sbFlags";
        Write "sbFlags" <- #flags@[#nidx <- $$true];
        Retv

      with Method "sbRemove" (nidx: Bit rfSize) : Void :=
        Read flags <- "sbFlags";
        Write "sbFlags" <- #flags@[#nidx <- $$false];
        Retv
    }.

  Definition sbSearch1 := MethodSig "sbSearch1"(Bit rfSize) : Bool.
  Definition sbSearch2 := MethodSig "sbSearch2"(Bit rfSize) : Bool.
  Definition sbSearch3 := MethodSig "sbSearch3"(Bit rfSize) : Bool.
  Definition sbInsert := MethodSig "sbInsert"(Bit rfSize) : Void.
  Definition sbRemove := MethodSig "sbRemove"(Bit rfSize) : Void.

  Definition e2wEnq := MethodSig ("e2w" -- "enq")(Struct RfWrite): Void.
  Definition e2wDeq := MethodSig ("e2w" -- "deq")(Void): Struct RfWrite.

  Section Executer.

    Local Definition doMem := doMem dataK addrSize.
    Local Definition toHost := toHost dataK.
    
    Definition executer :=
      MODULE {
        Rule "executeArith" :=
          Call d2e <- d2eDeq();
          LET op <- #d2e!D2E@."op";
          Assert (#op == $$opArith);

          LET src1 <- #d2e!D2E@."src1";
          LET src2 <- #d2e!D2E@."src2";
          LET dst <- #d2e!D2E@."dst";
          Call srcOk1 <- sbSearch1(#src1);
          Call srcOk2 <- sbSearch2(#src2);
          Call dstOk <- sbSearch3(#dst);
          Assert (#srcOk1 && #srcOk2 && #dstOk);

          LET arithOp <- #d2e!D2E@."arithOp";
          Call val1 <- rfRead1(#src1);
          Call val2 <- rfRead2(#src2);
          LET execVal <- execArith exec arithOp val1 val2;
          Call sbInsert(#dst);
          Call e2wEnq (STRUCT { "idx" ::= #dst; "val" ::= #execVal });
          Retv

        with Rule "executeLd" :=
          Call d2e <- d2eDeq();
          LET op <- #d2e!D2E@."op";
          Assert (#op == $$opLd);

          LET dst <- #d2e!D2E@."dst";
          LET addr <- #d2e!D2E@."addr";
          Call val <- doMem(STRUCT { "isLoad" ::= $$true;
                                     "addr" ::= #addr;
                                     "data" ::= $$Default });
          Call dstOk <- sbSearch3(#dst);
          Assert #dstOk;

          Call sbInsert(#dst);
          Call e2wEnq (STRUCT { "idx" ::= #dst; "val" ::= #val });
          Retv

        with Rule "executeSt" :=
          Call d2e <- d2eDeq();
          LET op <- #d2e!D2E@."op";
          Assert (#op == $$opSt);

          LET addr <- #d2e!D2E@."addr";
          LET src1 <- #d2e!D2E@."src1";
          Call srcOk1 <- sbSearch1(#src1);
          Assert #srcOk1;
          
          Call val <- rfRead1(#src1);
          Call doMem(STRUCT { "isLoad" ::= $$false;
                              "addr" ::= #addr;
                              "data" ::= $$Default });
          Retv

        with Rule "executeTh" :=
          Call d2e <- d2eDeq();
          LET op <- #d2e!D2E@."op";
          Assert (#op == $$opTh);

          LET src1 <- #d2e!D2E@."src1";
          Call srcOk1 <- sbSearch1(#src1);
          Assert #srcOk1;
          
          Call val1 <- rfRead1(#src1);
          Call toHost(#val1);
          Retv
            
      }.

  End Executer.

  Definition writeback :=
      MODULE {
        Rule "writeback" :=
          Call e2w <- e2wDeq();
          Call rfWrite(#e2w);
          Retv
      }.

  Definition pipelinedProc (init: ProcInit instK dataK addrSize rfSize pgmSize) :=
    ((regFile (rfInit init))
       ++ (decoder (pcInit init) (pgmInit init))
       ++ executer
       ++ scoreboard
       ++ writeback)%kami.
  
End PipelinedProc.

