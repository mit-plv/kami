Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.OneEltFifo Ex.ProcMemSpec.

Set Implicit Arguments.

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
    
    Definition regFile :=
      MODULE {
        Register "rf" : Vector dataK rfSize <- rfInit
        with Method "rfRead1" (idx: Bit rfSize): dataK :=
          Read rf <- "rf";
          Ret #rf@[#idx]
        with Method "rfRead2" (idx: Bit rfSize): dataK :=
          Read rf <- "rf";
          Ret #rf@[#idx]
        with Method "rfWrite" (wr: Struct RfWrite): Void :=
          Read rf <- "rf";
          Write "rf" <- #rf@[#wr!RfWrite@."idx" <- #wr!RfWrite@."val"];
          Retv
      }.
    Lemma regFile_PhoasWf: ModPhoasWf regFile.
    Proof. kequiv. Qed.
    Lemma regFile_RegsWf: ModRegsWf regFile.
    Proof. kvr. Qed.
    
    Definition rfRead1 := MethodSig "rfRead1"(Bit rfSize): dataK.
    Definition rfRead2 := MethodSig "rfRead2"(Bit rfSize): dataK.
    Definition rfWrite := MethodSig "rfWrite"(Struct RfWrite): Void.

  End RegFile.

  Hint Resolve regFile_PhoasWf regFile_RegsWf.

  Definition D2E :=
    STRUCT { "op" :: opK;
             "arithOp" :: opArithK;
             "src1" :: Bit rfSize;
             "src2" :: Bit rfSize;
             "dst" :: Bit rfSize;
             "addr" :: Bit addrSize;
             "pc" :: Bit pgmSize
           }.

  Definition d2e := oneEltFifo "d2e" (Struct D2E).
  Definition d2eEnq := MethodSig ("d2e" -- "enq")(Struct D2E): Void.
  Definition d2eDeq := MethodSig ("d2e" -- "deq")(Void): Struct D2E.

  Section Decoder.
    Variables (pcInit : ConstT (Bit pgmSize))
              (pgmInit : ConstT (Vector instK pgmSize)).
    
    Definition decoder :=
      MODULE {
        Register "pc" : Bit pgmSize <- pcInit
        with Register "pgm" : Vector instK pgmSize <- pgmInit

        with Rule "decode" :=
          Read pc: Bit pgmSize <- "pc";
          Read pgm <- "pgm";
          LET inst <- #pgm@[#pc];
          LET decoded <- STRUCT { "op" ::= getOp dec inst;
                                  "arithOp" ::= getArithOp dec inst;
                                  "src1" ::= getSrc1 dec inst;
                                  "src2" ::= getSrc2 dec inst;
                                  "dst" ::= getDst dec inst;
                                  "addr" ::= getAddr dec inst;
                                  "pc" ::= #pc };
          Call d2eEnq(#decoded);
          Write "pc" <- #pc + $1;
          Retv
        }.
    Lemma decoder_PhoasWf: ModPhoasWf decoder.
    Proof. kequiv. Qed.
    Lemma decoder_RegsWf: ModRegsWf decoder.
    Proof. kvr. Qed.

  End Decoder.

  Hint Resolve decoder_PhoasWf decoder_RegsWf.
  
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
  Lemma scoreboard_PhoasWf: ModPhoasWf scoreboard.
  Proof. kequiv. Qed.
  Lemma scoreboard_RegsWf: ModRegsWf scoreboard.
  Proof. kvr. Qed.

  Hint Resolve scoreboard_PhoasWf scoreboard_RegsWf.
  
  Definition sbSearch1 := MethodSig "sbSearch1"(Bit rfSize) : Bool.
  Definition sbSearch2 := MethodSig "sbSearch2"(Bit rfSize) : Bool.
  Definition sbSearch3 := MethodSig "sbSearch3"(Bit rfSize) : Bool.
  Definition sbInsert := MethodSig "sbInsert"(Bit rfSize) : Void.
  Definition sbRemove := MethodSig "sbRemove"(Bit rfSize) : Void.

  Definition e2w := oneEltFifo "e2w" (Struct RfWrite).
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
    Lemma executer_PhoasWf: ModPhoasWf executer.
    Proof. kequiv. Qed.
    Lemma executer_RegsWf: ModRegsWf executer.
    Proof. kvr. Qed.
    
  End Executer.

  Hint Resolve executer_PhoasWf executer_RegsWf.
  
  Definition writeback :=
    MODULE {
      Rule "writeback" :=
        Call e2w <- e2wDeq();
        Call rfWrite(#e2w);
        Call sbRemove(#e2w!RfWrite@."idx");
        Retv
    }.
  Lemma writeback_PhoasWf: ModPhoasWf writeback.
  Proof. kequiv. Qed.
  Lemma writeback_RegsWf: ModRegsWf writeback.
  Proof. kvr. Qed.
  Hint Resolve writeback_PhoasWf writeback_RegsWf.

  Variable (init: ProcInit instK dataK rfSize pgmSize).
  
  Definition procImpl :=
    (((decoder (pcInit init) (pgmInit init))
        ++ d2e
        ++ executer)
       ++ (regFile (rfInit init))
       ++ e2w
       ++ scoreboard
       ++ writeback)%kami.
  Lemma procImpl_PhoasWf: ModPhoasWf procImpl.
  Proof. kequiv. Qed.
  Lemma procImpl_RegsWf: ModRegsWf procImpl.
  Proof. kvr. Qed.
  Hint Resolve procImpl_PhoasWf procImpl_RegsWf.
  
  Definition procMemImpl :=
    (procImpl ++ memory dataK addrSize)%kami.
  Lemma procMemImpl_PhoasWf: ModPhoasWf procMemImpl.
  Proof. kequiv. Qed.
  Lemma procMemImpl_RegsWf: ModRegsWf procMemImpl.
  Proof. kvr. Qed.

End PipelinedProc.

Hint Resolve regFile_PhoasWf regFile_RegsWf.
Hint Resolve decoder_PhoasWf decoder_RegsWf.
Hint Resolve scoreboard_PhoasWf scoreboard_RegsWf.
Hint Resolve executer_PhoasWf executer_RegsWf.
Hint Resolve writeback_PhoasWf writeback_RegsWf.
Hint Resolve procImpl_PhoasWf procImpl_RegsWf.
Hint Resolve procMemImpl_PhoasWf procMemImpl_RegsWf.

Hint Unfold regFile d2e decoder scoreboard e2w executer writeback
     procImpl procMemImpl: ModuleDefs.
Hint Unfold RfWrite rfRead1 rfRead2 rfWrite D2E d2eEnq d2eDeq
     sbSearch1 sbSearch2 sbSearch3 sbInsert sbRemove
     e2wEnq e2wDeq doMem toHost: MethDefs.

