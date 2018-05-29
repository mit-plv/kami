Require Import Kami.

Set Implicit Arguments.

Section Spec.
  Variables (instK dataK: Kind)
            (addrSize rfSize: nat).
  
  Section AbstractISA.

    (* opcode *)

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
      { execArith: forall ty, ty opK -> ty dataK -> ty dataK ->
                              Expr ty (SyntaxKind dataK);
      }.

    Global Arguments getOp _ [ty].
    Global Arguments getArithOp _ [ty].
    Global Arguments getSrc1 _ [ty].
    Global Arguments getSrc2 _ [ty].
    Global Arguments getDst _ [ty].
    Global Arguments getAddr _ [ty].

    Global Arguments execArith _ [ty].

  End AbstractISA.

  Section Memory.

    Definition MemRq :=
      STRUCT { "isLoad" :: Bool;
               "addr" :: Bit addrSize;
               "data" :: dataK
             }.
    Definition MemRs := dataK.

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
    Lemma memory_PhoasWf: ModPhoasWf memory.
    Proof. kequiv. Qed.
    Lemma memory_RegsWf: ModRegsWf memory.
    Proof. kvr. Qed.

    Definition doMem := MethodSig "doMem"(Struct MemRq): MemRs.

  End Memory.

  Section ProcSpec.
    Variables (pgmSize: nat)
              (dec: Decoder)
              (exec: Executer).
    
    Definition toHost := MethodSig "toHost"(dataK): Void.

    Record ProcInit :=
      { pcInit : ConstT (Bit pgmSize);
        rfInit : ConstT (Vector dataK rfSize);
        pgmInit : ConstT (Vector instK pgmSize)
      }.
    
    Variable (procInit: ProcInit).

    Definition procSpec :=
      MODULE {
        Register "pc" : Bit pgmSize <- (pcInit procInit)
        with Register "rf" : Vector dataK rfSize <- (rfInit procInit)
        with Register "pgm" : Vector instK pgmSize <- (pgmInit procInit)

        with Rule "doArith" :=
          Read pc: Bit pgmSize <- "pc";
          Read rf <- "rf";
          Read pgm <- "pgm";

          LET inst <- #pgm@[#pc];
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

          Call toHost(#val1);
          Write "pc" <- #pc + $1;
          Retv
      }.
    Lemma procSpec_PhoasWf: ModPhoasWf procSpec.
    Proof. kequiv. Qed.
    Lemma procSpec_RegsWf: ModRegsWf procSpec.
    Proof. kvr. Qed.
    
  End ProcSpec.

  Definition procMemSpec (dec: Decoder) (exec: Executer)
             (pgmSize: nat) (procInit: ProcInit pgmSize) :=
    (procSpec dec exec procInit ++ memory)%kami.

End Spec.

Hint Resolve memory_PhoasWf memory_RegsWf.
Hint Resolve procSpec_PhoasWf procSpec_RegsWf.

Hint Unfold memory procSpec procMemSpec: ModuleDefs.
Hint Unfold opArith opLd opSt opTh opK
     opArithAdd opArithSub opArithMul opArithDiv opArithK
     MemRq MemRs doMem toHost: MethDefs.

