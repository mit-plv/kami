Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.

Set Implicit Arguments.

(* Checklist
 * 0) Modular verification / Collapsing pipeline stages / Amortization
 * 1) Unified concept of instruction and data memory
 * 2) Control Status Registers (CSRs) and exceptions
 *)

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Section BTB.
    Variable indexSize tagSize: nat.
    Hypothesis (Haddr: indexSize + tagSize = addrSize).

    Definition getIndex {ty} (pcv: fullType ty (SyntaxKind (Bit addrSize))):
      Expr ty (SyntaxKind (Bit indexSize)) :=
      UniBit (Trunc _ _)
             (eq_rect_r (fun n => Expr ty (SyntaxKind (Bit n)))
                        (#pcv >> $$(natToWord 2 2))%kami_expr
                        Haddr).

    Definition getTag {ty} (pcv: fullType ty (SyntaxKind (Bit addrSize))):
      Expr ty (SyntaxKind (Bit tagSize)) :=
      UniBit (TruncLsb _ _)
             (eq_rect_r (fun n => Expr ty (SyntaxKind (Bit n)))
                        (#pcv)%kami_expr
                        Haddr).

    Definition btbUpdateStr :=
      STRUCT { "curPc" :: Bit addrSize; "nextPc" :: Bit addrSize }.

    Definition btbPredPc := MethodSig "predPc"(Bit addrSize): Bit addrSize.
    Definition btbUpdate := MethodSig "update"(Struct btbUpdateStr): Void.

    Definition btb :=
      MODULE {
          Register "targets" : Vector (Bit addrSize) indexSize <- Default
          with Register "tags" : Vector (Bit tagSize) indexSize <- Default
          with Register "valid" : Vector Bool indexSize <- Default

          with Method "predPc" (pc: Bit addrSize): Bit addrSize :=
            LET index <- getIndex pc;
            LET tag <- getTag pc;

            Read targets <- "targets";
            Read valid <- "valid";
            Read tags <- "tags";

            If (#valid@[#index] && (#tag == #tags@[#index]))
            then Ret #targets@[#index]
            else Ret (#pc + $4)
            as npc;
            
            Ret #npc
                
          with Method "update" (upd: Struct btbUpdateStr): Void :=
            LET curPc <- #upd ! btbUpdateStr @."curPc";
            LET nextPc <- #upd ! btbUpdateStr @."nextPc";
            LET index <- getIndex curPc;
            LET tag <- getTag curPc;

            Read targets: Vector (Bit addrSize) indexSize <- "targets";
            Read valid: Vector Bool indexSize <- "valid";
            Read tags: Vector (Bit tagSize) indexSize <- "tags";

            If (#nextPc != (#curPc + $4))
            then
              Write "valid" <- #valid@[#index <- $$true];
              Write "tags" <- #tags@[#index <- #tag];
              Write "targets" <- #targets@[#index <- #nextPc];
              Retv
            else
              If (#tag == #tags@[#index])
              then
                Write "valid" <- #valid@[#index <- $$false];
                Retv
              else
                Retv
              as _;
              Retv
            as _;
            Retv
      }.

  End BTB.

  Section Redirect.
    Variable redirName: string.

    Definition redirectStr :=
      STRUCT { "pc" :: Bit addrSize; "nextPc" :: Bit addrSize }.
    Definition RedirectK := Struct (Maybe (Struct redirectStr)).

    Definition redirGet := MethodSig (redirName -- "get")(): RedirectK.
    Definition redirSetInvalid := MethodSig (redirName -- "setInvalid")(): Void.
    Definition redirSetValid := MethodSig (redirName -- "setValid")(Struct redirectStr): Void.

    Definition redirect :=
      MODULE {
          Register redirName : RedirectK <- Default

          with Method (redirName -- "get") (): RedirectK :=
            Read redir <- redirName;
            Ret #redir

          with Method (redirName -- "setInvalid") (): Void :=
            Write redirName: RedirectK <- STRUCT { "isValid" ::= $$false; "value" ::= $$Default };
            Retv

          with Method (redirName -- "setValid")(v: Struct redirectStr): Void :=
            Write redirName: RedirectK <- STRUCT { "isValid" ::= $$true; "value" ::= #v };
            Retv
        }.

  End Redirect.

  Section Epoch.
    Variable epochName: string.

    Definition getEpoch := MethodSig (epochName -- "getEpoch")() : Bool.
    Definition toggleEpoch := MethodSig (epochName -- "toggleEpoch")() : Void.

    Definition epoch :=
      MODULE {
        Register epochName : Bool <- false

        with Method (epochName -- "getEpoch") () : Bool :=
          Read epoch <- epochName;
          Ret #epoch

        with Method (epochName -- "toggleEpoch") () : Void :=
          Read epoch <- epochName;
          Write epochName <- !#epoch;
          Retv
      }.

  End Epoch.

  Section Fetch.
    Variables (iMemReqName f2dName: string).

    Definition iMemReq := MethodSig iMemReqName(Struct (RqFromProc dataBytes (Bit addrSize))): Void.

    Definition F2D :=
      STRUCT { "pc" :: Bit addrSize;
               "predPc" :: Bit addrSize;
               "decEpoch" :: Bool;
               "exeEpoch" :: Bool }.
    Definition f2dEnq := MethodSig (f2dName -- "enq")(Struct F2D): Void.

    Definition fetch :=
      MODULE {
        Register "pc" : Bit addrSize <- Default

        with Rule "doFetch" :=
          Read pc <- "pc";
          Call iMemReq(STRUCT { "addr" ::= #pc;
                                "op" ::= $$false;
                                "data" ::= $$Default });
          Call predPc <- btbPredPc(#pc);
          Write "pc" <- #predPc;

          Call decEpoch <- (getEpoch "dec")();
          Call exeEpoch <- (getEpoch "exe")();

          Call f2dEnq (STRUCT { "pc" ::= #pc;
                                "predPc" ::= #predPc;
                                "decEpoch" ::= #decEpoch;
                                "exeEpoch" ::= #exeEpoch });
          Retv

        with Rule "redirect" :=
          Call exeRedir <- (redirGet "exe")();
          If (#exeRedir!(Maybe (Struct redirectStr))@."isValid")
          then
            LET r <- #exeRedir!(Maybe (Struct redirectStr))@."value";
            Write "pc" <- #r!redirectStr@."nextPc";
            Call btbUpdate(STRUCT { "curPc" ::= #r!redirectStr@."pc";
                                    "nextPc" ::= #r!redirectStr@."nextPc" });
            Call (toggleEpoch "exe")();
            Retv
          else
            Call decRedir <- (redirGet "dec")();
            If (#decRedir!(Maybe (Struct redirectStr))@."isValid")
            then
              LET r <- #decRedir!(Maybe (Struct redirectStr))@."value";
              Write "pc" <- #r!redirectStr@."nextPc";
              Call btbUpdate(STRUCT { "curPc" ::= #r!redirectStr@."pc";
                                      "nextPc" ::= #r!redirectStr@."nextPc" });
              Call (toggleEpoch "dec")();
              Retv
            else
              Retv
            as _;
            Retv
          as _;
          Call (redirSetInvalid "exe")();
          Call (redirSetInvalid "dec")();
          Retv
      }.

  End Fetch.

End Processor.

