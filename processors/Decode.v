Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Proc.Fetch Proc.AbstractIsa.

Set Implicit Arguments.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Section BHT.
    Variable (indexSize: nat).

    Definition satCntInit: ConstT (Vector (Bit 2) indexSize) :=
      ConstVector (replicate (ConstBit (natToWord _ 1)) indexSize).

    Definition getIndex {ty} (pcv: fullType ty (SyntaxKind (Bit addrSize))):
      Expr ty (SyntaxKind (Bit indexSize)) :=
      UniBit (ZeroExtendTrunc _ _) (#pcv >> $$(natToWord 2 2))%kami_expr.

    Definition getTaken {ty} (cntv: fullType ty (SyntaxKind (Bit 2))):
      Expr ty (SyntaxKind Bool) :=
      (IF (#cntv >> $$(natToWord 1 1) == $0)
       then $$(ConstBool false)
       else $$(ConstBool true))%kami_expr.

    Definition nextSatCnt {ty} (cntv: fullType ty (SyntaxKind (Bit 2)))
               (takenv: fullType ty (SyntaxKind Bool)):
      Expr ty (SyntaxKind (Bit 2)) :=
      (IF #takenv
       then (IF (#cntv == $0) then $1 else $3)
       else (IF (#cntv == $3) then $2 else $0)
      )%kami_expr.

    Definition bhtUpdateStr :=
      STRUCT { "pc" :: Bit addrSize; "taken" :: Bool }.

    Definition bhtPredTaken := MethodSig "predTaken"(Bit addrSize): Bool.
    Definition bhtUpdate := MethodSig "update"(Struct bhtUpdateStr): Void.

    Definition bht :=
      MODULE {
        Register "satCnt" : Vector (Bit 2) indexSize <- satCntInit

        with Method "predTaken"(pc: Bit addrSize): Bool :=
          LET index <- getIndex pc;
          Read satCnt <- "satCnt";
          LET cnt <- #satCnt@[#index];
          LET ret <- getTaken cnt;
          Ret #ret

        with Method "update"(upd: Struct bhtUpdateStr): Void :=
          LET pc <- #upd!bhtUpdateStr@."pc";
          LET taken <- #upd!bhtUpdateStr@."taken";
          LET index <- getIndex pc;
          Read satCnt <- "satCnt";
          LET cnt <- #satCnt@[#index];
          LET next <- nextSatCnt cnt taken;
          Write "satCnt" <- #satCnt@[#index <- #next];
          Retv
      }.

  End BHT.

  Section Decode.
    Variables (f2dName iMemRepName: string).
    Variable decodeInst: DecodeT rfIdx dataBytes.

    Definition f2dDeq := MethodSig (f2dName -- "deq")(): Struct (F2D addrSize).
    Definition iMemRep := MethodSig iMemRepName(): Struct (RsToProc dataBytes).

    Definition decode :=
      MODULE {
        Rule "doDecode" :=
          Call f2d <- f2dDeq();
          Call instStr <- iMemRep();
          LET inst <- #instStr!(RsToProc dataBytes)@."data";

          Call decEpoch <- (getEpoch "dec")();
          Call exeEpoch <- (getEpoch "exe")();

          If (#exeEpoch == #f2d!(F2D addrSize)@."exeEpoch"
              && #decEpoch == #f2d!(F2D addrSize)@."decEpoch")
          then
            LET dInst <- decodeInst _ inst;
              (* TODO: implement *)
            Retv
          else
            Retv
          as _;
          Retv
      }.
    
  End Decode.

End Processor.

