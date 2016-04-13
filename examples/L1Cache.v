Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.Semantics Lts.Specialize Lts.Equiv.
Require Import Ex.Msi Ex.MemTypes Ex.RegFile.

Set Implicit Arguments.

Section L1Cache.
  Variables IdxBits TagBits LgDataBytes LgNumDatas LgNumWays LgProcRqs LgPRqs: nat.
  Variable Id: Kind.
  Definition AddrBits := TagBits + IdxBits + LgNumDatas + LgDataBytes.
  Definition Addr := Bit AddrBits.
  Definition Data := Bit (LgDataBytes * 8).
  Definition Line := Vector Data LgNumDatas.
 
  Definition RqFromProc := Ex.MemTypes.RqFromProc LgDataBytes Addr Id.
  Definition RsToProc := Ex.MemTypes.RsToProc LgDataBytes Id.
  Definition FromP := Ex.MemTypes.FromP LgDataBytes LgNumDatas Addr Id.
  Definition RqFromP := Ex.MemTypes.RqFromP Addr.
  Definition RsFromP := Ex.MemTypes.RsFromP LgDataBytes LgNumDatas Addr Id.
  Definition RqToP := Ex.MemTypes.RqToP  Addr Id.
  Definition RsToP := Ex.MemTypes.RsToP LgDataBytes LgNumDatas Addr.

  Definition ProcRqIdx := Bit LgProcRqs.

  Definition procRqRqRead := MethodSig "procRq.rqRead" (ProcRqIdx): RqFromProc.
  Definition procRqStateRead := MethodSig "procRq.stateRead"(ProcRqIdx): RqState.
  Definition procRqWaitRead := MethodSig "procRq.waitRead"(ProcRqIdx): Bool.
  Definition procRqReplacedRead := MethodSig "procRq.replRead"(ProcRqIdx): Maybe Addr.
  Definition procRqDataRead := MethodSig "procRq.dataRead"(ProcRqIdx): Data.
  Definition procRqRqWrite := MethodSig "procRq.rqWrite" (WritePort LgProcRqs RqFromProc): Void.
  Definition procRqStateWrite := MethodSig "procRq.stateWrite"(WritePort LgProcRqs RqState): Void.
  Definition procRqWaitWrite := MethodSig "procRq.waitWrite"(WritePort LgProcRqs Bool): Void.
  Definition procRqReplacedWrite := MethodSig "procRq.replWrite"(WritePort LgProcRqs (Maybe Addr)): Void.
  Definition procRqDataWrite := MethodSig "procRq.dataWrite"(WritePort LgProcRqs Data): Void.

  Definition PRqIdx := Bit LgPRqs.
  
  Definition pRqRqRead := MethodSig "pRq.rqRead" (PRqIdx): RqFromP.
  Definition pRqStateRead := MethodSig "pRq.stateRead" (PRqIdx): RqState.
  Definition pRqLineRead := MethodSig "pRq.lineRead" (PRqIdx): Line.
  Definition pRqRqWrite := MethodSig "pRq.rqWrite" (WritePort LgPRqs RqFromP): Void.
  Definition pRqStateWrite := MethodSig "pRq.stateWrite" (WritePort LgPRqs RqState): Void.
  Definition pRqLineWrite := MethodSig "pRq.lineWrite" (WritePort LgPRqs Line): Void.

  Definition rqFromProcPop := MethodSig "rqFromProc.pop" (Void): RqFromProc.
  Definition fromPPop := MethodSig "fromP.pop" (Void): FromP.

  Definition rsToProcEnq := MethodSig "rsToProc.enq" (RsToProc): Void.
  Definition rqToPEnq := MethodSig "rqToP.enq" (RqToP): Void.
  Definition rsToPEnq := MethodSig "rsToP.enq" (RsToP): Void.

End L1Cache.
