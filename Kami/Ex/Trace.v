Require Import List.
Require Import Notations.
Require Import Coq.Numbers.BinNums.
Require Import Lib.Word.
Require Import Kami.Syntax Kami.Semantics.
Require Import Ex.SC Ex.IsaRv32.

Section AbstractTrace.
  Definition address := type (Bit rv32iAddrSize).

  Definition data := type (MemTypes.Data rv32iDataBytes).

  Definition register := type (Bit rv32iRfIdx).

  Definition regfile := StateT rv32iDataBytes rv32iRfIdx type.

  Definition rget (rf : regfile) (r : register) : data :=
    if weq r (wzero _)
    then wzero _
    else evalExpr (ReadIndex #r #rf)%kami_expr.

  Definition rset (rf : regfile) (r : register) (v : data) : regfile :=
    if weq r (wzero _)
    then rf
    else evalExpr (UpdateVector #rf #r #v)%kami_expr.

  Definition memory := address -> option data.

  Definition mget (m : memory) (addr : address) : option data :=
    m addr.

  Definition mset (m : memory) (addr : address) (val : data) : memory :=
    fun a => if weq a addr then Some val else m a.

  Definition spReg : register := gprToRaw x2.

  Inductive TraceEvent : Type :=
  | Rd (addr : address)
  | Wr (addr : address)
  | Branch (taken : bool)
  | ToHost
  | FromHost.

  Inductive hasTrace : regfile -> memory -> address -> data -> list TraceEvent -> Prop :=
  | htStackDone : forall rf mem pc maxsp,
      rget rf spReg > maxsp ->
      hasTrace rf mem pc maxsp nil
  | htLd : forall inst val rf mem pc maxsp trace',
      rget rf spReg <= maxsp ->
      mget mem pc = Some inst ->
      evalExpr (rv32iGetOptype type inst) = opLd ->
      let addr := evalExpr (rv32iGetLdAddr type inst) in
      let dstIdx := evalExpr (rv32iGetLdDst type inst) in
      let srcIdx := evalExpr (rv32iGetLdSrc type inst) in
      let srcVal := rget rf srcIdx in
      let laddr := evalExpr (rv32iCalcLdAddr type addr srcVal) in
      let laddr_aligned := evalExpr (rv32iAlignAddr type laddr) in
      mget mem laddr_aligned = Some val ->
      hasTrace (rset rf dstIdx val) mem (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf mem pc maxsp (Rd pc :: Rd laddr_aligned :: trace')
  | htSt : forall inst rf mem pc maxsp trace',
      rget rf spReg <= maxsp ->
      mget mem pc = Some inst ->
      evalExpr (rv32iGetOptype type inst) = opSt ->
      let addr := evalExpr (rv32iGetStAddr type inst) in
      let srcIdx := evalExpr (rv32iGetStSrc type inst) in
      let srcVal := rget rf srcIdx in
      let vsrcIdx := evalExpr (rv32iGetStVSrc type inst) in
      let stVal := rget rf vsrcIdx in
      let saddr := evalExpr (rv32iCalcStAddr type addr srcVal) in
      let saddr_aligned := evalExpr (rv32iAlignAddr type saddr) in
      hasTrace rf (mset mem saddr_aligned stVal) (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf mem pc maxsp (Rd pc :: Wr saddr_aligned :: trace')
  | htTh : forall inst rf mem pc maxsp trace',
      rget rf spReg <= maxsp ->
      mget mem pc = Some inst ->
      evalExpr (rv32iGetOptype type inst) = opTh ->
      hasTrace rf mem (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf mem pc maxsp (Rd pc :: ToHost :: trace')
  | htFh : forall inst rf val mem pc maxsp trace',
      rget rf spReg <= maxsp ->
      mget mem pc = Some inst ->
      evalExpr (rv32iGetOptype type inst) = opFh ->
      let dst := evalExpr (rv32iGetDst type inst) in
      hasTrace (rset rf dst val) mem (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf mem pc maxsp (Rd pc :: FromHost :: trace')
  | htNmBranch : forall inst rf mem pc maxsp trace',
      rget rf spReg <= maxsp ->
      mget mem pc = Some inst ->
      evalExpr (rv32iGetOptype type inst) = opNm ->
      evalExpr (getOpcodeE #inst)%kami_expr = rv32iOpBRANCH ->
      hasTrace rf mem (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf mem pc maxsp (Rd pc :: Branch (evalExpr (rv32iBranchTaken type rf inst)) :: trace')
  | htNm : forall inst rf mem pc maxsp trace',
      rget rf spReg <= maxsp ->
      mget mem pc = Some inst ->
      evalExpr (rv32iGetOptype type inst) = opNm ->
      evalExpr (getOpcodeE #inst)%kami_expr <> rv32iOpBRANCH ->
      let src1 := evalExpr (rv32iGetSrc1 type inst) in
      let val1 := rget rf src1 in
      let src2 := evalExpr (rv32iGetSrc2 type inst) in
      let val2 := rget rf src2 in
      let dst := evalExpr (rv32iGetDst type inst) in
      let execVal := evalExpr (rv32iExec type val1 val2 pc inst) in
      hasTrace (rset rf dst execVal) mem (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf mem pc maxsp (Rd pc :: trace').


  (* With this representation, the property "fromhost values don't
   * affect the trace" is equivalent to "hasTrace is deterministic",
   * since the trace hides fromhost values. *)
  Definition abstractHiding rf mem pc maxsp : Prop :=
    forall trace trace',
      hasTrace rf mem pc maxsp trace ->
      hasTrace rf mem pc maxsp trace' ->
      trace = trace'.

End AbstractTrace.

Section KamiTrace.
  Definition censorLabel censorMeth (l : LabelT) : LabelT :=
    match l with
    | {| annot := a;
         defs := d;
         calls := c; |} =>
      {| annot := a;
         defs := FMap.M.mapi censorMeth d;
         calls := FMap.M.mapi censorMeth c; |}
    end.

  Definition censorLabelSeq censorMeth : LabelSeqT -> LabelSeqT :=
    map (censorLabel censorMeth).

  Definition censorSCMeth (n : String.string) (t : {x : SignatureT & SignT x}) : {x : SignatureT & SignT x} :=
    if String.string_dec n "exec"
    then match t with
         | existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (argV, retV) =>
           existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (evalExpr (STRUCT { "addr" ::= #argV!(RqFromProc rv32iAddrSize rv32iDataBytes)@."addr";
                                      "op" ::= #argV!(RqFromProc rv32iAddrSize rv32iDataBytes)@."op";
                                      "data" ::= $0 })%kami_expr,
                   evalExpr (STRUCT { "data" ::= $0 })%kami_expr)
         | _ => t
         end
    else if String.string_dec n "toHost"
    then match t with
         | existT _
                  {| arg := Bit 32;
                     ret := Bit 0 |}
                  (argV, retV) =>
           existT _
                  {| arg := Bit 32;
                     ret := Bit 0 |}
                  ($0, retV)
         | _ => t
         end
    else if String.string_dec n "fromHost"
    then match t with
         | existT _
                  {| arg := Bit 0;
                     ret := Bit 32 |}
                  (argV, retV) =>
           existT _
                  {| arg := Bit 0;
                     ret := Bit 32 |}
                  (argV, $0)
         | _ => t
         end
    else t.

  Definition extractFhLabel extractFh (l : LabelT) : option (word 32) :=
    match l with
    | {| annot := _;
         defs := _;
         calls := c; |} => extractFh c
    end.

  Definition extractFhLabelSeq extractFh : LabelSeqT -> list (option (word 32)) :=
    map (extractFhLabel extractFh).

  Open Scope string_scope.

  Definition extractFhSC (cs : MethsT) : option (word 32) :=
    match (FMap.M.find "fromHost" cs) with
    | Some (existT _
                   {| arg := Bit 0;
                      ret := Bit 32 |}
                   (argV, retV)) => Some retV
    | _ => None
    end.

  Definition fhTiming : list (option (word 32)) -> list bool :=
    map (fun o => match o with
               | Some _ => true
               | None => false
               end).

  Definition kamiHiding censorMeth extractFh m regs : Prop :=
    forall labels newRegs fhs,
      Multistep m regs newRegs labels ->
      extractFhLabelSeq extractFh labels = fhs ->
      forall fhs',
        fhTiming fhs = fhTiming fhs' ->
        exists labels' newRegs',
          Multistep m regs newRegs' labels' /\
          censorLabelSeq censorMeth labels = censorLabelSeq censorMeth  labels' /\
          extractFhLabelSeq extractFh labels' = fhs'.
End KamiTrace.
