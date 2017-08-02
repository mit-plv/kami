Require Import List.
Require Import Lib.Word.
Require Import Notations.
Require Import Coq.Numbers.BinNums.
Require Import Ex.IsaRv32.

Inductive TraceEvent : Set :=
| Rd (addr : word 32)
| Wr (addr : word 32)
| Branch (taken : bool)
| ToHost.

Definition Gpr_eq_dec : forall (r1 r2 : Gpr), {r1 = r2} + {r1 <> r2}.
Proof.
  intros; case r1; case r2;
    solve [ left; reflexivity | right; discriminate ].
Defined.

Definition registers := Gpr -> word 32.

Definition rget (regs : registers) (reg : Gpr) : word 32 :=
  if Gpr_eq_dec reg x0 then wzero 32 else regs reg.

Definition rset (regs : registers) (reg : Gpr) (val : word 32) : registers :=
  if Gpr_eq_dec reg x0
  then regs
  else fun r => if Gpr_eq_dec r reg then val else regs r.

Definition memory := word 32 -> option (word 32).

Definition mget (m : memory) (addr : word 32) : option (word 32) :=
  m addr.

Definition mset (m : memory) (addr : word 32) (val : word 32) : memory :=
  fun a => if weq a addr then Some val else m a.

Definition spReg := x2.

Definition sext {sz sz' : nat} (w : word sz) : word sz' := ZToWord sz' (wordToZ w).

Inductive hasTrace : registers -> memory -> word 32 -> word 32 -> list TraceEvent -> Prop :=
| htStackDone : forall regs mem pc maxsp,
    regs spReg > maxsp ->
    hasTrace regs mem pc maxsp nil
| htJAL : forall rd ofs regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (JAL rd ofs)) ->
    hasTrace (rset regs rd (pc ^+ $4)) mem (pc ^+ sext ofs) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: trace')
| htJALR : forall rs1 rd ofs regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (JALR rs1 rd ofs)) ->
    hasTrace (rset regs rd (pc ^+ $4)) mem (rget regs rs1 ^+ sext ofs) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: trace')
| htBEQTrue : forall rs1 rs2 ofs regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (BEQ rs1 rs2 ofs)) ->
    rget regs rs1 = rget regs rs2 ->
    hasTrace regs mem (pc ^+ sext ofs) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: Branch true :: trace')
| htBEQFalse : forall rs1 rs2 ofs regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (BEQ rs1 rs2 ofs)) ->
    rget regs rs1 <> rget regs rs2 ->
    hasTrace regs mem (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: Branch false :: trace')
| htBNETrue : forall rs1 rs2 ofs regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (BNE rs1 rs2 ofs)) ->
    rget regs rs1 <> rget regs rs2 ->
    hasTrace regs mem (pc ^+ sext ofs) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: Branch true :: trace')
| htBNEFalse : forall rs1 rs2 ofs regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (BNE rs1 rs2 ofs)) ->
    rget regs rs1 = rget regs rs2 ->
    hasTrace regs mem (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: Branch false :: trace')
| htBLTTrue : forall rs1 rs2 ofs regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (BLT rs1 rs2 ofs)) ->
    wslt (rget regs rs1) (rget regs rs2) ->
    hasTrace regs mem (pc ^+ sext ofs) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: Branch true :: trace')
| htBLTFalse : forall rs1 rs2 ofs regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (BLT rs1 rs2 ofs)) ->
    ~(wslt (rget regs rs1) (rget regs rs2)) ->
    hasTrace regs mem (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: Branch false :: trace')
| htBGETrue : forall rs1 rs2 ofs regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (BGE rs1 rs2 ofs)) ->
    ~(wslt (rget regs rs1) (rget regs rs2)) ->
    hasTrace regs mem (pc ^+ sext ofs) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: Branch true :: trace')
| htBGEFalse : forall rs1 rs2 ofs regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (BGE rs1 rs2 ofs)) ->
    wslt (rget regs rs1) (rget regs rs2) ->
    hasTrace regs mem (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: Branch false :: trace')
| htBLTUTrue : forall rs1 rs2 ofs regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (BLTU rs1 rs2 ofs)) ->
    wlt (rget regs rs1) (rget regs rs2) ->
    hasTrace regs mem (pc ^+ sext ofs) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: Branch true :: trace')
| htBLTUFalse : forall rs1 rs2 ofs regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (BLTU rs1 rs2 ofs)) ->
    ~(wlt (rget regs rs1) (rget regs rs2)) ->
    hasTrace regs mem (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: Branch false :: trace')
| htBGEUTrue : forall rs1 rs2 ofs regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (BGEU rs1 rs2 ofs)) ->
    ~(wlt (rget regs rs1) (rget regs rs2)) ->
    hasTrace regs mem (pc ^+ sext ofs) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: Branch true :: trace')
| htBGEUFalse : forall rs1 rs2 ofs regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (BGEU rs1 rs2 ofs)) ->
    wlt (rget regs rs1) (rget regs rs2) ->
    hasTrace regs mem (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: Branch false :: trace')
| htLW : forall rs1 rd ofs val regs mem pc maxsp trace',
    let addr := rget regs rs1 ^+ sext ofs in
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (LW rs1 rd ofs)) ->
    mget mem addr = Some val ->
    hasTrace (rset regs rd val) mem (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: Rd addr :: trace')
| htSW : forall rs1 rs2 ofs regs mem pc maxsp trace',
    let addr := rget regs rs1 ^+ sext ofs in
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (SW rs1 rs2 ofs)) ->
    hasTrace regs (mset mem addr (rget regs rs2)) (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: Wr addr :: trace')
| htADDI : forall rs1 rd ofs regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (ADDI rs1 rd ofs)) ->
    hasTrace (rset regs rd (rget regs rs1 ^+ sext ofs)) mem (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: trace')
| htADD : forall rs1 rs2 rd regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (ADD rs1 rs2 rd)) ->
    hasTrace (rset regs rd (rget regs rs1 ^+ rget regs rs2)) mem (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: trace')
| htSUB : forall rs1 rs2 rd regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (SUB rs1 rs2 rd)) ->
    hasTrace (rset regs rd (rget regs rs1 ^- rget regs rs2)) mem (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: trace')
| htMUL : forall rs1 rs2 rd regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (MUL rs1 rs2 rd)) ->
    hasTrace (rset regs rd (rget regs rs1 ^* rget regs rs2)) mem (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: trace')
| htSLL : forall rs1 rs2 rd regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (SLL rs1 rs2 rd)) ->
    hasTrace (rset regs rd (sll (rget regs rs1) (wordToNat (rget regs rs2)))) mem (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: trace')
| htSRL : forall rs1 rs2 rd regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (SRL rs1 rs2 rd)) ->
    hasTrace (rset regs rd (srl (rget regs rs1) (wordToNat (rget regs rs2)))) mem (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: trace')
| htOR : forall rs1 rs2 rd regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (OR rs1 rs2 rd)) ->
    hasTrace (rset regs rd (rget regs rs1 ^| rget regs rs2)) mem (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: trace')
| htAND : forall rs1 rs2 rd regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (AND rs1 rs2 rd)) ->
    hasTrace (rset regs rd (rget regs rs1 ^& rget regs rs2)) mem (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: trace')
| htXOR : forall rs1 rs2 rd regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (XOR rs1 rs2 rd)) ->
    hasTrace (rset regs rd (wxor (rget regs rs1) (rget regs rs2))) mem (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: trace')
| htTOHOST : forall rs1 regs mem pc maxsp trace',
    regs spReg <= maxsp ->
    mget mem pc = Some (rv32iToRaw (TOHOST rs1)) ->
    hasTrace regs mem (pc ^+ $4) maxsp trace' ->
    hasTrace regs mem pc maxsp (Rd pc :: ToHost :: trace').
