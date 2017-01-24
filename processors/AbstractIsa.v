Require Import Kami.
Require Import Ex.MemTypes.

Set Implicit Arguments.

Section AbstractIsa.
  Variables (rfIdx dataBytes: nat).

  Definition IType := Bit 4.
  Definition iTypeUnsupported: ConstT IType := WO~0~0~0~0.
  Definition iTypeAlu: ConstT IType := WO~0~0~0~1.
  Definition iTypeLd: ConstT IType := WO~0~0~1~0.
  Definition iTypeSt: ConstT IType := WO~0~0~1~1.
  Definition iTypeJ: ConstT IType := WO~0~1~0~0.
  Definition iTypeJr: ConstT IType := WO~0~1~0~1.
  Definition iTypeBr: ConstT IType := WO~0~1~1~0.
  Definition iTypeCsrr: ConstT IType := WO~0~1~1~1.
  Definition iTypeCsrw: ConstT IType := WO~1~0~0~0.
  Definition iTypeAuipc: ConstT IType := WO~1~0~0~1.

  Definition AluFunc := Bit 4.
  Definition aluAdd: ConstT AluFunc := WO~0~0~0~0.
  Definition aluSub: ConstT AluFunc := WO~0~0~0~1.
  Definition aluAnd: ConstT AluFunc := WO~0~0~1~0.
  Definition aluOr: ConstT AluFunc := WO~0~0~1~1.
  Definition aluXor: ConstT AluFunc := WO~0~1~0~0.
  Definition aluSlt: ConstT AluFunc := WO~0~1~0~1.
  Definition aluSltu: ConstT AluFunc := WO~0~1~1~0.
  Definition aluSll: ConstT AluFunc := WO~0~1~1~1.
  Definition aluSra: ConstT AluFunc := WO~1~0~0~0.
  Definition aluSrl: ConstT AluFunc := WO~1~0~0~1.

  Definition BrFunc := Bit 3.
  Definition brEq: ConstT BrFunc := WO~0~0~0.
  Definition brNeq: ConstT BrFunc := WO~0~0~1.
  Definition brLt: ConstT BrFunc := WO~0~1~0.
  Definition brLtu: ConstT BrFunc := WO~0~1~1.
  Definition brGe: ConstT BrFunc := WO~1~0~0.
  Definition brGeu: ConstT BrFunc := WO~1~0~1.
  Definition brAT: ConstT BrFunc := WO~1~1~0.
  Definition brNT: ConstT BrFunc := WO~1~1~1.

  Definition decodedInst :=
    STRUCT { "iType" :: IType;
             "aluFunc" :: AluFunc;
             "brFunc" :: BrFunc;
             "dst" :: Bit rfIdx; "hasDst" :: Bool;
             "src1" :: Bit rfIdx; "hasSrc1" :: Bool;
             "src2" :: Bit rfIdx; "hasSrc2" :: Bool;
             (* csr :: Bit csrIdx; hasCsr :: Bool; *) (* TODO: later *)
             "imm" :: Data dataBytes
           }.

  Definition DecodedInst := Struct decodedInst.

  Definition DecodeT := forall {ty}, fullType ty (SyntaxKind (Data dataBytes)) ->
                                     Expr ty (SyntaxKind DecodedInst).

End AbstractIsa.

