Require Import Kami.Syntax String Lib.Struct Lib.ilist.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section Syntax.
  
  Inductive RtlExpr: Kind -> Type :=
| RtlReadReg k: string -> RtlExpr k
| RtlReadInput k: string -> RtlExpr k
| RtlReadWire k: (string * list nat) -> RtlExpr k
| RtlConst k: ConstT k -> RtlExpr k
| RtlUniBool: UniBoolOp -> RtlExpr Bool -> RtlExpr Bool
| RtlBinBool: BinBoolOp -> RtlExpr Bool -> RtlExpr Bool -> RtlExpr Bool
| RtlUniBit n1 n2: UniBitOp n1 n2 -> RtlExpr (Bit n1) -> RtlExpr (Bit n2)
| RtlBinBit n1 n2 n3: BinBitOp n1 n2 n3 -> RtlExpr (Bit n1) -> RtlExpr (Bit n2) ->
                      RtlExpr (Bit n3)
| RtlBinBitBool n1 n2: BinBitBoolOp n1 n2 -> RtlExpr (Bit n1) -> RtlExpr (Bit n2) ->
                       RtlExpr Bool
| RtlITE k: RtlExpr Bool -> RtlExpr k -> RtlExpr k -> RtlExpr k
| RtlEq k: RtlExpr (k) -> RtlExpr (k) -> RtlExpr (Bool)
| RtlReadIndex i k: RtlExpr ((Bit i)) -> RtlExpr ((Vector k i)) -> RtlExpr (k)
| RtlReadField n (ls: Vector.t _ n) (i: Fin.t n):
    RtlExpr ((Struct ls)) -> RtlExpr ((Vector.nth (Vector.map (@attrType _) ls) i))
| RtlBuildVector n k: Vec (RtlExpr (n)) k -> RtlExpr ((Vector n k))
| RtlBuildStruct n (attrs: Vector.t _ n):
    ilist (fun a => RtlExpr ((attrType a))) attrs -> RtlExpr ((Struct attrs))
| RtlUpdateVector i k: RtlExpr ((Vector k i)) -> RtlExpr ((Bit i)) -> RtlExpr (k)
                       -> RtlExpr ((Vector k i)).

  Record RtlModule :=
    { regs: list (string * Kind);
      inputs: list (string * Kind);
      outputs: list (string * sigT RtlExpr);
      regWrites: list (string * (RtlExpr Bool * sigT RtlExpr));
      wires: list (string * list nat * sigT RtlExpr) }.
End Syntax.
