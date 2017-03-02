Require Import Kami.Syntax String Compile.Rtl Lib.ilist Lib.Struct List.

Set Implicit Arguments.
Set Asymmetric Patterns.


Open Scope string.
Definition getRegRead s := s ++ "$read".
Definition getRegWrite s := s ++ "$write".
Definition getRegActionWrite a s := a ++ "$" ++ s ++ "$write".
Definition getRegActionEn a s := a ++ "$" ++ s ++ "$en".

Definition getMethCallRet f := f ++ "$ret".
Definition getMethCallArg f := f ++ "$arg".
Definition getMethCallActionArg a f := a ++ "$" ++ f ++ "$arg".
Definition getMethCallActionEn a f := a ++ "$" ++ f ++ "$en".

Definition getMethDefRet f := f ++ "$ret".
Definition getMethDefArg f := f ++ "$arg".
Definition getMethDefGuard f := f ++ "$g".

Definition getRuleGuard r := r ++ "$g".

Close Scope string.

Section Compile.
  Variable name: string.
  Fixpoint convertExprToRtl k (e: Expr (fun _ => list nat) (SyntaxKind k)): RtlExpr k :=
    match e in Expr _ (SyntaxKind k) return RtlExpr k with
      | Var k' x' =>   match k' return
                             (forall x,
                                match k' return (Expr (fun _ => list nat) k' -> Set) with
                                  | SyntaxKind k => fun _ => RtlExpr k
                                  | NativeKind _ _ => fun _ => IDProp
                                end (Var (fun _ : Kind => list nat) k' x))
                       with
                         | SyntaxKind k => fun x => RtlReadWire k (name, x)
                         | NativeKind t c => fun _ => idProp
                       end x'
      | Const k x => RtlConst x
      | UniBool x x0 => RtlUniBool x (@convertExprToRtl _ x0)
      | BinBool x x0 x1 => RtlBinBool x (@convertExprToRtl _ x0) (@convertExprToRtl _ x1)
      | UniBit n1 n2 x x0 => RtlUniBit x (@convertExprToRtl _ x0)
      | BinBit n1 n2 n3 x x0 x1 => RtlBinBit x (@convertExprToRtl _ x0) (@convertExprToRtl _ x1)
      | BinBitBool n1 n2 x x0 x1 => RtlBinBitBool x (@convertExprToRtl _ x0) (@convertExprToRtl _ x1)
      | Eq k x x0 => RtlEq (@convertExprToRtl _ x) (@convertExprToRtl _ x0)
      | ReadIndex i k x x0 => RtlReadIndex (@convertExprToRtl _ x) (@convertExprToRtl _ x0)
      | ReadField n ls i x => RtlReadField i (@convertExprToRtl _ x)
      | BuildVector k n x => RtlBuildVector (mapVec (@convertExprToRtl k) x)
      | BuildStruct n attrs x =>
        RtlBuildStruct
          ((fix buildStruct n attrs x :=
              match x in ilist _ attrs return ilist (fun a => RtlExpr (attrType a)) attrs with
                | inil => inil (fun a => RtlExpr (attrType a))
                | icons a na vs h t => icons a (@convertExprToRtl (attrType a) h) (buildStruct na vs t)
              end) n attrs x)
      | UpdateVector i k x x0 x1 => RtlUpdateVector (@convertExprToRtl _ x) (@convertExprToRtl _ x0) (@convertExprToRtl _ x1)
      | ITE k' x x0' x1' =>
        match k' return
              (forall x0 x1,
                 match k' return (Expr (fun _ => list nat) k' -> Set) with
                   | SyntaxKind k => fun _ => RtlExpr k
                   | NativeKind _ _ => fun _ => IDProp
                 end (ITE x x0 x1))
        with
          | SyntaxKind k => fun x0 x1 => RtlITE (@convertExprToRtl _ x) (@convertExprToRtl _ x0) (@convertExprToRtl _ x1)
          | NativeKind t c => fun _ _ => idProp
        end x0' x1'
    end.

  Local Definition inc ns := match ns with
                               | nil => nil
                               | x :: xs => S x :: xs
                             end.

  Local Notation cast k' startList := match k' with
                                       | SyntaxKind k => startList
                                       | NativeKind _ c => c
                                     end.
  
  Fixpoint convertActionToRtl_noGuard k (a: ActionT (fun _ => list nat) k) enable startList retList :=
    match a in ActionT _ _ with
      | MCall meth k argExpr cont =>
        (getMethCallActionArg name meth, nil, existT _ (arg k) (convertExprToRtl argExpr)) ::
        (getMethCallActionEn name meth, nil, existT _ Bool enable) ::
        (name, startList, existT _ (ret k) (RtlReadInput (ret k) (getMethCallRet meth))) ::
        convertActionToRtl_noGuard (cont startList) enable (inc startList) retList
      | Let_ k' expr cont =>
        let wires := convertActionToRtl_noGuard (cont (cast k' startList)) enable (inc startList) retList in
        match k' return Expr (fun _ => list nat) k' -> list (string * list nat * sigT RtlExpr) with
          | SyntaxKind k => fun expr => (name, startList, existT _ k (convertExprToRtl expr)) :: wires
          | _ => fun _ => wires
        end expr
      | ReadReg r k' cont =>
        let wires := convertActionToRtl_noGuard (cont (cast k' startList)) enable (inc startList) retList in
        match k' return list (string * list nat * sigT RtlExpr) with
          | SyntaxKind k => (name, startList, existT _ k (RtlReadReg k (getRegRead r))) :: wires
          | _ => wires
        end
      | WriteReg r k' expr cont =>
        let wires := convertActionToRtl_noGuard cont enable startList retList in
        match k' return Expr (fun _ => list nat) k' -> list (string * list nat * sigT RtlExpr) with
          | SyntaxKind k => fun expr => (getRegActionWrite name r, nil, existT _ k (convertExprToRtl expr)) ::
                                        (getRegActionEn name r, nil, existT _ Bool enable) :: wires
          | _ => fun _ => wires
        end expr
      | Assert_ pred cont => convertActionToRtl_noGuard cont enable startList retList
      | Return x => (name, retList, existT _ k (convertExprToRtl x)) :: nil
      | IfElse pred ktf t f cont =>
        convertActionToRtl_noGuard t (RtlBinBool And enable (convertExprToRtl pred)) (0 :: startList) (startList) ++
        convertActionToRtl_noGuard t
          (RtlBinBool And enable (RtlUniBool Neg (convertExprToRtl pred))) (0 :: inc startList) (inc startList) ++
        (name, inc (inc startList),
         existT _ ktf (RtlITE (convertExprToRtl pred) (RtlReadWire ktf (name, startList)) (RtlReadWire ktf (name, inc startList)))) ::
        convertActionToRtl_noGuard (cont (inc (inc startList))) enable (inc (inc (inc startList))) retList
    end.

  Fixpoint convertActionToRtl_guard k (a: ActionT (fun _ => list nat) k) startList: RtlExpr Bool :=
    match a in ActionT _ _ with
      | MCall meth k argExpr cont =>
        convertActionToRtl_guard (cont startList) (inc startList)
      | Let_ k' expr cont =>
        convertActionToRtl_guard (cont (cast k' startList)) (inc startList)
      | ReadReg r k' cont =>
        convertActionToRtl_guard (cont (cast k' startList)) (inc startList)
      | WriteReg r k' expr cont =>
        convertActionToRtl_guard cont startList
      | Assert_ pred cont => RtlBinBool And (convertExprToRtl pred)
                                        (convertActionToRtl_guard cont startList)
      | Return x => RtlConst (ConstBool true)
      | IfElse pred ktf t f cont =>
        RtlBinBool And
                   (RtlITE (convertExprToRtl pred) (convertActionToRtl_guard t (0 :: startList))
                           (convertActionToRtl_guard t (0 :: inc startList)))
                   (convertActionToRtl_guard (cont (inc (inc startList))) (inc (inc (inc startList))))
    end.
End Compile.
  
Definition convertRuleToRtl (r: Attribute (Action Void)) :=
  (getRuleGuard (attrName r), nil,
   existT _ Bool (convertActionToRtl_guard (attrName r) (attrType r (fun _ => list nat)) (1 :: nil))) ::
  convertActionToRtl_noGuard (attrName r) (attrType r (fun _ => list nat)) (RtlConst (ConstBool true)) (1 :: nil) (0 :: nil).

Definition convertMethodToRtl_wire (f: DefMethT) :=
  (getMethDefGuard (attrName f), nil,
   existT _ Bool (convertActionToRtl_guard (attrName f) (projT2 (attrType f) (fun _ => list nat) (1 :: nil)) (2 :: nil))) ::
  (attrName f, 1 :: nil,
   existT _ (arg (projT1 (attrType f))) (RtlReadInput (arg (projT1 (attrType f))) (getMethDefArg (attrName f)))) ::
  convertActionToRtl_noGuard (attrName f) (projT2 (attrType f) (fun _ => list nat) (1 :: nil))
   (RtlConst (ConstBool true)) (2 :: nil) (0 :: nil).

Definition convertMethodToRtl_output (f: DefMethT) :=
  (getMethDefRet (attrName f), existT _ _ (RtlReadWire (ret (projT1 (attrType f))) (attrName f, 0 :: nil))).
