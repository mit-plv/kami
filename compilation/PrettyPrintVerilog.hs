import Target
import Data.List
import Control.Monad.State.Lazy

instance Show a => Show (Attribute a) where
  show (Build_Attribute x y) = "(" ++ show x ++ ", " ++ show y ++ ")"

ppVecLen :: Int -> String
ppVecLen n = "[" ++ show (2^n-1) ++ ":0]"

finToInt :: T -> Int
finToInt (F1 _) = 0
finToInt (FS _ x) = succ (finToInt x)

vectorToList :: T0 a -> [a]
vectorToList Nil = []
vectorToList (Cons x _ xs) = x : vectorToList xs

instance Show Kind where
  show Bool = "Bool"
  show (Bit n) = "(Bit " ++ show n ++ ")"
  show (Vector k i) = "(Vector " ++ show k ++ " " ++ show i ++ ")"
  show (Struct n vec) = "(Struct " ++ show (vectorToList vec) ++ ")"

ilistToList :: Ilist a b -> [(a, b)]
ilistToList Inil = []
ilistToList (Icons a _ _ b vs) = (a,b): ilistToList vs

vecToList :: Vec a -> [a]
vecToList (Vec0 a) = [a]
vecToList (VecNext _ xs ys) = vecToList xs ++ vecToList ys

ppDecl :: String -> (String, [Int]) -> String
ppDecl s (x, v) =
  case v of
    [] -> x ++ ' ' : s
    _ -> case x of
           'l' : 'o' : 'g' : 'i' : 'c' : ' ' : ys -> "logic " ++ concatMap ppVecLen (reverse v) ++ ys ++ ' ' : s
           _ -> x ++ concatMap ppVecLen v ++ ' ' : s
--  x ++ concatMap ppVecLen v ++ ' ' : s 

ppType :: Kind -> (String, [Int])
ppType Bool = ("logic", [])
ppType (Bit i) = if i > 0
                 then ("logic [" ++ show (i-1) ++ ":0]", [])
                 else ("logic", [])
ppType (Vector k i) = (fst v, i : snd v)
                      where v = ppType k
ppType (Struct n v) = ("struct packed {" ++ concatMap (\x -> ppDecl (attrName x) (ppType (attrType x)) ++ "; ") (vectorToList v) ++ "}", [])


replChar :: Char -> String
replChar '.' = "$_$"
replChar c = c : []

sanitizeString :: String -> String
sanitizeString s = concatMap replChar s


ppDeclType :: String -> Kind -> String
ppDeclType s k = ppDecl s (ppType k)

ppPrintVar :: (String, [Int]) -> String
ppPrintVar (s, vs) = sanitizeString s ++ concatMap (\v -> '$' : show v) vs

ppWord :: [Bool] -> String
ppWord [] = []
ppWord (b : bs) = (if b then '1' else '0') : ppWord bs

ppConst :: ConstT -> String
ppConst (ConstBool b) = if b then "1'b1" else "1'b0"
ppConst (ConstBit sz w) = if sz == 0 then "1'b0" else show sz ++ "\'b" ++ ppWord w
ppConst (ConstVector k _ vs) = '{' : intercalate ", " (map ppConst (vecToList vs)) ++ "}"
ppConst (ConstStruct _ _ is) = '{' : intercalate ", " (map ppConst (snd (unzip (ilistToList is)))) ++ "}"

ppRtlExpr :: String -> RtlExpr -> State [(Int, Kind, String)] String
ppRtlExpr who e =
  case e of
    RtlReadReg k s -> return (sanitizeString s)
    RtlReadInput k var -> return $ ppPrintVar var
    RtlReadWire k var -> return $ ppPrintVar var
    RtlConst k c -> return $ ppConst c
    RtlUniBool Neg e -> uniExpr "~" e
    RtlBinBool And e1 e2 -> binExpr e1 "&" e2
    RtlBinBool Or e1 e2 -> binExpr e1 "|" e2
    RtlUniBit _ _ (Inv _) e -> uniExpr "~" e
    RtlUniBit sz retSz (ConstExtract lsb ret msb) e -> createTrunc (Bit sz) e (sz - msb - 1) lsb
    RtlUniBit sz retSz (Trunc _ _) e -> createTrunc (Bit sz) e (retSz - 1) 0
    RtlUniBit sz retSz (TruncLsb lsb _) e -> createTrunc (Bit sz) e (sz - 1) lsb
    RtlUniBit sz retSz (ZeroExtendTrunc _ _) e -> if sz < retSz
                                                  then
                                                    do
                                                      x <- ppRtlExpr who e
                                                      return $ '{' : show (retSz - sz) ++ "'b0, " ++ x ++ "}"
                                                  else createTrunc (Bit sz) e (retSz - 1) 0
    RtlUniBit sz retSz (SignExtendTrunc _ _) e -> if sz < retSz
                                                  then
                                                    do
                                                      (new, rest) <- optionAddToTrunc (Bit sz) e ('[' : show (sz - 1) ++ "]")
                                                      return $ "{{" ++ show (retSz - sz) ++ '{' : new ++ rest ++ "}}, " ++ new ++ "}"
                                                  else createTrunc (Bit sz) e (retSz - 1) 0
    RtlBinBit _ _ _ (Add _) e1 e2 -> binExpr e1 "+" e2
    RtlBinBit _ _ _ (Sub _) e1 e2 -> binExpr e1 "-" e2
    RtlBinBit _ _ _ (Mul _) e1 e2 -> binExpr e1 "*" e2
    RtlBinBit _ _ _ (Band _) e1 e2 -> binExpr e1 "&" e2
    RtlBinBit _ _ _ (Bor _) e1 e2 -> binExpr e1 "|" e2
    RtlBinBit _ _ _ (Bxor _) e1 e2 -> binExpr e1 "^" e2
    RtlBinBit _ _ _ (Sll _ _) e1 e2 -> binExpr e1 "<<" e2
    RtlBinBit _ _ _ (Srl _ _) e1 e2 -> binExpr e1 ">>" e2
    RtlBinBit _ _ _ (Sra _ _) e1 e2 ->
      do
        x1 <- ppRtlExpr who e1
        x2 <- ppRtlExpr who e2
        return $ "($signed(" ++ x1 ++ ") >>> " ++ x2 ++ ")"
    RtlBinBit _ _ _ (Concat _ _) e1 e2 ->
      do
        x1 <- ppRtlExpr who e1
        x2 <- ppRtlExpr who e2
        return $ '{' : x1 ++ ", " ++ x2 ++ "}"
    RtlBinBitBool _ _ (Lt _) e1 e2 -> binExpr e1 "<" e2
    RtlITE _ p e1 e2 -> triExpr p "?" e1 ":" e2
    RtlEq _ e1 e2 -> binExpr e1 "==" e2
    RtlReadIndex n k idx vec ->
      do
        xidx <- ppRtlExpr who idx
        xvec <- ppRtlExpr who vec
        (new, rest) <- optionAddToTrunc (Vector k n) vec ('[' : xidx ++ "]")
        return $ new ++ rest
    RtlReadField _ fields idx e ->
      do
        x <- ppRtlExpr who e
        return $ x ++ '.' : attrName (vectorToList fields !! finToInt idx)
    RtlBuildVector _ _ vs ->
      do
        strs <- mapM (ppRtlExpr who) (vecToList vs)
        return $ '{': intercalate ", " strs ++ "}"
    RtlBuildStruct _ _ es ->
      do
        strs <- mapM (ppRtlExpr who) (map snd (ilistToList es))
        return $ '{': intercalate ", " strs ++ "}"
    RtlUpdateVector n _ v idx val ->
      do
        xv <- ppRtlExpr who v
        xidx <- ppRtlExpr who idx
        xval <- ppRtlExpr who val
        return $  '{' : intercalate ", "
          (map (\i -> xidx ++ "==" ++ show n ++ "'d" ++ show i ++ " ? " ++ xval ++
                 ":" ++ xv ++ "[" ++ show i ++ "]")
           [0 .. ((2^n)-1)]) ++ "}"
  where
    optionAddToTrunc :: Kind -> RtlExpr -> String -> State [(Int, Kind, String)] (String, String)
    optionAddToTrunc k e rest =
      case e of
        RtlReadReg k s -> return $ (sanitizeString s, rest)
        RtlReadInput k var -> return $ (ppPrintVar var, rest)
        RtlReadWire k var -> return $ (ppPrintVar var, rest)
        _ -> do
          x <- ppRtlExpr who e
          new <- addToTrunc k x
          return $ (new, rest)
    createTrunc :: Kind -> RtlExpr -> Int -> Int -> State [(Int, Kind, String)] String
    createTrunc k e msb lsb =
      do
        (new, rest) <- optionAddToTrunc k e ('[' : show msb ++ ':' : show lsb ++ "]")
        return $ new ++ rest
    addToTrunc :: Kind -> String -> State [(Int, Kind, String)] String
    addToTrunc k s =
      do
        x <- get
        case Data.List.find (\(_, k', s') -> s' == s) x of
          Just (pos, _, _) -> return $ "_trunc$" ++ who ++ "$" ++ show pos
          Nothing ->
            do
              put ((Data.List.length x, k, s) : x)
              return $ "_trunc$" ++ who ++ "$" ++ show (Data.List.length x)
    uniExpr op e =
      do
        x <- ppRtlExpr who e
        return $ '(' : " " ++ op ++ " " ++ x ++ ")"
    binExpr e1 op e2 =
      do
        x1 <- ppRtlExpr who e1
        x2 <- ppRtlExpr who e2
        return $ '(' : x1 ++ " " ++ op ++ " " ++ x2 ++ ")"
    triExpr e1 op1 e2 op2 e3 =
      do
        x1 <- ppRtlExpr who e1
        x2 <- ppRtlExpr who e2
        x3 <- ppRtlExpr who e3
        return $ '(' : x1 ++ " " ++ op1 ++ " " ++ x2 ++ " " ++ op2 ++ " " ++ x3 ++ ")"

ppRtlModule :: RtlModule -> String
ppRtlModule m@(Build_RtlModule ins' outs' regs assigns') =
  "module top(\n" ++
  concatMap (\(nm, ty) -> "  input " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n") ins ++ "\n" ++
  concatMap (\(nm, ty) -> "  output " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n") outs ++ "\n" ++
  "  input CLK,\n" ++
  "  input RESET\n" ++
  ");\n" ++
  concatMap (\(nm, (ty, (init, expr))) -> "  " ++ ppDeclType (sanitizeString nm) ty ++ ";\n") regs ++ "\n" ++
  concatMap (\(nm, (ty, expr)) -> "  " ++ ppDeclType (ppPrintVar nm) ty ++ ";\n") assigns ++ "\n" ++
  
  concatMap (\(pos, ty, sexpr) -> "  " ++ ppDeclType ("_trunc$wire$" ++ show pos) ty ++ ";\n") assignTruncs ++ "\n" ++
  concatMap (\(pos, ty, sexpr) -> "  assign " ++ "_trunc$wire$" ++ show pos ++ " = " ++ doArray ty sexpr ++ ";\n") assignTruncs ++ "\n" ++
  
  concatMap (\(nm, (ty, sexpr)) -> "  assign " ++ ppPrintVar nm ++ " = " ++ doArray ty sexpr ++ ";\n") assignExprs ++ "\n" ++
  
  "  always @(posedge CLK) begin\n" ++
  concatMap (\(pos, ty, sexpr) -> "  " ++ ppDeclType ("_trunc$reg$" ++ show pos) ty ++ ";\n") regTruncs ++ "\n" ++
  concatMap (\(pos, ty, sexpr) -> "  assign " ++ "_trunc$reg$" ++ show pos ++ " = " ++ doArray ty sexpr ++ ";\n") regTruncs ++ "\n" ++
  
  concatMap (\(nm, (ty, (init, sexpr))) -> "    if(RESET) begin\n" ++
              "      " ++ sanitizeString nm ++ " <= " ++ doArray ty (ppConst init) ++ ";\n" ++
              "    end\n" ++
              "    else begin\n" ++
              "      " ++ sanitizeString nm ++ " <= " ++ doArray ty sexpr ++ ";\n" ++
              "    end\n") regExprs ++
  "  end\n\n" ++
  "endmodule\n"
  where
    doArray ty s = case ty of
                     Vector _ _ -> if head s == '{'
                                   then s
                                   else s
                     _ -> s
    ins = nubBy (\(a, _) (b, _) -> a == b) ins'
    outs = nubBy (\(a, _) (b, _) -> a == b) outs'
    assigns = nubBy (\(a, _) (b, _) -> a == b) assigns'
    convAssigns =
      mapM (\(nm, (ty, expr)) ->
              do
                s <- ppRtlExpr "wire" expr
                return (nm, (ty, s))) assigns
    convRegs =
      mapM (\(nm, (ty, (init, expr))) ->
              do
                s <- ppRtlExpr "reg" expr
                return (nm, (ty, (init, s)))) regs
    (assignExprs, assignTruncs) = runState convAssigns []
    (regExprs, regTruncs) = runState convRegs []


main =
  do
    --putStrLn $ show (methPos Target.mod (map attrName (getRules Target.mod)) "enq.f2d")
    --putStrLn $ show (map attrName (getRules Target.mod))
    --putStrLn $ show (getCallGraph Target.mod)
    putStrLn $ ppRtlModule target
