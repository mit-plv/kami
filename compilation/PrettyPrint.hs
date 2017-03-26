import P4st
import Data.List

ppVecLen :: Int -> String
ppVecLen n = "[" ++ show (2 ^ n) ++ "]"

finToInt :: T -> Int
finToInt (F1 _) = 0
finToInt (FS _ x) = succ (finToInt x)

vectorToList :: T0 a -> [a]
vectorToList Nil = []
vectorToList (Cons x _ xs) = x : vectorToList xs

ilistToList :: Ilist a b -> [(a, b)]
ilistToList Inil = []
ilistToList (Icons a _ _ b vs) = (a,b): ilistToList vs

vecToList :: Vec a -> [a]
vecToList (Vec0 a) = [a]
vecToList (VecNext _ xs ys) = vecToList xs ++ vecToList ys

ppDecl :: String -> (String, [Int]) -> String
ppDecl s (x, v) = x ++ ' ' : s ++ concatMap ppVecLen v

ppType :: Kind -> (String, [Int])
ppType Bool = ("logic", [])
ppType (Bit i) = if i > 0
                 then ("logic [" ++ show (i-1) ++ ":0]", [])
                 else ("logic", [])
ppType (Vector k i) = (fst v, i : snd v)
                      where v = ppType k
ppType (Struct n v) = ("struct {" ++ concatMap (\x -> ppDecl (attrName x) (ppType (attrType x)) ++ "; ") (vectorToList v) ++ "}", [])


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

ppRtlExpr :: RtlExpr -> String
ppRtlExpr (RtlReadReg k s) = s
ppRtlExpr (RtlReadInput k var) = ppPrintVar var
ppRtlExpr (RtlReadWire k var) = ppPrintVar var
ppRtlExpr (RtlConst k c) = ppConst c
ppRtlExpr (RtlUniBool Neg e) = "(~" ++ ppRtlExpr e ++ ")"
ppRtlExpr (RtlBinBool And e1 e2) = '(' : ppRtlExpr e1 ++ " & " ++ ppRtlExpr e2 ++ ")"
ppRtlExpr (RtlBinBool Or e1 e2) = '(' : ppRtlExpr e1 ++ " | " ++ ppRtlExpr e2 ++ ")"
ppRtlExpr (RtlUniBit _ _ (Inv _) e) = "(~" ++ ppRtlExpr e ++ ")"
ppRtlExpr (RtlUniBit sz retSz (ConstExtract lsb ret msb) e) = ppRtlExpr e ++ '[' : show (sz - msb - 1) ++ ':' : show lsb ++ "]"
ppRtlExpr (RtlUniBit sz retSz (Trunc _ _) e) = ppRtlExpr e ++ '[' : show (retSz - 1) ++ ":0]"
ppRtlExpr (RtlUniBit sz retSz (TruncLsb lsb _) e) = ppRtlExpr e ++ '[' : show (sz - 1) ++ ':' : show lsb ++ "]"
ppRtlExpr (RtlUniBit sz retSz (ZeroExtendTrunc _ _) e) = if sz < retSz
                                                         then "{ " ++ show (retSz - sz) ++ "'b0, " ++ ppRtlExpr e ++ "}"
                                                         else ppRtlExpr e ++ '[' : show (retSz - 1) ++ ":0]"
ppRtlExpr (RtlUniBit sz retSz (SignExtendTrunc _ _) e) = if sz < retSz
                                                         then "{{" ++ show (retSz - sz) ++ '{' : ppRtlExpr e ++ "[" ++
                                                              show sz ++ "]" ++ "}}, " ++ ppRtlExpr e ++ "}"
                                                         else ppRtlExpr e ++ '[' : show (retSz - 1) ++ ":0]"
ppRtlExpr (RtlBinBit _ _ _ (Add _) e1 e2) = '(' : ppRtlExpr e1 ++ " + " ++ ppRtlExpr e2 ++ ")"
ppRtlExpr (RtlBinBit _ _ _ (Sub _) e1 e2) = '(' : ppRtlExpr e1 ++ " - " ++ ppRtlExpr e2 ++ ")"
ppRtlExpr (RtlBinBit _ _ _ (Mul _) e1 e2) = '(' : ppRtlExpr e1 ++ " * " ++ ppRtlExpr e2 ++ ")"
ppRtlExpr (RtlBinBit _ _ _ (Band _) e1 e2) = '(' : ppRtlExpr e1 ++ " & " ++ ppRtlExpr e2 ++ ")"
ppRtlExpr (RtlBinBit _ _ _ (Bor _) e1 e2) = '(' : ppRtlExpr e1 ++ " | " ++ ppRtlExpr e2 ++ ")"
ppRtlExpr (RtlBinBit _ _ _ (Bxor _) e1 e2) = '(' : ppRtlExpr e1 ++ " ^ " ++ ppRtlExpr e2 ++ ")"
ppRtlExpr (RtlBinBit _ _ _ (Sll _ _) e1 e2) = '(' : ppRtlExpr e1 ++ " << " ++ ppRtlExpr e2 ++ ")"
ppRtlExpr (RtlBinBit _ _ _ (Srl _ _) e1 e2) = '(' : ppRtlExpr e1 ++ " >> " ++ ppRtlExpr e2 ++ ")"
ppRtlExpr (RtlBinBit _ _ _ (Sra _ _) e1 e2) = "($signed("  ++ ppRtlExpr e1 ++ ") >>> " ++ ppRtlExpr e2 ++ ")"
ppRtlExpr (RtlBinBit _ _ _ (Concat _ _) e1 e2) = '{' : ppRtlExpr e1 ++ ", " ++ ppRtlExpr e2 ++ "}"
ppRtlExpr (RtlBinBitBool _ _ (Lt _) e1 e2) =  '(' : ppRtlExpr e1 ++ "<" ++ ppRtlExpr e2 ++ "}"
ppRtlExpr (RtlITE _ p e1 e2) = '(' : ppRtlExpr p ++ '?' : ppRtlExpr e1 ++ ':' : ppRtlExpr e2 ++ ")"
ppRtlExpr (RtlEq _ e1 e2) = '(' : ppRtlExpr e1 ++ "==" ++ ppRtlExpr e2 ++ ")"
ppRtlExpr (RtlReadIndex _ _ v i) = ppRtlExpr v ++ '[' : ppRtlExpr i ++ "]"
ppRtlExpr (RtlReadField _ fields idx s) = ppRtlExpr s ++ '.' : attrName (vectorToList fields !! finToInt idx)
ppRtlExpr (RtlBuildVector _ _ vs) = '{' : intercalate ", " (map ppRtlExpr (vecToList vs)) ++ "}"
ppRtlExpr (RtlBuildStruct _ _ es) = '{' : intercalate ", " (map (\x -> ppRtlExpr (snd x)) (ilistToList es)) ++ "}"
ppRtlExpr (RtlUpdateVector n _ v idx val) =
  '{' : intercalate ", "
  (map (\i -> ppRtlExpr idx ++ "==" ++ show n ++ "'d" ++ show i ++ " ? " ++ ppRtlExpr val ++
              ":" ++ ppRtlExpr v ++ "[" ++ show i ++ "]")
   [0 .. ((2^n)-1)]) ++ "}"

ppRtlModule :: RtlModule -> String
ppRtlModule (Build_RtlModule ins outs regs assigns) =
  "module top(\n" ++
  concatMap (\(nm, ty) -> "  input " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n") ins ++ "\n" ++
  concatMap (\(nm, ty) -> "  output " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n") outs ++ "\n" ++
  "  input CLK,\n" ++
  "  input RESET\n" ++
  ");\n" ++
  concatMap (\(nm, (ty, (init, expr))) -> "  " ++ ppDeclType (sanitizeString nm) ty ++ ";\n") regs ++ "\n" ++
  concatMap (\(nm, (ty, expr)) -> "  " ++ ppDeclType (ppPrintVar nm) ty ++ ";\n") assigns ++ "\n" ++
  concatMap (\(nm, (ty, expr)) -> "  assign " ++ ppPrintVar nm ++ " = " ++ ppRtlExpr expr ++ ";\n") assigns ++ "\n" ++
  "  always @(posedge CLK) begin\n" ++
  concatMap (\(nm, (ty, (init, expr))) -> "    " ++ sanitizeString nm ++
                                          " <= RESET? " ++ ppConst init ++ ":" ++ ppRtlExpr expr ++ ";\n") regs ++
  "  end\n\n" ++
  "endmodule\n"

main =
  putStrLn (ppRtlModule p4stRtl)
