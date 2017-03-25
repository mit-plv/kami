import P4st
import Data.List

ppVecLen :: Int -> String
ppVecLen n = "[" ++ show (2 ^ n) ++ "]"

{-
ppVecArray :: Kind -> String
ppVecArray (Vector k i) = (ppVecLen i ++ fst v, snd v)
                          where v = ppVecArray k
ppVecArray k = ("", k)
-}

vectorToList :: T0 a -> [a]
vectorToList Nil = []
vectorToList (Cons x _ xs) = x : vectorToList xs

ppDecl :: String -> (String, [Int]) -> String
ppDecl s (x, v) = x ++ ' ' : s ++ concatMap ppVecLen v

ppType :: Kind -> (String, [Int])
ppType Bool = ("logic", [])
ppType (Bit i) = if i > 0
                 then ("logic [" ++ show (i-1) ++ ":0]", [])
                 else ("logic", [])
ppType (Vector k i) = (fst v, i : snd v)
                      where v = ppType k
ppType (Struct n v) = ("struct " ++ concatMap (\x -> ppDecl (attrName x) (ppType (attrType x)) ++ "; ") (vectorToList v), [])


ppDeclType :: String -> Kind -> String
ppDeclType s k = ppDecl s (ppType k)

ppPrintVar :: (String, [Int]) -> String
ppPrintVar (s, vs) = s ++ concatMap (\v -> '$' : show v) vs

ppWord :: [Bool] -> String
ppWord [] = []
ppWord (b : bs) = (if b then '1' else '0') : ppWord bs

ppConst :: ConstT -> String
ppConst (ConstBool b) = if b then "1'b1" else "1'b0"
ppConst (ConstBit sz w) = show sz ++ '\'' : ppWord w

ppRtlExpr :: RtlExpr -> String
ppRtlExpr (RtlReadReg k s) = s
ppRtlExpr (RtlReadInput k var) = ppPrintVar var
ppRtlExpr (RtlReadWire k var) = ppPrintVar var
ppRtlExpr (RtlConst k c) = ppConst c
ppRtlExpr (RtlUniBool Neg e) = "(~" ++ ppRtlExpr e ++ ")"
ppRtlExpr (RtlBinBool And e1 e2) = '(' : ppRtlExpr e1 ++ " & " ++ ppRtlExpr e2 ++ ")"
ppRtlExpr (RtlBinBool Or e1 e2) = '(' : ppRtlExpr e1 ++ " | " ++ ppRtlExpr e2 ++ ")"
ppRtlExpr (RtlUniBit _ _ (Inv _) e) = "(~" ++ ppRtlExpr e ++ ")"
ppRtlExpr (RtlUniBit _ _ (ConstExtract a b c) e) = ""
ppRtlExpr (RtlUniBit _ _ (Trunc _ _) e) = ""
ppRtlExpr (RtlUniBit _ _ (TruncLsb _ _) e) = ""
ppRtlExpr (RtlUniBit _ _ (ZeroExtendTrunc _ _) e) = ""
ppRtlExpr (RtlUniBit _ _ (SignExtendTrunc _ _) e) = ""
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

main =
  putStrLn "Hello world"
