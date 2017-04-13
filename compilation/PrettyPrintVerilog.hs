{-# OPTIONS_GHC -XStandaloneDeriving #-}

import Vtor
import Target
import Data.List
import Data.List.Split
import Control.Monad.State.Lazy
import qualified Data.HashMap.Strict as H

deriving instance Show T
deriving instance Show a => Show (Vtor a)
deriving instance Show a => Show (Attribute a)
deriving instance (Show a, Show b) => Show (Ilist a b)
deriving instance Show Target.Word
deriving instance Show a => Show (Vec a)
deriving instance Show Kind
deriving instance Show ConstT
deriving instance Show UniBoolOp
deriving instance Show BinBoolOp

deriving instance Show UniBitOp
deriving instance Show BinBitOp
deriving instance Show BinBitBoolOp
deriving instance Show RtlExpr
deriving instance Show RtlModule

ppVecLen :: Int -> String
ppVecLen n = "[" ++ show (2^n-1) ++ ":0]"

finToInt :: T -> Int
finToInt (F1 _) = 0
finToInt (FS _ x) = Prelude.succ (finToInt x)

vectorToList :: Vtor a -> [a]
vectorToList NilV = []
vectorToList (ConsV x _ xs) = x : vectorToList xs

ilistToList :: Ilist a b -> [b]
ilistToList Inil = []
ilistToList (Icons _ _ _ b vs) = b: ilistToList vs

vecToList :: Vec a -> [a]
vecToList (Vec0 a) = [a]
vecToList (VecNext _ xs ys) = vecToList xs ++ vecToList ys

wordToList :: Target.Word -> [Bool]
wordToList WO = []
wordToList (WS b _ w) = b : wordToList w

ppTypeVec :: Kind -> Int -> (Kind, [Int])
ppTypeVec k@(Vector k' i') i =
  let (k'', is) = ppTypeVec k' i'
  in (k', i : is)
ppTypeVec k i = (k, i : [])

ppTypeName :: Kind -> String
ppTypeName k =
  case ppTypeVec k 0 of
    (Struct _ _, _) -> "struct packed"
    (_, _) -> "logic"

ppType :: Kind -> String
ppType Bool = ""
ppType (Bit i) = if i > 0
                      then "[" ++ show (i-1) ++ ":0]"
                      else ""
ppType v@(Vector k i) =
  let (k', is) = ppTypeVec k i
  in case k' of
       Struct _ _ -> ppType k' ++ concatMap ppVecLen is
       _ -> concatMap ppVecLen is ++ ppType k'
ppType (Struct n v) = "{" ++ concatMap (\x -> ' ' : ppDeclType (ppName $ attrName x) (attrType x) ++ ";") (vectorToList v) ++ "}"

ppDottedName :: String -> String
ppDottedName s =
  case splitOn "." s of
    x : y : nil -> y ++ "$" ++ x
    x : nil -> x

ppName :: String -> String
ppName s = intercalate "$" (Data.List.map (\x -> ppDottedName x) (splitOneOf "$#" s))
  {-
  if elem '.' s
  then intercalate "$" (case splitOneOf ".#" s of
                          x : y : xs -> x : y : xs
                          ys -> ys)
  else Data.List.map (\x -> case x of
                         '#' -> '$'
                         c -> c) s
-}


ppDeclType :: String -> Kind -> String
ppDeclType s k = ppTypeName k ++ ppType k ++ " " ++ s

ppPrintVar :: (String, [Int]) -> String
ppPrintVar (s, vs) = ppName $ s ++ concatMap (\v -> '#' : show v) vs

ppWord :: [Bool] -> String
ppWord [] = []
ppWord (b : bs) = (if b then '1' else '0') : ppWord bs

ppConst :: ConstT -> String
ppConst (ConstBool b) = if b then "1'b1" else "1'b0"
ppConst (ConstBit sz w) = if sz == 0 then "1'b0" else show sz ++ "\'b" ++ ppWord (reverse $ wordToList w)
ppConst (ConstVector k _ vs) = '{' : intercalate ", " (Data.List.map ppConst (reverse $ vecToList vs)) ++ "}"
ppConst (ConstStruct _ _ is) = '{' : intercalate ", " (Data.List.map ppConst (ilistToList is)) ++ "}"



ppRtlExpr :: String -> RtlExpr -> State (H.HashMap String (Int, Kind)) String
ppRtlExpr who e =
  case e of
    RtlReadReg k s -> return (ppName s)
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
                                                      new <- optionAddToTrunc (Bit sz) e
                                                      return $ "{{" ++ show (retSz - sz) ++ '{' : new ++ '[' : show (sz - 1) ++ "]}}, " ++ new ++ "}"
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
    RtlBinBitBool _ _ (Lt0 _) e1 e2 -> binExpr e1 "<" e2
    RtlITE _ p e1 e2 -> triExpr p "?" e1 ":" e2
    RtlEq _ e1 e2 -> binExpr e1 "==" e2
    RtlReadIndex n k idx vec ->
      do
        xidx <- ppRtlExpr who idx
        xvec <- ppRtlExpr who vec
        new <- optionAddToTrunc (Vector k n) vec
        return $ new ++ '[' : xidx ++ "]"
    RtlReadField num fields idx e ->
      do
        new <- optionAddToTrunc (Struct num fields) e
        return $ new ++ '.' : attrName (vectorToList fields !! finToInt idx)
    RtlBuildVector _ _ vs ->
      do
        strs <- mapM (ppRtlExpr who) (reverse $ vecToList vs)
        return $ '{': intercalate ", " strs ++ "}"
    RtlBuildStruct _ _ es ->
      do
        strs <- mapM (ppRtlExpr who) (ilistToList es)
        return $ '{': intercalate ", " strs ++ "}"
    RtlUpdateVector n _ v idx val ->
      do
        xv <- ppRtlExpr who v
        xidx <- ppRtlExpr who idx
        xval <- ppRtlExpr who val
        return $  '{' : intercalate ", "
          (Data.List.map (\i -> xidx ++ "==" ++ show n ++ "'d" ++ show i ++ " ? " ++ xval ++
                           ":" ++ xv ++ "[" ++ show i ++ "]")
           (reverse [0 .. ((2^n)-1)])) ++ "}"
  where
    optionAddToTrunc :: Kind -> RtlExpr -> State (H.HashMap String (Int, Kind)) String
    optionAddToTrunc k e =
      case e of
        RtlReadReg k s -> return $ ppName s
        RtlReadInput k var -> return $ ppPrintVar var
        RtlReadWire k var -> return $ ppPrintVar var
        _ -> do
          x <- ppRtlExpr who e
          new <- addToTrunc k x
          return new
    createTrunc :: Kind -> RtlExpr -> Int -> Int -> State (H.HashMap String (Int, Kind)) String
    createTrunc k e msb lsb =
      do
        new <- optionAddToTrunc k e
        return $ new ++ '[' : show msb ++ ':' : show lsb ++ "]"
    addToTrunc :: Kind -> String -> State (H.HashMap String (Int, Kind)) String
    addToTrunc kind s =
      do
        x <- get
        case H.lookup s x of
          Just (pos, _) -> return $ "_trunc$" ++ who ++ "$" ++ show pos
          Nothing ->
            do
              put (H.insert s (H.size x, kind) x)
              return $ "_trunc$" ++ who ++ "$" ++ show (H.size x)
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

ppRfInstance :: (((String, [(String, Bool)]), String), (((Int, Kind)), ConstT)) -> String
ppRfInstance (((name, reads), write), ((idxType, dataType), _)) =
  "  " ++ ppName name ++ " " ++
  ppName name ++ "$inst(.CLK(CLK), .RESET_N(RESET_N), ." ++
  concatMap (\(read, _) ->
               ppName read ++ "$_g(" ++ ppName read ++ "$_g), ." ++
               ppName read ++ "$_en(" ++ ppName read ++ "$_en), ." ++
               ppName read ++ "$_arg(" ++ ppName read ++ "$_arg), ." ++
               ppName read ++ "$_ret(" ++ ppName read ++ "$_ret), .") reads ++
  ppName write ++ "$_g(" ++ ppName write ++ "$_g), ." ++
  ppName write ++ "$_en(" ++ ppName write ++ "$_en), ." ++
  ppName write ++ "$_arg(" ++ ppName write ++ "$_arg));\n\n"
  
ppRfModule :: (((String, [(String, Bool)]), String), ((Int, Kind), ConstT)) -> String
ppRfModule (((name, reads), write), ((idxType, dataType), init)) =
  "module " ++ ppName name ++ "(\n" ++
  concatMap (\(read, _) ->
               "  output " ++ ppDeclType (ppName read ++ "$_g") Bool ++ ",\n" ++
              "  input " ++ ppDeclType (ppName read ++ "$_en") Bool ++ ",\n" ++
              "  input " ++ ppDeclType (ppName read ++ "$_arg") (Bit idxType) ++ ",\n" ++
              "  output " ++ ppDeclType (ppName read ++ "$_ret") dataType ++ ",\n") reads ++
  "  output " ++ ppDeclType (ppName write ++ "$_g") Bool ++ ",\n" ++
  "  input " ++ ppDeclType (ppName write ++ "$_en") Bool ++ ",\n" ++
  "  input " ++ ppDeclType (ppName write ++ "$_arg")
  (Struct 2 (ConsV (Build_Attribute "addr" (Bit idxType)) 2 (ConsV (Build_Attribute "data" dataType) 1 NilV))) ++ ",\n" ++
  "  input logic CLK,\n" ++
  "  input logic RESET_N\n" ++
  ");\n" ++
  "  " ++ ppDeclType (ppName name ++ "$_data") dataType ++ "[0:" ++ show (2^idxType - 1) ++ "];\n" ++
  "  initial begin\n" ++
  "    " ++ ppName name ++ "$_data = " ++ '\'' : ppConst init ++ ";\n" ++
  "  end\n" ++
  concatMap (\(read, bypass) ->
               "  assign " ++ ppName read ++ "$_g = 1'b1;\n" ++
              "  assign " ++ ppName read ++ "$_ret = " ++
              if bypass
              then ppName write ++ "$_en && " ++ ppName write ++ "$_arg.addr == " ++
                   ppName read ++ "$_arg ? " ++ ppName write ++ "$_data : "
              else "" ++ ppName name ++ "$_data[" ++ ppName read ++ "$_arg];\n") reads ++
  "  assign " ++ ppName write ++ "$_g = 1'b1;\n" ++
  "  always@(posedge CLK) begin\n" ++
  "    if(" ++ ppName write ++ "$_en) begin\n" ++
  "      " ++ ppName name ++ "$_data[" ++ ppName write ++ "$_arg.addr] <= " ++ ppName write ++ "$_arg.data;\n" ++
  "    end\n" ++
  "  end\n" ++
  "endmodule\n\n"

removeDups :: Eq a => [(a, b)] -> [(a, b)]
removeDups = nubBy (\(a, _) (b, _) -> a == b)

ppRtlInstance :: RtlModule -> String
ppRtlInstance m@(Build_RtlModule regFs ins' outs' regInits' regWrites' assigns') =
  "  _design _designInst(.CLK(CLK), .RESET_N(RESET_N)" ++
  concatMap (\(nm, ty) -> ", ." ++ ppPrintVar nm ++ '(' : ppPrintVar nm ++ ")") (removeDups ins' ++ removeDups outs') ++ ");\n"
  
ppRtlModule :: RtlModule -> String
ppRtlModule m@(Build_RtlModule regFs ins' outs' regInits' regWrites' assigns') =
  "module _design(\n" ++
  concatMap (\(nm, ty) -> "  input " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n") ins ++ "\n" ++
  concatMap (\(nm, ty) -> "  output " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n") outs ++ "\n" ++
  "  input CLK,\n" ++
  "  input RESET_N\n" ++
  ");\n" ++
  concatMap (\(nm, (ty, init)) -> "  " ++ ppDeclType (ppName nm) ty ++ ";\n") regInits ++ "\n" ++

  concatMap (\(nm, (ty, expr)) -> "  " ++ ppDeclType (ppPrintVar nm) ty ++ ";\n") assigns ++ "\n" ++
  
  concatMap (\(sexpr, (pos, ty)) -> "  " ++ ppDeclType ("_trunc$wire$" ++ show pos) ty ++ ";\n") assignTruncs ++ "\n" ++
  concatMap (\(sexpr, (pos, ty)) -> "  " ++ ppDeclType ("_trunc$reg$" ++ show pos) ty ++ ";\n") regTruncs ++ "\n" ++

  concatMap (\(sexpr, (pos, ty)) -> "  assign " ++ "_trunc$wire$" ++ show pos ++ " = " ++ sexpr ++ ";\n") assignTruncs ++ "\n" ++
  concatMap (\(sexpr, (pos, ty)) -> "  assign " ++ "_trunc$reg$" ++ show pos ++ " = " ++ sexpr ++ ";\n") regTruncs ++ "\n" ++
  
  concatMap (\(nm, (ty, sexpr)) -> "  assign " ++ ppPrintVar nm ++ " = " ++ sexpr ++ ";\n") assignExprs ++ "\n" ++
  
  "  always @(posedge CLK) begin\n" ++
  "    if(!RESET_N) begin\n" ++
  concatMap (\(nm, (ty, init)) -> "      " ++ ppName nm ++ " <= " ++ ppConst init ++ ";\n") regInits ++
  "    end\n" ++
  "    else begin\n" ++
  concatMap (\(nm, (ty, sexpr)) -> "      " ++ ppName nm ++ " <= " ++ sexpr ++ ";\n") regExprs ++
  "    end\n" ++
  "  end\n" ++
  "endmodule\n\n"
  where
    ins = removeDups ins'
    outs = removeDups outs'
    regInits = removeDups regInits'
    regWrites = removeDups regWrites'
    assigns = removeDups assigns'
    convAssigns =
      mapM (\(nm, (ty, expr)) ->
              do
                s <- ppRtlExpr "wire" expr
                return (nm, (ty, s))) assigns
    convRegs =
      mapM (\(nm, (ty, expr)) ->
              do
                s <- ppRtlExpr "reg" expr
                return (nm, (ty, s))) regWrites
    (assignExprs, assignTruncs') = runState convAssigns H.empty
    (regExprs, regTruncs') = runState convRegs H.empty
    assignTruncs = H.toList assignTruncs'
    regTruncs = H.toList regTruncs'

ppGraph :: [(String, [String])] -> String
ppGraph x = case x of
              [] -> ""
              (a, b) : ys -> "(" ++ show a ++ ", " ++ show b ++ ", " ++ show (Data.List.length b) ++ "),\n" ++ ppGraph ys


maxOutEdge :: [(String, [String])] -> Int
maxOutEdge x = case x of
                 [] -> 0
                 (a, b) : ys -> Prelude.max (Data.List.length b) (maxOutEdge ys)

sumOutEdge :: [(String, [String])] -> Int
sumOutEdge x = case x of
                 [] -> 0
                 (a, b) : ys -> Data.List.length b + sumOutEdge ys

ppTopModule :: RtlModule -> String
ppTopModule m@(Build_RtlModule regFs ins' outs' regInits' regWrites' assigns') =
  concatMap ppRfModule regFs ++ ppRtlModule m ++
  "module top(\n" ++
  concatMap (\(nm, ty) -> "  input " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n") ins ++ "\n" ++
  concatMap (\(nm, ty) -> "  output " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n") outs ++ "\n" ++
  "  input CLK,\n" ++
  "  input RESET_N\n" ++
  ");\n" ++
  concatMap (\(nm, ty) -> "  " ++ ppDeclType (ppPrintVar nm) ty ++ ";\n") insAll ++ "\n" ++
  concatMap (\(nm, ty) -> "  " ++ ppDeclType (ppPrintVar nm) ty ++ ";\n") outsAll ++ "\n" ++
  concatMap ppRfInstance regFs ++
  ppRtlInstance m ++
  "endmodule\n"
  where
    insAll = removeDups ins'
    outsAll = removeDups outs'
    ins = Data.List.filter filtCond insAll
    outs = Data.List.filter filtCond outsAll
    badRead x read = x == read ++ "#_g" || x == read ++ "#_en" || x == read ++ "#_arg" || x == read ++ "#_ret"
    badReads x reads = foldl (\accum (v, _) -> badRead x v || accum) False reads
    filtCond ((x, _), _) = case Data.List.find (\((((_, reads), write), (_, _))) ->
                                                  badReads x reads ||
                                                  {-
                                                  x == read ++ "#_g" ||
                                                  x == read ++ "#_en" ||
                                                  x == read ++ "#_arg" ||
                                                  x == read ++ "#_ret" ||
                                                  -}
                                                  x == write ++ "#_g" ||
                                                  x == write ++ "#_en" ||
                                                  x == write ++ "#_arg" ||
                                                  x == write ++ "#_ret") regFs of
                          Nothing -> True
                          _ -> False

printDiff :: [(String, [String])] -> [(String, [String])] -> IO ()
printDiff (x:xs) (y:ys) =
  do
    if x == y
    then printDiff xs ys
    else putStrLn $ (show x) ++ " " ++ (show y)
printDiff [] [] = return ()
printDiff _ _ = putStrLn "Wrong lengths"
  

main =
  putStrLn $ ppTopModule target
