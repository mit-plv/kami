open Format

(* Borrowed from Compcert *)
let camlstring_of_coqstring (s: char list) =
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
    | [] -> r
    | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)

let string_of_de_brujin_index (i: int) =
  "x_" ^ string_of_int i

exception Should_not_happen

let ps = print_string
let pi = print_int

let ppDelim = " "
let ppBinary = "'b"
let ppNeg = "!"
let ppInv = "~"
let ppAnd = "&&"
let ppOr = "||"
let ppZeroExtend = "zeroExtend"
let ppSignExtend = "signExtend"
let ppAdd = "+"
let ppSub = "-"
let ppLt = "<"
let ppVUpdate = "update"

let ppDot = "."
let ppComma = ","
let ppSep = ";"
let ppColon = ":"
let ppQ = "?"
let ppEq = "=="
let ppRBracketL = "("
let ppRBracketR = ")"
let ppCBracketL = "{"
let ppCBracketR = "}"
let ppBracketL = "["
let ppBracketR = "]"
let ppBind = "="

let ppLet = "let"
let ppWriteReg = "<="
let ppIf = "if"
let ppElse = "else"
let ppBegin = "begin"
let ppEnd = "end"
let ppReturn = "return"
let ppWhen = "when"
let ppNoAction = "noAction"

let ppRule = "rule"
let ppEndRule = "endrule"
let ppMethod = "method"
let ppEndMethod = "endmethod"
let ppActionValue = "ActionValue#"
let ppModule = "module"
let ppEndModule = "endmodule"
let ppReg = "Reg#"
let ppAssign = "<-"
let ppMkReg = "mkReg"

let rec ppWord (w: word) =
  match w with
  | WO -> ""
  | WS (false, _, w') -> ppWord w' ^ "0"
  | WS (true, _, w') -> ppWord w' ^ "1"

let rec ppConst (c: constT) =
  match c with
  | ConstBool true -> "True"
  | ConstBool false -> "False"
  | ConstBit (sz, w) -> string_of_int sz ^ ppBinary ^ ppWord w
  | ConstVector (_, _, v) ->
     (* To remove the last comma + delim (", ") *)
     let ppv = ppConstVec v in
     ppCBracketL ^ (String.sub ppv 0 (String.length ppv - 2)) ^ ppCBracketR
  | ConstStruct (_, st) -> ppCBracketL ^ ppConstStruct st ^ ppCBracketR
and ppConstVec (v: constT vec) =
  match v with
  | Vec0 c -> ppConst c ^ ppComma ^ ppDelim
  | VecNext (_, v1, v2) -> ppConstVec v1 ^ ppConstVec v2
and ppConstStruct (stl: (kind attribute, constT) ilist) =
  match stl with
  | Inil -> ""
  | Icons ({ attrName = kn; attrType = _ }, _, c, Inil) ->
     camlstring_of_coqstring kn ^ ppColon ^ ppDelim ^ ppConst c
  | Icons ({ attrName = kn; attrType = _ }, _, c, stl') ->
     camlstring_of_coqstring kn ^ ppColon ^ ppDelim ^ ppConst c
     ^ ppComma ^ ppDelim ^ ppConstStruct stl'

let rec ppBExpr (e: bExpr) =
  match e with
  | BVar v -> string_of_de_brujin_index v
  | BConst (_, c) -> ppConst c
  | BUniBool (Neg, se) -> ppNeg ^ ppDelim ^ ppRBracketL ^ ppBExpr se ^ ppRBracketR
  | BBinBool (And, se1, se2) -> ppRBracketL ^ ppBExpr se1 ^ ppRBracketR
                                ^ ppDelim ^ ppAnd ^ ppDelim
                                ^ ppRBracketL ^ ppBExpr se2 ^ ppRBracketR
  | BBinBool (Or, se1, se2) -> ppRBracketL ^ ppBExpr se1 ^ ppRBracketR
                               ^ ppDelim ^ ppOr ^ ppDelim
                               ^ ppRBracketL ^ ppBExpr se2 ^ ppRBracketR
  | BUniBit (_, _, Inv _, se) -> ppInv ^ ppRBracketL ^ ppBExpr se ^ ppRBracketR
  | BUniBit (_, _, ConstExtract (_, n2, n3), se) ->
     ppRBracketL ^ ppBExpr se ^ ppRBracketR
     ^ ppBracketL ^ string_of_int (n2 + n3) ^ ppColon ^ string_of_int (n3 + 1) ^ ppBracketR
  | BUniBit (_, _, Trunc (_, n2), se) ->
     ppRBracketL ^ ppBExpr se ^ ppRBracketR
     ^ ppBracketL ^ string_of_int (n2 - 1) ^ ppColon ^ "0" ^ ppBracketR
  | BUniBit (_, _, ZeroExtendTrunc _, se) -> ppZeroExtend ^ ppRBracketL ^ ppBExpr se ^ ppRBracketR
  | BUniBit (_, _, SignExtendTrunc _, se) -> ppSignExtend ^ ppRBracketL ^ ppBExpr se ^ ppRBracketR
  | BUniBit (_, _, TruncLsb (n1, n2), se) -> 
     ppRBracketL ^ ppBExpr se ^ ppRBracketR
     ^ ppBracketL ^ string_of_int (n1 + n2 - 1) ^ ppColon ^ string_of_int n2 ^ ppBracketR
  | BBinBit (_, _, _, Add _, se1, se2) ->
     ppRBracketL ^ ppBExpr se1 ^ ppRBracketR
     ^ ppDelim ^ ppAdd ^ ppDelim ^ ppRBracketL ^ ppBExpr se2 ^ ppRBracketR
  | BBinBit (_, _, _, Sub _, se1, se2) ->
     ppRBracketL ^ ppBExpr se1 ^ ppRBracketR
     ^ ppDelim ^ ppSub ^ ppDelim ^ ppRBracketL ^ ppBExpr se2 ^ ppRBracketR
  | BBinBit (_, _, _, Concat (_, _), se1, se2) ->
     ppCBracketL ^ ppRBracketL ^ ppBExpr se1 ^ ppRBracketR
     ^ ppComma ^ ppRBracketL ^ ppBExpr se2 ^ ppRBracketR ^ ppCBracketR
  | BBinBitBool (_, _, Lt _, se1, se2) ->
     ppRBracketL ^ ppBExpr se1 ^ ppRBracketR
     ^ ppDelim ^ ppLt ^ ppDelim ^ ppRBracketL ^ ppBExpr se2 ^ ppRBracketR
  | BITE (ce, te, fe) ->
     ppBExpr ce ^ ppDelim ^ ppQ ^ ppDelim ^ ppBExpr te ^ ppDelim ^ ppColon ^ ppDelim ^ ppBExpr fe
  | BEq (se1, se2) -> ppBExpr se1 ^ ppDelim ^ ppEq ^ ppDelim ^ ppBExpr se2
  | BReadIndex (ie, ve) ->
     ppRBracketL ^ ppBExpr ve ^ ppRBracketR ^ ppBracketL ^ ppBExpr ie ^ ppBracketR
  | BReadField (fd, se) ->
     ppRBracketL ^ ppBExpr se ^ ppRBracketR ^ ppDot ^ camlstring_of_coqstring fd
  | BBuildVector (_, v) ->
     (* To remove the last comma + delim (", ") *)
     let ppv = ppBExprVec v in
     ppCBracketL ^ (String.sub ppv 0 (String.length ppv - 2)) ^ ppCBracketR
  | BBuildStruct st -> ppCBracketL ^ ppBExprStruct st ^ ppCBracketR
  | BUpdateVector (ve, ie, vale) -> 
     ppVUpdate ^ ppDelim ^ ppRBracketL ^ ppBExpr ve ^ ppComma ^ ppDelim
     ^ ppBExpr ie ^ ppComma ^ ppDelim ^ ppBExpr vale ^ ppRBracketR
  | BReadReg r -> camlstring_of_coqstring r
and ppBExprVec (v: bExpr vec) =
  match v with
  | Vec0 e -> ppBExpr e ^ ppComma ^ ppDelim
  | VecNext (_, v1, v2) -> ppBExprVec v1 ^ ppBExprVec v2
and ppBExprStruct (st: bExpr attribute list) =
  match st with
  | [] -> ""
  | { attrName = n; attrType = e } :: [] ->
     camlstring_of_coqstring n ^ ppComma ^ ppDelim ^ ppBExpr e
  | { attrName = n; attrType = e } :: st' ->
     camlstring_of_coqstring n ^ ppComma ^ ppDelim ^ ppBExpr e
     ^ ppComma ^ ppDelim ^ ppBExprStruct st'

let rec ppBAction (a: bAction) =
  (match a with
   | BMCall (bind, meth, e) ->
      ps ppLet; print_space (); ps (string_of_de_brujin_index bind); print_space ();
      ps ppBind; print_space ();
      ps (camlstring_of_coqstring meth);
      ps ppRBracketL; ps (ppBExpr e); ps ppRBracketR
   | BLet (bind, e) ->
      ps ppLet; print_space (); ps (string_of_de_brujin_index bind); print_space ();
      ps ppBind; print_space ();
      ps ppRBracketL; ps (ppBExpr e); ps ppRBracketR
   | BWriteReg (reg, e) ->
      ps (camlstring_of_coqstring reg); print_space ();
      ps ppWriteReg; print_space (); ps (ppBExpr e)
   | BIfElse (ce, ta, fa) ->
      ps ppIf; print_space (); ps (ppBExpr ce); print_space (); ps ppBegin;
      print_break 0 4; open_hovbox 0;
      ppBActions ta;
      close_box (); print_break 0 (-4);
      ps ppEnd; print_space (); ps ppElse; ps ppBegin;
      print_break 0 4; open_hovbox 0;
      ppBActions fa;
      close_box (); print_break 0 (-4);
      ps ppEnd
   | BAssert e -> ps ppNoAction; print_space (); ps ppWhen; print_space ();
                  ps ppRBracketL; ps (ppBExpr e); ps ppRBracketR
   | BReturn e -> ps ppReturn; print_space (); ps (ppBExpr e)); ps ppSep
and ppBActions (aa: bAction list) =
  match aa with
  | [] -> ()
  | a' :: [] -> ppBAction a'
  | a' :: aa' -> ppBAction a'; print_cut (); force_newline (); ppBActions aa'

let ppBRule (r: bRule) =
  match r with
  | { attrName = rn; attrType = rb } ->
     open_hovbox 0;
     ps ppRule; print_space (); ps (camlstring_of_coqstring rn); ps ppSep;
     print_break 0 4; open_hovbox 0;
     ppBActions rb;
     close_box (); print_break 0 (-4); force_newline ();
     ps ppEndRule;
     close_box ()

let rec ppBRules (rl: bRule list) =
  match rl with
  | [] -> ()
  | r :: rl' -> ppBRule r; print_cut (); ppBRules rl'
     
let rec ppKind (k: kind) =
  match k with
  | Bool -> "Bool"
  | Bit w ->
     if w = 0 then "Void"
     else "Bit#" ^ ppRBracketL ^ string_of_int w ^ ppRBracketR
  | Vector (k', w) -> "Vector#" ^ ppRBracketL
                      ^ string_of_int (int_of_float (float 2 ** float w))
                      ^ ppComma ^ ppDelim ^ ppKind k' ^ ppRBracketR
  | Struct sl -> "Struct" ^ ppDelim ^ ppCBracketL ^ ppDelim ^ ppAttrKinds sl
                 ^ ppDelim ^ ppCBracketR
and ppAttrKinds (ks: kind attribute list) =
  match ks with
  | [] -> ""
  | { attrName = kn; attrType = k } :: ks' ->
     ppKind k ^ ppDelim ^ (camlstring_of_coqstring kn) ^ ppSep ^ ppDelim

let ppBMethod (d: bMethod) =
  match d with
  | { attrName = dn; attrType = ({ arg = asig; ret = rsig}, db) } ->
     open_hovbox 0;
     ps ppMethod; print_space (); ps ppActionValue;
     ps ppRBracketL; ps (ppKind rsig); ps ppRBracketR; print_space ();
     ps (camlstring_of_coqstring dn); print_space ();
     ps ppRBracketL; ps (ppKind asig); print_space ();
     ps (string_of_de_brujin_index 0); (* method argument is always x_0 by convention *)
     ps ppRBracketR; ps ppSep;
     print_break 0 4; open_hovbox 0;
     ppBActions db;
     close_box (); print_break 0 (-4); force_newline ();
     ps ppEndMethod;
     close_box ()

let rec ppBMethods (dl: bMethod list) =
  match dl with
  | [] -> ()
  | d :: dl' -> ppBMethod d; print_cut (); force_newline (); ppBMethods dl'

let ppRegInit (r: regInitT) =
  match r with
  | { attrName = rn; attrType = ExistT (_, SyntaxConst (k, c)) } ->
     open_hovbox 0;
     ps ppReg; ps ppRBracketL; ps (ppKind k); ps ppRBracketR; print_space ();
     ps (camlstring_of_coqstring rn); print_space ();
     ps ppAssign; print_space ();
     ps ppMkReg; ps ppRBracketL; ps (ppConst c); ps ppRBracketR; ps ppSep;
     close_box ()
  | _ -> raise Should_not_happen

let rec ppRegInits (rl: regInitT list) =
  match rl with
  | [] -> ()
  | r :: rl' ->
     open_hovbox 0;
     ppRegInit r; print_cut (); ppRegInits rl';
     close_box ()
                                         
let ppBModule (n: string) (m: bModule) =
  match m with
  | { bregs = br; brules = brl; bdms = bd } ->
     ps ppModule; print_space (); ps n; ps "(Empty)"; (* temporarily *) ps ppSep;
     print_break 0 4; open_hovbox 0;
     ppRegInits br;
     print_cut (); force_newline ();
     ppBRules brl;
     print_cut (); force_newline ();
     ppBMethods bd;
     close_box(); print_break 0 (-4);
     ps ppEndModule;
     print_newline ();

