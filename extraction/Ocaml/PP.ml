open Format
open Target

(* string manipulations *)
let bsv_keywords =
  [ (* Bluespec keywords *)
    "action"; "actionvalue"; "ancestor";
    "begin"; "bit"; "case"; "clocked_by"; "default"; "default_clock"; "default_reset";
    "dependencies"; "deriving"; "determines"; "e"; "else"; "enable"; "end"; "enum"; "export"; "for";
    "function"; "if"; "ifc_inout"; "import"; "inout"; "input_clock"; "input_reset"; "instance";
    "interface"; "let"; "match"; "matches"; "method"; "module"; "numeric"; "output_clock";
    "output_reset"; "package"; "parameter"; "path"; "port"; "endaction"; "endactionvalue";
    "endcase"; "endfunction"; "endinstance"; "endinterface"; "endmethod"; "endmodule"; "endpackage";
    "provisos"; "reset_by"; "return"; "rule"; "rules"; "same_family"; "schedule"; "struct";
    "tagged"; "type"; "typeclass"; "typedef"; "union"; "valueOf"; "valueof"; "void"; "while";
    "endrule"; "endrules"; "endtypeclass";
    (* Verilog keywords *)
    "alias"; "always"; "always_comb"; "always_ff"; "always_latch"; "and"; "assert";
    "assert_strobe"; "assign"; "assume"; "automatic"; "before"; "begin"; "end"; "bind"; "bins";
    "binsof"; "bit"; "break"; "buf"; "bufif0"; "bufif1"; "byte"; "case"; "endcase"; "casex";
    "expect"; "export"; "extends"; "extern"; "final"; "first_match"; "for"; "force"; "foreach";
    "forever"; "fork"; "forkjoin"; "function"; "endfunction"; "generate"; "endgenerate"; "genvar";
    "highz0"; "highz1"; "if"; "iff"; "ifnone"; "ignore_bins"; "illegal_bins"; "import"; "incdir";
    "include"; "initial"; "inout"; "input"; "inside"; "instance"; "int"; "integer"; "interface";
    "endinterface"; "intersect"; "join"; "join_any"; "join_none"; "large"; "liblist"; "library";
    "local"; "localparam"; "logic"; "longint"; "macromodule"; "matches"; "medium"; "modport";
    "module"; "endmodule"; "negedge"; "new"; "nmos"; "nor"; "noshowcancelled"; "not"; "casez";
    "cell"; "chandle"; "class"; "clocking"; "endclocking"; "cmos"; "config"; "const";
    "constraint"; "context"; "continue"; "cover"; "covergroup"; "endgroup"; "coverpoint";
    "cross"; "deassign"; "default"; "defparam"; "design"; "disable"; "dist"; "real"; "realtime";
    "ref"; "reg"; "release"; "repeat"; "return"; "rnmos"; "rpmos"; "rtran"; "rtranif0"; "rtranif1";
    "scalared"; "sequence"; "shortint"; "shortreal"; "showcancelled"; "endclass"; "endconfig";
    "do"; "edge"; "else"; "enum"; "event"; "nand"; "endsequence"; "151"; "notif0"; "notif1";
    "null"; "or"; "output"; "package"; "packed"; "parameter"; "pmos"; "posedge"; "primitive";
    "priority"; "program"; "property"; "protected"; "pull0"; "pull1"; "pulldown"; "pullup";
    "pulsestyle_onevent"; "pulsestyle_ondetect"; "pure"; "rand"; "randc"; "randcase";
    "randsequence"; "rcmos"; "endpackage"; "endprimitive"; "endprogram"; "endproperty";
    "signed"; "time"; "var"; "small"; "timeprecision"; "vectored"; "solve"; "timeunit";
    "specify"; "endspecify"; "tran"; "specparam"; "tranif0"; "static"; "tranif1"; "string"; "tri";
    "strong0"; "tri0"; "strong1"; "tri1"; "struct"; "triand"; "super"; "trior"; "supply0";
    "trireg"; "supply1"; "type"; "table"; "endtable"; "typedef"; "tagged"; "union"; "task";
    "endtask"; "unique"; "this"; "unsigned"; "throughout"; "use"; "virtual"; "void"; "wait";
    "wait_order"; "wand"; "weak0"; "weak1"; "while"; "wildcard"; "wire"; "with"; "within"; "wor";
    "xnor"; "xor"]

(* Partial definition borrowed from Compcert *)
(* TODO: '.' -> "__" / '$' -> "___" *)
let bstring_of_charlist (s: char list) =
  let rec string_of_charlist (s: char list) =
    match s with
    | [] -> ""
    | c :: s -> (Char.escaped (if c = '.' || c = '$' then '_' else c)) ^ (string_of_charlist s)
  in
  let str = string_of_charlist s in
  let bstr = String.uncapitalize str in
  if List.mem bstr bsv_keywords then bstr ^ "_" else bstr

let string_of_de_brujin_index (i: int) =
  "x_" ^ string_of_int i

exception Should_not_happen of string

let ps = print_string
let pi = print_int

let ppDelim = " "
let ppHexa = "'h"
let ppNeg = "!"
let ppInv = "~"
let ppAnd = "&&"
let ppOr = "||"
let ppZeroExtend = "zeroExtend"
let ppSignExtend = "signExtend"
let ppTruncate = "truncate"
let ppAdd = "+"
let ppSub = "-"
let ppMul = "*"
let ppBand = "&"
let ppBor = "|"
let ppBxor = "^"
let ppSll = "<<"
let ppSrl = ">>"
let ppSra = ">>" (* TODO: distinguish *)
let ppLt = "<"
let ppVUpdate = "update"

let ppDot = "."
let ppComma = ","
let ppSep = ";"
let ppColon = ":"
let ppTypeCast = "'"
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
let ppAction = "Action"
let ppModule = "module"
let ppEndModule = "endmodule"
let ppInterface = "interface"
let ppEndInterface = "endinterface"
let ppReg = "Reg#"
let ppAssign = "<-"
let ppMkReg = "mkReg"
let ppDefaultValue = "unpack(0)"
let ppBool = "Bool"
let ppVoid = "void"
let ppBit = "Bit#"
let ppVector = "Vector#"
let ppTypeDef = "typedef"
let ppDerivations = "deriving(Eq, Bits)"
let ppStruct = "struct"
let ppStructNamePrefix = "Struct"
let ppModuleNamePrefix = "Module"
let ppVec = "vec"
let ppFunction = "function"

let ppNoRules = "// No rules in this module"
let ppNoMeths = "// No methods in this module"

(* Global references for generating structs *)
let structIdx : int ref = ref 0
let getStructName (_: unit) = (structIdx := !structIdx + 1);
                              ppStructNamePrefix ^ string_of_int !structIdx

module StringMap = Map.Make (String)
let glbStructs : ((kind attribute list) StringMap.t) ref = ref StringMap.empty

let initMem : constT option ref = ref None
let getInitMem (_: unit) =
  match !initMem with
  | Some im -> im
  | None -> raise (Should_not_happen "Initial memory not provided")

let setInitMem (c: constT) = initMem := Some c
let resetInitMem (_: unit) = initMem := None

let initRfs : constT list option ref = ref None
let getInitRf (i: int) =
  match !initRfs with
  | Some rfs ->
     (try
        (List.nth rfs i)
      with _ -> raise (Should_not_happen "Initial rf not provided"))
  | None -> raise (Should_not_happen "Initial rf not provided")

let setInitRfs (c: constT list) = initRfs := Some c
let resetInitRfs (_: unit) = initRfs := None

let resetGlbStructs (_: unit) = glbStructs := StringMap.empty
let findGlbStructName (k: kind attribute list) =
  StringMap.fold (fun s k' cs -> if (k = k') then s else cs) !glbStructs ""
let addGlbStruct (k: kind attribute list) =
  let name = findGlbStructName k in
  if name = "" then
    let newName = getStructName () in
    (glbStructs := StringMap.add newName k !glbStructs; newName)
  else ((); name)

(* Global references end *)

(* Simple analyses: better to generate a new file Analysis.ml *)
let rec getCallsBA (al: bAction list) =
  match al with
  | [] -> []
  | BMCall (bind, meth, msig, e) :: tl ->
     (bstring_of_charlist meth, msig) :: (getCallsBA tl)
  | BIfElse (_, _, _, ta, fa) :: tl ->
     List.append (List.append (getCallsBA ta) (getCallsBA fa)) (getCallsBA tl)
  | _ :: tl -> getCallsBA tl

let rec getCallsBR (rl: bRule list) =
  match rl with
  | [] -> []
  | { attrName = _; attrType = rb } :: tl ->
     List.append (getCallsBA rb) (getCallsBR tl)

let rec getCallsBM (ml: bMethod list) =
  match ml with
  | [] -> []
  | { attrName = _; attrType = (_, mb) } :: tl ->
     List.append (getCallsBA mb) (getCallsBM tl)

let getCallsB (bm: bModule) =
  match bm with
  | { bregs = _; brules = rl; bdms = ml } ->
     let calls = List.append (getCallsBR rl) (getCallsBM ml) in
     List.fold_left (fun acc e -> if List.mem e acc then acc else e :: acc) [] calls

let getDefsB (bm: bModule) =
  match bm with
  | { bregs = _; brules = _; bdms = ml } ->
     List.map (fun bm -> match bm with
                         | { attrName = mn; attrType = (msig, _) } ->
                            (bstring_of_charlist mn, msig)) ml

type bModuleDC = bModule * (string * signatureT) list * (string * signatureT) list

let toBModuleDC (bm: bModule) = (bm, getDefsB bm, getCallsB bm)
let toBModuleDCL (bml: bModule list) = List.map (fun bm -> toBModuleDC bm) bml

let rec vectorToList (vec: 'a t0) =
  match vec with
  | Nil -> []
  | Cons (e, _, v) -> e :: (vectorToList v)

let rec collectStrK (k: kind) =
  match k with
  | Vector (k', _) -> collectStrK k'
  | Struct (_, sv) ->
     let sl = vectorToList sv in
     let _ = addGlbStruct sl in collectStrKL sl
  | _ -> ()
and collectStrKL (kl: kind attribute list) =
  match kl with
  | [] -> ()
  | { attrName = _; attrType = k } :: kl' ->
     collectStrK k; collectStrKL kl'

let rec collectStrC (c: constT) =
  match c with
  | ConstVector (_, _, v) -> collectStrVec v
  | ConstStruct (_, kv, _) ->
     let kl = vectorToList kv in
     let _ = addGlbStruct kl in collectStrKL kl
  | _ -> ()
and collectStrVec (v: constT vec) =
  match v with
  | Vec0 c -> collectStrC c
  | VecNext (_, v1, v2) -> collectStrVec v1; collectStrVec v2

let rec collectStrE (e: bExpr) =
  match e with
  | BConst (k, _) -> collectStrK k
  | BUniBool (_, se) -> collectStrE se
  | BBinBool (_, se1, se2) -> collectStrE se1; collectStrE se2
  | BUniBit (_, _, _, se) -> collectStrE se
  | BBinBit (_, _, _, _, se1, se2) -> collectStrE se1; collectStrE se2
  | BBinBitBool (_, _, _, se1, se2) -> collectStrE se1; collectStrE se2
  | BITE (ce, te, fe) -> collectStrE ce; collectStrE te; collectStrE fe
  | BEq (se1, se2) -> collectStrE se1; collectStrE se2
  | BReadIndex (ie, ve) -> collectStrE ie; collectStrE ve
  | BReadField (fd, se) -> collectStrE se
  | BBuildVector (_, v) -> collectStrV v
  | BBuildStruct (_, kv, _) ->
     let kl = vectorToList kv in
     let _ = addGlbStruct kl in collectStrKL kl
  | BUpdateVector (ve, ie, vale) -> collectStrE ve; collectStrE ie; collectStrE vale
  | _ -> ()
and collectStrV (v: bExpr vec) =
  match v with
  | Vec0 e -> collectStrE e
  | VecNext (_, v1, v2) -> collectStrV v1; collectStrV v2

let rec collectStrAL (al: bAction list) =
  match al with
  | [] -> ()
  | a :: al' -> collectStrA a; collectStrAL al'
and collectStrA (a: bAction) =
  match a with
  | BMCall (_, _, msig, _) -> collectStrK (arg msig); collectStrK (ret msig)
  | BLet (_, ok, e) ->
     (match ok with
      | Some k -> collectStrK k
      | _ -> ()); collectStrE e
  | BWriteReg (_, e) -> collectStrE e
  | BIfElse (ce, _, _, ta, fa) -> collectStrE ce; collectStrAL ta; collectStrAL fa
  | BAssert e -> collectStrE e
  | BReturn e -> collectStrE e

let rec collectStrBR (rl: bRule list) =
  match rl with
  | [] -> ()
  | { attrName = _; attrType = rb } :: tl ->
     collectStrAL rb; collectStrBR tl

let rec collectStrBM (ml: bMethod list) =
  match ml with
  | [] -> ()
  | { attrName = _; attrType = (msig, mb) } :: tl ->
     collectStrK (arg msig); collectStrK (ret msig);
     collectStrAL mb; collectStrBM tl

let collectStrB (bm: bModule) =
  match bm with
  | { bregs = _; brules = rl; bdms = ml } ->
     collectStrBR rl; collectStrBM ml

(* Simple analyses end *)

let rec ppKind (k: kind) =
  match k with
  | Bool -> ppBool
  | Bit w ->
     if w = 0 then ppVoid
     else ppBit ^ ppRBracketL ^ string_of_int w ^ ppRBracketR
  | Vector (k', w) -> ppVector ^ ppRBracketL
                      ^ string_of_int (int_of_float (float 2 ** float w))
                      ^ ppComma ^ ppDelim ^ ppKind k' ^ ppRBracketR
  | Struct (_, sv) -> let sl = vectorToList sv in addGlbStruct sl

let rec ppAttrKinds (ks: kind attribute list) =
  match ks with
  | [] -> ""
  | { attrName = kn; attrType = k } :: ks' ->
     ppKind k ^ ppDelim ^ (bstring_of_charlist kn) ^ ppSep ^ ppDelim
     ^ ppAttrKinds ks'

let rec ppWord (w: word) =
  match w with
  | WO -> ""
  | WS (false, _, w') -> ppWord w' ^ "0"
  | WS (true, _, w') -> ppWord w' ^ "1"

let rec wordToInt (w: word) =
  match w with
  | WO -> 0
  | WS (false, _, w') -> 2 * (wordToInt w')
  | WS (true, _, w') -> 2 * (wordToInt w') + 1

let rec ppConst (c: constT) =
  match c with
  | ConstBool true -> "True"
  | ConstBool false -> "False"
  | ConstBit (sz, w) -> string_of_int sz ^ ppHexa ^ Printf.sprintf "%x" (wordToInt w)
  | ConstVector (_, _, v) ->
     (* To remove the last comma + delim (", ") *)
     let ppv = ppConstVec v in
     ppVec ^ ppRBracketL ^ (String.sub ppv 0 (String.length ppv - 2)) ^ ppRBracketR
  | ConstStruct (_, kv, st) ->
     let kl = vectorToList kv in
     addGlbStruct kl ^ ppDelim ^ ppCBracketL ^ ppConstStruct st ^ ppCBracketR
and ppConstVec (v: constT vec) =
  match v with
  | Vec0 c -> ppConst c ^ ppComma ^ ppDelim
  | VecNext (_, v1, v2) -> ppConstVec v1 ^ ppConstVec v2
and ppConstStruct (stl: (kind attribute, constT) ilist) =
  match stl with
  | Inil -> ""
  | Icons ({ attrName = kn; attrType = _ }, _, _, c, Inil) ->
     bstring_of_charlist kn ^ ppColon ^ ppDelim ^ ppConst c
  | Icons ({ attrName = kn; attrType = _ }, _, _, c, stl') ->
     bstring_of_charlist kn ^ ppColon ^ ppDelim ^ ppConst c
     ^ ppComma ^ ppDelim ^ ppConstStruct stl'

let rec ppBExpr (e: bExpr) =
  match e with
  | BVar v -> ps (string_of_de_brujin_index v)
  | BConst (k, c) -> ps ppRBracketL; ps (ppKind k); ps ppRBracketR; ps ppTypeCast;
                     ps ppRBracketL; ps (ppConst c); ps ppRBracketR
  | BUniBool (Neg, se) -> ps ppNeg; print_space (); ps ppRBracketL; ppBExpr se; ps ppRBracketR
  | BBinBool (And, se1, se2) -> ps ppRBracketL; ppBExpr se1; ps ppRBracketR; print_space ();
                                ps ppAnd; print_space ();
                                ps ppRBracketL; ppBExpr se2; ps ppRBracketR
  | BBinBool (Or, se1, se2) -> ps ppRBracketL; ppBExpr se1; ps ppRBracketR; print_space ();
                               ps ppOr; print_space ();
                               ps ppRBracketL; ppBExpr se2; ps ppRBracketR
  | BUniBit (_, _, Inv _, se) -> ps ppInv; ps ppRBracketL; ppBExpr se; ps ppRBracketR
  | BUniBit (_, _, ConstExtract (n1, n2, _), se) ->
     ps ppRBracketL; ppBExpr se; ps ppRBracketR;
     ps ppBracketL; ps (string_of_int (n1 + n2 - 1)); ps ppColon;
     ps (string_of_int n1); ps ppBracketR
  | BUniBit (_, _, Trunc (n1, _), se) ->
     ps ppRBracketL; ppBExpr se; ps ppRBracketR;
     ps ppBracketL; ps (string_of_int (n1 - 1)); ps ppColon; ps "0"; ps ppBracketR
  | BUniBit (fn, tn, ZeroExtendTrunc _, se) ->
     (if (fn >= tn) then ps ppTruncate else ps ppZeroExtend);
     ps ppRBracketL; ppBExpr se; ps ppRBracketR
  | BUniBit (fn, tn, SignExtendTrunc _, se) ->
     (if (fn >= tn) then ps ppTruncate else ps ppSignExtend);
     ps ppRBracketL; ppBExpr se; ps ppRBracketR
  | BUniBit (_, _, TruncLsb (n1, n2), se) -> 
     ps ppRBracketL; ppBExpr se; ps ppRBracketR;
     ps ppBracketL; ps (string_of_int (n1 + n2 - 1)); ps ppColon;
     ps (string_of_int n1); ps ppBracketR
  | BBinBit (_, _, _, Add _, se1, se2) ->
     ps ppRBracketL; ppBExpr se1; ps ppRBracketR; print_space ();
     ps ppAdd; print_space (); ps ppRBracketL; ppBExpr se2; ps ppRBracketR
  | BBinBit (_, _, _, Sub _, se1, se2) ->
     ps ppRBracketL; ppBExpr se1; ps ppRBracketR; print_space ();
     ps ppSub; print_space (); ps ppRBracketL; ppBExpr se2; ps ppRBracketR
  | BBinBit (_, _, _, Mul _, se1, se2) ->
     ps ppRBracketL; ppBExpr se1; ps ppRBracketR; print_space ();
     ps ppMul; print_space (); ps ppRBracketL; ppBExpr se2; ps ppRBracketR
  | BBinBit (_, _, _, Band _, se1, se2) ->
     ps ppRBracketL; ppBExpr se1; ps ppRBracketR; print_space ();
     ps ppBand; print_space (); ps ppRBracketL; ppBExpr se2; ps ppRBracketR
  | BBinBit (_, _, _, Bor _, se1, se2) ->
     ps ppRBracketL; ppBExpr se1; ps ppRBracketR; print_space ();
     ps ppBor; print_space (); ps ppRBracketL; ppBExpr se2; ps ppRBracketR
  | BBinBit (_, _, _, Bxor _, se1, se2) ->
     ps ppRBracketL; ppBExpr se1; ps ppRBracketR; print_space ();
     ps ppBxor; print_space (); ps ppRBracketL; ppBExpr se2; ps ppRBracketR
  | BBinBit (_, _, _, Sll _, se1, se2) ->
     ps ppRBracketL; ppBExpr se1; ps ppRBracketR; print_space ();
     ps ppSll; print_space (); ps ppRBracketL; ppBExpr se2; ps ppRBracketR
  | BBinBit (_, _, _, Srl _, se1, se2) ->
     ps ppRBracketL; ppBExpr se1; ps ppRBracketR; print_space ();
     ps ppSrl; print_space (); ps ppRBracketL; ppBExpr se2; ps ppRBracketR
  | BBinBit (_, _, _, Sra _, se1, se2) ->
     ps ppRBracketL; ppBExpr se1; ps ppRBracketR; print_space ();
     ps ppSra; print_space (); ps ppRBracketL; ppBExpr se2; ps ppRBracketR
  | BBinBit (_, _, _, Concat (_, _), se1, se2) ->
     ps ppCBracketL; ps ppRBracketL; ppBExpr se1; ps ppRBracketR;
     ps ppComma; ps ppRBracketL; ppBExpr se2; ps ppRBracketR; ps ppCBracketR
  | BBinBitBool (_, _, Lt _, se1, se2) ->
     ps ppRBracketL; ppBExpr se1; ps ppRBracketR; print_space ();
     ps ppLt; print_space (); ps ppRBracketL; ppBExpr se2; ps ppRBracketR
  | BITE (ce, te, fe) ->
     ps ppRBracketL;
     ppBExpr ce; print_space (); ps ppQ; print_space ();
     ps ppRBracketL; ppBExpr te; ps ppRBracketR; print_space ();
     ps ppColon; print_space ();
     ps ppRBracketL; ppBExpr fe; ps ppRBracketR;
     ps ppRBracketR
  | BEq (se1, se2) -> ppBExpr se1; print_space (); ps ppEq; print_space (); ppBExpr se2
  | BReadIndex (ie, ve) ->
     ps ppRBracketL; ppBExpr ve; ps ppRBracketR; ps ppBracketL; ppBExpr ie; ps ppBracketR
  | BReadField (fd, se) ->
     ps ppRBracketL; ppBExpr se; ps ppRBracketR; ps ppDot; ps (bstring_of_charlist fd)
  | BBuildVector (_, v) ->
     ps ppVec; ps ppRBracketL; ppBExprVec v true; ps ppRBracketR
  | BBuildStruct (_, kv, st) ->
     let kl = vectorToList kv in
     ps (addGlbStruct kl); print_space (); ps ppCBracketL; ppBExprStruct st; ps ppCBracketR
  | BUpdateVector (ve, ie, vale) -> 
     ps ppVUpdate; print_space (); ps ppRBracketL; ppBExpr ve; ps ppComma; print_space ();
     ppBExpr ie; ps ppComma; print_space (); ppBExpr vale; ps ppRBracketR
  | BReadReg r -> ps (bstring_of_charlist r)
and ppBExprVec (v: bExpr vec) (tail: bool) =
  match v with
  | Vec0 e -> ppBExpr e; if tail then () else (ps ppComma; print_space ())
  | VecNext (_, v1, v2) -> ppBExprVec v1 false; ppBExprVec v2 (tail && true)
and ppBExprStruct (stl: bExpr attribute list) =
  match stl with
  | [] -> ()
  | { attrName = kn; attrType = e } :: [] ->
     ps (bstring_of_charlist kn); print_space (); ps ppColon; print_space (); ppBExpr e
  | { attrName = kn; attrType = e } :: stl' ->
     ps (bstring_of_charlist kn); print_space (); ps ppColon; print_space (); ppBExpr e;
     ps ppComma; print_space (); ppBExprStruct stl'

let rec ppBAction (ife: int option) (a: bAction) =
  match a with
  | BMCall (bind, meth, msig, e) ->
     ps ppLet; print_space (); ps (string_of_de_brujin_index bind); print_space ();
     (* (if ret msig = Bit 0 then ps ppBind else ps ppAssign); *) ps ppAssign;
     print_space ();
     ps (bstring_of_charlist meth);
     ps ppRBracketL;
     (if arg msig = Bit 0 then () else ppBExpr e);
     ps ppRBracketR; ps ppSep
  | BLet (bind, ok, e) ->
     (match ok with
      | Some k -> ps (ppKind k)
      | None -> ps ppLet);
     print_space (); ps (string_of_de_brujin_index bind); print_space ();
     ps ppBind; print_space ();
     ps ppRBracketL; ppBExpr e; ps ppRBracketR; ps ppSep
  | BWriteReg (reg, e) ->
     ps (bstring_of_charlist reg); print_space ();
     ps ppWriteReg; print_space (); ppBExpr e; ps ppSep
  | BIfElse (ce, bind, bk, ta, fa) ->
     (* let-bind for the branch return *)
     (if (bk = Bit 0) then ()
      else
        (ps ppLet; print_space (); ps (string_of_de_brujin_index bind); print_space ();
         ps ppBind; print_space (); ps ppQ; ps ppSep; print_cut (); force_newline ()));
     ps ppIf; print_space (); ps ppRBracketL; ppBExpr ce; ps ppRBracketR;
     print_space (); ps ppBegin;
     print_break 0 4; (* force_newline (); *) open_hovbox 0;
     ppBActions (bk = Bit 0) (Some bind) ta;
     close_box (); print_break 0 (-4); force_newline ();
     ps ppEnd; print_space (); ps ppElse; print_space (); ps ppBegin;
     print_break 0 4; (* force_newline (); *) open_hovbox 0;
     ppBActions (bk = Bit 0) (Some bind) fa;
     close_box (); print_break 0 (-4); force_newline ();
     ps ppEnd
  | BAssert e ->
     ps ppWhen; print_space (); ps ppRBracketL;
     ppBExpr e; ps ppComma; print_space ();
     ps ppNoAction; ps ppRBracketR; ps ppSep
  | BReturn e ->
     (match ife with
      | Some bind ->
         (ps (string_of_de_brujin_index bind); print_space ();
          ps ppBind; print_space (); ppBExpr e; ps ppSep)
      | _ -> (ps ppReturn; print_space (); ppBExpr e; ps ppSep))
and ppBActions (noret: bool) (ife: int option) (aa: bAction list) =
  match aa with
  | [] -> ()
  | a' :: [] -> if noret then () else ppBAction ife a'
  | a' :: aa' -> ppBAction ife a'; print_cut (); force_newline (); ppBActions noret ife aa'

let ppBRule (r: bRule) =
  match r with
  | { attrName = rn; attrType = rb } ->
     open_hovbox 0;
     ps ppRule; print_space (); ps (bstring_of_charlist rn); ps ppSep;
     print_break 0 4; open_hovbox 0;
     ppBActions true None rb;
     close_box (); print_break 0 (-4); force_newline ();
     ps ppEndRule;
     close_box ()

let rec ppBRules (rl: bRule list) =
  match rl with
  | [] -> ()
  | r :: rl' -> ppBRule r; print_cut (); force_newline (); ppBRules rl'
     
let ppBMethod (d: bMethod) =
  match d with
  | { attrName = dn; attrType = ({ arg = asig; ret = rsig}, db) } ->
     open_hovbox 0;
     ps ppMethod; print_space ();
     (if rsig = Bit 0 then
        ps ppAction
      else
        (ps ppActionValue; ps ppRBracketL; ps (ppKind rsig); ps ppRBracketR));
     print_space ();
     ps (bstring_of_charlist dn); print_space ();
     ps ppRBracketL;
     (if asig = Bit 0 then ()
      else (ps (ppKind asig); print_space ();
            ps (string_of_de_brujin_index 0) (* method argument is always x_0 by convention *)
     ));
     ps ppRBracketR; ps ppSep;
     print_break 0 4; open_hovbox 0;
     ppBActions (rsig = Bit 0) None db;
     close_box (); print_break 0 (-4); force_newline ();
     ps ppEndMethod;
     close_box ()

let rec ppBMethods (dl: bMethod list) =
  match dl with
  | [] -> ()
  | d :: dl' -> ppBMethod d; print_cut (); force_newline (); ppBMethods dl'

let ppBInterface (d: bMethod) =
  match d with
  | { attrName = dn; attrType = ({ arg = asig; ret = rsig }, _) } ->
     open_hovbox 0;
     ps ppMethod; print_space ();
     (if rsig = Bit 0 then
        ps ppAction
      else
        (ps ppActionValue; ps ppRBracketL; ps (ppKind rsig); ps ppRBracketR));
     print_space ();
     ps (bstring_of_charlist dn); print_space ();
     ps ppRBracketL;
     (if asig = Bit 0 then ()
      else (ps (ppKind asig); print_space ();
            ps (string_of_de_brujin_index 0) (* method argument is always x_0 by convention *)
     ));
     ps ppRBracketR; ps ppSep;
     close_box ()

let rec ppBInterfaces (dl: bMethod list) =
  match dl with
  | [] -> ()
  | d :: dl' -> ppBInterface d; print_cut(); ppBInterfaces dl'

let replaceInit (tg: string) (default: string) =
  if String.sub tg 0 3 = "pgm" then
    ppConst (getInitMem ())
  else if String.sub tg 0 2 = "rf" then
    ppConst (getInitRf (String.length tg - 4))
  else
    default

let ppRegInit (r: regInitT) =
  match r with
  | { attrName = rn; attrType = riv } ->
     (match riv with
      | RegInitCustom (ExistT (_, SyntaxConst (k, c))) ->
         open_hbox ();
         ps ppReg; ps ppRBracketL; ps (ppKind k); ps ppRBracketR; print_space ();
         ps (bstring_of_charlist rn); print_space ();
         ps ppAssign; print_space ();
         ps ppMkReg; ps ppRBracketL;
         ps (replaceInit (bstring_of_charlist rn) (ppConst c));
         ps ppRBracketR; ps ppSep;
         close_box ()
      | RegInitDefault (SyntaxKind k) ->
         open_hbox ();
         ps ppReg; ps ppRBracketL; ps (ppKind k); ps ppRBracketR; print_space ();
         ps (bstring_of_charlist rn); print_space ();
         ps ppAssign; print_space ();
         ps ppMkReg; ps ppRBracketL;
         ps (replaceInit (bstring_of_charlist rn) ppDefaultValue);
         ps ppRBracketR; ps ppSep;
         close_box ()
      | _ -> raise (Should_not_happen
                      ("NativeKind register detected; name: " ^ (bstring_of_charlist rn))))

let rec ppRegInits (rl: regInitT list) =
  match rl with
  | [] -> ()
  | r :: rl' ->
     ppRegInit r; print_cut (); ppRegInits rl'

let ppImports (_: unit) =
  ps "import Vector::*;"; print_cut(); force_newline ();
  ps "import BuildVector::*;"; print_cut(); force_newline ()

(* NOTE: especially for struct declarations, print each with a single line *)
let ppGlbStructs (_: unit) =
  open_hbox ();
  (StringMap.iter (fun nm kl ->
       ps ppTypeDef; print_space (); ps ppStruct; print_space ();
       ps ppCBracketL; print_space (); ps (ppAttrKinds kl); print_space (); ps ppCBracketR;
       print_space (); ps nm; print_space (); ps ppDerivations; ps ppSep;
       print_cut (); force_newline ()) !glbStructs);
  print_cut (); force_newline ();
  close_box ()

let ppBModuleInterface (n: string) (m: bModule) =
  match m with
  | { bregs = br; brules = brl; bdms = bd } ->
     ps ppInterface; print_space (); ps n; ps ppSep;
     print_break 1 4; open_hovbox 0;
     ppBInterfaces bd;
     close_box (); print_break 0 (-4); force_newline ();
     ps ppEndInterface;
     print_cut (); force_newline ();
     force_newline ()

let ppCallArg (cn: string) (csig: signatureT) =
  open_hbox ();
  ps ppFunction; print_space ();
  (if ret csig = Bit 0 then
     ps ppAction
   else
     (ps ppActionValue; ps ppRBracketL; ps (ppKind (ret csig)); ps ppRBracketR));
  print_space ();
  ps cn; ps ppRBracketL;
  (if arg csig = Bit 0 then
     ()
   else
     (ps (ppKind (arg csig)); print_space (); ps "_"));
  ps ppRBracketR;
  close_box ()

let rec ppCallArgs (cs: (string * signatureT) list) =
  match cs with
  | [] -> ()
  | (cn, csig) :: [] -> ppCallArg cn csig
  | (cn, csig) :: tl -> ppCallArg cn csig; ps ppComma; print_space (); ppCallArgs tl

let ppBModuleCallArgs (cargs: (string * signatureT) list) =
  match cargs with
  | [] -> ()
  | _ -> ps "#"; ps ppRBracketL; ppCallArgs cargs; ps ppRBracketR
                                         
let ppBModule (ifcn: string) (m: bModule) =
  match m with
  | { bregs = br; brules = brl; bdms = bd } ->
     open_hovbox 2;
     ps ppModule; print_space ();
     ps ("mk" ^ ifcn); ppBModuleCallArgs (getCallsB m); print_space ();
     ps ppRBracketL; ps ifcn; ps ppRBracketR; ps ppSep;
     close_box ();
     print_break 0 4; open_hovbox 0;
     ppRegInits br;
     print_cut (); force_newline ();
     (if (brl = []) then ps ppNoRules else ppBRules brl);
     print_cut (); force_newline ();
     (if (bd = []) then ps ppNoMeths else ppBMethods bd);
     close_box(); print_break 0 (-4); force_newline ();
     ps ppEndModule;
     print_cut (); force_newline ()

let ppBModuleFull (ifcn: string) (m: bModule) =
  ppBModuleInterface ifcn m;
  ppBModule ifcn m

let rec ppBModules (bml: bModule list) (idx: int) =
  match bml with
  | [] -> ()
  | bm :: bml' -> ppBModuleFull (ppModuleNamePrefix ^ string_of_int idx) bm;
                  force_newline ();
                  ppBModules bml' (succ idx)

let rec preAnalyses (bml: bModule list) =
  match bml with
  | [] -> ()
  | bm :: bml' -> collectStrB bm; preAnalyses bml'

let rec callsToInsts (dmap: int StringMap.t) (calls: (string * signatureT) list) =
  match calls with
  | [] -> []
  | (meth, _) :: calls' ->
     let cipair = try (StringMap.find meth dmap, meth)
                  with Not_found -> (-1, meth) in
     cipair :: (callsToInsts dmap calls')

let rec ppCallInsts (cis: (int * string) list) =
  match cis with
  | [] -> ()
  | (idx, meth) :: [] ->
     (if (idx >= 0) then
        (ps ("m" ^ string_of_int idx); ps ppDot)
      else ()); ps meth
  | (idx, meth) :: cis' ->
     (if (idx >= 0) then
        (ps ("m" ^ string_of_int idx); ps ppDot)
      else ()); ps meth; ps ppComma; print_space (); ppCallInsts cis'

let ppModuleInst (dmap: int StringMap.t) (bmdc: bModuleDC) (idx: int) =
  ps (ppModuleNamePrefix ^ string_of_int idx); print_space ();
  ps ("m" ^ string_of_int idx); print_space (); ps ppAssign; print_space ();
  ps ("mk" ^ ppModuleNamePrefix ^ string_of_int idx); print_space ();
  ps ppRBracketL;
  ppCallInsts (callsToInsts dmap ((fun (_, _, c) -> c) bmdc));
  ps ppRBracketR; ps ppSep

let rec ppModulesInst (dmap: int StringMap.t) (bmdcl: bModuleDC list) (idx: int) =
  match bmdcl with
  | [] -> ()
  | bmdc :: bmdcl' -> ppModuleInst dmap bmdc idx; print_cut (); force_newline ();
                      ppModulesInst dmap bmdcl' (succ idx)

let rec makeDefMap (bmdcl: bModuleDC list) (idx: int) =
  match bmdcl with
  | [] -> StringMap.empty
  | (_, d, _) :: bmdcl' ->
     List.fold_left (fun dmap df -> StringMap.add (fst df) idx dmap)
                    (makeDefMap bmdcl' (succ idx)) d

let rec makeCallMap (bmdcl: bModuleDC list) (idx: int) =
  match bmdcl with
  | [] -> StringMap.empty
  | (_, _, c) :: bmdcl' ->
     List.fold_left (fun dmap df ->
         if StringMap.mem (fst df) dmap
         then StringMap.add (fst df) (idx :: StringMap.find (fst df) dmap) dmap
         else StringMap.add (fst df) [idx] dmap)
                    (makeCallMap bmdcl' (succ idx)) c

let makeModuleOrderPairs (defs: int StringMap.t) (calls: (int list) StringMap.t) =
  StringMap.fold (fun k di ps ->
      if StringMap.mem k calls then
        let cis = StringMap.find k calls in
        List.append (List.map
                       (fun ci -> if di = ci
                                  then raise (Should_not_happen "Call-cycle in a module")
                                  else (di, ci)) cis) ps
      else ps) defs []

let rec makeModuleOrder (mids: int list) (pairs: (int * int) list) =
  match mids with
  | [] -> []
  | _ ->
     let no_incomings = List.filter (fun i -> not (List.mem i (List.map snd pairs))) mids in
     let incomings = List.filter (fun i -> List.mem i (List.map snd pairs)) mids in
     List.append no_incomings
                 (makeModuleOrder incomings
                                  (List.filter (fun ii -> not (List.mem (fst ii) no_incomings))
                                               pairs))

let ppTopModule (bmdcl: bModuleDC list) (idx: int)
                (extCallsAll: (string * signatureT) list)  =
  open_hovbox 2;
  ps ppModule; print_space ();
  ps "mkTop"; ppBModuleCallArgs extCallsAll; print_space ();
  ps ppRBracketL; ps "Empty"; ps ppRBracketR; ps ppSep;
  close_box ();
  print_break 0 4; open_hovbox 0;
  ppModulesInst (makeDefMap bmdcl idx) bmdcl idx;
  close_box(); print_break 0 (-4);
  ps ppEndModule

let rec makeMids (idxInit: int) (numMods: int) =
  if numMods = 0 then []
  else idxInit :: (makeMids (succ idxInit) (numMods - 1))

let rec permute (ls: 'a list) (ps: int list) =
  match ps with
  | [] -> []
  | p :: ps' -> (List.nth ls p) :: (permute ls ps')

(* NOTE: idxInit should be larger than 0 *)
let ppBModulesFull (bml: bModule list) =
  let idxInit = 1 in
  let bmdcl = toBModuleDCL bml in
  let defsAll = List.concat (List.map (fun (_, d, _) -> d) bmdcl) in
  let callsAll = List.concat (List.map (fun (_, _, c) -> c) bmdcl) in
  let extCallsAll = List.filter (fun meth -> not (List.mem meth defsAll)) callsAll in
  let moduleOrder =
    makeModuleOrder (makeMids 0 (List.length bmdcl))
                    (makeModuleOrderPairs (makeDefMap bmdcl 0)
                                          (makeCallMap bmdcl 0)) in
  ppImports ();
  preAnalyses bml;
  ppGlbStructs ();
  ppBModules (permute bml moduleOrder) idxInit;
  ppTopModule (permute bmdcl moduleOrder) idxInit extCallsAll;
  resetGlbStructs ();
  print_newline ()

let ppBModulesFullInitMemRfs (bml: bModule list) (initMem: constT) (initRfs: constT list) =
  setInitMem initMem;
  setInitRfs initRfs;
  ppBModulesFull bml;
  resetInitMem ();
  resetInitRfs ()

