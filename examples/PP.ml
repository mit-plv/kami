#use "Extracted.ml"

(* Borrowed from Compcert *)
let camlstring_of_coqstring (s: char list) =
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
    | [] -> r
    | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)

let ppDelim = " "
let ppEndLine = "\n"
let ppFail = "(FAIL)"

(* TODO *)
let rec ppBExpr (e: bExpr) = raise Not_found

let ppSep = ";"
let ppParenL = "("
let ppParenR = ")"
let ppBind = "="

let ppLet = "let"
let ppWriteReg = "<="
let ppIf = "if"
let ppElse = "else"
let ppBegin = "begin"
let ppEnd = "end"

let ppRule = "rule"
let ppEndRule = "endrule"
let ppMethod = "method"
let ppEndMethod = "endmethod"
let ppActionValue = "ActionValue#"
let ppModule = "module"

let rec ppBAction (a: bAction) =
  (match a with
   | BMCall (bind, meth, e) ->
      ppLet ^ ppDelim ^ (camlstring_of_coqstring bind) ^ ppDelim ^ ppBind ^ ppDelim
      ^ (camlstring_of_coqstring meth) ^ ppParenL ^ (ppBExpr e) ^ ppParenR
   | BLet (bind, e) ->
      ppLet ^ ppDelim ^ (camlstring_of_coqstring bind) ^ ppDelim ^ ppBind ^ ppDelim
      ^ ppParenL ^ (ppBExpr e) ^ ppParenR
   | BWriteReg (reg, e) ->
      (camlstring_of_coqstring reg) ^ ppDelim ^ ppWriteReg ^ ppDelim ^ (ppBExpr e)
   | BIfElse (ce, ta, fa) ->
      ppIf ^ ppDelim ^ (ppBExpr ce) ^ ppDelim ^ ppBegin ^ ppEndLine
      ^ ppBActions ta ^ ppEnd ^ ppDelim ^ ppElse ^ ppBegin ^ ppEndLine
      ^ ppBActions fa ^ ppEnd
   | _ -> "") ^ ppSep
and ppBActions (aa: bAction list) =
  match aa with
  | [] -> ""
  | a' :: aa' -> (ppBAction a') ^ ppEndLine ^ (ppBActions aa')

let ppBRule (r: bRule) =
  match r with
  | { attrName = rn; attrType = rb } ->
      ppRule ^ ppDelim ^ (camlstring_of_coqstring rn) ^ ppSep ^ ppEndLine
      ^ ppBActions rb ^ ppEndRule

(* TODO *)
let ppKind (k: kind) = raise Not_found

(* TODO: implement *)
let ppBMethod (d: bMethod) =
  match d with
  | { attrName = dn; attrType = ({ arg = asig; ret = rsig}, db) } ->
      ppMethod ^ ppDelim ^ ppActionValue ^ (camlstring_of_coqstring dn) ^ ppDelim
      ^ ppParenL ^ (ppKind asig) ^ ppParenR ^ ppBActions db ^ ppEndMethod

(* TODO: implement *)
let ppBModule (n: string) (m: bModule) =
  match m with
  | { bregs = br; brules = brl; bdms = bd } ->
     ppModule ^ ppDelim ^ n ^ ppSep ^ ppEndLine
