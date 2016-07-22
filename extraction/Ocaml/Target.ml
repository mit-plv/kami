type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (x, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, p) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (x0, h) -> h

type 'a exc = 'a option

(** val value : 'a1 -> 'a1 option **)

let value x =
  Some x

(** val error : 'a1 option **)

let error =
  None

(** val plus : int -> int -> int **)

let rec plus = (+)

(** val mult : int -> int -> int **)

let rec mult = ( * )

(** val nth_error : 'a1 list -> int -> 'a1 exc **)

let rec nth_error l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    match l with
    | [] -> error
    | x :: l0 -> value x)
    (fun n0 ->
    match l with
    | [] -> error
    | a :: l0 -> nth_error l0 n0)
    n

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val div2 : int -> int **)

let rec div2 = fun n -> n/2

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

type ('a, 'b) ilist =
| Icons of 'a * 'a list * 'b * ('a, 'b) ilist
| Inil

(** val imap : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> ('a1, 'a2) ilist -> ('a1, 'a3) ilist **)

let rec imap f as0 = function
| Icons (a, as1, b, il') -> Icons (a, as1, (f a b), (imap f as1 il'))
| Inil -> Inil

type word =
| WO
| WS of bool * int * word

(** val wordToNat : int -> word -> int **)

let rec wordToNat sz = function
| WO -> 0
| WS (b, n, w') ->
  if b
  then Pervasives.succ (mult (wordToNat n w') (Pervasives.succ (Pervasives.succ 0)))
  else mult (wordToNat n w') (Pervasives.succ (Pervasives.succ 0))

(** val mod2 : int -> bool **)

let rec mod2 n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    false)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      true)
      (fun n' ->
      mod2 n')
      n0)
    n

(** val natToWord : int -> int -> word **)

let rec natToWord sz n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    WO)
    (fun sz' -> WS ((mod2 n), sz',
    (natToWord sz' (div2 n))))
    sz

(** val wones : int -> word **)

let rec wones sz =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    WO)
    (fun sz' -> WS (true, sz',
    (wones sz')))
    sz

type 'a indexBound = { ibound : int }

(** val ibound : 'a1 -> 'a1 list -> 'a1 indexBound -> int **)

let ibound _ _ x = x.ibound

(** val indexBound_head : 'a1 -> 'a1 list -> 'a1 indexBound **)

let indexBound_head a bound =
  { ibound = 0 }

(** val indexBound_tail : 'a1 -> 'a1 -> 'a1 list -> 'a1 indexBound -> 'a1 indexBound **)

let indexBound_tail a a' bound sB' =
  { ibound = (Pervasives.succ sB'.ibound) }

type 'a boundedIndex = { bindex : 'a; indexb : 'a indexBound }

(** val bindex : 'a1 list -> 'a1 boundedIndex -> 'a1 **)

let bindex _ x = x.bindex

(** val indexb : 'a1 list -> 'a1 boundedIndex -> 'a1 indexBound **)

let indexb _ x = x.indexb

(** val none_neq_Some : 'a1 -> 'a2 **)

let none_neq_Some a =
  assert false (* absurd case *)

(** val nth_Bounded' : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a1 **)

let nth_Bounded' projAC c = function
| Some a -> a
| None -> none_neq_Some c

(** val nth_Bounded : ('a1 -> 'a2) -> 'a1 list -> 'a2 boundedIndex -> 'a1 **)

let nth_Bounded projAC bound idx1 =
  nth_Bounded' projAC idx1.bindex (nth_error bound idx1.indexb.ibound)

type 'kind attribute = { attrName : char list; attrType : 'kind }

(** val attrName : 'a1 attribute -> char list **)

let attrName x = x.attrName

(** val attrType : 'a1 attribute -> 'a1 **)

let attrType x = x.attrType

type 'kind boundedIndexFull = char list boundedIndex

(** val getAttr : 'a1 attribute list -> 'a1 boundedIndexFull -> 'a1 attribute **)

let getAttr attrs idx1 =
  nth_Bounded attrName attrs idx1

(** val getAttrType : 'a1 attribute list -> 'a1 boundedIndexFull -> 'a1 **)

let getAttrType attrs idx1 =
  (getAttr attrs idx1).attrType

(** val string_of_nat : int -> char list **)

let rec string_of_nat n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    'a'::[])
    (fun n' ->
    append ('a'::[]) (string_of_nat n'))
    n

(** val indexSymbol : char list **)

let indexSymbol =
  '$'::[]

(** val prefixSymbol : char list **)

let prefixSymbol =
  '.'::[]

(** val addIndexToStr : ('a1 -> char list) -> 'a1 -> char list -> char list **)

let addIndexToStr strA i s =
  append s (append indexSymbol (strA i))

(** val withPrefix : char list -> char list -> char list **)

let withPrefix pre str =
  append str (append prefixSymbol pre)

(** val getDefaultConstBit : int -> word **)

let rec getDefaultConstBit n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    WO)
    (fun m -> WS (false, m,
    (getDefaultConstBit m)))
    n

type 'a vec =
| Vec0 of 'a
| VecNext of int * 'a vec * 'a vec

(** val replicate : 'a1 -> int -> 'a1 vec **)

let rec replicate v n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Vec0
    v)
    (fun m -> VecNext (m, (replicate v m),
    (replicate v m)))
    n

(** val mapVec : ('a1 -> 'a2) -> int -> 'a1 vec -> 'a2 vec **)

let rec mapVec map0 n = function
| Vec0 e -> Vec0 (map0 e)
| VecNext (n', v1, v2) -> VecNext (n', (mapVec map0 n' v1), (mapVec map0 n' v2))

type kind =
| Bool
| Bit of int
| Vector of kind * int
| Struct of kind attribute list

type fullKind =
| SyntaxKind of kind
| NativeKind of __

type constT =
| ConstBool of bool
| ConstBit of int * word
| ConstVector of kind * int * constT vec
| ConstStruct of kind attribute list * (kind attribute, constT) ilist

type constFullT =
| SyntaxConst of kind * constT
| NativeConst of __ * __

(** val getDefaultConst : kind -> constT **)

let rec getDefaultConst = function
| Bool -> ConstBool false
| Bit n -> ConstBit (n, (getDefaultConstBit n))
| Vector (k0, n) -> ConstVector (k0, n, (replicate (getDefaultConst k0) n))
| Struct ls ->
  ConstStruct (ls,
    (let rec help = function
     | [] -> Inil
     | x :: xs -> Icons (x, xs, (getDefaultConst x.attrType), (help xs))
     in help ls))

type signatureT = { arg : kind; ret : kind }

(** val arg : signatureT -> kind **)

let arg x = x.arg

(** val ret : signatureT -> kind **)

let ret x = x.ret

type uniBoolOp =
| Neg

type binBoolOp =
| And
| Or

type uniBitOp =
| Inv of int
| ConstExtract of int * int * int
| Trunc of int * int
| ZeroExtendTrunc of int * int
| SignExtendTrunc of int * int
| TruncLsb of int * int

type binBitOp =
| Add of int
| Sub of int
| Concat of int * int

type binBitBoolOp =
| Lt of int

type 'ty fullType = __

type 'ty expr =
| Var of fullKind * 'ty fullType
| Const of kind * constT
| UniBool of uniBoolOp * 'ty expr
| BinBool of binBoolOp * 'ty expr * 'ty expr
| UniBit of int * int * uniBitOp * 'ty expr
| BinBit of int * int * int * binBitOp * 'ty expr * 'ty expr
| BinBitBool of int * int * binBitBoolOp * 'ty expr * 'ty expr
| ITE of fullKind * 'ty expr * 'ty expr * 'ty expr
| Eq of kind * 'ty expr * 'ty expr
| ReadIndex of int * kind * 'ty expr * 'ty expr
| ReadField of kind attribute list * kind boundedIndexFull * 'ty expr
| BuildVector of kind * int * 'ty expr vec
| BuildStruct of kind attribute list * (kind attribute, 'ty expr) ilist
| UpdateVector of int * kind * 'ty expr * 'ty expr * 'ty expr

type 'ty actionT =
| MCall of char list * signatureT * 'ty expr * ('ty -> 'ty actionT)
| Let_ of fullKind * 'ty expr * ('ty fullType -> 'ty actionT)
| ReadReg of char list * fullKind * ('ty fullType -> 'ty actionT)
| WriteReg of char list * fullKind * 'ty expr * 'ty actionT
| IfElse of 'ty expr * kind * 'ty actionT * 'ty actionT * ('ty -> 'ty actionT)
| Assert_ of 'ty expr * 'ty actionT
| Return of 'ty expr

type action = __ -> __ actionT

type methodT = __ -> __ -> __ actionT

type regInitT = (fullKind, constFullT) sigT attribute

type defMethT = (signatureT, methodT) sigT attribute

(** val void : kind **)

let void =
  Bit 0

type modules =
| Mod of regInitT list * action attribute list * defMethT list
| ConcatMod of modules * modules

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x :: xs -> app x (concat xs)

type nameRec = { nameVal : char list }

(** val nameVal : nameRec -> char list **)

let nameVal x = x.nameVal

type nameRecIdx = { isRep : bool; nameRec0 : nameRec }

(** val isRep : nameRecIdx -> bool **)

let isRep x = x.isRep

(** val nameRec0 : nameRecIdx -> nameRec **)

let nameRec0 x = x.nameRec0

(** val convNameRec : bool -> nameRec -> nameRecIdx **)

let convNameRec rep n =
  { isRep = rep; nameRec0 = n }

type 'ty genActionT =
| GMCall of nameRecIdx * signatureT * 'ty expr * ('ty -> 'ty genActionT)
| GIndex of ('ty -> 'ty genActionT)
| GLet_ of fullKind * 'ty expr * ('ty fullType -> 'ty genActionT)
| GReadReg of nameRecIdx * fullKind * ('ty fullType -> 'ty genActionT)
| GWriteReg of nameRecIdx * fullKind * 'ty expr * 'ty genActionT
| GIfElse of 'ty expr * kind * 'ty genActionT * 'ty genActionT * ('ty -> 'ty genActionT)
| GAssert_ of 'ty expr * 'ty genActionT
| GReturn of 'ty expr

(** val strFromName : ('a1 -> char list) -> 'a1 -> nameRecIdx -> char list **)

let strFromName strA i n =
  if n.isRep then addIndexToStr strA i n.nameRec0.nameVal else n.nameRec0.nameVal

(** val getGenAction :
    ('a1 -> char list) -> kind -> ('a1 -> constT) -> 'a1 -> kind -> 'a2 genActionT -> 'a2 actionT **)

let rec getGenAction strA genK getConstK i k = function
| GMCall (meth, s, e, c) ->
  MCall ((strFromName strA i meth), s, e, (fun v -> getGenAction strA genK getConstK i k (c v)))
| GIndex c ->
  Let_ ((SyntaxKind genK), (Const (genK, (getConstK i))), (fun v ->
    getGenAction strA genK getConstK i k (Obj.magic c v)))
| GLet_ (k', e, c) -> Let_ (k', e, (fun v -> getGenAction strA genK getConstK i k (c v)))
| GReadReg (r, k0, c) ->
  ReadReg ((strFromName strA i r), k0, (fun v -> getGenAction strA genK getConstK i k (c v)))
| GWriteReg (r, k0, e, c) ->
  WriteReg ((strFromName strA i r), k0, e, (getGenAction strA genK getConstK i k c))
| GIfElse (e, k0, aT, aF, c) ->
  IfElse (e, k0, (getGenAction strA genK getConstK i k0 aT),
    (getGenAction strA genK getConstK i k0 aF), (fun v ->
    getGenAction strA genK getConstK i k (c v)))
| GAssert_ (e, c) -> Assert_ (e, (getGenAction strA genK getConstK i k c))
| GReturn e -> Return e

type genAction = __ -> __ genActionT

type genMethodT = __ -> __ -> __ genActionT

(** val getActionFromGen :
    ('a1 -> char list) -> kind -> ('a1 -> constT) -> genAction -> 'a1 -> 'a2 actionT **)

let getActionFromGen strA genK getConstK gr i =
  getGenAction strA genK getConstK i void (Obj.magic gr __)

(** val getMethFromGen :
    ('a1 -> char list) -> kind -> ('a1 -> constT) -> (signatureT, genMethodT) sigT -> 'a1 ->
    (signatureT, __ -> __ -> __ actionT) sigT **)

let getMethFromGen strA genK getConstK gf i =
  ExistT ((projT1 gf), (fun _ argv ->
    getGenAction strA genK getConstK i (projT1 gf).ret (projT2 gf __ argv)))

type 'ty sinActionT =
| SMCall of nameRec * signatureT * 'ty expr * ('ty -> 'ty sinActionT)
| SLet_ of fullKind * 'ty expr * ('ty fullType -> 'ty sinActionT)
| SReadReg of nameRec * fullKind * ('ty fullType -> 'ty sinActionT)
| SWriteReg of nameRec * fullKind * 'ty expr * 'ty sinActionT
| SIfElse of 'ty expr * kind * 'ty sinActionT * 'ty sinActionT * ('ty -> 'ty sinActionT)
| SAssert_ of 'ty expr * 'ty sinActionT
| SReturn of 'ty expr

(** val convSinToGen : bool -> kind -> kind -> 'a1 sinActionT -> 'a1 genActionT **)

let rec convSinToGen rep genK k = function
| SMCall (name, sig0, ar, cont) ->
  GMCall ((convNameRec rep name), sig0, ar, (fun a0 -> convSinToGen rep genK k (cont a0)))
| SLet_ (lretT', ar, cont) -> GLet_ (lretT', ar, (fun a0 -> convSinToGen rep genK k (cont a0)))
| SReadReg (reg, k0, cont) ->
  GReadReg ((convNameRec rep reg), k0, (fun a0 -> convSinToGen rep genK k (cont a0)))
| SWriteReg (reg, k0, e, cont) ->
  GWriteReg ((convNameRec rep reg), k0, e, (convSinToGen rep genK k cont))
| SIfElse (ce, k0, ta, fa, cont) ->
  GIfElse (ce, k0, (convSinToGen rep genK k0 ta), (convSinToGen rep genK k0 fa), (fun a0 ->
    convSinToGen rep genK k (cont a0)))
| SAssert_ (ae, cont) -> GAssert_ (ae, (convSinToGen rep genK k cont))
| SReturn e -> GReturn e

(** val getSinAction : kind -> 'a1 sinActionT -> 'a1 actionT **)

let rec getSinAction k = function
| SMCall (meth, s, e, c) -> MCall (meth.nameVal, s, e, (fun v -> getSinAction k (c v)))
| SLet_ (k', e, c) -> Let_ (k', e, (fun v -> getSinAction k (c v)))
| SReadReg (r, k0, c) -> ReadReg (r.nameVal, k0, (fun v -> getSinAction k (c v)))
| SWriteReg (r, k0, e, c) -> WriteReg (r.nameVal, k0, e, (getSinAction k c))
| SIfElse (e, k0, aT, aF, c) ->
  IfElse (e, k0, (getSinAction k0 aT), (getSinAction k0 aF), (fun v -> getSinAction k (c v)))
| SAssert_ (e, c) -> Assert_ (e, (getSinAction k c))
| SReturn e -> Return e

type sinAction = __ -> __ sinActionT

type sinMethodT = __ -> __ -> __ sinActionT

(** val getActionFromSin : sinAction -> 'a1 actionT **)

let getActionFromSin gr =
  getSinAction void (Obj.magic gr __)

(** val getMethFromSin :
    (signatureT, sinMethodT) sigT -> (signatureT, __ -> __ -> __ actionT) sigT **)

let getMethFromSin gf =
  ExistT ((projT1 gf), (fun _ argv -> getSinAction (projT1 gf).ret (projT2 gf __ argv)))

(** val getListFromRep :
    ('a1 -> char list) -> ('a1 -> 'a2) -> char list -> 'a1 list -> 'a2 attribute list **)

let getListFromRep strA gen s ls =
  map (fun i -> { attrName = (addIndexToStr strA i s); attrType = (gen i) }) ls

(** val repRule :
    ('a1 -> char list) -> kind -> ('a1 -> constT) -> genAction -> char list -> 'a1 list -> (__ -> __
    actionT) attribute list **)

let repRule strA genK getConstK gr =
  getListFromRep strA (fun x _ -> getActionFromGen strA genK getConstK gr x)

(** val repMeth :
    ('a1 -> char list) -> kind -> ('a1 -> constT) -> (signatureT, genMethodT) sigT -> char list ->
    'a1 list -> (signatureT, __ -> __ -> __ actionT) sigT attribute list **)

let repMeth strA genK getConstK gf =
  getListFromRep strA (getMethFromGen strA genK getConstK gf)

type metaReg =
| OneReg of (fullKind, constFullT) sigT * nameRec
| RepReg of (__ -> char list) * (__ -> (fullKind, constFullT) sigT) * nameRec * __ list

(** val getListFromMetaReg : metaReg -> (fullKind, constFullT) sigT attribute list **)

let getListFromMetaReg = function
| OneReg (b, s) -> { attrName = s.nameVal; attrType = b } :: []
| RepReg (strA, bgen, s, ls) -> getListFromRep strA bgen s.nameVal ls

type metaRule =
| OneRule of sinAction * nameRec
| RepRule of (__ -> char list) * kind * (__ -> constT) * genAction * nameRec * __ list

(** val getListFromMetaRule : metaRule -> (__ -> __ actionT) attribute list **)

let getListFromMetaRule = function
| OneRule (b, s) -> { attrName = s.nameVal; attrType = (fun _ -> getActionFromSin b) } :: []
| RepRule (strA, genK, getConstK, bgen, s, ls) -> repRule strA genK getConstK bgen s.nameVal ls

type metaMeth =
| OneMeth of (signatureT, sinMethodT) sigT * nameRec
| RepMeth of (__ -> char list) * kind * (__ -> constT) * (signatureT, genMethodT) sigT * nameRec
   * __ list

(** val getListFromMetaMeth :
    metaMeth -> (signatureT, __ -> __ -> __ actionT) sigT attribute list **)

let getListFromMetaMeth = function
| OneMeth (b, s) -> { attrName = s.nameVal; attrType = (getMethFromSin b) } :: []
| RepMeth (strA, genK, getConstK, bgen, s, ls) -> repMeth strA genK getConstK bgen s.nameVal ls

type metaModule = { metaRegs : metaReg list; metaRules : metaRule list; metaMeths : metaMeth list }

(** val metaRegs : metaModule -> metaReg list **)

let metaRegs x = x.metaRegs

(** val metaRules : metaModule -> metaRule list **)

let metaRules x = x.metaRules

(** val metaMeths : metaModule -> metaMeth list **)

let metaMeths x = x.metaMeths

(** val modFromMeta : metaModule -> modules **)

let modFromMeta m =
  Mod ((concat (map getListFromMetaReg m.metaRegs)), (concat (map getListFromMetaRule m.metaRules)),
    (concat (map getListFromMetaMeth m.metaMeths)))

(** val getNatListToN : int -> int list **)

let rec getNatListToN n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    0 :: [])
    (fun n' ->
    n :: (getNatListToN n'))
    n

(** val natToWordConst : int -> int -> constT **)

let natToWordConst sz i =
  ConstBit (sz, (natToWord sz i))

type 'a sinReg = { regGen : ('a -> (fullKind, constFullT) sigT); regName : nameRec }

type sinRule = { ruleGen : sinAction; ruleName : nameRec }

type sinMeth = { methGen : (signatureT, sinMethodT) sigT; methName : nameRec }

type 'a sinModule = { sinRegs : 'a sinReg list; sinRules : sinRule list; sinMeths : sinMeth list }

(** val sinRegs : 'a1 sinModule -> 'a1 sinReg list **)

let sinRegs x = x.sinRegs

(** val sinRules : 'a1 sinModule -> sinRule list **)

let sinRules x = x.sinRules

(** val sinMeths : 'a1 sinModule -> sinMeth list **)

let sinMeths x = x.sinMeths

(** val regsToRep : ('a1 -> char list) -> 'a1 list -> 'a1 sinReg list -> metaReg list **)

let rec regsToRep strA ls = function
| [] -> []
| s :: rs' ->
  let { regGen = rg; regName = rn } = s in
  (RepReg ((Obj.magic strA), (Obj.magic rg), rn, (Obj.magic ls))) :: (regsToRep strA ls rs')

(** val rulesToRep :
    ('a1 -> char list) -> kind -> ('a1 -> constT) -> 'a1 list -> sinRule list -> metaRule list **)

let rec rulesToRep strA genK getConstK ls = function
| [] -> []
| s :: rs' ->
  let { ruleGen = rg; ruleName = rn } = s in
  (RepRule ((Obj.magic strA), genK, (Obj.magic getConstK), (fun _ ->
  convSinToGen true genK void (rg __)), rn,
  (Obj.magic ls))) :: (rulesToRep strA genK getConstK ls rs')

(** val methsToRep :
    ('a1 -> char list) -> kind -> ('a1 -> constT) -> 'a1 list -> sinMeth list -> metaMeth list **)

let rec methsToRep strA genK getConstK ls = function
| [] -> []
| s :: rs' ->
  let { methGen = rg; methName = rn } = s in
  (RepMeth ((Obj.magic strA), genK, (Obj.magic getConstK), (ExistT ((projT1 rg), (fun _ argv ->
  convSinToGen true genK (projT1 rg).ret (projT2 rg __ argv)))), rn,
  (Obj.magic ls))) :: (methsToRep strA genK getConstK ls rs')

(** val getMetaFromSin :
    ('a1 -> char list) -> kind -> ('a1 -> constT) -> 'a1 list -> 'a1 sinModule -> metaModule **)

let getMetaFromSin strA genK getConstK ls m =
  { metaRegs = (regsToRep strA ls m.sinRegs); metaRules =
    (rulesToRep strA genK getConstK ls m.sinRules); metaMeths =
    (methsToRep strA genK getConstK ls m.sinMeths) }

(** val getMetaFromSinNat : int -> int sinModule -> metaModule **)

let getMetaFromSinNat lgn s =
  getMetaFromSin string_of_nat (Bit lgn) (natToWordConst lgn)
    (getNatListToN (wordToNat lgn (wones lgn))) s

(** val icons' :
    (kind attribute, 'a1 expr) sigT -> kind attribute list -> (kind attribute, 'a1 expr) ilist ->
    (kind attribute, 'a1 expr) ilist **)

let icons' na attrs tl =
  Icons ((projT1 na), attrs, (projT2 na), tl)

(** val maybe : kind -> kind **)

let maybe t =
  Struct ({ attrName = ('v'::('a'::('l'::('i'::('d'::[]))))); attrType = Bool } :: ({ attrName =
    ('v'::('a'::('l'::('u'::('e'::[]))))); attrType = t } :: []))

(** val makeConst : kind -> constT -> constFullT **)

let makeConst k c =
  SyntaxConst (k, c)

type metaModuleElt =
| MMERegister of metaReg
| MMERule of metaRule
| MMEMeth of metaMeth

type inMetaModule =
| NilInMetaModule
| ConsInMetaModule of metaModuleElt * inMetaModule

(** val makeMetaModule : inMetaModule -> metaModule **)

let rec makeMetaModule = function
| NilInMetaModule -> { metaRegs = []; metaRules = []; metaMeths = [] }
| ConsInMetaModule (e, i) ->
  let { metaRegs = iregs; metaRules = irules; metaMeths = imeths } = makeMetaModule i in
  (match e with
   | MMERegister mreg -> { metaRegs = (mreg :: iregs); metaRules = irules; metaMeths = imeths }
   | MMERule mrule -> { metaRegs = iregs; metaRules = (mrule :: irules); metaMeths = imeths }
   | MMEMeth mmeth -> { metaRegs = iregs; metaRules = irules; metaMeths = (mmeth :: imeths) })

type sinModuleElt =
| SMERegister of int sinReg
| SMERule of sinRule
| SMEMeth of sinMeth

type inSinModule =
| NilInSinModule
| ConsInSinModule of sinModuleElt * inSinModule

(** val makeSinModule : inSinModule -> int sinModule **)

let rec makeSinModule = function
| NilInSinModule -> { sinRegs = []; sinRules = []; sinMeths = [] }
| ConsInSinModule (e, i) ->
  let { sinRegs = iregs; sinRules = irules; sinMeths = imeths } = makeSinModule i in
  (match e with
   | SMERegister mreg -> { sinRegs = (mreg :: iregs); sinRules = irules; sinMeths = imeths }
   | SMERule mrule -> { sinRegs = iregs; sinRules = (mrule :: irules); sinMeths = imeths }
   | SMEMeth mmeth -> { sinRegs = iregs; sinRules = irules; sinMeths = (mmeth :: imeths) })

type tyS = int

type exprS = tyS expr

type actionS =
| MCallS of char list * signatureT * exprS * int * actionS
| LetS_ of fullKind * exprS * int * actionS
| ReadRegS of char list * int * actionS
| WriteRegS of char list * fullKind * exprS * actionS
| IfElseS of exprS * kind * actionS * actionS * int * actionS
| AssertS_ of exprS * actionS
| ReturnS of exprS

(** val getActionS : int -> kind -> tyS actionT -> int * actionS **)

let rec getActionS n lret = function
| MCall (meth, s, e, c) ->
  let (m, a') = getActionS (Pervasives.succ n) lret (c n) in (m, (MCallS (meth, s, e, n, a')))
| Let_ (lret', e, cn) ->
  (match lret' with
   | SyntaxKind k ->
     let ma' = getActionS (Pervasives.succ n) lret (Obj.magic cn n) in
     let (m, a') = ma' in (m, (LetS_ ((SyntaxKind k), e, n, a')))
   | NativeKind c -> (n, (ReturnS (Const (lret, (getDefaultConst lret))))))
| ReadReg (r, k, cn) ->
  (match k with
   | SyntaxKind k0 ->
     let ma' = getActionS (Pervasives.succ n) lret (Obj.magic cn n) in
     let (m, a') = ma' in (m, (ReadRegS (r, n, a')))
   | NativeKind c -> (n, (ReturnS (Const (lret, (getDefaultConst lret))))))
| WriteReg (r, k, e, c) -> let (m, a') = getActionS n lret c in (m, (WriteRegS (r, k, e, a')))
| IfElse (e, k, ta, fa, c) ->
  let (tm, ta') = getActionS n k ta in
  let (fm, fa') = getActionS tm k fa in
  let (m, a') = getActionS (Pervasives.succ fm) lret (c fm) in
  (m, (IfElseS (e, k, ta', fa', fm, a')))
| Assert_ (e, c) -> let (m, a') = getActionS n lret c in (m, (AssertS_ (e, a')))
| Return e -> (n, (ReturnS e))

type methodTS = actionS

type defMethTS = (signatureT, methodTS) sigT attribute

type modulesS =
| ModS of regInitT list * actionS attribute list * defMethTS list
| ConcatModsS of modulesS * modulesS

(** val getMethS : (signatureT, methodT) sigT -> (signatureT, methodTS) sigT **)

let getMethS = function
| ExistT (arg0, meth) ->
  ExistT (arg0, (snd (getActionS (Pervasives.succ 0) arg0.ret (Obj.magic meth __ 0))))

(** val getModuleS : modules -> modulesS **)

let rec getModuleS = function
| Mod (regs, rules, dms) ->
  ModS (regs,
    (map (fun a -> { attrName = a.attrName; attrType =
      (snd (getActionS 0 void ((Obj.magic a).attrType __))) }) rules),
    (map (fun a -> { attrName = a.attrName; attrType = (getMethS a.attrType) }) dms))
| ConcatMod (m1, m2) -> ConcatModsS ((getModuleS m1), (getModuleS m2))

type bExpr =
| BVar of int
| BConst of kind * constT
| BUniBool of uniBoolOp * bExpr
| BBinBool of binBoolOp * bExpr * bExpr
| BUniBit of int * int * uniBitOp * bExpr
| BBinBit of int * int * int * binBitOp * bExpr * bExpr
| BBinBitBool of int * int * binBitBoolOp * bExpr * bExpr
| BITE of bExpr * bExpr * bExpr
| BEq of bExpr * bExpr
| BReadIndex of bExpr * bExpr
| BReadField of char list * bExpr
| BBuildVector of int * bExpr vec
| BBuildStruct of kind attribute list * (kind attribute, bExpr) ilist
| BUpdateVector of bExpr * bExpr * bExpr
| BReadReg of char list

type bAction =
| BMCall of int * char list * signatureT * bExpr
| BLet of int * kind option * bExpr
| BWriteReg of char list * bExpr
| BIfElse of bExpr * int * kind * bAction list * bAction list
| BAssert of bExpr
| BReturn of bExpr

type bRule = bAction list attribute

type bMethod = (signatureT * bAction list) attribute

type bModule = { bregs : regInitT list; brules : bRule list; bdms : bMethod list }

(** val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

let bind oa f =
  match oa with
  | Some a -> f a
  | None -> None

(** val bindVec : int -> 'a1 option vec -> 'a1 vec option **)

let rec bindVec n = function
| Vec0 oa -> bind oa (fun a -> Some (Vec0 a))
| VecNext (n0, v1, v2) ->
  bind (bindVec n0 v1) (fun bv1 -> bind (bindVec n0 v2) (fun bv2 -> Some (VecNext (n0, bv1, bv2))))

(** val bindList :
    kind attribute list -> (kind attribute, bExpr option) ilist -> (kind attribute, bExpr) ilist
    option **)

let rec bindList attrs = function
| Icons (a, ats, o, t) ->
  (match o with
   | Some e -> bind (bindList ats t) (fun bl -> Some (Icons (a, ats, e, bl)))
   | None -> None)
| Inil -> Some Inil

(** val exprSToBExpr : fullKind -> exprS -> bExpr option **)

let rec exprSToBExpr k = function
| Var (vk, i) ->
  (match vk with
   | SyntaxKind sk -> Some (BVar (Obj.magic i))
   | NativeKind c -> None)
| Const (k0, c) -> Some (BConst (k0, c))
| UniBool (op, se) -> bind (exprSToBExpr (SyntaxKind Bool) se) (fun be -> Some (BUniBool (op, be)))
| BinBool (op, e1, e2) ->
  bind (exprSToBExpr (SyntaxKind Bool) e1) (fun be1 ->
    bind (exprSToBExpr (SyntaxKind Bool) e2) (fun be2 -> Some (BBinBool (op, be1, be2))))
| UniBit (n1, n2, op, e0) ->
  bind (exprSToBExpr (SyntaxKind (Bit n1)) e0) (fun be -> Some (BUniBit (n1, n2, op, be)))
| BinBit (n1, n2, n3, op, e1, e2) ->
  bind (exprSToBExpr (SyntaxKind (Bit n1)) e1) (fun be1 ->
    bind (exprSToBExpr (SyntaxKind (Bit n2)) e2) (fun be2 -> Some (BBinBit (n1, n2, n3, op, be1,
      be2))))
| BinBitBool (n1, n2, op, e1, e2) ->
  bind (exprSToBExpr (SyntaxKind (Bit n1)) e1) (fun be1 ->
    bind (exprSToBExpr (SyntaxKind (Bit n2)) e2) (fun be2 -> Some (BBinBitBool (n1, n2, op, be1,
      be2))))
| ITE (k0, ce, te, fe) ->
  bind (exprSToBExpr (SyntaxKind Bool) ce) (fun bce ->
    bind (exprSToBExpr k0 te) (fun bte ->
      bind (exprSToBExpr k0 fe) (fun bfe -> Some (BITE (bce, bte, bfe)))))
| Eq (k0, e1, e2) ->
  bind (exprSToBExpr (SyntaxKind k0) e1) (fun be1 ->
    bind (exprSToBExpr (SyntaxKind k0) e2) (fun be2 -> Some (BEq (be1, be2))))
| ReadIndex (i, k0, ie, ve) ->
  bind (exprSToBExpr (SyntaxKind (Bit i)) ie) (fun bie ->
    bind (exprSToBExpr (SyntaxKind (Vector (k0, i))) ve) (fun bve -> Some (BReadIndex (bie, bve))))
| ReadField (attrs, s, e0) ->
  bind (exprSToBExpr (SyntaxKind (Struct attrs)) e0) (fun be -> Some (BReadField (s.bindex, be)))
| BuildVector (n, lgn, v) ->
  bind (bindVec lgn (mapVec (exprSToBExpr (SyntaxKind n)) lgn v)) (fun bv -> Some (BBuildVector
    (lgn, bv)))
| BuildStruct (attrs, st) ->
  bind (bindList attrs (imap (fun a e0 -> exprSToBExpr (SyntaxKind a.attrType) e0) attrs st))
    (fun bl -> Some (BBuildStruct (attrs, bl)))
| UpdateVector (i, k0, ve, ie, ke) ->
  bind (exprSToBExpr (SyntaxKind (Vector (k0, i))) ve) (fun bve ->
    bind (exprSToBExpr (SyntaxKind (Bit i)) ie) (fun bie ->
      bind (exprSToBExpr (SyntaxKind k0) ke) (fun bke -> Some (BUpdateVector (bve, bie, bke)))))

(** val actionSToBAction : kind -> actionS -> bAction list option **)

let rec actionSToBAction k = function
| MCallS (name, msig, arge, idx1, cont) ->
  bind (actionSToBAction k cont) (fun bc ->
    bind (exprSToBExpr (SyntaxKind msig.arg) arge) (fun be -> Some ((BMCall (idx1, name, msig,
      be)) :: bc)))
| LetS_ (lretT', e0, idx1, cont) ->
  (match lretT' with
   | SyntaxKind k0 ->
     bind (actionSToBAction k cont) (fun bc ->
       bind (exprSToBExpr (SyntaxKind k0) e0) (fun be -> Some ((BLet (idx1, (Some k0), be)) :: bc)))
   | NativeKind c -> None)
| ReadRegS (reg, idx1, cont) ->
  bind (actionSToBAction k cont) (fun bc -> Some ((BLet (idx1, None, (BReadReg reg))) :: bc))
| WriteRegS (reg, k0, e0, cont) ->
  bind (actionSToBAction k cont) (fun bc ->
    bind (exprSToBExpr k0 e0) (fun be -> Some ((BWriteReg (reg, be)) :: bc)))
| IfElseS (ce, iretK, ta, fa, idx1, cont) ->
  bind (actionSToBAction k cont) (fun bc ->
    bind (exprSToBExpr (SyntaxKind Bool) ce) (fun bce ->
      bind (actionSToBAction iretK ta) (fun bta ->
        bind (actionSToBAction iretK fa) (fun bfa -> Some ((BIfElse (bce, idx1, iretK, bta,
          bfa)) :: bc)))))
| AssertS_ (e0, cont) ->
  bind (actionSToBAction k cont) (fun bc ->
    bind (exprSToBExpr (SyntaxKind Bool) e0) (fun be -> Some ((BAssert be) :: bc)))
| ReturnS e0 -> bind (exprSToBExpr (SyntaxKind k) e0) (fun be -> Some ((BReturn be) :: []))

(** val rulesToBRules : actionS attribute list -> bAction list attribute list option **)

let rec rulesToBRules = function
| [] -> Some []
| a :: rs ->
  let { attrName = rn; attrType = rb } = a in
  bind (rulesToBRules rs) (fun brs ->
    bind (actionSToBAction void rb) (fun brb -> Some ({ attrName = rn; attrType = brb } :: brs)))

(** val methsToBMethods : defMethTS list -> bMethod list option **)

let rec methsToBMethods = function
| [] -> Some []
| d :: ms ->
  let { attrName = mn; attrType = attrType0 } = d in
  let ExistT (sig0, mb) = attrType0 in
  bind (methsToBMethods ms) (fun bms ->
    bind (actionSToBAction sig0.ret mb) (fun bmb -> Some ({ attrName = mn; attrType = (sig0,
      bmb) } :: bms)))

(** val modulesSToBModules : modulesS -> bModule list option **)

let rec modulesSToBModules = function
| ModS (regs, rules, dms) ->
  bind (rulesToBRules rules) (fun brules0 ->
    bind (methsToBMethods dms) (fun bdms0 -> Some ({ bregs = regs; brules = brules0; bdms =
      bdms0 } :: [])))
| ConcatModsS (m1, m2) ->
  bind (modulesSToBModules m1) (fun bm1 ->
    bind (modulesSToBModules m2) (fun bm2 -> Some (app bm1 bm2)))

(** val msi : kind **)

let msi =
  Bit (Pervasives.succ (Pervasives.succ 0))

(** val mod0 : int **)

let mod0 =
  Pervasives.succ (Pervasives.succ (Pervasives.succ 0))

(** val sh : int **)

let sh =
  Pervasives.succ 0

(** val inv : int **)

let inv =
  0

(** val toCompat : 'a1 expr -> 'a1 expr **)

let toCompat x =
  ITE ((SyntaxKind (Bit (Pervasives.succ (Pervasives.succ 0)))), (Eq (msi, x, (Const ((Bit
    (Pervasives.succ (Pervasives.succ 0))), (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) mod0))))))), (Const ((Bit (Pervasives.succ
    (Pervasives.succ 0))), (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) inv))))), (ITE ((SyntaxKind (Bit
    (Pervasives.succ (Pervasives.succ 0)))), (Eq (msi, x, (Const ((Bit (Pervasives.succ
    (Pervasives.succ 0))), (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) sh))))))), (Const ((Bit (Pervasives.succ
    (Pervasives.succ 0))), (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) sh))))), (Const ((Bit (Pervasives.succ
    (Pervasives.succ 0))), (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) mod0))))))))

(** val isCompat : 'a1 expr -> 'a1 expr -> 'a1 expr **)

let isCompat x y =
  UniBool (Neg, (BinBitBool ((Pervasives.succ (Pervasives.succ 0)), (Pervasives.succ
    (Pervasives.succ 0)), (Lt (Pervasives.succ (Pervasives.succ 0))), (toCompat y), x)))

(** val memOp : kind **)

let memOp =
  Bool

(** val child : int -> kind **)

let child lgNumChildren =
  Bit lgNumChildren

(** val data : int -> kind **)

let data lgDataBytes =
  Bit
    (mult lgDataBytes (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))

(** val line : int -> int -> kind **)

let line lgDataBytes lgNumDatas =
  Vector ((data lgDataBytes), lgNumDatas)

(** val rqFromProc : int -> kind -> kind **)

let rqFromProc lgDataBytes addr3 =
  Struct ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = addr3 } :: ({ attrName =
    ('o'::('p'::[])); attrType = memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
    (data lgDataBytes) } :: [])))

(** val rsToProc : int -> kind **)

let rsToProc lgDataBytes =
  Struct ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType = (data lgDataBytes) } :: [])

(** val fromP : int -> int -> kind -> kind -> kind **)

let fromP lgDataBytes lgNumDatas addr3 id =
  Struct ({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType = Bool } :: ({ attrName =
    ('a'::('d'::('d'::('r'::[])))); attrType = addr3 } :: ({ attrName = ('t'::('o'::[])); attrType =
    msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
    (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: [])))))

(** val rqToP : kind -> kind -> kind **)

let rqToP addr3 id =
  Struct ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = addr3 } :: ({ attrName =
    ('f'::('r'::('o'::('m'::[])))); attrType = msi } :: ({ attrName = ('t'::('o'::[])); attrType =
    msi } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: []))))

(** val rsToP : int -> int -> kind -> kind **)

let rsToP lgDataBytes lgNumDatas addr3 =
  Struct ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = addr3 } :: ({ attrName =
    ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
    (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('s'::('V'::('o'::('l'::[])))));
    attrType = Bool } :: []))))

(** val rqFromC : int -> kind -> kind -> kind **)

let rqFromC lgNumChildren addr3 id =
  Struct ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
    (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType = (rqToP addr3 id) } :: []))

(** val rsFromC : int -> int -> int -> kind -> kind **)

let rsFromC lgDataBytes lgNumDatas lgNumChildren addr3 =
  Struct ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
    (child lgNumChildren) } :: ({ attrName = ('r'::('s'::[])); attrType =
    (rsToP lgDataBytes lgNumDatas addr3) } :: []))

(** val toC : int -> int -> int -> kind -> kind -> kind **)

let toC lgDataBytes lgNumDatas lgNumChildren addr3 id =
  Struct ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
    (child lgNumChildren) } :: ({ attrName = ('m'::('s'::('g'::[]))); attrType =
    (fromP lgDataBytes lgNumDatas addr3 id) } :: []))

(** val dataArray : int -> kind -> kind **)

let dataArray idxBits data2 =
  Vector (data2, idxBits)

(** val addr : int -> kind **)

let addr idxBits =
  Bit idxBits

(** val writePort : int -> kind -> kind **)

let writePort idxBits data2 =
  Struct ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (addr idxBits) } :: ({ attrName =
    ('d'::('a'::('t'::('a'::[])))); attrType = data2 } :: []))

(** val regFileS : char list -> int -> kind -> constT -> int sinModule **)

let regFileS name idxBits data2 init =
  makeSinModule (ConsInSinModule ((SMERegister { regGen = (fun x -> ExistT ((SyntaxKind
    (dataArray idxBits data2)), (makeConst (dataArray idxBits data2) init))); regName = { nameVal =
    (withPrefix name ('d'::('a'::('t'::('a'::('A'::('r'::('r'::('a'::('y'::[])))))))))) } }),
    (ConsInSinModule ((SMEMeth { methGen = (ExistT ({ arg = (addr idxBits); ret = data2 },
    (fun _ a -> SReadReg ({ nameVal =
    (withPrefix name ('d'::('a'::('t'::('a'::('A'::('r'::('r'::('a'::('y'::[])))))))))) },
    (SyntaxKind (dataArray idxBits data2)), (fun full -> SReturn (ReadIndex (idxBits, data2, (Var
    ((SyntaxKind (addr idxBits)), a)), (Var ((SyntaxKind (dataArray idxBits data2)), full)))))))));
    methName = { nameVal = (withPrefix name ('r'::('e'::('a'::('d'::[]))))) } }), (ConsInSinModule
    ((SMEMeth { methGen = (ExistT ({ arg = (writePort idxBits data2); ret = void }, (fun _ w ->
    SReadReg ({ nameVal =
    (withPrefix name ('d'::('a'::('t'::('a'::('A'::('r'::('r'::('a'::('y'::[])))))))))) },
    (SyntaxKind (dataArray idxBits data2)), (fun full -> SWriteReg ({ nameVal =
    (withPrefix name ('d'::('a'::('t'::('a'::('A'::('r'::('r'::('a'::('y'::[])))))))))) },
    (SyntaxKind (Vector (data2, idxBits))), (UpdateVector (idxBits, data2, (Var ((SyntaxKind
    (dataArray idxBits data2)), full)), (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[]))));
    attrType = (addr idxBits) } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
    data2 } :: [])), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
    (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (addr idxBits) }.attrName ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      data2 }.attrName :: [])) }, (Var ((SyntaxKind (writePort idxBits data2)), w)))), (ReadField
    (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (addr idxBits) } :: ({ attrName =
    ('d'::('a'::('t'::('a'::[])))); attrType = data2 } :: [])), { bindex =
    ('d'::('a'::('t'::('a'::[])))); indexb =
    (indexBound_tail ('d'::('a'::('t'::('a'::[])))) { attrName = ('a'::('d'::('d'::('r'::[]))));
      attrType = (addr idxBits) }.attrName ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      data2 }.attrName :: [])
      (indexBound_head { attrName = ('d'::('a'::('t'::('a'::[])))); attrType = data2 }.attrName [])) },
    (Var ((SyntaxKind (writePort idxBits data2)), w)))))), (SReturn (Const (void,
    (getDefaultConst void)))))))))); methName = { nameVal =
    (withPrefix name ('w'::('r'::('i'::('t'::('e'::[])))))) } }), NilInSinModule))))))

(** val regFileM : char list -> int -> kind -> constT -> metaModule **)

let regFileM name idxBits data2 init =
  makeMetaModule (ConsInMetaModule ((MMERegister (OneReg ((ExistT ((SyntaxKind
    (dataArray idxBits data2)), (makeConst (dataArray idxBits data2) init))), { nameVal =
    (withPrefix name ('d'::('a'::('t'::('a'::('A'::('r'::('r'::('a'::('y'::[])))))))))) }))),
    (ConsInMetaModule ((MMEMeth (OneMeth ((ExistT ({ arg = (addr idxBits); ret = data2 },
    (fun _ a -> SReadReg ({ nameVal =
    (withPrefix name ('d'::('a'::('t'::('a'::('A'::('r'::('r'::('a'::('y'::[])))))))))) },
    (SyntaxKind (dataArray idxBits data2)), (fun full -> SReturn (ReadIndex (idxBits, data2, (Var
    ((SyntaxKind (addr idxBits)), a)), (Var ((SyntaxKind (dataArray idxBits data2)), full))))))))),
    { nameVal = (withPrefix name ('r'::('e'::('a'::('d'::[]))))) }))), (ConsInMetaModule ((MMEMeth
    (OneMeth ((ExistT ({ arg = (writePort idxBits data2); ret = void }, (fun _ w -> SReadReg
    ({ nameVal =
    (withPrefix name ('d'::('a'::('t'::('a'::('A'::('r'::('r'::('a'::('y'::[])))))))))) },
    (SyntaxKind (dataArray idxBits data2)), (fun full -> SWriteReg ({ nameVal =
    (withPrefix name ('d'::('a'::('t'::('a'::('A'::('r'::('r'::('a'::('y'::[])))))))))) },
    (SyntaxKind (Vector (data2, idxBits))), (UpdateVector (idxBits, data2, (Var ((SyntaxKind
    (dataArray idxBits data2)), full)), (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[]))));
    attrType = (addr idxBits) } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
    data2 } :: [])), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
    (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (addr idxBits) }.attrName ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      data2 }.attrName :: [])) }, (Var ((SyntaxKind (writePort idxBits data2)), w)))), (ReadField
    (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (addr idxBits) } :: ({ attrName =
    ('d'::('a'::('t'::('a'::[])))); attrType = data2 } :: [])), { bindex =
    ('d'::('a'::('t'::('a'::[])))); indexb =
    (indexBound_tail ('d'::('a'::('t'::('a'::[])))) { attrName = ('a'::('d'::('d'::('r'::[]))));
      attrType = (addr idxBits) }.attrName ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      data2 }.attrName :: [])
      (indexBound_head { attrName = ('d'::('a'::('t'::('a'::[])))); attrType = data2 }.attrName [])) },
    (Var ((SyntaxKind (writePort idxBits data2)), w)))))), (SReturn (Const (void,
    (getDefaultConst void)))))))))), { nameVal =
    (withPrefix name ('w'::('r'::('i'::('t'::('e'::[])))))) }))), NilInMetaModule))))))

(** val addrBits : int -> int -> int -> int **)

let addrBits idxBits tagBits lgNumDatas =
  plus (plus tagBits idxBits) lgNumDatas

(** val addr0 : int -> int -> int -> kind **)

let addr0 idxBits tagBits lgNumDatas =
  Bit (addrBits idxBits tagBits lgNumDatas)

(** val tag : int -> kind **)

let tag tagBits =
  Bit tagBits

(** val idx : int -> kind **)

let idx idxBits =
  Bit idxBits

(** val tagIdx : int -> int -> kind **)

let tagIdx idxBits tagBits =
  Bit (plus tagBits idxBits)

(** val data0 : int -> kind **)

let data0 lgDataBytes =
  Bit
    (mult lgDataBytes (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))

(** val offset : int -> kind **)

let offset lgNumDatas =
  Bit lgNumDatas

(** val line0 : int -> int -> kind **)

let line0 lgNumDatas lgDataBytes =
  Vector ((data0 lgDataBytes), lgNumDatas)

(** val rqFromProc0 : int -> int -> int -> int -> kind **)

let rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes =
  rqFromProc lgDataBytes (addr0 idxBits tagBits lgNumDatas)

(** val rsToProc0 : int -> kind **)

let rsToProc0 lgDataBytes =
  rsToProc lgDataBytes

(** val fromP0 : int -> int -> int -> int -> kind -> kind **)

let fromP0 idxBits tagBits lgNumDatas lgDataBytes id =
  fromP lgDataBytes lgNumDatas (tagIdx idxBits tagBits) id

(** val rqToP0 : int -> int -> kind -> kind **)

let rqToP0 idxBits tagBits id =
  rqToP (tagIdx idxBits tagBits) id

(** val rsToP0 : int -> int -> int -> int -> kind **)

let rsToP0 idxBits tagBits lgNumDatas lgDataBytes =
  rsToP lgDataBytes lgNumDatas (tagIdx idxBits tagBits)

(** val rqFromProcPop : int -> int -> int -> int -> signatureT attribute **)

let rqFromProcPop idxBits tagBits lgNumDatas lgDataBytes =
  { attrName =
    (withPrefix ('r'::('q'::('F'::('r'::('o'::('m'::('P'::('r'::('o'::('c'::[]))))))))))
      ('d'::('e'::('q'::[])))); attrType = { arg = void; ret =
    (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes) } }

(** val rqFromProcFirst : int -> int -> int -> int -> signatureT attribute **)

let rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes =
  { attrName =
    (withPrefix ('r'::('q'::('F'::('r'::('o'::('m'::('P'::('r'::('o'::('c'::[]))))))))))
      ('f'::('i'::('r'::('s'::('t'::('E'::('l'::('t'::[]))))))))); attrType = { arg = void; ret =
    (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes) } }

(** val fromPPop : int -> int -> int -> int -> kind -> signatureT attribute **)

let fromPPop idxBits tagBits lgNumDatas lgDataBytes id =
  { attrName =
    (withPrefix ('f'::('r'::('o'::('m'::('P'::('a'::('r'::('e'::('n'::('t'::[]))))))))))
      ('d'::('e'::('q'::[])))); attrType = { arg = void; ret =
    (fromP0 idxBits tagBits lgNumDatas lgDataBytes id) } }

(** val rsToProcEnq : int -> signatureT attribute **)

let rsToProcEnq lgDataBytes =
  { attrName =
    (withPrefix ('r'::('s'::('T'::('o'::('P'::('r'::('o'::('c'::[])))))))) ('e'::('n'::('q'::[]))));
    attrType = { arg = (rsToProc0 lgDataBytes); ret = void } }

(** val rqToPEnq : int -> int -> kind -> signatureT attribute **)

let rqToPEnq idxBits tagBits id =
  { attrName =
    (withPrefix ('r'::('q'::('T'::('o'::('P'::('a'::('r'::('e'::('n'::('t'::[]))))))))))
      ('e'::('n'::('q'::[])))); attrType = { arg = (rqToP0 idxBits tagBits id); ret = void } }

(** val rsToPEnq : int -> int -> int -> int -> signatureT attribute **)

let rsToPEnq idxBits tagBits lgNumDatas lgDataBytes =
  { attrName =
    (withPrefix ('r'::('s'::('T'::('o'::('P'::('a'::('r'::('e'::('n'::('t'::[]))))))))))
      ('e'::('n'::('q'::[])))); attrType = { arg = (rsToP0 idxBits tagBits lgNumDatas lgDataBytes);
    ret = void } }

(** val readLine : int -> int -> int -> signatureT attribute **)

let readLine idxBits lgNumDatas lgDataBytes =
  { attrName = (withPrefix ('l'::('i'::('n'::('e'::[])))) ('r'::('e'::('a'::('d'::[])))));
    attrType = { arg = (idx idxBits); ret = (line0 lgNumDatas lgDataBytes) } }

(** val writeLine : int -> int -> int -> signatureT attribute **)

let writeLine idxBits lgNumDatas lgDataBytes =
  { attrName = (withPrefix ('l'::('i'::('n'::('e'::[])))) ('w'::('r'::('i'::('t'::('e'::[]))))));
    attrType = { arg = (writePort idxBits (line0 lgNumDatas lgDataBytes)); ret = void } }

(** val readTag : int -> int -> signatureT attribute **)

let readTag idxBits tagBits =
  { attrName = (withPrefix ('t'::('a'::('g'::[]))) ('r'::('e'::('a'::('d'::[]))))); attrType =
    { arg = (idx idxBits); ret = (tag tagBits) } }

(** val writeTag : int -> int -> signatureT attribute **)

let writeTag idxBits tagBits =
  { attrName = (withPrefix ('t'::('a'::('g'::[]))) ('w'::('r'::('i'::('t'::('e'::[]))))));
    attrType = { arg = (writePort idxBits (tag tagBits)); ret = void } }

(** val readCs : int -> signatureT attribute **)

let readCs idxBits =
  { attrName = (withPrefix ('c'::('s'::[])) ('r'::('e'::('a'::('d'::[]))))); attrType = { arg =
    (idx idxBits); ret = msi } }

(** val writeCs : int -> signatureT attribute **)

let writeCs idxBits =
  { attrName = (withPrefix ('c'::('s'::[])) ('w'::('r'::('i'::('t'::('e'::[])))))); attrType =
    { arg = (writePort idxBits msi); ret = void } }

(** val getTagIdx : int -> int -> int -> 'a1 expr -> 'a1 expr **)

let getTagIdx idxBits tagBits lgNumDatas x =
  UniBit ((plus (plus tagBits idxBits) lgNumDatas), (plus tagBits idxBits), (TruncLsb
    ((plus tagBits idxBits), lgNumDatas)), x)

(** val getTag : int -> int -> int -> 'a1 expr -> 'a1 expr **)

let getTag idxBits tagBits lgNumDatas x =
  UniBit ((plus tagBits idxBits), tagBits, (TruncLsb (tagBits, idxBits)),
    (getTagIdx idxBits tagBits lgNumDatas x))

(** val getIdx : int -> int -> int -> 'a1 expr -> 'a1 expr **)

let getIdx idxBits tagBits lgNumDatas x =
  UniBit ((plus tagBits idxBits), idxBits, (Trunc (tagBits, idxBits)),
    (getTagIdx idxBits tagBits lgNumDatas x))

(** val getOffset : int -> int -> int -> 'a1 expr -> 'a1 expr **)

let getOffset idxBits tagBits lgNumDatas x =
  UniBit ((plus (plus tagBits idxBits) lgNumDatas), lgNumDatas, (Trunc ((plus tagBits idxBits),
    lgNumDatas)), x)

(** val makeTagIdx : int -> int -> 'a1 expr -> 'a1 expr -> 'a1 expr **)

let makeTagIdx idxBits tagBits tag0 idx1 =
  BinBit (tagBits, idxBits, (plus tagBits idxBits), (Concat (tagBits, idxBits)), tag0, idx1)

(** val getIdxFromTagIdx : int -> int -> 'a1 expr -> 'a1 expr **)

let getIdxFromTagIdx idxBits tagBits x =
  UniBit ((plus tagBits idxBits), idxBits, (Trunc (tagBits, idxBits)), x)

(** val getTagFromTagIdx : int -> int -> 'a1 expr -> 'a1 expr **)

let getTagFromTagIdx idxBits tagBits x =
  UniBit ((plus tagBits idxBits), tagBits, (TruncLsb (tagBits, idxBits)), x)

(** val l1Cache : int -> int -> int -> int -> kind -> int sinModule **)

let l1Cache idxBits tagBits lgNumDatas lgDataBytes id =
  makeSinModule (ConsInSinModule ((SMERegister { regGen = (fun x -> ExistT ((SyntaxKind Bool),
    (makeConst Bool (ConstBool false)))); regName = { nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[]))))))))))) } }),
    (ConsInSinModule ((SMERegister { regGen = (fun x -> ExistT ((SyntaxKind Bool),
    (makeConst Bool (ConstBool false)))); regName = { nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('R'::('e'::('p'::('l'::('a'::('c'::('e'::[]))))))))))))) } }),
    (ConsInSinModule ((SMERegister { regGen = (fun x -> ExistT ((SyntaxKind Bool),
    (makeConst Bool (ConstBool false)))); regName = { nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('W'::('a'::('i'::('t'::[])))))))))) } }), (ConsInSinModule
    ((SMERegister { regGen = (fun x -> ExistT ((SyntaxKind
    (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)),
    (makeConst (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)
      (getDefaultConst (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes))))); regName =
    { nameVal = ('p'::('r'::('o'::('c'::('R'::('q'::[])))))) } }), (ConsInSinModule ((SMERule
    { ruleGen = (fun _ -> SReadReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[]))))))))))) }, (SyntaxKind
    Bool), (fun valid -> SAssert_ ((UniBool (Neg, (Var ((SyntaxKind Bool), valid)))), (SMCall
    ({ nameVal = (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrName },
    (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType, (Const
    ((rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.arg,
    (getDefaultConst (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.arg))),
    (fun rq -> SLet_ ((SyntaxKind (idx idxBits)),
    (getIdx idxBits tagBits lgNumDatas (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[]))));
      attrType = (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
      memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) } :: []))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
        memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data lgDataBytes) }.attrName :: []))) }, (Var ((SyntaxKind
      (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.ret), rq))))), (fun idx1 ->
    SMCall ({ nameVal = (readTag idxBits tagBits).attrName }, (readTag idxBits tagBits).attrType,
    (Var ((SyntaxKind (idx idxBits)), idx1)), (fun tag0 -> SMCall ({ nameVal =
    (readCs idxBits).attrName }, (readCs idxBits).attrType, (Var ((SyntaxKind (idx idxBits)),
    idx1)), (fun cs -> SAssert_ ((BinBool (And, (BinBool (And, (Eq
    ((readTag idxBits tagBits).attrType.ret, (Var ((SyntaxKind
    (readTag idxBits tagBits).attrType.ret), tag0)),
    (getTag idxBits tagBits lgNumDatas (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[]))));
      attrType = (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
      memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) } :: []))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
        memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data lgDataBytes) }.attrName :: []))) }, (Var ((SyntaxKind
      (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.ret), rq))))))), (Eq
    ((readCs idxBits).attrType.ret, (Var ((SyntaxKind (readCs idxBits).attrType.ret), cs)), (Const
    ((Bit (Pervasives.succ (Pervasives.succ 0))), (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) sh))))))))), (ReadField (({ attrName =
    ('a'::('d'::('d'::('r'::[])))); attrType = (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName =
    ('o'::('p'::[])); attrType = memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
    (data lgDataBytes) } :: []))), { bindex = ('o'::('p'::[])); indexb =
    (indexBound_tail ('o'::('p'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
      memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) }.attrName :: []))
      (indexBound_head { attrName = ('o'::('p'::[])); attrType = memOp }.attrName ({ attrName =
        ('d'::('a'::('t'::('a'::[])))); attrType = (data lgDataBytes) }.attrName :: []))) }, (Var
    ((SyntaxKind (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.ret), rq)))))),
    (SWriteReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[]))))))))))) }, (SyntaxKind
    Bool), (Const (Bool, (ConstBool true))), (SWriteReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('R'::('e'::('p'::('l'::('a'::('c'::('e'::[]))))))))))))) },
    (SyntaxKind Bool), (Const (Bool, (ConstBool false))), (SWriteReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('W'::('a'::('i'::('t'::[])))))))))) }, (SyntaxKind Bool),
    (Const (Bool, (ConstBool false))), (SWriteReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::[])))))) }, (SyntaxKind
    (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.ret), (Var ((SyntaxKind
    (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.ret), rq)), (SReturn (Const
    (void, (getDefaultConst void)))))))))))))))))))))))))); ruleName = { nameVal =
    ('l'::('1'::('M'::('i'::('s'::('s'::('B'::('y'::('S'::('t'::('a'::('t'::('e'::[]))))))))))))) } }),
    (ConsInSinModule ((SMERule { ruleGen = (fun _ -> SReadReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[]))))))))))) }, (SyntaxKind
    Bool), (fun valid -> SAssert_ ((UniBool (Neg, (Var ((SyntaxKind Bool), valid)))), (SMCall
    ({ nameVal = (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrName },
    (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType, (Const
    ((rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.arg,
    (getDefaultConst (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.arg))),
    (fun rq -> SLet_ ((SyntaxKind (idx idxBits)),
    (getIdx idxBits tagBits lgNumDatas (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[]))));
      attrType = (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
      memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) } :: []))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
        memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data lgDataBytes) }.attrName :: []))) }, (Var ((SyntaxKind
      (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.ret), rq))))), (fun idx1 ->
    SMCall ({ nameVal = (readTag idxBits tagBits).attrName }, (readTag idxBits tagBits).attrType,
    (Var ((SyntaxKind (idx idxBits)), idx1)), (fun tag0 -> SMCall ({ nameVal =
    (readCs idxBits).attrName }, (readCs idxBits).attrType, (Var ((SyntaxKind (idx idxBits)),
    idx1)), (fun cs -> SAssert_ ((BinBool (Or, (UniBool (Neg, (Eq
    ((readTag idxBits tagBits).attrType.ret, (Var ((SyntaxKind
    (readTag idxBits tagBits).attrType.ret), tag0)),
    (getTag idxBits tagBits lgNumDatas (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[]))));
      attrType = (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
      memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) } :: []))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
        memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data lgDataBytes) }.attrName :: []))) }, (Var ((SyntaxKind
      (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.ret), rq))))))))), (Eq
    ((readCs idxBits).attrType.ret, (Var ((SyntaxKind (readCs idxBits).attrType.ret), cs)), (Const
    ((Bit (Pervasives.succ (Pervasives.succ 0))), (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) inv))))))))), (SWriteReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[]))))))))))) }, (SyntaxKind
    Bool), (Const (Bool, (ConstBool true))), (SWriteReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('R'::('e'::('p'::('l'::('a'::('c'::('e'::[]))))))))))))) },
    (SyntaxKind Bool), (Const (Bool, (ConstBool true))), (SWriteReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('W'::('a'::('i'::('t'::[])))))))))) }, (SyntaxKind Bool),
    (Const (Bool, (ConstBool false))), (SWriteReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::[])))))) }, (SyntaxKind
    (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.ret), (Var ((SyntaxKind
    (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.ret), rq)), (SReturn (Const
    (void, (getDefaultConst void)))))))))))))))))))))))))); ruleName = { nameVal =
    ('l'::('1'::('M'::('i'::('s'::('s'::('B'::('y'::('L'::('i'::('n'::('e'::[])))))))))))) } }),
    (ConsInSinModule ((SMERule { ruleGen = (fun _ -> SReadReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[]))))))))))) }, (SyntaxKind
    Bool), (fun valid -> SAssert_ ((UniBool (Neg, (Var ((SyntaxKind Bool), valid)))), (SMCall
    ({ nameVal = (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrName },
    (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType, (Const
    ((rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.arg,
    (getDefaultConst (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.arg))),
    (fun rq -> SLet_ ((SyntaxKind (idx idxBits)),
    (getIdx idxBits tagBits lgNumDatas (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[]))));
      attrType = (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
      memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) } :: []))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
        memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data lgDataBytes) }.attrName :: []))) }, (Var ((SyntaxKind
      (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.ret), rq))))), (fun idx1 ->
    SMCall ({ nameVal = (readTag idxBits tagBits).attrName }, (readTag idxBits tagBits).attrType,
    (Var ((SyntaxKind (idx idxBits)), idx1)), (fun tag0 -> SMCall ({ nameVal =
    (readCs idxBits).attrName }, (readCs idxBits).attrType, (Var ((SyntaxKind (idx idxBits)),
    idx1)), (fun cs -> SAssert_ ((BinBool (And, (Eq ((readTag idxBits tagBits).attrType.ret, (Var
    ((SyntaxKind (readTag idxBits tagBits).attrType.ret), tag0)),
    (getTag idxBits tagBits lgNumDatas (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[]))));
      attrType = (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
      memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) } :: []))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
        memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data lgDataBytes) }.attrName :: []))) }, (Var ((SyntaxKind
      (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.ret), rq))))))), (BinBool
    (Or, (BinBool (And, (Eq ((readCs idxBits).attrType.ret, (Var ((SyntaxKind
    (readCs idxBits).attrType.ret), cs)), (Const ((Bit (Pervasives.succ (Pervasives.succ 0))),
    (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) sh))))))), (UniBool (Neg, (ReadField
    (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
    (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
    memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
    (data lgDataBytes) } :: []))), { bindex = ('o'::('p'::[])); indexb =
    (indexBound_tail ('o'::('p'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
      memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) }.attrName :: []))
      (indexBound_head { attrName = ('o'::('p'::[])); attrType = memOp }.attrName ({ attrName =
        ('d'::('a'::('t'::('a'::[])))); attrType = (data lgDataBytes) }.attrName :: []))) }, (Var
    ((SyntaxKind (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.ret), rq)))))))),
    (BinBool (And, (Eq ((readCs idxBits).attrType.ret, (Var ((SyntaxKind
    (readCs idxBits).attrType.ret), cs)), (Const ((Bit (Pervasives.succ (Pervasives.succ 0))),
    (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) mod0))))))), (ReadField (({ attrName =
    ('a'::('d'::('d'::('r'::[])))); attrType = (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName =
    ('o'::('p'::[])); attrType = memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
    (data lgDataBytes) } :: []))), { bindex = ('o'::('p'::[])); indexb =
    (indexBound_tail ('o'::('p'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
      memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) }.attrName :: []))
      (indexBound_head { attrName = ('o'::('p'::[])); attrType = memOp }.attrName ({ attrName =
        ('d'::('a'::('t'::('a'::[])))); attrType = (data lgDataBytes) }.attrName :: []))) }, (Var
    ((SyntaxKind (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.ret),
    rq)))))))))), (SWriteReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[]))))))))))) }, (SyntaxKind
    Bool), (Const (Bool, (ConstBool true))), (SWriteReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('R'::('e'::('p'::('l'::('a'::('c'::('e'::[]))))))))))))) },
    (SyntaxKind Bool), (Const (Bool, (ConstBool false))), (SWriteReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('W'::('a'::('i'::('t'::[])))))))))) }, (SyntaxKind Bool),
    (Const (Bool, (ConstBool false))), (SWriteReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::[])))))) }, (SyntaxKind
    (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.ret), (Var ((SyntaxKind
    (rqFromProcFirst idxBits tagBits lgNumDatas lgDataBytes).attrType.ret), rq)), (SReturn (Const
    (void, (getDefaultConst void)))))))))))))))))))))))))); ruleName = { nameVal =
    ('l'::('1'::('H'::('i'::('t'::[]))))) } }), (ConsInSinModule ((SMERule { ruleGen = (fun _ ->
    SReadReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[]))))))))))) }, (SyntaxKind
    Bool), (fun valid -> SAssert_ ((Var ((SyntaxKind Bool), valid)), (SReadReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('R'::('e'::('p'::('l'::('a'::('c'::('e'::[]))))))))))))) },
    (SyntaxKind Bool), (fun replace -> SAssert_ ((Var ((SyntaxKind Bool), replace)), (SReadReg
    ({ nameVal = ('p'::('r'::('o'::('c'::('R'::('q'::[])))))) }, (SyntaxKind
    (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), (fun rq -> SLet_ ((SyntaxKind
    (idx idxBits)),
    (getIdx idxBits tagBits lgNumDatas (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[]))));
      attrType = (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
      memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) } :: []))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
        memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data lgDataBytes) }.attrName :: []))) }, (Var ((SyntaxKind
      (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), rq))))), (fun idx1 -> SMCall
    ({ nameVal = (readTag idxBits tagBits).attrName }, (readTag idxBits tagBits).attrType, (Var
    ((SyntaxKind (idx idxBits)), idx1)), (fun tag0 -> SMCall ({ nameVal =
    (readCs idxBits).attrName }, (readCs idxBits).attrType, (Var ((SyntaxKind (idx idxBits)),
    idx1)), (fun cs -> SMCall ({ nameVal = (readLine idxBits lgNumDatas lgDataBytes).attrName },
    (readLine idxBits lgNumDatas lgDataBytes).attrType, (Var ((SyntaxKind (idx idxBits)), idx1)),
    (fun line2 -> SIfElse ((UniBool (Neg, (Eq ((readCs idxBits).attrType.ret, (Var ((SyntaxKind
    (readCs idxBits).attrType.ret), cs)), (Const ((Bit (Pervasives.succ (Pervasives.succ 0))),
    (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) inv))))))))), void, (SMCall ({ nameVal =
    (rsToPEnq idxBits tagBits lgNumDatas lgDataBytes).attrName },
    (rsToPEnq idxBits tagBits lgNumDatas lgDataBytes).attrType, (BuildStruct
    (((projT1 (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (Bit
        (plus tagBits idxBits)) },
        (makeTagIdx idxBits tagBits (Var ((SyntaxKind (readTag idxBits tagBits).attrType.ret),
          tag0)) (Var ((SyntaxKind (idx idxBits)), idx1)))))) :: ((projT1 (ExistT ({ attrName =
                                                                    ('t'::('o'::[])); attrType =
                                                                    (Bit (Pervasives.succ
                                                                    (Pervasives.succ 0))) }, (Const
                                                                    ((Bit (Pervasives.succ
                                                                    (Pervasives.succ 0))), (ConstBit
                                                                    ((Pervasives.succ
                                                                    (Pervasives.succ 0)),
                                                                    (natToWord (Pervasives.succ
                                                                      (Pervasives.succ 0)) inv)))))))) :: (
    (projT1 (ExistT ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
      (readLine idxBits lgNumDatas lgDataBytes).attrType.ret }, (Var ((SyntaxKind
      (readLine idxBits lgNumDatas lgDataBytes).attrType.ret), line2))))) :: ((projT1 (ExistT
                                                                                ({ attrName =
                                                                                ('i'::('s'::('V'::('o'::('l'::[])))));
                                                                                attrType = Bool },
                                                                                (Const (Bool,
                                                                                (ConstBool
                                                                                true)))))) :: [])))),
    (icons' (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (Bit
      (plus tagBits idxBits)) },
      (makeTagIdx idxBits tagBits (Var ((SyntaxKind (readTag idxBits tagBits).attrType.ret), tag0))
        (Var ((SyntaxKind (idx idxBits)), idx1)))))
      ((projT1 (ExistT ({ attrName = ('t'::('o'::[])); attrType = (Bit (Pervasives.succ
         (Pervasives.succ 0))) }, (Const ((Bit (Pervasives.succ (Pervasives.succ 0))), (ConstBit
         ((Pervasives.succ (Pervasives.succ 0)),
         (natToWord (Pervasives.succ (Pervasives.succ 0)) inv)))))))) :: ((projT1 (ExistT
                                                                            ({ attrName =
                                                                            ('l'::('i'::('n'::('e'::[]))));
                                                                            attrType =
                                                                            (readLine idxBits
                                                                              lgNumDatas
                                                                              lgDataBytes).attrType.ret },
                                                                            (Var ((SyntaxKind
                                                                            (readLine idxBits
                                                                              lgNumDatas
                                                                              lgDataBytes).attrType.ret),
                                                                            line2))))) :: ((projT1
                                                                                           (ExistT
                                                                                           ({ attrName =
                                                                                           ('i'::('s'::('V'::('o'::('l'::[])))));
                                                                                           attrType =
                                                                                           Bool },
                                                                                           (Const
                                                                                           (Bool,
                                                                                           (ConstBool
                                                                                           true)))))) :: [])))
      (icons' (ExistT ({ attrName = ('t'::('o'::[])); attrType = (Bit (Pervasives.succ
        (Pervasives.succ 0))) }, (Const ((Bit (Pervasives.succ (Pervasives.succ 0))), (ConstBit
        ((Pervasives.succ (Pervasives.succ 0)),
        (natToWord (Pervasives.succ (Pervasives.succ 0)) inv)))))))
        ((projT1 (ExistT ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
           (readLine idxBits lgNumDatas lgDataBytes).attrType.ret }, (Var ((SyntaxKind
           (readLine idxBits lgNumDatas lgDataBytes).attrType.ret), line2))))) :: ((projT1 (ExistT
                                                                                     ({ attrName =
                                                                                     ('i'::('s'::('V'::('o'::('l'::[])))));
                                                                                     attrType =
                                                                                     Bool }, (Const
                                                                                     (Bool,
                                                                                     (ConstBool
                                                                                     true)))))) :: []))
        (icons' (ExistT ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (readLine idxBits lgNumDatas lgDataBytes).attrType.ret }, (Var ((SyntaxKind
          (readLine idxBits lgNumDatas lgDataBytes).attrType.ret), line2))))
          ((projT1 (ExistT ({ attrName = ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool },
             (Const (Bool, (ConstBool true)))))) :: [])
          (icons' (ExistT ({ attrName = ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool },
            (Const (Bool, (ConstBool true))))) [] Inil)))))), (fun x -> SReturn (Const (void,
    (getDefaultConst void)))))), (SReturn (Const (void, (getDefaultConst void)))), (fun x -> SMCall
    ({ nameVal = (writeCs idxBits).attrName }, (writeCs idxBits).attrType, (BuildStruct
    (((projT1 (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx idxBits) }, (Var
        ((SyntaxKind (idx idxBits)), idx1))))) :: ((projT1 (ExistT ({ attrName =
                                                     ('d'::('a'::('t'::('a'::[])))); attrType = (Bit
                                                     (Pervasives.succ (Pervasives.succ 0))) },
                                                     (Const ((Bit (Pervasives.succ (Pervasives.succ
                                                     0))), (ConstBit ((Pervasives.succ
                                                     (Pervasives.succ 0)),
                                                     (natToWord (Pervasives.succ (Pervasives.succ
                                                       0)) inv)))))))) :: [])),
    (icons' (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx idxBits) }, (Var
      ((SyntaxKind (idx idxBits)), idx1))))
      ((projT1 (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType = (Bit
         (Pervasives.succ (Pervasives.succ 0))) }, (Const ((Bit (Pervasives.succ (Pervasives.succ
         0))), (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
         (natToWord (Pervasives.succ (Pervasives.succ 0)) inv)))))))) :: [])
      (icons' (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType = (Bit (Pervasives.succ
        (Pervasives.succ 0))) }, (Const ((Bit (Pervasives.succ (Pervasives.succ 0))), (ConstBit
        ((Pervasives.succ (Pervasives.succ 0)),
        (natToWord (Pervasives.succ (Pervasives.succ 0)) inv))))))) [] Inil)))), (fun x0 ->
    SWriteReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('R'::('e'::('p'::('l'::('a'::('c'::('e'::[]))))))))))))) },
    (SyntaxKind Bool), (Const (Bool, (ConstBool false))), (SReturn (Const (void,
    (getDefaultConst void)))))))))))))))))))))))))))); ruleName = { nameVal =
    ('w'::('r'::('i'::('t'::('e'::('b'::('a'::('c'::('k'::[]))))))))) } }), (ConsInSinModule
    ((SMERule { ruleGen = (fun _ -> SReadReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[]))))))))))) }, (SyntaxKind
    Bool), (fun valid -> SAssert_ ((Var ((SyntaxKind Bool), valid)), (SReadReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('R'::('e'::('p'::('l'::('a'::('c'::('e'::[]))))))))))))) },
    (SyntaxKind Bool), (fun replace -> SAssert_ ((UniBool (Neg, (Var ((SyntaxKind Bool),
    replace)))), (SReadReg ({ nameVal = ('p'::('r'::('o'::('c'::('R'::('q'::[])))))) }, (SyntaxKind
    (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), (fun rq -> SLet_ ((SyntaxKind
    (idx idxBits)),
    (getIdx idxBits tagBits lgNumDatas (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[]))));
      attrType = (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
      memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) } :: []))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
        memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data lgDataBytes) }.attrName :: []))) }, (Var ((SyntaxKind
      (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), rq))))), (fun idx1 -> SMCall
    ({ nameVal = (readCs idxBits).attrName }, (readCs idxBits).attrType, (Var ((SyntaxKind
    (idx idxBits)), idx1)), (fun cs -> SLet_ ((SyntaxKind msi), (ITE ((SyntaxKind (Bit
    (Pervasives.succ (Pervasives.succ 0)))), (ReadField (({ attrName =
    ('a'::('d'::('d'::('r'::[])))); attrType = (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName =
    ('o'::('p'::[])); attrType = memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
    (data lgDataBytes) } :: []))), { bindex = ('o'::('p'::[])); indexb =
    (indexBound_tail ('o'::('p'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
      memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) }.attrName :: []))
      (indexBound_head { attrName = ('o'::('p'::[])); attrType = memOp }.attrName ({ attrName =
        ('d'::('a'::('t'::('a'::[])))); attrType = (data lgDataBytes) }.attrName :: []))) }, (Var
    ((SyntaxKind (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), rq)))), (Const ((Bit
    (Pervasives.succ (Pervasives.succ 0))), (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) mod0))))), (Const ((Bit (Pervasives.succ
    (Pervasives.succ 0))), (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) sh))))))), (fun toS -> SReadReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('W'::('a'::('i'::('t'::[])))))))))) }, (SyntaxKind Bool),
    (fun wait -> SAssert_ ((BinBool (And, (UniBool (Neg, (Var ((SyntaxKind Bool), wait)))),
    (BinBitBool ((Pervasives.succ (Pervasives.succ 0)), (Pervasives.succ (Pervasives.succ 0)), (Lt
    (Pervasives.succ (Pervasives.succ 0))), (Var ((SyntaxKind (readCs idxBits).attrType.ret), cs)),
    (Var ((SyntaxKind msi), toS)))))), (SMCall ({ nameVal =
    (rqToPEnq idxBits tagBits id).attrName }, (rqToPEnq idxBits tagBits id).attrType, (BuildStruct
    (((projT1 (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (tagIdx idxBits tagBits) },
        (getTagIdx idxBits tagBits lgNumDatas (ReadField (({ attrName =
          ('a'::('d'::('d'::('r'::[])))); attrType =
          (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
          memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
          (data lgDataBytes) } :: []))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
          (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
            (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
            memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
            (data lgDataBytes) }.attrName :: []))) }, (Var ((SyntaxKind
          (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), rq)))))))) :: ((projT1 (ExistT
                                                                                  ({ attrName =
                                                                                  ('f'::('r'::('o'::('m'::[]))));
                                                                                  attrType =
                                                                                  (readCs idxBits).attrType.ret },
                                                                                  (Var ((SyntaxKind
                                                                                  (readCs idxBits).attrType.ret),
                                                                                  cs))))) :: (
    (projT1 (ExistT ({ attrName = ('t'::('o'::[])); attrType = msi }, (Var ((SyntaxKind msi),
      toS))))) :: ((projT1 (ExistT ({ attrName = ('i'::('d'::[])); attrType = id }, (Const
                     ({ attrName = ('i'::('d'::[])); attrType = id }.attrType,
                     (getDefaultConst { attrName = ('i'::('d'::[])); attrType = id }.attrType)))))) :: [])))),
    (icons' (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (tagIdx idxBits tagBits) },
      (getTagIdx idxBits tagBits lgNumDatas (ReadField (({ attrName =
        ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
        memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data lgDataBytes) } :: []))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
        (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
          memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
          (data lgDataBytes) }.attrName :: []))) }, (Var ((SyntaxKind
        (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), rq)))))))
      ((projT1 (ExistT ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
         (readCs idxBits).attrType.ret }, (Var ((SyntaxKind (readCs idxBits).attrType.ret), cs))))) :: (
      (projT1 (ExistT ({ attrName = ('t'::('o'::[])); attrType = msi }, (Var ((SyntaxKind msi),
        toS))))) :: ((projT1 (ExistT ({ attrName = ('i'::('d'::[])); attrType = id }, (Const
                       ({ attrName = ('i'::('d'::[])); attrType = id }.attrType,
                       (getDefaultConst { attrName = ('i'::('d'::[])); attrType = id }.attrType)))))) :: [])))
      (icons' (ExistT ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
        (readCs idxBits).attrType.ret }, (Var ((SyntaxKind (readCs idxBits).attrType.ret), cs))))
        ((projT1 (ExistT ({ attrName = ('t'::('o'::[])); attrType = msi }, (Var ((SyntaxKind msi),
           toS))))) :: ((projT1 (ExistT ({ attrName = ('i'::('d'::[])); attrType = id }, (Const
                          ({ attrName = ('i'::('d'::[])); attrType = id }.attrType,
                          (getDefaultConst { attrName = ('i'::('d'::[])); attrType = id }.attrType)))))) :: []))
        (icons' (ExistT ({ attrName = ('t'::('o'::[])); attrType = msi }, (Var ((SyntaxKind msi),
          toS))))
          ((projT1 (ExistT ({ attrName = ('i'::('d'::[])); attrType = id }, (Const ({ attrName =
             ('i'::('d'::[])); attrType = id }.attrType,
             (getDefaultConst { attrName = ('i'::('d'::[])); attrType = id }.attrType)))))) :: [])
          (icons' (ExistT ({ attrName = ('i'::('d'::[])); attrType = id }, (Const ({ attrName =
            ('i'::('d'::[])); attrType = id }.attrType,
            (getDefaultConst { attrName = ('i'::('d'::[])); attrType = id }.attrType))))) [] Inil)))))),
    (fun x -> SWriteReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('W'::('a'::('i'::('t'::[])))))))))) }, (SyntaxKind Bool),
    (Const (Bool, (ConstBool true))), (SReturn (Const (void,
    (getDefaultConst void)))))))))))))))))))))))))))); ruleName = { nameVal =
    ('u'::('p'::('g'::('R'::('q'::[]))))) } }), (ConsInSinModule ((SMERule { ruleGen = (fun _ ->
    SMCall ({ nameVal = (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrName },
    (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType, (Const
    ((fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.arg,
    (getDefaultConst (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.arg))),
    (fun fromP3 -> SAssert_ ((UniBool (Neg, (ReadField (({ attrName =
    ('i'::('s'::('R'::('q'::[])))); attrType = Bool } :: ({ attrName =
    ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) } :: ({ attrName =
    ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
    (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: []))))),
    { bindex = ('i'::('s'::('R'::('q'::[])))); indexb =
    (indexBound_head { attrName = ('i'::('s'::('R'::('q'::[])))); attrType = Bool }.attrName
      ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
      msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
      (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
      id }.attrName :: []))))) }, (Var ((SyntaxKind
    (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3)))))), (SLet_
    ((SyntaxKind (idx idxBits)),
    (getIdxFromTagIdx idxBits tagBits (ReadField (({ attrName = ('i'::('s'::('R'::('q'::[]))));
      attrType = Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType =
      msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
      (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: []))))),
      { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_tail ('a'::('d'::('d'::('r'::[])))) { attrName = ('i'::('s'::('R'::('q'::[]))));
        attrType = Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
        msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
        (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
        id }.attrName :: []))))
        (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
          id }.attrName :: []))))) }, (Var ((SyntaxKind
      (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3))))), (fun idx1 ->
    SMCall ({ nameVal = (readCs idxBits).attrName }, (readCs idxBits).attrType, (Var ((SyntaxKind
    (idx idxBits)), idx1)), (fun cs -> SMCall ({ nameVal = (writeCs idxBits).attrName },
    (writeCs idxBits).attrType, (BuildStruct
    (((projT1 (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx idxBits) }, (Var
        ((SyntaxKind (idx idxBits)), idx1))))) :: ((projT1 (ExistT ({ attrName =
                                                     ('d'::('a'::('t'::('a'::[])))); attrType =
                                                     (getAttrType ({ attrName =
                                                       ('i'::('s'::('R'::('q'::[])))); attrType =
                                                       Bool } :: ({ attrName =
                                                       ('a'::('d'::('d'::('r'::[])))); attrType =
                                                       (tagIdx idxBits tagBits) } :: ({ attrName =
                                                       ('t'::('o'::[])); attrType =
                                                       msi } :: ({ attrName =
                                                       ('l'::('i'::('n'::('e'::[])))); attrType =
                                                       (line lgDataBytes lgNumDatas) } :: ({ attrName =
                                                       ('i'::('d'::[])); attrType = id } :: [])))))
                                                       { bindex = ('t'::('o'::[])); indexb =
                                                       (indexBound_tail ('t'::('o'::[]))
                                                         { attrName =
                                                         ('i'::('s'::('R'::('q'::[])))); attrType =
                                                         Bool }.attrName ({ attrName =
                                                         ('a'::('d'::('d'::('r'::[])))); attrType =
                                                         (tagIdx idxBits tagBits) }.attrName :: ({ attrName =
                                                         ('t'::('o'::[])); attrType =
                                                         msi }.attrName :: ({ attrName =
                                                         ('l'::('i'::('n'::('e'::[])))); attrType =
                                                         (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                         ('i'::('d'::[])); attrType =
                                                         id }.attrName :: []))))
                                                         (indexBound_tail ('t'::('o'::[]))
                                                           { attrName =
                                                           ('a'::('d'::('d'::('r'::[]))));
                                                           attrType =
                                                           (tagIdx idxBits tagBits) }.attrName
                                                           ({ attrName = ('t'::('o'::[]));
                                                           attrType =
                                                           msi }.attrName :: ({ attrName =
                                                           ('l'::('i'::('n'::('e'::[]))));
                                                           attrType =
                                                           (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                           ('i'::('d'::[])); attrType =
                                                           id }.attrName :: [])))
                                                           (indexBound_head { attrName =
                                                             ('t'::('o'::[])); attrType =
                                                             msi }.attrName ({ attrName =
                                                             ('l'::('i'::('n'::('e'::[]))));
                                                             attrType =
                                                             (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                             ('i'::('d'::[])); attrType =
                                                             id }.attrName :: []))))) }) },
                                                     (ReadField (({ attrName =
                                                     ('i'::('s'::('R'::('q'::[])))); attrType =
                                                     Bool } :: ({ attrName =
                                                     ('a'::('d'::('d'::('r'::[])))); attrType =
                                                     (tagIdx idxBits tagBits) } :: ({ attrName =
                                                     ('t'::('o'::[])); attrType =
                                                     msi } :: ({ attrName =
                                                     ('l'::('i'::('n'::('e'::[])))); attrType =
                                                     (line lgDataBytes lgNumDatas) } :: ({ attrName =
                                                     ('i'::('d'::[])); attrType = id } :: []))))),
                                                     { bindex = ('t'::('o'::[])); indexb =
                                                     (indexBound_tail ('t'::('o'::[])) { attrName =
                                                       ('i'::('s'::('R'::('q'::[])))); attrType =
                                                       Bool }.attrName ({ attrName =
                                                       ('a'::('d'::('d'::('r'::[])))); attrType =
                                                       (tagIdx idxBits tagBits) }.attrName :: ({ attrName =
                                                       ('t'::('o'::[])); attrType =
                                                       msi }.attrName :: ({ attrName =
                                                       ('l'::('i'::('n'::('e'::[])))); attrType =
                                                       (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                       ('i'::('d'::[])); attrType =
                                                       id }.attrName :: []))))
                                                       (indexBound_tail ('t'::('o'::[]))
                                                         { attrName =
                                                         ('a'::('d'::('d'::('r'::[])))); attrType =
                                                         (tagIdx idxBits tagBits) }.attrName
                                                         ({ attrName = ('t'::('o'::[])); attrType =
                                                         msi }.attrName :: ({ attrName =
                                                         ('l'::('i'::('n'::('e'::[])))); attrType =
                                                         (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                         ('i'::('d'::[])); attrType =
                                                         id }.attrName :: [])))
                                                         (indexBound_head { attrName =
                                                           ('t'::('o'::[])); attrType =
                                                           msi }.attrName ({ attrName =
                                                           ('l'::('i'::('n'::('e'::[]))));
                                                           attrType =
                                                           (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                           ('i'::('d'::[])); attrType =
                                                           id }.attrName :: []))))) }, (Var
                                                     ((SyntaxKind
                                                     (fromPPop idxBits tagBits lgNumDatas
                                                       lgDataBytes id).attrType.ret), fromP3))))))) :: [])),
    (icons' (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx idxBits) }, (Var
      ((SyntaxKind (idx idxBits)), idx1))))
      ((projT1 (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
         (getAttrType ({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
           Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
           (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType =
           msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
           (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
           id } :: []))))) { bindex = ('t'::('o'::[])); indexb =
           (indexBound_tail ('t'::('o'::[])) { attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
             Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
             (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
             msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
             (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
             id }.attrName :: []))))
             (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[]))));
               attrType = (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[]));
               attrType = msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
               (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[]));
               attrType = id }.attrName :: [])))
               (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName
                 ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
                 (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[]));
                 attrType = id }.attrName :: []))))) }) }, (ReadField (({ attrName =
         ('i'::('s'::('R'::('q'::[])))); attrType = Bool } :: ({ attrName =
         ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) } :: ({ attrName =
         ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[]))));
         attrType = (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
         id } :: []))))), { bindex = ('t'::('o'::[])); indexb =
         (indexBound_tail ('t'::('o'::[])) { attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
           Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
           (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
           msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
           (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
           id }.attrName :: []))))
           (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
             (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
             msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
             (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
             id }.attrName :: [])))
             (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName ({ attrName =
               ('l'::('i'::('n'::('e'::[])))); attrType =
               (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[]));
               attrType = id }.attrName :: []))))) }, (Var ((SyntaxKind
         (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3))))))) :: [])
      (icons' (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (getAttrType ({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
          Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType =
          msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
          id } :: []))))) { bindex = ('t'::('o'::[])); indexb =
          (indexBound_tail ('t'::('o'::[])) { attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
            Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
            (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
            msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
            (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
            id }.attrName :: []))))
            (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[]))));
              attrType = (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[]));
              attrType = msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
              (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
              id }.attrName :: [])))
              (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName
                ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
                (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[]));
                attrType = id }.attrName :: []))))) }) }, (ReadField (({ attrName =
        ('i'::('s'::('R'::('q'::[])))); attrType = Bool } :: ({ attrName =
        ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) } :: ({ attrName =
        ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[]))));
        attrType = (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
        id } :: []))))), { bindex = ('t'::('o'::[])); indexb =
        (indexBound_tail ('t'::('o'::[])) { attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
          Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
          id }.attrName :: []))))
          (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
            (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
            msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
            (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
            id }.attrName :: [])))
            (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName ({ attrName =
              ('l'::('i'::('n'::('e'::[])))); attrType =
              (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
              id }.attrName :: []))))) }, (Var ((SyntaxKind
        (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3)))))) [] Inil)))),
    (fun x -> SMCall ({ nameVal = (writeTag idxBits tagBits).attrName },
    (writeTag idxBits tagBits).attrType, (BuildStruct
    (((projT1 (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx idxBits) }, (Var
        ((SyntaxKind (idx idxBits)), idx1))))) :: ((projT1 (ExistT ({ attrName =
                                                     ('d'::('a'::('t'::('a'::[])))); attrType =
                                                     (tag tagBits) },
                                                     (getTagFromTagIdx idxBits tagBits (ReadField
                                                       (({ attrName =
                                                       ('i'::('s'::('R'::('q'::[])))); attrType =
                                                       Bool } :: ({ attrName =
                                                       ('a'::('d'::('d'::('r'::[])))); attrType =
                                                       (tagIdx idxBits tagBits) } :: ({ attrName =
                                                       ('t'::('o'::[])); attrType =
                                                       msi } :: ({ attrName =
                                                       ('l'::('i'::('n'::('e'::[])))); attrType =
                                                       (line lgDataBytes lgNumDatas) } :: ({ attrName =
                                                       ('i'::('d'::[])); attrType = id } :: []))))),
                                                       { bindex = ('a'::('d'::('d'::('r'::[]))));
                                                       indexb =
                                                       (indexBound_tail
                                                         ('a'::('d'::('d'::('r'::[])))) { attrName =
                                                         ('i'::('s'::('R'::('q'::[])))); attrType =
                                                         Bool }.attrName ({ attrName =
                                                         ('a'::('d'::('d'::('r'::[])))); attrType =
                                                         (tagIdx idxBits tagBits) }.attrName :: ({ attrName =
                                                         ('t'::('o'::[])); attrType =
                                                         msi }.attrName :: ({ attrName =
                                                         ('l'::('i'::('n'::('e'::[])))); attrType =
                                                         (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                         ('i'::('d'::[])); attrType =
                                                         id }.attrName :: []))))
                                                         (indexBound_head { attrName =
                                                           ('a'::('d'::('d'::('r'::[]))));
                                                           attrType =
                                                           (tagIdx idxBits tagBits) }.attrName
                                                           ({ attrName = ('t'::('o'::[]));
                                                           attrType =
                                                           msi }.attrName :: ({ attrName =
                                                           ('l'::('i'::('n'::('e'::[]))));
                                                           attrType =
                                                           (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                           ('i'::('d'::[])); attrType =
                                                           id }.attrName :: []))))) }, (Var
                                                       ((SyntaxKind
                                                       (fromPPop idxBits tagBits lgNumDatas
                                                         lgDataBytes id).attrType.ret), fromP3)))))))) :: [])),
    (icons' (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx idxBits) }, (Var
      ((SyntaxKind (idx idxBits)), idx1))))
      ((projT1 (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType = (tag tagBits) },
         (getTagFromTagIdx idxBits tagBits (ReadField (({ attrName = ('i'::('s'::('R'::('q'::[]))));
           attrType = Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
           (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType =
           msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
           (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
           id } :: []))))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
           (indexBound_tail ('a'::('d'::('d'::('r'::[])))) { attrName =
             ('i'::('s'::('R'::('q'::[])))); attrType = Bool }.attrName ({ attrName =
             ('a'::('d'::('d'::('r'::[])))); attrType =
             (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
             msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
             (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
             id }.attrName :: []))))
             (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
               (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
               msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
               (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[]));
               attrType = id }.attrName :: []))))) }, (Var ((SyntaxKind
           (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3)))))))) :: [])
      (icons' (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType = (tag tagBits) },
        (getTagFromTagIdx idxBits tagBits (ReadField (({ attrName = ('i'::('s'::('R'::('q'::[]))));
          attrType = Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType =
          msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
          id } :: []))))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
          (indexBound_tail ('a'::('d'::('d'::('r'::[])))) { attrName =
            ('i'::('s'::('R'::('q'::[])))); attrType = Bool }.attrName ({ attrName =
            ('a'::('d'::('d'::('r'::[])))); attrType =
            (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
            msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
            (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
            id }.attrName :: []))))
            (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
              (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
              msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
              (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
              id }.attrName :: []))))) }, (Var ((SyntaxKind
          (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3))))))) [] Inil)))),
    (fun x0 -> SWriteReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('W'::('a'::('i'::('t'::[])))))))))) }, (SyntaxKind Bool),
    (Const (Bool, (ConstBool false))), (SIfElse ((Eq ((readCs idxBits).attrType.ret, (Var
    ((SyntaxKind (readCs idxBits).attrType.ret), cs)), (Const ((Bit (Pervasives.succ
    (Pervasives.succ 0))), (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) inv))))))), void, (SMCall ({ nameVal =
    (writeLine idxBits lgNumDatas lgDataBytes).attrName },
    (writeLine idxBits lgNumDatas lgDataBytes).attrType, (BuildStruct
    (((projT1 (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx idxBits) }, (Var
        ((SyntaxKind (idx idxBits)), idx1))))) :: ((projT1 (ExistT ({ attrName =
                                                     ('d'::('a'::('t'::('a'::[])))); attrType =
                                                     (getAttrType ({ attrName =
                                                       ('i'::('s'::('R'::('q'::[])))); attrType =
                                                       Bool } :: ({ attrName =
                                                       ('a'::('d'::('d'::('r'::[])))); attrType =
                                                       (tagIdx idxBits tagBits) } :: ({ attrName =
                                                       ('t'::('o'::[])); attrType =
                                                       msi } :: ({ attrName =
                                                       ('l'::('i'::('n'::('e'::[])))); attrType =
                                                       (line lgDataBytes lgNumDatas) } :: ({ attrName =
                                                       ('i'::('d'::[])); attrType = id } :: [])))))
                                                       { bindex = ('l'::('i'::('n'::('e'::[]))));
                                                       indexb =
                                                       (indexBound_tail
                                                         ('l'::('i'::('n'::('e'::[])))) { attrName =
                                                         ('i'::('s'::('R'::('q'::[])))); attrType =
                                                         Bool }.attrName ({ attrName =
                                                         ('a'::('d'::('d'::('r'::[])))); attrType =
                                                         (tagIdx idxBits tagBits) }.attrName :: ({ attrName =
                                                         ('t'::('o'::[])); attrType =
                                                         msi }.attrName :: ({ attrName =
                                                         ('l'::('i'::('n'::('e'::[])))); attrType =
                                                         (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                         ('i'::('d'::[])); attrType =
                                                         id }.attrName :: []))))
                                                         (indexBound_tail
                                                           ('l'::('i'::('n'::('e'::[]))))
                                                           { attrName =
                                                           ('a'::('d'::('d'::('r'::[]))));
                                                           attrType =
                                                           (tagIdx idxBits tagBits) }.attrName
                                                           ({ attrName = ('t'::('o'::[]));
                                                           attrType =
                                                           msi }.attrName :: ({ attrName =
                                                           ('l'::('i'::('n'::('e'::[]))));
                                                           attrType =
                                                           (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                           ('i'::('d'::[])); attrType =
                                                           id }.attrName :: [])))
                                                           (indexBound_tail
                                                             ('l'::('i'::('n'::('e'::[]))))
                                                             { attrName = ('t'::('o'::[]));
                                                             attrType = msi }.attrName ({ attrName =
                                                             ('l'::('i'::('n'::('e'::[]))));
                                                             attrType =
                                                             (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                             ('i'::('d'::[])); attrType =
                                                             id }.attrName :: []))
                                                             (indexBound_head { attrName =
                                                               ('l'::('i'::('n'::('e'::[]))));
                                                               attrType =
                                                               (line lgDataBytes lgNumDatas) }.attrName
                                                               ({ attrName = ('i'::('d'::[]));
                                                               attrType = id }.attrName :: []))))) }) },
                                                     (ReadField (({ attrName =
                                                     ('i'::('s'::('R'::('q'::[])))); attrType =
                                                     Bool } :: ({ attrName =
                                                     ('a'::('d'::('d'::('r'::[])))); attrType =
                                                     (tagIdx idxBits tagBits) } :: ({ attrName =
                                                     ('t'::('o'::[])); attrType =
                                                     msi } :: ({ attrName =
                                                     ('l'::('i'::('n'::('e'::[])))); attrType =
                                                     (line lgDataBytes lgNumDatas) } :: ({ attrName =
                                                     ('i'::('d'::[])); attrType = id } :: []))))),
                                                     { bindex = ('l'::('i'::('n'::('e'::[]))));
                                                     indexb =
                                                     (indexBound_tail ('l'::('i'::('n'::('e'::[]))))
                                                       { attrName = ('i'::('s'::('R'::('q'::[]))));
                                                       attrType = Bool }.attrName ({ attrName =
                                                       ('a'::('d'::('d'::('r'::[])))); attrType =
                                                       (tagIdx idxBits tagBits) }.attrName :: ({ attrName =
                                                       ('t'::('o'::[])); attrType =
                                                       msi }.attrName :: ({ attrName =
                                                       ('l'::('i'::('n'::('e'::[])))); attrType =
                                                       (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                       ('i'::('d'::[])); attrType =
                                                       id }.attrName :: []))))
                                                       (indexBound_tail
                                                         ('l'::('i'::('n'::('e'::[])))) { attrName =
                                                         ('a'::('d'::('d'::('r'::[])))); attrType =
                                                         (tagIdx idxBits tagBits) }.attrName
                                                         ({ attrName = ('t'::('o'::[])); attrType =
                                                         msi }.attrName :: ({ attrName =
                                                         ('l'::('i'::('n'::('e'::[])))); attrType =
                                                         (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                         ('i'::('d'::[])); attrType =
                                                         id }.attrName :: [])))
                                                         (indexBound_tail
                                                           ('l'::('i'::('n'::('e'::[]))))
                                                           { attrName = ('t'::('o'::[])); attrType =
                                                           msi }.attrName ({ attrName =
                                                           ('l'::('i'::('n'::('e'::[]))));
                                                           attrType =
                                                           (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                           ('i'::('d'::[])); attrType =
                                                           id }.attrName :: []))
                                                           (indexBound_head { attrName =
                                                             ('l'::('i'::('n'::('e'::[]))));
                                                             attrType =
                                                             (line lgDataBytes lgNumDatas) }.attrName
                                                             ({ attrName = ('i'::('d'::[]));
                                                             attrType = id }.attrName :: []))))) },
                                                     (Var ((SyntaxKind
                                                     (fromPPop idxBits tagBits lgNumDatas
                                                       lgDataBytes id).attrType.ret), fromP3))))))) :: [])),
    (icons' (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx idxBits) }, (Var
      ((SyntaxKind (idx idxBits)), idx1))))
      ((projT1 (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
         (getAttrType ({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
           Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
           (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType =
           msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
           (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
           id } :: []))))) { bindex = ('l'::('i'::('n'::('e'::[])))); indexb =
           (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName =
             ('i'::('s'::('R'::('q'::[])))); attrType = Bool }.attrName ({ attrName =
             ('a'::('d'::('d'::('r'::[])))); attrType =
             (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
             msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
             (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
             id }.attrName :: []))))
             (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName =
               ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) }.attrName
               ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
               ('l'::('i'::('n'::('e'::[])))); attrType =
               (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[]));
               attrType = id }.attrName :: [])))
               (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName = ('t'::('o'::[]));
                 attrType = msi }.attrName ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
                 (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[]));
                 attrType = id }.attrName :: []))
                 (indexBound_head { attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
                   (line lgDataBytes lgNumDatas) }.attrName ({ attrName = ('i'::('d'::[]));
                   attrType = id }.attrName :: []))))) }) }, (ReadField (({ attrName =
         ('i'::('s'::('R'::('q'::[])))); attrType = Bool } :: ({ attrName =
         ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) } :: ({ attrName =
         ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[]))));
         attrType = (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
         id } :: []))))), { bindex = ('l'::('i'::('n'::('e'::[])))); indexb =
         (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName =
           ('i'::('s'::('R'::('q'::[])))); attrType = Bool }.attrName ({ attrName =
           ('a'::('d'::('d'::('r'::[])))); attrType =
           (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
           msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
           (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
           id }.attrName :: []))))
           (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName =
             ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) }.attrName
             ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
             ('l'::('i'::('n'::('e'::[])))); attrType =
             (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
             id }.attrName :: [])))
             (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName = ('t'::('o'::[]));
               attrType = msi }.attrName ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
               (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[]));
               attrType = id }.attrName :: []))
               (indexBound_head { attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
                 (line lgDataBytes lgNumDatas) }.attrName ({ attrName = ('i'::('d'::[])); attrType =
                 id }.attrName :: []))))) }, (Var ((SyntaxKind
         (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3))))))) :: [])
      (icons' (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (getAttrType ({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
          Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType =
          msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
          id } :: []))))) { bindex = ('l'::('i'::('n'::('e'::[])))); indexb =
          (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName =
            ('i'::('s'::('R'::('q'::[])))); attrType = Bool }.attrName ({ attrName =
            ('a'::('d'::('d'::('r'::[])))); attrType =
            (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
            msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
            (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
            id }.attrName :: []))))
            (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName =
              ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) }.attrName
              ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
              ('l'::('i'::('n'::('e'::[])))); attrType =
              (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
              id }.attrName :: [])))
              (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName = ('t'::('o'::[]));
                attrType = msi }.attrName ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
                (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[]));
                attrType = id }.attrName :: []))
                (indexBound_head { attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
                  (line lgDataBytes lgNumDatas) }.attrName ({ attrName = ('i'::('d'::[]));
                  attrType = id }.attrName :: []))))) }) }, (ReadField (({ attrName =
        ('i'::('s'::('R'::('q'::[])))); attrType = Bool } :: ({ attrName =
        ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) } :: ({ attrName =
        ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[]))));
        attrType = (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
        id } :: []))))), { bindex = ('l'::('i'::('n'::('e'::[])))); indexb =
        (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName = ('i'::('s'::('R'::('q'::[]))));
          attrType = Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
          id }.attrName :: []))))
          (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName =
            ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) }.attrName
            ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
            ('l'::('i'::('n'::('e'::[])))); attrType =
            (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
            id }.attrName :: [])))
            (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName = ('t'::('o'::[]));
              attrType = msi }.attrName ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
              (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
              id }.attrName :: []))
              (indexBound_head { attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
                (line lgDataBytes lgNumDatas) }.attrName ({ attrName = ('i'::('d'::[])); attrType =
                id }.attrName :: []))))) }, (Var ((SyntaxKind
        (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3)))))) [] Inil)))),
    (fun x1 -> SReturn (Const (void, (getDefaultConst void)))))), (SReturn (Const (void,
    (getDefaultConst void)))), (fun x1 -> SReturn (Const (void,
    (getDefaultConst void)))))))))))))))))))); ruleName = { nameVal =
    ('u'::('p'::('g'::('R'::('s'::[]))))) } }), (ConsInSinModule ((SMERule { ruleGen = (fun _ ->
    SReadReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[]))))))))))) }, (SyntaxKind
    Bool), (fun valid -> SAssert_ ((Var ((SyntaxKind Bool), valid)), (SReadReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('R'::('e'::('p'::('l'::('a'::('c'::('e'::[]))))))))))))) },
    (SyntaxKind Bool), (fun replace -> SAssert_ ((UniBool (Neg, (Var ((SyntaxKind Bool),
    replace)))), (SReadReg ({ nameVal = ('p'::('r'::('o'::('c'::('R'::('q'::[])))))) }, (SyntaxKind
    (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), (fun rq -> SAssert_ ((UniBool (Neg,
    (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
    (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
    memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
    (data lgDataBytes) } :: []))), { bindex = ('o'::('p'::[])); indexb =
    (indexBound_tail ('o'::('p'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
      memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) }.attrName :: []))
      (indexBound_head { attrName = ('o'::('p'::[])); attrType = memOp }.attrName ({ attrName =
        ('d'::('a'::('t'::('a'::[])))); attrType = (data lgDataBytes) }.attrName :: []))) }, (Var
    ((SyntaxKind (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), rq)))))), (SLet_
    ((SyntaxKind (idx idxBits)),
    (getIdx idxBits tagBits lgNumDatas (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[]))));
      attrType = (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
      memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) } :: []))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
        memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data lgDataBytes) }.attrName :: []))) }, (Var ((SyntaxKind
      (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), rq))))), (fun idx1 -> SMCall
    ({ nameVal = (readCs idxBits).attrName }, (readCs idxBits).attrType, (Var ((SyntaxKind
    (idx idxBits)), idx1)), (fun cs -> SAssert_ ((UniBool (Neg, (BinBitBool ((Pervasives.succ
    (Pervasives.succ 0)), (Pervasives.succ (Pervasives.succ 0)), (Lt (Pervasives.succ
    (Pervasives.succ 0))), (Var ((SyntaxKind (readCs idxBits).attrType.ret), cs)), (Const ((Bit
    (Pervasives.succ (Pervasives.succ 0))), (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) sh))))))))), (SMCall ({ nameVal =
    (readLine idxBits lgNumDatas lgDataBytes).attrName },
    (readLine idxBits lgNumDatas lgDataBytes).attrType, (Var ((SyntaxKind (idx idxBits)), idx1)),
    (fun line2 -> SWriteReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[]))))))))))) }, (SyntaxKind
    Bool), (Const (Bool, (ConstBool false))), (SMCall ({ nameVal =
    (rsToProcEnq lgDataBytes).attrName }, (rsToProcEnq lgDataBytes).attrType, (BuildStruct
    (((projT1 (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data0 lgDataBytes) }, (ReadIndex (lgNumDatas, (data0 lgDataBytes),
        (getOffset idxBits tagBits lgNumDatas (ReadField (({ attrName =
          ('a'::('d'::('d'::('r'::[])))); attrType =
          (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
          memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
          (data lgDataBytes) } :: []))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
          (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
            (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
            memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
            (data lgDataBytes) }.attrName :: []))) }, (Var ((SyntaxKind
          (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), rq))))), (Var ((SyntaxKind
        (readLine idxBits lgNumDatas lgDataBytes).attrType.ret), line2))))))) :: []),
    (icons' (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType = (data0 lgDataBytes) },
      (ReadIndex (lgNumDatas, (data0 lgDataBytes),
      (getOffset idxBits tagBits lgNumDatas (ReadField (({ attrName =
        ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
        memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data lgDataBytes) } :: []))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
        (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
          memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
          (data lgDataBytes) }.attrName :: []))) }, (Var ((SyntaxKind
        (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), rq))))), (Var ((SyntaxKind
      (readLine idxBits lgNumDatas lgDataBytes).attrType.ret), line2)))))) [] Inil))), (fun x ->
    SMCall ({ nameVal = (rqFromProcPop idxBits tagBits lgNumDatas lgDataBytes).attrName },
    (rqFromProcPop idxBits tagBits lgNumDatas lgDataBytes).attrType, (Const
    ((rqFromProcPop idxBits tagBits lgNumDatas lgDataBytes).attrType.arg,
    (getDefaultConst (rqFromProcPop idxBits tagBits lgNumDatas lgDataBytes).attrType.arg))),
    (fun rq' -> SAssert_ ((Eq ((rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes), (Var
    ((SyntaxKind (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), rq)), (Var ((SyntaxKind
    (rqFromProcPop idxBits tagBits lgNumDatas lgDataBytes).attrType.ret), rq')))), (SReturn (Const
    (void, (getDefaultConst void)))))))))))))))))))))))))))))))); ruleName = { nameVal =
    ('l'::('d'::[])) } }), (ConsInSinModule ((SMERule { ruleGen = (fun _ -> SReadReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[]))))))))))) }, (SyntaxKind
    Bool), (fun valid -> SAssert_ ((Var ((SyntaxKind Bool), valid)), (SReadReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('R'::('e'::('p'::('l'::('a'::('c'::('e'::[]))))))))))))) },
    (SyntaxKind Bool), (fun replace -> SAssert_ ((UniBool (Neg, (Var ((SyntaxKind Bool),
    replace)))), (SReadReg ({ nameVal = ('p'::('r'::('o'::('c'::('R'::('q'::[])))))) }, (SyntaxKind
    (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), (fun rq -> SAssert_ ((ReadField
    (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
    (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
    memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
    (data lgDataBytes) } :: []))), { bindex = ('o'::('p'::[])); indexb =
    (indexBound_tail ('o'::('p'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
      memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) }.attrName :: []))
      (indexBound_head { attrName = ('o'::('p'::[])); attrType = memOp }.attrName ({ attrName =
        ('d'::('a'::('t'::('a'::[])))); attrType = (data lgDataBytes) }.attrName :: []))) }, (Var
    ((SyntaxKind (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), rq)))), (SLet_ ((SyntaxKind
    (idx idxBits)),
    (getIdx idxBits tagBits lgNumDatas (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[]))));
      attrType = (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
      memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) } :: []))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
        memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data lgDataBytes) }.attrName :: []))) }, (Var ((SyntaxKind
      (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), rq))))), (fun idx1 -> SMCall
    ({ nameVal = (readCs idxBits).attrName }, (readCs idxBits).attrType, (Var ((SyntaxKind
    (idx idxBits)), idx1)), (fun cs -> SAssert_ ((Eq ((readCs idxBits).attrType.ret, (Var
    ((SyntaxKind (readCs idxBits).attrType.ret), cs)), (Const ((Bit (Pervasives.succ
    (Pervasives.succ 0))), (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) mod0))))))), (SMCall ({ nameVal =
    (readLine idxBits lgNumDatas lgDataBytes).attrName },
    (readLine idxBits lgNumDatas lgDataBytes).attrType, (Var ((SyntaxKind (idx idxBits)), idx1)),
    (fun line2 -> SWriteReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[]))))))))))) }, (SyntaxKind
    Bool), (Const (Bool, (ConstBool false))), (SLet_ ((SyntaxKind (offset lgNumDatas)),
    (getOffset idxBits tagBits lgNumDatas (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[]))));
      attrType = (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
      memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) } :: []))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
        memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data lgDataBytes) }.attrName :: []))) }, (Var ((SyntaxKind
      (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), rq))))), (fun offset0 -> SMCall
    ({ nameVal = (rsToProcEnq lgDataBytes).attrName }, (rsToProcEnq lgDataBytes).attrType,
    (BuildStruct
    (((projT1 (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType = (data lgDataBytes) },
        (Const ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data lgDataBytes) }.attrType,
        (getDefaultConst { attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
          (data lgDataBytes) }.attrType)))))) :: []),
    (icons' (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType = (data lgDataBytes) },
      (Const ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType = (data lgDataBytes) }.attrType,
      (getDefaultConst { attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data lgDataBytes) }.attrType))))) [] Inil))), (fun x -> SMCall ({ nameVal =
    (writeLine idxBits lgNumDatas lgDataBytes).attrName },
    (writeLine idxBits lgNumDatas lgDataBytes).attrType, (BuildStruct
    (((projT1 (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx idxBits) }, (Var
        ((SyntaxKind (idx idxBits)), idx1))))) :: ((projT1 (ExistT ({ attrName =
                                                     ('d'::('a'::('t'::('a'::[])))); attrType =
                                                     (Vector ((data0 lgDataBytes), lgNumDatas)) },
                                                     (UpdateVector (lgNumDatas, (data0 lgDataBytes),
                                                     (Var ((SyntaxKind
                                                     (readLine idxBits lgNumDatas lgDataBytes).attrType.ret),
                                                     line2)), (Var ((SyntaxKind
                                                     (offset lgNumDatas)), offset0)), (ReadField
                                                     (({ attrName = ('a'::('d'::('d'::('r'::[]))));
                                                     attrType =
                                                     (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName =
                                                     ('o'::('p'::[])); attrType =
                                                     memOp } :: ({ attrName =
                                                     ('d'::('a'::('t'::('a'::[])))); attrType =
                                                     (data lgDataBytes) } :: []))), { bindex =
                                                     ('d'::('a'::('t'::('a'::[])))); indexb =
                                                     (indexBound_tail ('d'::('a'::('t'::('a'::[]))))
                                                       { attrName = ('a'::('d'::('d'::('r'::[]))));
                                                       attrType =
                                                       (addr0 idxBits tagBits lgNumDatas) }.attrName
                                                       ({ attrName = ('o'::('p'::[])); attrType =
                                                       memOp }.attrName :: ({ attrName =
                                                       ('d'::('a'::('t'::('a'::[])))); attrType =
                                                       (data lgDataBytes) }.attrName :: []))
                                                       (indexBound_tail
                                                         ('d'::('a'::('t'::('a'::[])))) { attrName =
                                                         ('o'::('p'::[])); attrType =
                                                         memOp }.attrName ({ attrName =
                                                         ('d'::('a'::('t'::('a'::[])))); attrType =
                                                         (data lgDataBytes) }.attrName :: [])
                                                         (indexBound_head { attrName =
                                                           ('d'::('a'::('t'::('a'::[]))));
                                                           attrType = (data lgDataBytes) }.attrName
                                                           []))) }, (Var ((SyntaxKind
                                                     (rqFromProc0 idxBits tagBits lgNumDatas
                                                       lgDataBytes)), rq))))))))) :: [])),
    (icons' (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx idxBits) }, (Var
      ((SyntaxKind (idx idxBits)), idx1))))
      ((projT1 (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType = (Vector
         ((data0 lgDataBytes), lgNumDatas)) }, (UpdateVector (lgNumDatas, (data0 lgDataBytes), (Var
         ((SyntaxKind (readLine idxBits lgNumDatas lgDataBytes).attrType.ret), line2)), (Var
         ((SyntaxKind (offset lgNumDatas)), offset0)), (ReadField (({ attrName =
         ('a'::('d'::('d'::('r'::[])))); attrType =
         (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
         memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
         (data lgDataBytes) } :: []))), { bindex = ('d'::('a'::('t'::('a'::[])))); indexb =
         (indexBound_tail ('d'::('a'::('t'::('a'::[])))) { attrName =
           ('a'::('d'::('d'::('r'::[])))); attrType = (addr0 idxBits tagBits lgNumDatas) }.attrName
           ({ attrName = ('o'::('p'::[])); attrType = memOp }.attrName :: ({ attrName =
           ('d'::('a'::('t'::('a'::[])))); attrType = (data lgDataBytes) }.attrName :: []))
           (indexBound_tail ('d'::('a'::('t'::('a'::[])))) { attrName = ('o'::('p'::[])); attrType =
             memOp }.attrName ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
             (data lgDataBytes) }.attrName :: [])
             (indexBound_head { attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
               (data lgDataBytes) }.attrName []))) }, (Var ((SyntaxKind
         (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), rq))))))))) :: [])
      (icons' (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType = (Vector
        ((data0 lgDataBytes), lgNumDatas)) }, (UpdateVector (lgNumDatas, (data0 lgDataBytes), (Var
        ((SyntaxKind (readLine idxBits lgNumDatas lgDataBytes).attrType.ret), line2)), (Var
        ((SyntaxKind (offset lgNumDatas)), offset0)), (ReadField (({ attrName =
        ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
        memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data lgDataBytes) } :: []))), { bindex = ('d'::('a'::('t'::('a'::[])))); indexb =
        (indexBound_tail ('d'::('a'::('t'::('a'::[])))) { attrName = ('a'::('d'::('d'::('r'::[]))));
          attrType = (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[]));
          attrType = memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
          (data lgDataBytes) }.attrName :: []))
          (indexBound_tail ('d'::('a'::('t'::('a'::[])))) { attrName = ('o'::('p'::[])); attrType =
            memOp }.attrName ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
            (data lgDataBytes) }.attrName :: [])
            (indexBound_head { attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
              (data lgDataBytes) }.attrName []))) }, (Var ((SyntaxKind
        (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), rq)))))))) [] Inil)))), (fun x0 ->
    SMCall ({ nameVal = (rqFromProcPop idxBits tagBits lgNumDatas lgDataBytes).attrName },
    (rqFromProcPop idxBits tagBits lgNumDatas lgDataBytes).attrType, (Const
    ((rqFromProcPop idxBits tagBits lgNumDatas lgDataBytes).attrType.arg,
    (getDefaultConst (rqFromProcPop idxBits tagBits lgNumDatas lgDataBytes).attrType.arg))),
    (fun rq' -> SAssert_ ((Eq ((rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes), (Var
    ((SyntaxKind (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), rq)), (Var ((SyntaxKind
    (rqFromProcPop idxBits tagBits lgNumDatas lgDataBytes).attrType.ret), rq')))), (SReturn (Const
    (void, (getDefaultConst void)))))))))))))))))))))))))))))))))))); ruleName = { nameVal =
    ('s'::('t'::[])) } }), (ConsInSinModule ((SMERule { ruleGen = (fun _ -> SMCall ({ nameVal =
    (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrName },
    (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType, (Const
    ((fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.arg,
    (getDefaultConst (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.arg))),
    (fun fromP3 -> SAssert_ ((ReadField (({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
    Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
    (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
    ('l'::('i'::('n'::('e'::[])))); attrType = (line lgDataBytes lgNumDatas) } :: ({ attrName =
    ('i'::('d'::[])); attrType = id } :: []))))), { bindex = ('i'::('s'::('R'::('q'::[]))));
    indexb =
    (indexBound_head { attrName = ('i'::('s'::('R'::('q'::[])))); attrType = Bool }.attrName
      ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
      msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
      (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
      id }.attrName :: []))))) }, (Var ((SyntaxKind
    (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3)))), (SLet_
    ((SyntaxKind (idx idxBits)),
    (getIdxFromTagIdx idxBits tagBits (ReadField (({ attrName = ('i'::('s'::('R'::('q'::[]))));
      attrType = Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType =
      msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
      (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: []))))),
      { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_tail ('a'::('d'::('d'::('r'::[])))) { attrName = ('i'::('s'::('R'::('q'::[]))));
        attrType = Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
        msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
        (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
        id }.attrName :: []))))
        (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
          id }.attrName :: []))))) }, (Var ((SyntaxKind
      (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3))))), (fun idx1 ->
    SMCall ({ nameVal = (readCs idxBits).attrName }, (readCs idxBits).attrType, (Var ((SyntaxKind
    (idx idxBits)), idx1)), (fun cs -> SMCall ({ nameVal = (readTag idxBits tagBits).attrName },
    (readTag idxBits tagBits).attrType, (Var ((SyntaxKind (idx idxBits)), idx1)), (fun tag0 ->
    SAssert_ ((BinBool (Or, (UniBool (Neg, (BinBitBool ((Pervasives.succ (Pervasives.succ 0)),
    (Pervasives.succ (Pervasives.succ 0)), (Lt (Pervasives.succ (Pervasives.succ 0))), (ReadField
    (({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType = Bool } :: ({ attrName =
    ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) } :: ({ attrName =
    ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
    (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: []))))),
    { bindex = ('t'::('o'::[])); indexb =
    (indexBound_tail ('t'::('o'::[])) { attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
      Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
      msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
      (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
      id }.attrName :: []))))
      (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
        msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
        (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
        id }.attrName :: [])))
        (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName ({ attrName =
          ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
          id }.attrName :: []))))) }, (Var ((SyntaxKind
    (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3)))), (Var
    ((SyntaxKind (readCs idxBits).attrType.ret), cs)))))), (UniBool (Neg, (Eq
    ((readTag idxBits tagBits).attrType.ret, (Var ((SyntaxKind
    (readTag idxBits tagBits).attrType.ret), tag0)),
    (getTagFromTagIdx idxBits tagBits (ReadField (({ attrName = ('i'::('s'::('R'::('q'::[]))));
      attrType = Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType =
      msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
      (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: []))))),
      { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_tail ('a'::('d'::('d'::('r'::[])))) { attrName = ('i'::('s'::('R'::('q'::[]))));
        attrType = Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
        msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
        (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
        id }.attrName :: []))))
        (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
          id }.attrName :: []))))) }, (Var ((SyntaxKind
      (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3))))))))))),
    (SReturn (Const (void, (getDefaultConst void)))))))))))))))); ruleName = { nameVal =
    ('d'::('r'::('o'::('p'::[])))) } }), (ConsInSinModule ((SMERule { ruleGen = (fun _ -> SMCall
    ({ nameVal = (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrName },
    (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType, (Const
    ((fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.arg,
    (getDefaultConst (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.arg))),
    (fun fromP3 -> SAssert_ ((ReadField (({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
    Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
    (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
    ('l'::('i'::('n'::('e'::[])))); attrType = (line lgDataBytes lgNumDatas) } :: ({ attrName =
    ('i'::('d'::[])); attrType = id } :: []))))), { bindex = ('i'::('s'::('R'::('q'::[]))));
    indexb =
    (indexBound_head { attrName = ('i'::('s'::('R'::('q'::[])))); attrType = Bool }.attrName
      ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
      msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
      (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
      id }.attrName :: []))))) }, (Var ((SyntaxKind
    (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3)))), (SLet_
    ((SyntaxKind (idx idxBits)),
    (getIdxFromTagIdx idxBits tagBits (ReadField (({ attrName = ('i'::('s'::('R'::('q'::[]))));
      attrType = Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType =
      msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
      (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: []))))),
      { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_tail ('a'::('d'::('d'::('r'::[])))) { attrName = ('i'::('s'::('R'::('q'::[]))));
        attrType = Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
        msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
        (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
        id }.attrName :: []))))
        (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
          id }.attrName :: []))))) }, (Var ((SyntaxKind
      (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3))))), (fun idx1 ->
    SMCall ({ nameVal = (readCs idxBits).attrName }, (readCs idxBits).attrType, (Var ((SyntaxKind
    (idx idxBits)), idx1)), (fun cs -> SMCall ({ nameVal = (readTag idxBits tagBits).attrName },
    (readTag idxBits tagBits).attrType, (Var ((SyntaxKind (idx idxBits)), idx1)), (fun tag0 ->
    SMCall ({ nameVal = (readLine idxBits lgNumDatas lgDataBytes).attrName },
    (readLine idxBits lgNumDatas lgDataBytes).attrType, (Var ((SyntaxKind (idx idxBits)), idx1)),
    (fun line2 -> SAssert_ ((BinBool (And, (BinBitBool ((Pervasives.succ (Pervasives.succ 0)),
    (Pervasives.succ (Pervasives.succ 0)), (Lt (Pervasives.succ (Pervasives.succ 0))), (ReadField
    (({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType = Bool } :: ({ attrName =
    ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) } :: ({ attrName =
    ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
    (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: []))))),
    { bindex = ('t'::('o'::[])); indexb =
    (indexBound_tail ('t'::('o'::[])) { attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
      Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
      msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
      (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
      id }.attrName :: []))))
      (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
        msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
        (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
        id }.attrName :: [])))
        (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName ({ attrName =
          ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
          id }.attrName :: []))))) }, (Var ((SyntaxKind
    (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3)))), (Var
    ((SyntaxKind (readCs idxBits).attrType.ret), cs)))), (Eq
    ((readTag idxBits tagBits).attrType.ret, (Var ((SyntaxKind
    (readTag idxBits tagBits).attrType.ret), tag0)),
    (getTagFromTagIdx idxBits tagBits (ReadField (({ attrName = ('i'::('s'::('R'::('q'::[]))));
      attrType = Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType =
      msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
      (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: []))))),
      { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_tail ('a'::('d'::('d'::('r'::[])))) { attrName = ('i'::('s'::('R'::('q'::[]))));
        attrType = Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
        msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
        (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
        id }.attrName :: []))))
        (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
          id }.attrName :: []))))) }, (Var ((SyntaxKind
      (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3))))))))), (SReadReg
    ({ nameVal = ('p'::('r'::('o'::('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[]))))))))))) },
    (SyntaxKind Bool), (fun valid -> SReadReg ({ nameVal =
    ('p'::('r'::('o'::('c'::('R'::('q'::('W'::('a'::('i'::('t'::[])))))))))) }, (SyntaxKind Bool),
    (fun wait -> SReadReg ({ nameVal = ('p'::('r'::('o'::('c'::('R'::('q'::[])))))) }, (SyntaxKind
    (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), (fun procRq -> SAssert_ ((UniBool (Neg,
    (BinBool (And, (BinBool (And, (BinBool (And, (Var ((SyntaxKind Bool), valid)), (UniBool (Neg,
    (Var ((SyntaxKind Bool), wait)))))), (Eq ((tagIdx idxBits tagBits),
    (getTagIdx idxBits tagBits lgNumDatas (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[]))));
      attrType = (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
      memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) } :: []))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
        memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (data lgDataBytes) }.attrName :: []))) }, (Var ((SyntaxKind
      (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), procRq))))), (ReadField (({ attrName =
    ('i'::('s'::('R'::('q'::[])))); attrType = Bool } :: ({ attrName =
    ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) } :: ({ attrName =
    ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
    (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: []))))),
    { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
    (indexBound_tail ('a'::('d'::('d'::('r'::[])))) { attrName = ('i'::('s'::('R'::('q'::[]))));
      attrType = Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
      msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
      (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
      id }.attrName :: []))))
      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
        msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
        (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
        id }.attrName :: []))))) }, (Var ((SyntaxKind
    (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3)))))))), (BinBool
    (Or, (BinBool (And, (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
    (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
    memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
    (data lgDataBytes) } :: []))), { bindex = ('o'::('p'::[])); indexb =
    (indexBound_tail ('o'::('p'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
      memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) }.attrName :: []))
      (indexBound_head { attrName = ('o'::('p'::[])); attrType = memOp }.attrName ({ attrName =
        ('d'::('a'::('t'::('a'::[])))); attrType = (data lgDataBytes) }.attrName :: []))) }, (Var
    ((SyntaxKind (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), procRq)))), (Eq
    ((readCs idxBits).attrType.ret, (Var ((SyntaxKind (readCs idxBits).attrType.ret), cs)), (Const
    ((Bit (Pervasives.succ (Pervasives.succ 0))), (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) mod0))))))))), (BinBool (And, (UniBool (Neg,
    (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
    (addr0 idxBits tagBits lgNumDatas) } :: ({ attrName = ('o'::('p'::[])); attrType =
    memOp } :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
    (data lgDataBytes) } :: []))), { bindex = ('o'::('p'::[])); indexb =
    (indexBound_tail ('o'::('p'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (addr0 idxBits tagBits lgNumDatas) }.attrName ({ attrName = ('o'::('p'::[])); attrType =
      memOp }.attrName :: ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
      (data lgDataBytes) }.attrName :: []))
      (indexBound_head { attrName = ('o'::('p'::[])); attrType = memOp }.attrName ({ attrName =
        ('d'::('a'::('t'::('a'::[])))); attrType = (data lgDataBytes) }.attrName :: []))) }, (Var
    ((SyntaxKind (rqFromProc0 idxBits tagBits lgNumDatas lgDataBytes)), procRq)))))), (Eq
    ((readCs idxBits).attrType.ret, (Var ((SyntaxKind (readCs idxBits).attrType.ret), cs)), (Const
    ((Bit (Pervasives.succ (Pervasives.succ 0))), (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) sh))))))))))))))), (SMCall ({ nameVal =
    (rsToPEnq idxBits tagBits lgNumDatas lgDataBytes).attrName },
    (rsToPEnq idxBits tagBits lgNumDatas lgDataBytes).attrType, (BuildStruct
    (((projT1 (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (getAttrType ({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
          Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType =
          msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
          id } :: []))))) { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
          (indexBound_tail ('a'::('d'::('d'::('r'::[])))) { attrName =
            ('i'::('s'::('R'::('q'::[])))); attrType = Bool }.attrName ({ attrName =
            ('a'::('d'::('d'::('r'::[])))); attrType =
            (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
            msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
            (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
            id }.attrName :: []))))
            (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
              (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
              msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
              (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
              id }.attrName :: []))))) }) }, (ReadField (({ attrName =
        ('i'::('s'::('R'::('q'::[])))); attrType = Bool } :: ({ attrName =
        ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) } :: ({ attrName =
        ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[]))));
        attrType = (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
        id } :: []))))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
        (indexBound_tail ('a'::('d'::('d'::('r'::[])))) { attrName = ('i'::('s'::('R'::('q'::[]))));
          attrType = Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
          id }.attrName :: []))))
          (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
            (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
            msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
            (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
            id }.attrName :: []))))) }, (Var ((SyntaxKind
        (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3))))))) :: (
    (projT1 (ExistT ({ attrName = ('t'::('o'::[])); attrType =
      (getAttrType ({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType = Bool } :: ({ attrName =
        ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) } :: ({ attrName =
        ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[]))));
        attrType = (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
        id } :: []))))) { bindex = ('t'::('o'::[])); indexb =
        (indexBound_tail ('t'::('o'::[])) { attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
          Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
          id }.attrName :: []))))
          (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
            (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
            msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
            (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
            id }.attrName :: [])))
            (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName ({ attrName =
              ('l'::('i'::('n'::('e'::[])))); attrType =
              (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
              id }.attrName :: []))))) }) }, (ReadField (({ attrName =
      ('i'::('s'::('R'::('q'::[])))); attrType = Bool } :: ({ attrName =
      ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) } :: ({ attrName =
      ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
      (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: []))))),
      { bindex = ('t'::('o'::[])); indexb =
      (indexBound_tail ('t'::('o'::[])) { attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
        Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
        msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
        (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
        id }.attrName :: []))))
        (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
          id }.attrName :: [])))
          (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName ({ attrName =
            ('l'::('i'::('n'::('e'::[])))); attrType =
            (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
            id }.attrName :: []))))) }, (Var ((SyntaxKind
      (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3))))))) :: (
    (projT1 (ExistT ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
      (readLine idxBits lgNumDatas lgDataBytes).attrType.ret }, (Var ((SyntaxKind
      (readLine idxBits lgNumDatas lgDataBytes).attrType.ret), line2))))) :: ((projT1 (ExistT
                                                                                ({ attrName =
                                                                                ('i'::('s'::('V'::('o'::('l'::[])))));
                                                                                attrType = Bool },
                                                                                (Const (Bool,
                                                                                (ConstBool
                                                                                false)))))) :: [])))),
    (icons' (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (getAttrType ({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType = Bool } :: ({ attrName =
        ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) } :: ({ attrName =
        ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[]))));
        attrType = (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
        id } :: []))))) { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
        (indexBound_tail ('a'::('d'::('d'::('r'::[])))) { attrName = ('i'::('s'::('R'::('q'::[]))));
          attrType = Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
          id }.attrName :: []))))
          (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
            (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
            msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
            (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
            id }.attrName :: []))))) }) }, (ReadField (({ attrName = ('i'::('s'::('R'::('q'::[]))));
      attrType = Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType =
      msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
      (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: []))))),
      { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_tail ('a'::('d'::('d'::('r'::[])))) { attrName = ('i'::('s'::('R'::('q'::[]))));
        attrType = Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
        msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
        (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
        id }.attrName :: []))))
        (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
          id }.attrName :: []))))) }, (Var ((SyntaxKind
      (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3))))))
      ((projT1 (ExistT ({ attrName = ('t'::('o'::[])); attrType =
         (getAttrType ({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
           Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
           (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType =
           msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
           (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
           id } :: []))))) { bindex = ('t'::('o'::[])); indexb =
           (indexBound_tail ('t'::('o'::[])) { attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
             Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
             (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
             msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
             (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
             id }.attrName :: []))))
             (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[]))));
               attrType = (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[]));
               attrType = msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
               (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[]));
               attrType = id }.attrName :: [])))
               (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName
                 ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
                 (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[]));
                 attrType = id }.attrName :: []))))) }) }, (ReadField (({ attrName =
         ('i'::('s'::('R'::('q'::[])))); attrType = Bool } :: ({ attrName =
         ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) } :: ({ attrName =
         ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[]))));
         attrType = (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
         id } :: []))))), { bindex = ('t'::('o'::[])); indexb =
         (indexBound_tail ('t'::('o'::[])) { attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
           Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
           (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
           msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
           (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
           id }.attrName :: []))))
           (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
             (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
             msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
             (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
             id }.attrName :: [])))
             (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName ({ attrName =
               ('l'::('i'::('n'::('e'::[])))); attrType =
               (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[]));
               attrType = id }.attrName :: []))))) }, (Var ((SyntaxKind
         (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3))))))) :: (
      (projT1 (ExistT ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
        (readLine idxBits lgNumDatas lgDataBytes).attrType.ret }, (Var ((SyntaxKind
        (readLine idxBits lgNumDatas lgDataBytes).attrType.ret), line2))))) :: ((projT1 (ExistT
                                                                                  ({ attrName =
                                                                                  ('i'::('s'::('V'::('o'::('l'::[])))));
                                                                                  attrType = Bool },
                                                                                  (Const (Bool,
                                                                                  (ConstBool
                                                                                  false)))))) :: [])))
      (icons' (ExistT ({ attrName = ('t'::('o'::[])); attrType =
        (getAttrType ({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
          Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType =
          msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
          id } :: []))))) { bindex = ('t'::('o'::[])); indexb =
          (indexBound_tail ('t'::('o'::[])) { attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
            Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
            (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
            msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
            (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
            id }.attrName :: []))))
            (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[]))));
              attrType = (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[]));
              attrType = msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
              (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
              id }.attrName :: [])))
              (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName
                ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
                (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[]));
                attrType = id }.attrName :: []))))) }) }, (ReadField (({ attrName =
        ('i'::('s'::('R'::('q'::[])))); attrType = Bool } :: ({ attrName =
        ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) } :: ({ attrName =
        ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[]))));
        attrType = (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
        id } :: []))))), { bindex = ('t'::('o'::[])); indexb =
        (indexBound_tail ('t'::('o'::[])) { attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
          Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
          id }.attrName :: []))))
          (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
            (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
            msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
            (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
            id }.attrName :: [])))
            (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName ({ attrName =
              ('l'::('i'::('n'::('e'::[])))); attrType =
              (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
              id }.attrName :: []))))) }, (Var ((SyntaxKind
        (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3))))))
        ((projT1 (ExistT ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
           (readLine idxBits lgNumDatas lgDataBytes).attrType.ret }, (Var ((SyntaxKind
           (readLine idxBits lgNumDatas lgDataBytes).attrType.ret), line2))))) :: ((projT1 (ExistT
                                                                                     ({ attrName =
                                                                                     ('i'::('s'::('V'::('o'::('l'::[])))));
                                                                                     attrType =
                                                                                     Bool }, (Const
                                                                                     (Bool,
                                                                                     (ConstBool
                                                                                     false)))))) :: []))
        (icons' (ExistT ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (readLine idxBits lgNumDatas lgDataBytes).attrType.ret }, (Var ((SyntaxKind
          (readLine idxBits lgNumDatas lgDataBytes).attrType.ret), line2))))
          ((projT1 (ExistT ({ attrName = ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool },
             (Const (Bool, (ConstBool false)))))) :: [])
          (icons' (ExistT ({ attrName = ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool },
            (Const (Bool, (ConstBool false))))) [] Inil)))))), (fun x -> SMCall ({ nameVal =
    (writeCs idxBits).attrName }, (writeCs idxBits).attrType, (BuildStruct
    (((projT1 (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx idxBits) }, (Var
        ((SyntaxKind (idx idxBits)), idx1))))) :: ((projT1 (ExistT ({ attrName =
                                                     ('d'::('a'::('t'::('a'::[])))); attrType =
                                                     (getAttrType ({ attrName =
                                                       ('i'::('s'::('R'::('q'::[])))); attrType =
                                                       Bool } :: ({ attrName =
                                                       ('a'::('d'::('d'::('r'::[])))); attrType =
                                                       (tagIdx idxBits tagBits) } :: ({ attrName =
                                                       ('t'::('o'::[])); attrType =
                                                       msi } :: ({ attrName =
                                                       ('l'::('i'::('n'::('e'::[])))); attrType =
                                                       (line lgDataBytes lgNumDatas) } :: ({ attrName =
                                                       ('i'::('d'::[])); attrType = id } :: [])))))
                                                       { bindex = ('t'::('o'::[])); indexb =
                                                       (indexBound_tail ('t'::('o'::[]))
                                                         { attrName =
                                                         ('i'::('s'::('R'::('q'::[])))); attrType =
                                                         Bool }.attrName ({ attrName =
                                                         ('a'::('d'::('d'::('r'::[])))); attrType =
                                                         (tagIdx idxBits tagBits) }.attrName :: ({ attrName =
                                                         ('t'::('o'::[])); attrType =
                                                         msi }.attrName :: ({ attrName =
                                                         ('l'::('i'::('n'::('e'::[])))); attrType =
                                                         (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                         ('i'::('d'::[])); attrType =
                                                         id }.attrName :: []))))
                                                         (indexBound_tail ('t'::('o'::[]))
                                                           { attrName =
                                                           ('a'::('d'::('d'::('r'::[]))));
                                                           attrType =
                                                           (tagIdx idxBits tagBits) }.attrName
                                                           ({ attrName = ('t'::('o'::[]));
                                                           attrType =
                                                           msi }.attrName :: ({ attrName =
                                                           ('l'::('i'::('n'::('e'::[]))));
                                                           attrType =
                                                           (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                           ('i'::('d'::[])); attrType =
                                                           id }.attrName :: [])))
                                                           (indexBound_head { attrName =
                                                             ('t'::('o'::[])); attrType =
                                                             msi }.attrName ({ attrName =
                                                             ('l'::('i'::('n'::('e'::[]))));
                                                             attrType =
                                                             (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                             ('i'::('d'::[])); attrType =
                                                             id }.attrName :: []))))) }) },
                                                     (ReadField (({ attrName =
                                                     ('i'::('s'::('R'::('q'::[])))); attrType =
                                                     Bool } :: ({ attrName =
                                                     ('a'::('d'::('d'::('r'::[])))); attrType =
                                                     (tagIdx idxBits tagBits) } :: ({ attrName =
                                                     ('t'::('o'::[])); attrType =
                                                     msi } :: ({ attrName =
                                                     ('l'::('i'::('n'::('e'::[])))); attrType =
                                                     (line lgDataBytes lgNumDatas) } :: ({ attrName =
                                                     ('i'::('d'::[])); attrType = id } :: []))))),
                                                     { bindex = ('t'::('o'::[])); indexb =
                                                     (indexBound_tail ('t'::('o'::[])) { attrName =
                                                       ('i'::('s'::('R'::('q'::[])))); attrType =
                                                       Bool }.attrName ({ attrName =
                                                       ('a'::('d'::('d'::('r'::[])))); attrType =
                                                       (tagIdx idxBits tagBits) }.attrName :: ({ attrName =
                                                       ('t'::('o'::[])); attrType =
                                                       msi }.attrName :: ({ attrName =
                                                       ('l'::('i'::('n'::('e'::[])))); attrType =
                                                       (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                       ('i'::('d'::[])); attrType =
                                                       id }.attrName :: []))))
                                                       (indexBound_tail ('t'::('o'::[]))
                                                         { attrName =
                                                         ('a'::('d'::('d'::('r'::[])))); attrType =
                                                         (tagIdx idxBits tagBits) }.attrName
                                                         ({ attrName = ('t'::('o'::[])); attrType =
                                                         msi }.attrName :: ({ attrName =
                                                         ('l'::('i'::('n'::('e'::[])))); attrType =
                                                         (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                         ('i'::('d'::[])); attrType =
                                                         id }.attrName :: [])))
                                                         (indexBound_head { attrName =
                                                           ('t'::('o'::[])); attrType =
                                                           msi }.attrName ({ attrName =
                                                           ('l'::('i'::('n'::('e'::[]))));
                                                           attrType =
                                                           (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                           ('i'::('d'::[])); attrType =
                                                           id }.attrName :: []))))) }, (Var
                                                     ((SyntaxKind
                                                     (fromPPop idxBits tagBits lgNumDatas
                                                       lgDataBytes id).attrType.ret), fromP3))))))) :: [])),
    (icons' (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx idxBits) }, (Var
      ((SyntaxKind (idx idxBits)), idx1))))
      ((projT1 (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
         (getAttrType ({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
           Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
           (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType =
           msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
           (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
           id } :: []))))) { bindex = ('t'::('o'::[])); indexb =
           (indexBound_tail ('t'::('o'::[])) { attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
             Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
             (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
             msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
             (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
             id }.attrName :: []))))
             (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[]))));
               attrType = (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[]));
               attrType = msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
               (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[]));
               attrType = id }.attrName :: [])))
               (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName
                 ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
                 (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[]));
                 attrType = id }.attrName :: []))))) }) }, (ReadField (({ attrName =
         ('i'::('s'::('R'::('q'::[])))); attrType = Bool } :: ({ attrName =
         ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) } :: ({ attrName =
         ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[]))));
         attrType = (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
         id } :: []))))), { bindex = ('t'::('o'::[])); indexb =
         (indexBound_tail ('t'::('o'::[])) { attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
           Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
           (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
           msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
           (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
           id }.attrName :: []))))
           (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
             (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
             msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
             (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
             id }.attrName :: [])))
             (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName ({ attrName =
               ('l'::('i'::('n'::('e'::[])))); attrType =
               (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[]));
               attrType = id }.attrName :: []))))) }, (Var ((SyntaxKind
         (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3))))))) :: [])
      (icons' (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (getAttrType ({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
          Bool } :: ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) } :: ({ attrName = ('t'::('o'::[])); attrType =
          msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
          id } :: []))))) { bindex = ('t'::('o'::[])); indexb =
          (indexBound_tail ('t'::('o'::[])) { attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
            Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
            (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
            msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
            (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
            id }.attrName :: []))))
            (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[]))));
              attrType = (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[]));
              attrType = msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
              (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
              id }.attrName :: [])))
              (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName
                ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
                (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[]));
                attrType = id }.attrName :: []))))) }) }, (ReadField (({ attrName =
        ('i'::('s'::('R'::('q'::[])))); attrType = Bool } :: ({ attrName =
        ('a'::('d'::('d'::('r'::[])))); attrType = (tagIdx idxBits tagBits) } :: ({ attrName =
        ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[]))));
        attrType = (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('d'::[])); attrType =
        id } :: []))))), { bindex = ('t'::('o'::[])); indexb =
        (indexBound_tail ('t'::('o'::[])) { attrName = ('i'::('s'::('R'::('q'::[])))); attrType =
          Bool }.attrName ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (tagIdx idxBits tagBits) }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
          id }.attrName :: []))))
          (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
            (tagIdx idxBits tagBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
            msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
            (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
            id }.attrName :: [])))
            (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName ({ attrName =
              ('l'::('i'::('n'::('e'::[])))); attrType =
              (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
              id }.attrName :: []))))) }, (Var ((SyntaxKind
        (fromPPop idxBits tagBits lgNumDatas lgDataBytes id).attrType.ret), fromP3)))))) [] Inil)))),
    (fun x0 -> SReturn (Const (void, (getDefaultConst void)))))))))))))))))))))))))))))); ruleName =
    { nameVal = ('p'::('P'::('r'::('o'::('c'::('e'::('s'::('s'::[])))))))) } }),
    NilInSinModule))))))))))))))))))))))))))))

(** val addrBits0 : int -> int **)

let addrBits0 idxBits =
  idxBits

(** val addr1 : int -> kind **)

let addr1 idxBits =
  Bit (addrBits0 idxBits)

(** val rqToP1 : int -> kind -> kind **)

let rqToP1 idxBits id =
  rqToP (addr1 idxBits) id

(** val rqFromC0 : int -> int -> kind -> kind **)

let rqFromC0 idxBits lgNumChildren id =
  rqFromC lgNumChildren (addr1 idxBits) id

(** val rsToP1 : int -> int -> int -> kind **)

let rsToP1 idxBits lgNumDatas lgDataBytes =
  rsToP lgDataBytes lgNumDatas (addr1 idxBits)

(** val rsFromC0 : int -> int -> int -> int -> kind **)

let rsFromC0 idxBits lgNumDatas lgDataBytes lgNumChildren =
  rsFromC lgDataBytes lgNumDatas lgNumChildren (addr1 idxBits)

(** val fromP1 : int -> int -> int -> kind -> kind **)

let fromP1 idxBits lgNumDatas lgDataBytes id =
  fromP lgDataBytes lgNumDatas (addr1 idxBits) id

(** val toC0 : int -> int -> int -> int -> kind -> kind **)

let toC0 idxBits lgNumDatas lgDataBytes lgNumChildren id =
  toC lgDataBytes lgNumDatas lgNumChildren (addr1 idxBits) id

(** val rqToPPop : int -> kind -> signatureT attribute **)

let rqToPPop idxBits id =
  { attrName =
    (withPrefix ('r'::('q'::('T'::('o'::('P'::('a'::('r'::('e'::('n'::('t'::[]))))))))))
      ('d'::('e'::('q'::[])))); attrType = { arg = void; ret = (rqToP1 idxBits id) } }

(** val rqFromCEnq : int -> int -> kind -> signatureT attribute **)

let rqFromCEnq idxBits lgNumChildren id =
  { attrName =
    (withPrefix ('r'::('q'::('F'::('r'::('o'::('m'::('C'::('h'::('i'::('l'::('d'::[])))))))))))
      ('e'::('n'::('q'::[])))); attrType = { arg = (rqFromC0 idxBits lgNumChildren id); ret =
    void } }

(** val rsToPPop : int -> int -> int -> signatureT attribute **)

let rsToPPop idxBits lgNumDatas lgDataBytes =
  { attrName =
    (withPrefix ('r'::('s'::('T'::('o'::('P'::('a'::('r'::('e'::('n'::('t'::[]))))))))))
      ('d'::('e'::('q'::[])))); attrType = { arg = void; ret =
    (rsToP1 idxBits lgNumDatas lgDataBytes) } }

(** val rsFromCEnq : int -> int -> int -> int -> signatureT attribute **)

let rsFromCEnq idxBits lgNumDatas lgDataBytes lgNumChildren =
  { attrName =
    (withPrefix ('r'::('s'::('F'::('r'::('o'::('m'::('C'::('h'::('i'::('l'::('d'::[])))))))))))
      ('e'::('n'::('q'::[])))); attrType = { arg =
    (rsFromC0 idxBits lgNumDatas lgDataBytes lgNumChildren); ret = void } }

(** val toCPop : int -> int -> int -> int -> kind -> signatureT attribute **)

let toCPop idxBits lgNumDatas lgDataBytes lgNumChildren id =
  { attrName =
    (withPrefix ('t'::('o'::('C'::('h'::('i'::('l'::('d'::[]))))))) ('d'::('e'::('q'::[]))));
    attrType = { arg = void; ret = (toC0 idxBits lgNumDatas lgDataBytes lgNumChildren id) } }

(** val fromPEnq : int -> int -> int -> kind -> signatureT attribute **)

let fromPEnq idxBits lgNumDatas lgDataBytes id =
  { attrName =
    (withPrefix ('f'::('r'::('o'::('m'::('P'::('a'::('r'::('e'::('n'::('t'::[]))))))))))
      ('e'::('n'::('q'::[])))); attrType = { arg = (fromP1 idxBits lgNumDatas lgDataBytes id); ret =
    void } }

(** val childParent : int -> int -> int -> int -> kind -> metaModule **)

let childParent idxBits lgNumDatas lgDataBytes lgNumChildren id =
  makeMetaModule (ConsInMetaModule ((MMERule (RepRule ((Obj.magic string_of_nat), (Bit
    lgNumChildren), (Obj.magic (natToWordConst lgNumChildren)), (fun _ -> GIndex (fun i -> GMCall
    ({ isRep = true; nameRec0 = { nameVal = (rqToPPop idxBits id).attrName } },
    (rqToPPop idxBits id).attrType, (Const ((rqToPPop idxBits id).attrType.arg,
    (getDefaultConst (rqToPPop idxBits id).attrType.arg))), (fun rq -> GMCall ({ isRep = false;
    nameRec0 = { nameVal = (rqFromCEnq idxBits lgNumChildren id).attrName } },
    (rqFromCEnq idxBits lgNumChildren id).attrType, (BuildStruct
    (((projT1 (ExistT ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) }, (Var ((SyntaxKind { attrName =
        ('c'::('h'::('i'::('l'::('d'::[]))))); attrType = (child lgNumChildren) }.attrType), i))))) :: (
    (projT1 (ExistT ({ attrName = ('r'::('q'::[])); attrType = (rqToPPop idxBits id).attrType.ret },
      (Var ((SyntaxKind (rqToPPop idxBits id).attrType.ret), rq))))) :: [])),
    (icons' (ExistT ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) }, (Var ((SyntaxKind { attrName = ('c'::('h'::('i'::('l'::('d'::[])))));
      attrType = (child lgNumChildren) }.attrType), i))))
      ((projT1 (ExistT ({ attrName = ('r'::('q'::[])); attrType =
         (rqToPPop idxBits id).attrType.ret }, (Var ((SyntaxKind
         (rqToPPop idxBits id).attrType.ret), rq))))) :: [])
      (icons' (ExistT ({ attrName = ('r'::('q'::[])); attrType =
        (rqToPPop idxBits id).attrType.ret }, (Var ((SyntaxKind (rqToPPop idxBits id).attrType.ret),
        rq)))) [] Inil)))), (fun x -> GReturn (Const (void, (getDefaultConst void))))))))),
    { nameVal = ('r'::('q'::('F'::('r'::('o'::('m'::('C'::('T'::('o'::('P'::[])))))))))) },
    (Obj.magic (getNatListToN (wordToNat lgNumChildren (wones lgNumChildren))))))),
    (ConsInMetaModule ((MMERule (RepRule ((Obj.magic string_of_nat), (Bit lgNumChildren),
    (Obj.magic (natToWordConst lgNumChildren)), (fun _ -> GIndex (fun i -> GMCall ({ isRep = true;
    nameRec0 = { nameVal = (rsToPPop idxBits lgNumDatas lgDataBytes).attrName } },
    (rsToPPop idxBits lgNumDatas lgDataBytes).attrType, (Const
    ((rsToPPop idxBits lgNumDatas lgDataBytes).attrType.arg,
    (getDefaultConst (rsToPPop idxBits lgNumDatas lgDataBytes).attrType.arg))), (fun rs -> GMCall
    ({ isRep = false; nameRec0 = { nameVal =
    (rsFromCEnq idxBits lgNumDatas lgDataBytes lgNumChildren).attrName } },
    (rsFromCEnq idxBits lgNumDatas lgDataBytes lgNumChildren).attrType, (BuildStruct
    (((projT1 (ExistT ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) }, (Var ((SyntaxKind { attrName =
        ('c'::('h'::('i'::('l'::('d'::[]))))); attrType = (child lgNumChildren) }.attrType), i))))) :: (
    (projT1 (ExistT ({ attrName = ('r'::('s'::[])); attrType =
      (rsToPPop idxBits lgNumDatas lgDataBytes).attrType.ret }, (Var ((SyntaxKind
      (rsToPPop idxBits lgNumDatas lgDataBytes).attrType.ret), rs))))) :: [])),
    (icons' (ExistT ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) }, (Var ((SyntaxKind { attrName = ('c'::('h'::('i'::('l'::('d'::[])))));
      attrType = (child lgNumChildren) }.attrType), i))))
      ((projT1 (ExistT ({ attrName = ('r'::('s'::[])); attrType =
         (rsToPPop idxBits lgNumDatas lgDataBytes).attrType.ret }, (Var ((SyntaxKind
         (rsToPPop idxBits lgNumDatas lgDataBytes).attrType.ret), rs))))) :: [])
      (icons' (ExistT ({ attrName = ('r'::('s'::[])); attrType =
        (rsToPPop idxBits lgNumDatas lgDataBytes).attrType.ret }, (Var ((SyntaxKind
        (rsToPPop idxBits lgNumDatas lgDataBytes).attrType.ret), rs)))) [] Inil)))), (fun x ->
    GReturn (Const (void, (getDefaultConst void))))))))), { nameVal =
    ('r'::('s'::('F'::('r'::('o'::('m'::('C'::('T'::('o'::('P'::[])))))))))) },
    (Obj.magic (getNatListToN (wordToNat lgNumChildren (wones lgNumChildren))))))),
    (ConsInMetaModule ((MMERule (RepRule ((Obj.magic string_of_nat), (Bit lgNumChildren),
    (Obj.magic (natToWordConst lgNumChildren)), (fun _ -> GIndex (fun i -> GMCall ({ isRep = false;
    nameRec0 = { nameVal = (toCPop idxBits lgNumDatas lgDataBytes lgNumChildren id).attrName } },
    (toCPop idxBits lgNumDatas lgDataBytes lgNumChildren id).attrType, (Const
    ((toCPop idxBits lgNumDatas lgDataBytes lgNumChildren id).attrType.arg,
    (getDefaultConst (toCPop idxBits lgNumDatas lgDataBytes lgNumChildren id).attrType.arg))),
    (fun msg -> GAssert_ ((Eq
    ((getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
       (child lgNumChildren) } :: ({ attrName = ('m'::('s'::('g'::[]))); attrType =
       (fromP lgDataBytes lgNumDatas (addr1 idxBits) id) } :: [])) { bindex =
       ('c'::('h'::('i'::('l'::('d'::[]))))); indexb =
       (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
         (child lgNumChildren) }.attrName ({ attrName = ('m'::('s'::('g'::[]))); attrType =
         (fromP lgDataBytes lgNumDatas (addr1 idxBits) id) }.attrName :: [])) }), (Var ((SyntaxKind
    (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) } :: ({ attrName = ('m'::('s'::('g'::[]))); attrType =
      (fromP lgDataBytes lgNumDatas (addr1 idxBits) id) } :: [])) { bindex =
      ('c'::('h'::('i'::('l'::('d'::[]))))); indexb =
      (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) }.attrName ({ attrName = ('m'::('s'::('g'::[]))); attrType =
        (fromP lgDataBytes lgNumDatas (addr1 idxBits) id) }.attrName :: [])) })), i)), (ReadField
    (({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
    (child lgNumChildren) } :: ({ attrName = ('m'::('s'::('g'::[]))); attrType =
    (fromP lgDataBytes lgNumDatas (addr1 idxBits) id) } :: [])), { bindex =
    ('c'::('h'::('i'::('l'::('d'::[]))))); indexb =
    (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) }.attrName ({ attrName = ('m'::('s'::('g'::[]))); attrType =
      (fromP lgDataBytes lgNumDatas (addr1 idxBits) id) }.attrName :: [])) }, (Var ((SyntaxKind
    (toCPop idxBits lgNumDatas lgDataBytes lgNumChildren id).attrType.ret), msg)))))), (GMCall
    ({ isRep = true; nameRec0 = { nameVal =
    (fromPEnq idxBits lgNumDatas lgDataBytes id).attrName } },
    (fromPEnq idxBits lgNumDatas lgDataBytes id).attrType, (ReadField (({ attrName =
    ('c'::('h'::('i'::('l'::('d'::[]))))); attrType = (child lgNumChildren) } :: ({ attrName =
    ('m'::('s'::('g'::[]))); attrType = (fromP lgDataBytes lgNumDatas (addr1 idxBits) id) } :: [])),
    { bindex = ('m'::('s'::('g'::[]))); indexb =
    (indexBound_tail ('m'::('s'::('g'::[]))) { attrName = ('c'::('h'::('i'::('l'::('d'::[])))));
      attrType = (child lgNumChildren) }.attrName ({ attrName = ('m'::('s'::('g'::[]))); attrType =
      (fromP lgDataBytes lgNumDatas (addr1 idxBits) id) }.attrName :: [])
      (indexBound_head { attrName = ('m'::('s'::('g'::[]))); attrType =
        (fromP lgDataBytes lgNumDatas (addr1 idxBits) id) }.attrName [])) }, (Var ((SyntaxKind
    (toCPop idxBits lgNumDatas lgDataBytes lgNumChildren id).attrType.ret), msg)))), (fun x ->
    GReturn (Const (void, (getDefaultConst void))))))))))), { nameVal =
    ('f'::('r'::('o'::('m'::('P'::('T'::('o'::('C'::[])))))))) },
    (Obj.magic (getNatListToN (wordToNat lgNumChildren (wones lgNumChildren))))))),
    NilInMetaModule))))))

(** val foldInc' :
    kind -> int -> ('a1 expr -> 'a1 expr -> 'a1 expr) -> 'a1 expr -> int -> 'a1 expr **)

let rec foldInc' a lgIdx f init n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    init)
    (fun m ->
    f (Const ((Bit lgIdx), (ConstBit (lgIdx, (natToWord lgIdx m))))) (foldInc' a lgIdx f init m))
    n

(** val foldInc : kind -> int -> ('a1 expr -> 'a1 expr -> 'a1 expr) -> 'a1 expr -> 'a1 expr **)

let foldInc a lgIdx f init =
  foldInc' a lgIdx f init (wordToNat lgIdx (wones lgIdx))

(** val addrBits1 : int -> int **)

let addrBits1 idxBits =
  idxBits

(** val addr2 : int -> kind **)

let addr2 idxBits =
  Bit (addrBits1 idxBits)

(** val idx0 : int -> kind **)

let idx0 idxBits =
  Bit idxBits

(** val data1 : int -> kind **)

let data1 lgDataBytes =
  Bit
    (mult lgDataBytes (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))))

(** val line1 : int -> int -> kind **)

let line1 lgNumDatas lgDataBytes =
  Vector ((data1 lgDataBytes), lgNumDatas)

(** val rqToP2 : int -> kind -> kind **)

let rqToP2 idxBits id =
  rqToP (addr2 idxBits) id

(** val rqFromC1 : int -> int -> kind -> kind **)

let rqFromC1 idxBits lgNumChildren id =
  rqFromC lgNumChildren (addr2 idxBits) id

(** val rsToP2 : int -> int -> int -> kind **)

let rsToP2 idxBits lgNumDatas lgDataBytes =
  rsToP lgDataBytes lgNumDatas (addr2 idxBits)

(** val rsFromC1 : int -> int -> int -> int -> kind **)

let rsFromC1 idxBits lgNumDatas lgDataBytes lgNumChildren =
  rsFromC lgDataBytes lgNumDatas lgNumChildren (addr2 idxBits)

(** val fromP2 : int -> int -> int -> kind -> kind **)

let fromP2 idxBits lgNumDatas lgDataBytes id =
  fromP lgDataBytes lgNumDatas (addr2 idxBits) id

(** val toC1 : int -> int -> int -> int -> kind -> kind **)

let toC1 idxBits lgNumDatas lgDataBytes lgNumChildren id =
  toC lgDataBytes lgNumDatas lgNumChildren (addr2 idxBits) id

(** val rqFromCPop : int -> int -> kind -> signatureT attribute **)

let rqFromCPop idxBits lgNumChildren id =
  { attrName =
    (withPrefix ('r'::('q'::('F'::('r'::('o'::('m'::('C'::('h'::('i'::('l'::('d'::[])))))))))))
      ('d'::('e'::('q'::[])))); attrType = { arg = void; ret =
    (rqFromC1 idxBits lgNumChildren id) } }

(** val rqFromCFirst : int -> int -> kind -> signatureT attribute **)

let rqFromCFirst idxBits lgNumChildren id =
  { attrName =
    (withPrefix ('r'::('q'::('F'::('r'::('o'::('m'::('C'::('h'::('i'::('l'::('d'::[])))))))))))
      ('f'::('i'::('r'::('s'::('t'::('E'::('l'::('t'::[]))))))))); attrType = { arg = void; ret =
    (rqFromC1 idxBits lgNumChildren id) } }

(** val rsFromCPop : int -> int -> int -> int -> signatureT attribute **)

let rsFromCPop idxBits lgNumDatas lgDataBytes lgNumChildren =
  { attrName =
    (withPrefix ('r'::('s'::('F'::('r'::('o'::('m'::('C'::('h'::('i'::('l'::('d'::[])))))))))))
      ('d'::('e'::('q'::[])))); attrType = { arg = void; ret =
    (rsFromC1 idxBits lgNumDatas lgDataBytes lgNumChildren) } }

(** val toCEnq : int -> int -> int -> int -> kind -> signatureT attribute **)

let toCEnq idxBits lgNumDatas lgDataBytes lgNumChildren id =
  { attrName =
    (withPrefix ('t'::('o'::('C'::('h'::('i'::('l'::('d'::[]))))))) ('e'::('n'::('q'::[]))));
    attrType = { arg = (toC1 idxBits lgNumDatas lgDataBytes lgNumChildren id); ret = void } }

(** val dir : int -> kind **)

let dir lgNumChildren =
  Vector (msi, lgNumChildren)

(** val dirw : int -> kind **)

let dirw lgNumChildren =
  Vector (Bool, lgNumChildren)

(** val readLine0 : int -> int -> int -> signatureT attribute **)

let readLine0 idxBits lgNumDatas lgDataBytes =
  { attrName = (withPrefix ('m'::('l'::('i'::('n'::('e'::[]))))) ('r'::('e'::('a'::('d'::[])))));
    attrType = { arg = (idx0 idxBits); ret = (line1 lgNumDatas lgDataBytes) } }

(** val writeLine0 : int -> int -> int -> signatureT attribute **)

let writeLine0 idxBits lgNumDatas lgDataBytes =
  { attrName =
    (withPrefix ('m'::('l'::('i'::('n'::('e'::[]))))) ('w'::('r'::('i'::('t'::('e'::[]))))));
    attrType = { arg = (writePort idxBits (line1 lgNumDatas lgDataBytes)); ret = void } }

(** val readDir : int -> int -> signatureT attribute **)

let readDir idxBits lgNumChildren =
  { attrName = (withPrefix ('m'::('c'::('s'::[]))) ('r'::('e'::('a'::('d'::[]))))); attrType =
    { arg = (idx0 idxBits); ret = (dir lgNumChildren) } }

(** val writeDir : int -> int -> signatureT attribute **)

let writeDir idxBits lgNumChildren =
  { attrName = (withPrefix ('m'::('c'::('s'::[]))) ('w'::('r'::('i'::('t'::('e'::[]))))));
    attrType = { arg = (writePort idxBits (dir lgNumChildren)); ret = void } }

(** val child0 : int -> kind **)

let child0 lgNumChildren =
  child lgNumChildren

(** val getIdx0 : int -> 'a1 expr -> 'a1 expr **)

let getIdx0 idxBits x =
  x

(** val othersCompat : int -> 'a1 expr -> 'a1 expr -> 'a1 expr -> 'a1 expr **)

let othersCompat lgNumChildren c x dir0 =
  foldInc Bool lgNumChildren (fun idx1 old -> ITE ((SyntaxKind Bool), (UniBool (Neg, (Eq
    ((child0 lgNumChildren), c, idx1)))), (BinBool (And,
    (isCompat x (ReadIndex (lgNumChildren, msi, idx1, dir0))), old)), old)) (Const (Bool, (ConstBool
    true)))

(** val findIncompat : int -> 'a1 expr -> 'a1 expr -> 'a1 expr -> 'a1 expr -> 'a1 expr **)

let findIncompat lgNumChildren c x dir0 dirw0 =
  foldInc (maybe (child0 lgNumChildren)) lgNumChildren (fun idx1 old -> ITE ((SyntaxKind (Struct
    ((projT1 (ExistT ({ attrName = ('v'::('a'::('l'::('i'::('d'::[]))))); attrType = Bool }, (Const
       (Bool, (ConstBool true)))))) :: ((projT1 (ExistT ({ attrName =
                                          ('v'::('a'::('l'::('u'::('e'::[]))))); attrType = (Bit
                                          lgNumChildren) }, idx1))) :: [])))), (BinBool (And,
    (BinBool (And, (BinBool (And, (UniBool (Neg, (ReadField (({ attrName =
    ('v'::('a'::('l'::('i'::('d'::[]))))); attrType = Bool } :: ({ attrName =
    ('v'::('a'::('l'::('u'::('e'::[]))))); attrType = (child0 lgNumChildren) } :: [])), { bindex =
    ('v'::('a'::('l'::('i'::('d'::[]))))); indexb =
    (indexBound_head { attrName = ('v'::('a'::('l'::('i'::('d'::[]))))); attrType = Bool }.attrName
      ({ attrName = ('v'::('a'::('l'::('u'::('e'::[]))))); attrType =
      (child0 lgNumChildren) }.attrName :: [])) }, old)))), (UniBool (Neg, (Eq
    ((child0 lgNumChildren), c, idx1)))))), (UniBool (Neg,
    (isCompat x (ReadIndex (lgNumChildren, msi, idx1, dir0))))))), (UniBool (Neg, (ReadIndex
    (lgNumChildren, Bool, idx1, dirw0)))))), (BuildStruct
    (((projT1 (ExistT ({ attrName = ('v'::('a'::('l'::('i'::('d'::[]))))); attrType = Bool }, (Const
        (Bool, (ConstBool true)))))) :: ((projT1 (ExistT ({ attrName =
                                           ('v'::('a'::('l'::('u'::('e'::[]))))); attrType = (Bit
                                           lgNumChildren) }, idx1))) :: [])),
    (icons' (ExistT ({ attrName = ('v'::('a'::('l'::('i'::('d'::[]))))); attrType = Bool }, (Const
      (Bool, (ConstBool true)))))
      ((projT1 (ExistT ({ attrName = ('v'::('a'::('l'::('u'::('e'::[]))))); attrType = (Bit
         lgNumChildren) }, idx1))) :: [])
      (icons' (ExistT ({ attrName = ('v'::('a'::('l'::('u'::('e'::[]))))); attrType = (Bit
        lgNumChildren) }, idx1)) [] Inil)))), old)) (BuildStruct
    (((projT1 (ExistT ({ attrName = ('v'::('a'::('l'::('i'::('d'::[]))))); attrType = Bool }, (Const
        (Bool, (ConstBool false)))))) :: ((projT1 (ExistT ({ attrName =
                                            ('v'::('a'::('l'::('u'::('e'::[]))))); attrType =
                                            (child0 lgNumChildren) }, (Const ({ attrName =
                                            ('v'::('a'::('l'::('u'::('e'::[]))))); attrType =
                                            (child0 lgNumChildren) }.attrType,
                                            (getDefaultConst { attrName =
                                              ('v'::('a'::('l'::('u'::('e'::[]))))); attrType =
                                              (child0 lgNumChildren) }.attrType)))))) :: [])),
    (icons' (ExistT ({ attrName = ('v'::('a'::('l'::('i'::('d'::[]))))); attrType = Bool }, (Const
      (Bool, (ConstBool false)))))
      ((projT1 (ExistT ({ attrName = ('v'::('a'::('l'::('u'::('e'::[]))))); attrType =
         (child0 lgNumChildren) }, (Const ({ attrName = ('v'::('a'::('l'::('u'::('e'::[])))));
         attrType = (child0 lgNumChildren) }.attrType,
         (getDefaultConst { attrName = ('v'::('a'::('l'::('u'::('e'::[]))))); attrType =
           (child0 lgNumChildren) }.attrType)))))) :: [])
      (icons' (ExistT ({ attrName = ('v'::('a'::('l'::('u'::('e'::[]))))); attrType =
        (child0 lgNumChildren) }, (Const ({ attrName = ('v'::('a'::('l'::('u'::('e'::[])))));
        attrType = (child0 lgNumChildren) }.attrType,
        (getDefaultConst { attrName = ('v'::('a'::('l'::('u'::('e'::[]))))); attrType =
          (child0 lgNumChildren) }.attrType))))) [] Inil))))

(** val dirwInit : int -> constT **)

let dirwInit lgNumChildren =
  ConstVector (Bool, lgNumChildren, (replicate (ConstBool false) lgNumChildren))

(** val memDir : int -> int -> int -> int -> kind -> metaModule **)

let memDir idxBits lgNumDatas lgDataBytes lgNumChildren id =
  makeMetaModule (ConsInMetaModule ((MMERegister (OneReg ((ExistT ((SyntaxKind Bool),
    (makeConst Bool (ConstBool false)))), { nameVal =
    ('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[])))))))) }))), (ConsInMetaModule ((MMERegister
    (OneReg ((ExistT ((SyntaxKind (dirw lgNumChildren)),
    (makeConst (dirw lgNumChildren) (dirwInit lgNumChildren)))), { nameVal =
    ('c'::('R'::('q'::('D'::('i'::('r'::('w'::[]))))))) }))), (ConsInMetaModule ((MMERule (OneRule
    ((fun _ -> SReadReg ({ nameVal = ('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[])))))))) },
    (SyntaxKind Bool), (fun valid -> SAssert_ ((UniBool (Neg, (Var ((SyntaxKind Bool), valid)))),
    (SMCall ({ nameVal = (rqFromCFirst idxBits lgNumChildren id).attrName },
    (rqFromCFirst idxBits lgNumChildren id).attrType, (Const
    ((rqFromCFirst idxBits lgNumChildren id).attrType.arg,
    (getDefaultConst (rqFromCFirst idxBits lgNumChildren id).attrType.arg))), (fun rqChild -> SLet_
    ((SyntaxKind
    (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
      (rqToP (addr2 idxBits) id) } :: [])) { bindex = ('c'::('h'::('i'::('l'::('d'::[])))));
      indexb =
      (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
        (rqToP (addr2 idxBits) id) }.attrName :: [])) })), (ReadField (({ attrName =
    ('c'::('h'::('i'::('l'::('d'::[]))))); attrType = (child lgNumChildren) } :: ({ attrName =
    ('r'::('q'::[])); attrType = (rqToP (addr2 idxBits) id) } :: [])), { bindex =
    ('c'::('h'::('i'::('l'::('d'::[]))))); indexb =
    (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
      (rqToP (addr2 idxBits) id) }.attrName :: [])) }, (Var ((SyntaxKind
    (rqFromCFirst idxBits lgNumChildren id).attrType.ret), rqChild)))), (fun c -> SLet_ ((SyntaxKind
    (rqToP2 idxBits id)), (ReadField (({ attrName = ('c'::('h'::('i'::('l'::('d'::[])))));
    attrType = (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
    (rqToP (addr2 idxBits) id) } :: [])), { bindex = ('r'::('q'::[])); indexb =
    (indexBound_tail ('r'::('q'::[])) { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
      (rqToP (addr2 idxBits) id) }.attrName :: [])
      (indexBound_head { attrName = ('r'::('q'::[])); attrType =
        (rqToP (addr2 idxBits) id) }.attrName [])) }, (Var ((SyntaxKind
    (rqFromCFirst idxBits lgNumChildren id).attrType.ret), rqChild)))), (fun rq -> SLet_
    ((SyntaxKind (idx0 idxBits)),
    (getIdx0 idxBits (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
      msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('i'::('d'::[]));
      attrType = id } :: [])))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
        msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
        ('i'::('d'::[])); attrType = id }.attrName :: [])))) }, (Var ((SyntaxKind
      (rqToP2 idxBits id)), rq))))), (fun idx1 -> SMCall ({ nameVal =
    (readDir idxBits lgNumChildren).attrName }, (readDir idxBits lgNumChildren).attrType, (Var
    ((SyntaxKind (idx0 idxBits)), idx1)), (fun dir0 -> SAssert_ ((UniBool (Neg, (BinBitBool
    ((Pervasives.succ (Pervasives.succ 0)), (Pervasives.succ (Pervasives.succ 0)), (Lt
    (Pervasives.succ (Pervasives.succ 0))), (ReadField (({ attrName =
    ('a'::('d'::('d'::('r'::[])))); attrType = (addr2 idxBits) } :: ({ attrName =
    ('f'::('r'::('o'::('m'::[])))); attrType = msi } :: ({ attrName = ('t'::('o'::[])); attrType =
    msi } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: [])))), { bindex =
    ('f'::('r'::('o'::('m'::[])))); indexb =
    (indexBound_tail ('f'::('r'::('o'::('m'::[])))) { attrName = ('a'::('d'::('d'::('r'::[]))));
      attrType = (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
      msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
      ('i'::('d'::[])); attrType = id }.attrName :: [])))
      (indexBound_head { attrName = ('f'::('r'::('o'::('m'::[])))); attrType = msi }.attrName
        ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName = ('i'::('d'::[]));
        attrType = id }.attrName :: [])))) }, (Var ((SyntaxKind (rqToP2 idxBits id)), rq)))),
    (ReadIndex (lgNumChildren, msi, (Var ((SyntaxKind
    (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
      (rqToP (addr2 idxBits) id) } :: [])) { bindex = ('c'::('h'::('i'::('l'::('d'::[])))));
      indexb =
      (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
        (rqToP (addr2 idxBits) id) }.attrName :: [])) })), c)), (Var ((SyntaxKind
    (readDir idxBits lgNumChildren).attrType.ret), dir0)))))))), (SWriteReg ({ nameVal =
    ('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[])))))))) }, (SyntaxKind Bool), (Const (Bool,
    (ConstBool true))), (SLet_ ((SyntaxKind (dirw lgNumChildren)), (BuildVector (Bool,
    lgNumChildren, (replicate (Const (Bool, (ConstBool false))) lgNumChildren))), (fun dirw0 ->
    SWriteReg ({ nameVal = ('c'::('R'::('q'::('D'::('i'::('r'::('w'::[]))))))) }, (SyntaxKind
    (dirw lgNumChildren)), (Var ((SyntaxKind (dirw lgNumChildren)), dirw0)), (SReturn (Const (void,
    (getDefaultConst void)))))))))))))))))))))))))), { nameVal =
    ('m'::('i'::('s'::('s'::('B'::('y'::('S'::('t'::('a'::('t'::('e'::[]))))))))))) }))),
    (ConsInMetaModule ((MMERule (OneRule ((fun _ -> SReadReg ({ nameVal =
    ('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[])))))))) }, (SyntaxKind Bool), (fun valid ->
    SAssert_ ((Var ((SyntaxKind Bool), valid)), (SMCall ({ nameVal =
    (rqFromCFirst idxBits lgNumChildren id).attrName },
    (rqFromCFirst idxBits lgNumChildren id).attrType, (Const
    ((rqFromCFirst idxBits lgNumChildren id).attrType.arg,
    (getDefaultConst (rqFromCFirst idxBits lgNumChildren id).attrType.arg))), (fun rqChild -> SLet_
    ((SyntaxKind
    (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
      (rqToP (addr2 idxBits) id) } :: [])) { bindex = ('c'::('h'::('i'::('l'::('d'::[])))));
      indexb =
      (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
        (rqToP (addr2 idxBits) id) }.attrName :: [])) })), (ReadField (({ attrName =
    ('c'::('h'::('i'::('l'::('d'::[]))))); attrType = (child lgNumChildren) } :: ({ attrName =
    ('r'::('q'::[])); attrType = (rqToP (addr2 idxBits) id) } :: [])), { bindex =
    ('c'::('h'::('i'::('l'::('d'::[]))))); indexb =
    (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
      (rqToP (addr2 idxBits) id) }.attrName :: [])) }, (Var ((SyntaxKind
    (rqFromCFirst idxBits lgNumChildren id).attrType.ret), rqChild)))), (fun c -> SLet_ ((SyntaxKind
    (rqToP2 idxBits id)), (ReadField (({ attrName = ('c'::('h'::('i'::('l'::('d'::[])))));
    attrType = (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
    (rqToP (addr2 idxBits) id) } :: [])), { bindex = ('r'::('q'::[])); indexb =
    (indexBound_tail ('r'::('q'::[])) { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
      (rqToP (addr2 idxBits) id) }.attrName :: [])
      (indexBound_head { attrName = ('r'::('q'::[])); attrType =
        (rqToP (addr2 idxBits) id) }.attrName [])) }, (Var ((SyntaxKind
    (rqFromCFirst idxBits lgNumChildren id).attrType.ret), rqChild)))), (fun rq -> SMCall
    ({ nameVal = (readDir idxBits lgNumChildren).attrName },
    (readDir idxBits lgNumChildren).attrType,
    (getIdx0 idxBits (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
      msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('i'::('d'::[]));
      attrType = id } :: [])))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
        msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
        ('i'::('d'::[])); attrType = id }.attrName :: [])))) }, (Var ((SyntaxKind
      (rqToP2 idxBits id)), rq))))), (fun dir0 -> SReadReg ({ nameVal =
    ('c'::('R'::('q'::('D'::('i'::('r'::('w'::[]))))))) }, (SyntaxKind (dirw lgNumChildren)),
    (fun dirw0 -> SLet_ ((SyntaxKind (maybe (child0 lgNumChildren))),
    (findIncompat lgNumChildren (Var ((SyntaxKind
      (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
        (rqToP (addr2 idxBits) id) } :: [])) { bindex = ('c'::('h'::('i'::('l'::('d'::[])))));
        indexb =
        (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
          (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
          (rqToP (addr2 idxBits) id) }.attrName :: [])) })), c)) (ReadField (({ attrName =
      ('a'::('d'::('d'::('r'::[])))); attrType = (addr2 idxBits) } :: ({ attrName =
      ('f'::('r'::('o'::('m'::[])))); attrType = msi } :: ({ attrName = ('t'::('o'::[])); attrType =
      msi } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: [])))), { bindex =
      ('t'::('o'::[])); indexb =
      (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
        msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
        ('i'::('d'::[])); attrType = id }.attrName :: [])))
        (indexBound_tail ('t'::('o'::[])) { attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
          msi }.attrName ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
          ('i'::('d'::[])); attrType = id }.attrName :: []))
          (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName ({ attrName =
            ('i'::('d'::[])); attrType = id }.attrName :: [])))) }, (Var ((SyntaxKind
      (rqToP2 idxBits id)), rq)))) (Var ((SyntaxKind (readDir idxBits lgNumChildren).attrType.ret),
      dir0)) (Var ((SyntaxKind (dirw lgNumChildren)), dirw0))), (fun i -> SAssert_ ((ReadField
    (({ attrName = ('v'::('a'::('l'::('i'::('d'::[]))))); attrType = Bool } :: ({ attrName =
    ('v'::('a'::('l'::('u'::('e'::[]))))); attrType = (child0 lgNumChildren) } :: [])), { bindex =
    ('v'::('a'::('l'::('i'::('d'::[]))))); indexb =
    (indexBound_head { attrName = ('v'::('a'::('l'::('i'::('d'::[]))))); attrType = Bool }.attrName
      ({ attrName = ('v'::('a'::('l'::('u'::('e'::[]))))); attrType =
      (child0 lgNumChildren) }.attrName :: [])) }, (Var ((SyntaxKind
    (maybe (child0 lgNumChildren))), i)))), (SLet_ ((SyntaxKind
    (fromP2 idxBits lgNumDatas lgDataBytes id)), (BuildStruct
    (((projT1 (ExistT ({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType = Bool }, (Const (Bool,
        (ConstBool true)))))) :: ((projT1 (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[]))));
                                    attrType =
                                    (getAttrType ({ attrName = ('a'::('d'::('d'::('r'::[]))));
                                      attrType = (addr2 idxBits) } :: ({ attrName =
                                      ('f'::('r'::('o'::('m'::[])))); attrType =
                                      msi } :: ({ attrName = ('t'::('o'::[])); attrType =
                                      msi } :: ({ attrName = ('i'::('d'::[])); attrType =
                                      id } :: [])))) { bindex = ('a'::('d'::('d'::('r'::[]))));
                                      indexb =
                                      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[]))));
                                        attrType = (addr2 idxBits) }.attrName ({ attrName =
                                        ('f'::('r'::('o'::('m'::[])))); attrType =
                                        msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
                                        msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
                                        id }.attrName :: [])))) }) }, (ReadField (({ attrName =
                                    ('a'::('d'::('d'::('r'::[])))); attrType =
                                    (addr2 idxBits) } :: ({ attrName =
                                    ('f'::('r'::('o'::('m'::[])))); attrType =
                                    msi } :: ({ attrName = ('t'::('o'::[])); attrType =
                                    msi } :: ({ attrName = ('i'::('d'::[])); attrType =
                                    id } :: [])))), { bindex = ('a'::('d'::('d'::('r'::[]))));
                                    indexb =
                                    (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[]))));
                                      attrType = (addr2 idxBits) }.attrName ({ attrName =
                                      ('f'::('r'::('o'::('m'::[])))); attrType =
                                      msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
                                      msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
                                      id }.attrName :: [])))) }, (Var ((SyntaxKind
                                    (rqToP2 idxBits id)), rq))))))) :: ((projT1 (ExistT
                                                                          ({ attrName =
                                                                          ('t'::('o'::[]));
                                                                          attrType = msi },
                                                                          (toCompat (ReadField
                                                                            (({ attrName =
                                                                            ('a'::('d'::('d'::('r'::[]))));
                                                                            attrType =
                                                                            (addr2 idxBits) } :: ({ attrName =
                                                                            ('f'::('r'::('o'::('m'::[]))));
                                                                            attrType =
                                                                            msi } :: ({ attrName =
                                                                            ('t'::('o'::[]));
                                                                            attrType =
                                                                            msi } :: ({ attrName =
                                                                            ('i'::('d'::[]));
                                                                            attrType =
                                                                            id } :: [])))),
                                                                            { bindex =
                                                                            ('t'::('o'::[]));
                                                                            indexb =
                                                                            (indexBound_tail
                                                                              ('t'::('o'::[]))
                                                                              { attrName =
                                                                              ('a'::('d'::('d'::('r'::[]))));
                                                                              attrType =
                                                                              (addr2 idxBits) }.attrName
                                                                              ({ attrName =
                                                                              ('f'::('r'::('o'::('m'::[]))));
                                                                              attrType =
                                                                              msi }.attrName :: ({ attrName =
                                                                              ('t'::('o'::[]));
                                                                              attrType =
                                                                              msi }.attrName :: ({ attrName =
                                                                              ('i'::('d'::[]));
                                                                              attrType =
                                                                              id }.attrName :: [])))
                                                                              (indexBound_tail
                                                                                ('t'::('o'::[]))
                                                                                { attrName =
                                                                                ('f'::('r'::('o'::('m'::[]))));
                                                                                attrType =
                                                                                msi }.attrName
                                                                                ({ attrName =
                                                                                ('t'::('o'::[]));
                                                                                attrType =
                                                                                msi }.attrName :: ({ attrName =
                                                                                ('i'::('d'::[]));
                                                                                attrType =
                                                                                id }.attrName :: []))
                                                                                (indexBound_head
                                                                                  { attrName =
                                                                                  ('t'::('o'::[]));
                                                                                  attrType =
                                                                                  msi }.attrName
                                                                                  ({ attrName =
                                                                                  ('i'::('d'::[]));
                                                                                  attrType =
                                                                                  id }.attrName :: [])))) },
                                                                            (Var ((SyntaxKind
                                                                            (rqToP2 idxBits id)),
                                                                            rq)))))))) :: ((projT1
                                                                                           (ExistT
                                                                                           ({ attrName =
                                                                                           ('l'::('i'::('n'::('e'::[]))));
                                                                                           attrType =
                                                                                           (line
                                                                                           lgDataBytes
                                                                                           lgNumDatas) },
                                                                                           (Const
                                                                                           ({ attrName =
                                                                                           ('l'::('i'::('n'::('e'::[]))));
                                                                                           attrType =
                                                                                           (line
                                                                                           lgDataBytes
                                                                                           lgNumDatas) }.attrType,
                                                                                           (getDefaultConst
                                                                                           { attrName =
                                                                                           ('l'::('i'::('n'::('e'::[]))));
                                                                                           attrType =
                                                                                           (line
                                                                                           lgDataBytes
                                                                                           lgNumDatas) }.attrType)))))) :: (
    (projT1 (ExistT ({ attrName = ('i'::('d'::[])); attrType = id }, (Const ({ attrName =
      ('i'::('d'::[])); attrType = id }.attrType,
      (getDefaultConst { attrName = ('i'::('d'::[])); attrType = id }.attrType)))))) :: []))))),
    (icons' (ExistT ({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType = Bool }, (Const (Bool,
      (ConstBool true)))))
      ((projT1 (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
         (getAttrType ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
           (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
           msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
           ('i'::('d'::[])); attrType = id } :: [])))) { bindex = ('a'::('d'::('d'::('r'::[]))));
           indexb =
           (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
             (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
             msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
             msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))) }) },
         (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
         (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
         msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
         ('i'::('d'::[])); attrType = id } :: [])))), { bindex = ('a'::('d'::('d'::('r'::[]))));
         indexb =
         (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
           (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
           msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
           msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))) },
         (Var ((SyntaxKind (rqToP2 idxBits id)), rq))))))) :: ((projT1 (ExistT ({ attrName =
                                                                 ('t'::('o'::[])); attrType = msi },
                                                                 (toCompat (ReadField (({ attrName =
                                                                   ('a'::('d'::('d'::('r'::[]))));
                                                                   attrType =
                                                                   (addr2 idxBits) } :: ({ attrName =
                                                                   ('f'::('r'::('o'::('m'::[]))));
                                                                   attrType = msi } :: ({ attrName =
                                                                   ('t'::('o'::[])); attrType =
                                                                   msi } :: ({ attrName =
                                                                   ('i'::('d'::[])); attrType =
                                                                   id } :: [])))), { bindex =
                                                                   ('t'::('o'::[])); indexb =
                                                                   (indexBound_tail ('t'::('o'::[]))
                                                                     { attrName =
                                                                     ('a'::('d'::('d'::('r'::[]))));
                                                                     attrType =
                                                                     (addr2 idxBits) }.attrName
                                                                     ({ attrName =
                                                                     ('f'::('r'::('o'::('m'::[]))));
                                                                     attrType =
                                                                     msi }.attrName :: ({ attrName =
                                                                     ('t'::('o'::[])); attrType =
                                                                     msi }.attrName :: ({ attrName =
                                                                     ('i'::('d'::[])); attrType =
                                                                     id }.attrName :: [])))
                                                                     (indexBound_tail
                                                                       ('t'::('o'::[])) { attrName =
                                                                       ('f'::('r'::('o'::('m'::[]))));
                                                                       attrType = msi }.attrName
                                                                       ({ attrName =
                                                                       ('t'::('o'::[])); attrType =
                                                                       msi }.attrName :: ({ attrName =
                                                                       ('i'::('d'::[])); attrType =
                                                                       id }.attrName :: []))
                                                                       (indexBound_head { attrName =
                                                                         ('t'::('o'::[]));
                                                                         attrType = msi }.attrName
                                                                         ({ attrName =
                                                                         ('i'::('d'::[]));
                                                                         attrType =
                                                                         id }.attrName :: [])))) },
                                                                   (Var ((SyntaxKind
                                                                   (rqToP2 idxBits id)), rq)))))))) :: (
      (projT1 (ExistT ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
        (line lgDataBytes lgNumDatas) }, (Const ({ attrName = ('l'::('i'::('n'::('e'::[]))));
        attrType = (line lgDataBytes lgNumDatas) }.attrType,
        (getDefaultConst { attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrType)))))) :: ((projT1 (ExistT ({ attrName =
                                                               ('i'::('d'::[])); attrType = id },
                                                               (Const ({ attrName =
                                                               ('i'::('d'::[])); attrType =
                                                               id }.attrType,
                                                               (getDefaultConst { attrName =
                                                                 ('i'::('d'::[])); attrType =
                                                                 id }.attrType)))))) :: []))))
      (icons' (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (getAttrType ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
          msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
          ('i'::('d'::[])); attrType = id } :: [])))) { bindex = ('a'::('d'::('d'::('r'::[]))));
          indexb =
          (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
            (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
            msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
            msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))) }) },
        (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
        msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('i'::('d'::[]));
        attrType = id } :: [])))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
        (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
          msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))) },
        (Var ((SyntaxKind (rqToP2 idxBits id)), rq))))))
        ((projT1 (ExistT ({ attrName = ('t'::('o'::[])); attrType = msi },
           (toCompat (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
             (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
             msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
             ('i'::('d'::[])); attrType = id } :: [])))), { bindex = ('t'::('o'::[])); indexb =
             (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[]))));
               attrType = (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[]))));
               attrType = msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
               msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))
               (indexBound_tail ('t'::('o'::[])) { attrName = ('f'::('r'::('o'::('m'::[]))));
                 attrType = msi }.attrName ({ attrName = ('t'::('o'::[])); attrType =
                 msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: []))
                 (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName
                   ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))) }, (Var
             ((SyntaxKind (rqToP2 idxBits id)), rq)))))))) :: ((projT1 (ExistT ({ attrName =
                                                                 ('l'::('i'::('n'::('e'::[]))));
                                                                 attrType =
                                                                 (line lgDataBytes lgNumDatas) },
                                                                 (Const ({ attrName =
                                                                 ('l'::('i'::('n'::('e'::[]))));
                                                                 attrType =
                                                                 (line lgDataBytes lgNumDatas) }.attrType,
                                                                 (getDefaultConst { attrName =
                                                                   ('l'::('i'::('n'::('e'::[]))));
                                                                   attrType =
                                                                   (line lgDataBytes lgNumDatas) }.attrType)))))) :: (
        (projT1 (ExistT ({ attrName = ('i'::('d'::[])); attrType = id }, (Const ({ attrName =
          ('i'::('d'::[])); attrType = id }.attrType,
          (getDefaultConst { attrName = ('i'::('d'::[])); attrType = id }.attrType)))))) :: [])))
        (icons' (ExistT ({ attrName = ('t'::('o'::[])); attrType = msi },
          (toCompat (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
            (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
            msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
            ('i'::('d'::[])); attrType = id } :: [])))), { bindex = ('t'::('o'::[])); indexb =
            (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[]))));
              attrType = (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[]))));
              attrType = msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
              msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))
              (indexBound_tail ('t'::('o'::[])) { attrName = ('f'::('r'::('o'::('m'::[]))));
                attrType = msi }.attrName ({ attrName = ('t'::('o'::[])); attrType =
                msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: []))
                (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName
                  ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))) }, (Var
            ((SyntaxKind (rqToP2 idxBits id)), rq)))))))
          ((projT1 (ExistT ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
             (line lgDataBytes lgNumDatas) }, (Const ({ attrName = ('l'::('i'::('n'::('e'::[]))));
             attrType = (line lgDataBytes lgNumDatas) }.attrType,
             (getDefaultConst { attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
               (line lgDataBytes lgNumDatas) }.attrType)))))) :: ((projT1 (ExistT ({ attrName =
                                                                    ('i'::('d'::[])); attrType =
                                                                    id }, (Const ({ attrName =
                                                                    ('i'::('d'::[])); attrType =
                                                                    id }.attrType,
                                                                    (getDefaultConst { attrName =
                                                                      ('i'::('d'::[])); attrType =
                                                                      id }.attrType)))))) :: []))
          (icons' (ExistT ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
            (line lgDataBytes lgNumDatas) }, (Const ({ attrName = ('l'::('i'::('n'::('e'::[]))));
            attrType = (line lgDataBytes lgNumDatas) }.attrType,
            (getDefaultConst { attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
              (line lgDataBytes lgNumDatas) }.attrType)))))
            ((projT1 (ExistT ({ attrName = ('i'::('d'::[])); attrType = id }, (Const ({ attrName =
               ('i'::('d'::[])); attrType = id }.attrType,
               (getDefaultConst { attrName = ('i'::('d'::[])); attrType = id }.attrType)))))) :: [])
            (icons' (ExistT ({ attrName = ('i'::('d'::[])); attrType = id }, (Const ({ attrName =
              ('i'::('d'::[])); attrType = id }.attrType,
              (getDefaultConst { attrName = ('i'::('d'::[])); attrType = id }.attrType))))) [] Inil))))))),
    (fun rq' -> SMCall ({ nameVal =
    (toCEnq idxBits lgNumDatas lgDataBytes lgNumChildren id).attrName },
    (toCEnq idxBits lgNumDatas lgDataBytes lgNumChildren id).attrType, (BuildStruct
    (((projT1 (ExistT ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
          (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
          (rqToP (addr2 idxBits) id) } :: [])) { bindex = ('c'::('h'::('i'::('l'::('d'::[])))));
          indexb =
          (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
            (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
            (rqToP (addr2 idxBits) id) }.attrName :: [])) }) }, (Var ((SyntaxKind
        (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
          (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
          (rqToP (addr2 idxBits) id) } :: [])) { bindex = ('c'::('h'::('i'::('l'::('d'::[])))));
          indexb =
          (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
            (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
            (rqToP (addr2 idxBits) id) }.attrName :: [])) })), c))))) :: ((projT1 (ExistT
                                                                            ({ attrName =
                                                                            ('m'::('s'::('g'::[])));
                                                                            attrType =
                                                                            (fromP2 idxBits
                                                                              lgNumDatas lgDataBytes
                                                                              id) }, (Var
                                                                            ((SyntaxKind
                                                                            (fromP2 idxBits
                                                                              lgNumDatas lgDataBytes
                                                                              id)), rq'))))) :: [])),
    (icons' (ExistT ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
        (rqToP (addr2 idxBits) id) } :: [])) { bindex = ('c'::('h'::('i'::('l'::('d'::[])))));
        indexb =
        (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
          (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
          (rqToP (addr2 idxBits) id) }.attrName :: [])) }) }, (Var ((SyntaxKind
      (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
        (rqToP (addr2 idxBits) id) } :: [])) { bindex = ('c'::('h'::('i'::('l'::('d'::[])))));
        indexb =
        (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
          (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
          (rqToP (addr2 idxBits) id) }.attrName :: [])) })), c))))
      ((projT1 (ExistT ({ attrName = ('m'::('s'::('g'::[]))); attrType =
         (fromP2 idxBits lgNumDatas lgDataBytes id) }, (Var ((SyntaxKind
         (fromP2 idxBits lgNumDatas lgDataBytes id)), rq'))))) :: [])
      (icons' (ExistT ({ attrName = ('m'::('s'::('g'::[]))); attrType =
        (fromP2 idxBits lgNumDatas lgDataBytes id) }, (Var ((SyntaxKind
        (fromP2 idxBits lgNumDatas lgDataBytes id)), rq')))) [] Inil)))), (fun x -> SLet_
    ((SyntaxKind (Vector (Bool, lgNumChildren))), (UpdateVector (lgNumChildren, Bool, (Var
    ((SyntaxKind (dirw lgNumChildren)), dirw0)), (Var ((SyntaxKind
    (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
      (rqToP (addr2 idxBits) id) } :: [])) { bindex = ('c'::('h'::('i'::('l'::('d'::[])))));
      indexb =
      (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
        (rqToP (addr2 idxBits) id) }.attrName :: [])) })), c)), (Const (Bool, (ConstBool true))))),
    (fun dirw' -> SWriteReg ({ nameVal = ('c'::('R'::('q'::('D'::('i'::('r'::('w'::[]))))))) },
    (SyntaxKind (Vector (Bool, lgNumChildren))), (Var ((SyntaxKind (Vector (Bool, lgNumChildren))),
    dirw')), (SReturn (Const (void, (getDefaultConst void)))))))))))))))))))))))))))))), { nameVal =
    ('d'::('w'::('n'::('R'::('q'::[]))))) }))), (ConsInMetaModule ((MMERule (OneRule ((fun _ ->
    SMCall ({ nameVal = (rsFromCPop idxBits lgNumDatas lgDataBytes lgNumChildren).attrName },
    (rsFromCPop idxBits lgNumDatas lgDataBytes lgNumChildren).attrType, (Const
    ((rsFromCPop idxBits lgNumDatas lgDataBytes lgNumChildren).attrType.arg,
    (getDefaultConst (rsFromCPop idxBits lgNumDatas lgDataBytes lgNumChildren).attrType.arg))),
    (fun rsChild -> SLet_ ((SyntaxKind
    (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) } :: ({ attrName = ('r'::('s'::[])); attrType =
      (rsToP lgDataBytes lgNumDatas (addr2 idxBits)) } :: [])) { bindex =
      ('c'::('h'::('i'::('l'::('d'::[]))))); indexb =
      (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) }.attrName ({ attrName = ('r'::('s'::[])); attrType =
        (rsToP lgDataBytes lgNumDatas (addr2 idxBits)) }.attrName :: [])) })), (ReadField
    (({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
    (child lgNumChildren) } :: ({ attrName = ('r'::('s'::[])); attrType =
    (rsToP lgDataBytes lgNumDatas (addr2 idxBits)) } :: [])), { bindex =
    ('c'::('h'::('i'::('l'::('d'::[]))))); indexb =
    (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) }.attrName ({ attrName = ('r'::('s'::[])); attrType =
      (rsToP lgDataBytes lgNumDatas (addr2 idxBits)) }.attrName :: [])) }, (Var ((SyntaxKind
    (rsFromCPop idxBits lgNumDatas lgDataBytes lgNumChildren).attrType.ret), rsChild)))), (fun c ->
    SLet_ ((SyntaxKind (rsToP2 idxBits lgNumDatas lgDataBytes)), (ReadField (({ attrName =
    ('c'::('h'::('i'::('l'::('d'::[]))))); attrType = (child lgNumChildren) } :: ({ attrName =
    ('r'::('s'::[])); attrType = (rsToP lgDataBytes lgNumDatas (addr2 idxBits)) } :: [])),
    { bindex = ('r'::('s'::[])); indexb =
    (indexBound_tail ('r'::('s'::[])) { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) }.attrName ({ attrName = ('r'::('s'::[])); attrType =
      (rsToP lgDataBytes lgNumDatas (addr2 idxBits)) }.attrName :: [])
      (indexBound_head { attrName = ('r'::('s'::[])); attrType =
        (rsToP lgDataBytes lgNumDatas (addr2 idxBits)) }.attrName [])) }, (Var ((SyntaxKind
    (rsFromCPop idxBits lgNumDatas lgDataBytes lgNumChildren).attrType.ret), rsChild)))), (fun rs ->
    SLet_ ((SyntaxKind (idx0 idxBits)),
    (getIdx0 idxBits (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (addr2 idxBits) } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
      ('l'::('i'::('n'::('e'::[])))); attrType = (line lgDataBytes lgNumDatas) } :: ({ attrName =
      ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool } :: [])))), { bindex =
      ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr2 idxBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
        msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
        (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
        ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool }.attrName :: [])))) }, (Var
      ((SyntaxKind (rsToP2 idxBits lgNumDatas lgDataBytes)), rs))))), (fun idx1 -> SMCall
    ({ nameVal = (readDir idxBits lgNumChildren).attrName },
    (readDir idxBits lgNumChildren).attrType, (Var ((SyntaxKind (idx0 idxBits)), idx1)),
    (fun dir0 -> SLet_ ((SyntaxKind (Vector (msi, lgNumChildren))), (UpdateVector (lgNumChildren,
    msi, (Var ((SyntaxKind (readDir idxBits lgNumChildren).attrType.ret), dir0)), (Var ((SyntaxKind
    (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) } :: ({ attrName = ('r'::('s'::[])); attrType =
      (rsToP lgDataBytes lgNumDatas (addr2 idxBits)) } :: [])) { bindex =
      ('c'::('h'::('i'::('l'::('d'::[]))))); indexb =
      (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) }.attrName ({ attrName = ('r'::('s'::[])); attrType =
        (rsToP lgDataBytes lgNumDatas (addr2 idxBits)) }.attrName :: [])) })), c)), (ReadField
    (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (addr2 idxBits) } :: ({ attrName =
    ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
    (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('s'::('V'::('o'::('l'::[])))));
    attrType = Bool } :: [])))), { bindex = ('t'::('o'::[])); indexb =
    (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (addr2 idxBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
      msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
      (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
      ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool }.attrName :: [])))
      (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName ({ attrName =
        ('l'::('i'::('n'::('e'::[])))); attrType =
        (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
        ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool }.attrName :: [])))) }, (Var
    ((SyntaxKind (rsToP2 idxBits lgNumDatas lgDataBytes)), rs)))))), (fun dir' -> SMCall
    ({ nameVal = (writeDir idxBits lgNumChildren).attrName },
    (writeDir idxBits lgNumChildren).attrType, (BuildStruct
    (((projT1 (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx0 idxBits) },
        (Var ((SyntaxKind (idx0 idxBits)), idx1))))) :: ((projT1 (ExistT ({ attrName =
                                                           ('d'::('a'::('t'::('a'::[]))));
                                                           attrType = (Vector (msi,
                                                           lgNumChildren)) }, (Var ((SyntaxKind
                                                           (Vector (msi, lgNumChildren))), dir'))))) :: [])),
    (icons' (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx0 idxBits) }, (Var
      ((SyntaxKind (idx0 idxBits)), idx1))))
      ((projT1 (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType = (Vector (msi,
         lgNumChildren)) }, (Var ((SyntaxKind (Vector (msi, lgNumChildren))), dir'))))) :: [])
      (icons' (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType = (Vector (msi,
        lgNumChildren)) }, (Var ((SyntaxKind (Vector (msi, lgNumChildren))), dir')))) [] Inil)))),
    (fun x -> SReadReg ({ nameVal = ('c'::('R'::('q'::('D'::('i'::('r'::('w'::[]))))))) },
    (SyntaxKind (Vector (Bool, lgNumChildren))), (fun dirw0 -> SLet_ ((SyntaxKind (Vector (Bool,
    lgNumChildren))), (UpdateVector (lgNumChildren, Bool, (Var ((SyntaxKind (Vector (Bool,
    lgNumChildren))), dirw0)), (Var ((SyntaxKind
    (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) } :: ({ attrName = ('r'::('s'::[])); attrType =
      (rsToP lgDataBytes lgNumDatas (addr2 idxBits)) } :: [])) { bindex =
      ('c'::('h'::('i'::('l'::('d'::[]))))); indexb =
      (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) }.attrName ({ attrName = ('r'::('s'::[])); attrType =
        (rsToP lgDataBytes lgNumDatas (addr2 idxBits)) }.attrName :: [])) })), c)), (Const (Bool,
    (ConstBool false))))), (fun dirw' -> SWriteReg ({ nameVal =
    ('c'::('R'::('q'::('D'::('i'::('r'::('w'::[]))))))) }, (SyntaxKind (Vector (Bool,
    lgNumChildren))), (Var ((SyntaxKind (Vector (Bool, lgNumChildren))), dirw')), (SIfElse ((Eq
    (msi, (ReadIndex (lgNumChildren, msi, (Var ((SyntaxKind
    (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) } :: ({ attrName = ('r'::('s'::[])); attrType =
      (rsToP lgDataBytes lgNumDatas (addr2 idxBits)) } :: [])) { bindex =
      ('c'::('h'::('i'::('l'::('d'::[]))))); indexb =
      (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) }.attrName ({ attrName = ('r'::('s'::[])); attrType =
        (rsToP lgDataBytes lgNumDatas (addr2 idxBits)) }.attrName :: [])) })), c)), (Var
    ((SyntaxKind (readDir idxBits lgNumChildren).attrType.ret), dir0)))), (Const ((Bit
    (Pervasives.succ (Pervasives.succ 0))), (ConstBit ((Pervasives.succ (Pervasives.succ 0)),
    (natToWord (Pervasives.succ (Pervasives.succ 0)) mod0))))))), void, (SMCall ({ nameVal =
    (writeLine0 idxBits lgNumDatas lgDataBytes).attrName },
    (writeLine0 idxBits lgNumDatas lgDataBytes).attrType, (BuildStruct
    (((projT1 (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx0 idxBits) },
        (Var ((SyntaxKind (idx0 idxBits)), idx1))))) :: ((projT1 (ExistT ({ attrName =
                                                           ('d'::('a'::('t'::('a'::[]))));
                                                           attrType =
                                                           (getAttrType ({ attrName =
                                                             ('a'::('d'::('d'::('r'::[]))));
                                                             attrType =
                                                             (addr2 idxBits) } :: ({ attrName =
                                                             ('t'::('o'::[])); attrType =
                                                             msi } :: ({ attrName =
                                                             ('l'::('i'::('n'::('e'::[]))));
                                                             attrType =
                                                             (line lgDataBytes lgNumDatas) } :: ({ attrName =
                                                             ('i'::('s'::('V'::('o'::('l'::[])))));
                                                             attrType = Bool } :: [])))) { bindex =
                                                             ('l'::('i'::('n'::('e'::[]))));
                                                             indexb =
                                                             (indexBound_tail
                                                               ('l'::('i'::('n'::('e'::[]))))
                                                               { attrName =
                                                               ('a'::('d'::('d'::('r'::[]))));
                                                               attrType = (addr2 idxBits) }.attrName
                                                               ({ attrName = ('t'::('o'::[]));
                                                               attrType =
                                                               msi }.attrName :: ({ attrName =
                                                               ('l'::('i'::('n'::('e'::[]))));
                                                               attrType =
                                                               (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                               ('i'::('s'::('V'::('o'::('l'::[])))));
                                                               attrType = Bool }.attrName :: [])))
                                                               (indexBound_tail
                                                                 ('l'::('i'::('n'::('e'::[]))))
                                                                 { attrName = ('t'::('o'::[]));
                                                                 attrType = msi }.attrName
                                                                 ({ attrName =
                                                                 ('l'::('i'::('n'::('e'::[]))));
                                                                 attrType =
                                                                 (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                                 ('i'::('s'::('V'::('o'::('l'::[])))));
                                                                 attrType = Bool }.attrName :: []))
                                                                 (indexBound_head { attrName =
                                                                   ('l'::('i'::('n'::('e'::[]))));
                                                                   attrType =
                                                                   (line lgDataBytes lgNumDatas) }.attrName
                                                                   ({ attrName =
                                                                   ('i'::('s'::('V'::('o'::('l'::[])))));
                                                                   attrType =
                                                                   Bool }.attrName :: [])))) }) },
                                                           (ReadField (({ attrName =
                                                           ('a'::('d'::('d'::('r'::[]))));
                                                           attrType =
                                                           (addr2 idxBits) } :: ({ attrName =
                                                           ('t'::('o'::[])); attrType =
                                                           msi } :: ({ attrName =
                                                           ('l'::('i'::('n'::('e'::[]))));
                                                           attrType =
                                                           (line lgDataBytes lgNumDatas) } :: ({ attrName =
                                                           ('i'::('s'::('V'::('o'::('l'::[])))));
                                                           attrType = Bool } :: [])))), { bindex =
                                                           ('l'::('i'::('n'::('e'::[])))); indexb =
                                                           (indexBound_tail
                                                             ('l'::('i'::('n'::('e'::[]))))
                                                             { attrName =
                                                             ('a'::('d'::('d'::('r'::[]))));
                                                             attrType = (addr2 idxBits) }.attrName
                                                             ({ attrName = ('t'::('o'::[]));
                                                             attrType =
                                                             msi }.attrName :: ({ attrName =
                                                             ('l'::('i'::('n'::('e'::[]))));
                                                             attrType =
                                                             (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                             ('i'::('s'::('V'::('o'::('l'::[])))));
                                                             attrType = Bool }.attrName :: [])))
                                                             (indexBound_tail
                                                               ('l'::('i'::('n'::('e'::[]))))
                                                               { attrName = ('t'::('o'::[]));
                                                               attrType = msi }.attrName
                                                               ({ attrName =
                                                               ('l'::('i'::('n'::('e'::[]))));
                                                               attrType =
                                                               (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
                                                               ('i'::('s'::('V'::('o'::('l'::[])))));
                                                               attrType = Bool }.attrName :: []))
                                                               (indexBound_head { attrName =
                                                                 ('l'::('i'::('n'::('e'::[]))));
                                                                 attrType =
                                                                 (line lgDataBytes lgNumDatas) }.attrName
                                                                 ({ attrName =
                                                                 ('i'::('s'::('V'::('o'::('l'::[])))));
                                                                 attrType = Bool }.attrName :: [])))) },
                                                           (Var ((SyntaxKind
                                                           (rsToP2 idxBits lgNumDatas lgDataBytes)),
                                                           rs))))))) :: [])),
    (icons' (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx0 idxBits) }, (Var
      ((SyntaxKind (idx0 idxBits)), idx1))))
      ((projT1 (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
         (getAttrType ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
           (addr2 idxBits) } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
           ('l'::('i'::('n'::('e'::[])))); attrType =
           (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('s'::('V'::('o'::('l'::[])))));
           attrType = Bool } :: [])))) { bindex = ('l'::('i'::('n'::('e'::[])))); indexb =
           (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName =
             ('a'::('d'::('d'::('r'::[])))); attrType = (addr2 idxBits) }.attrName ({ attrName =
             ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
             ('l'::('i'::('n'::('e'::[])))); attrType =
             (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
             ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool }.attrName :: [])))
             (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName = ('t'::('o'::[]));
               attrType = msi }.attrName ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
               (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
               ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool }.attrName :: []))
               (indexBound_head { attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
                 (line lgDataBytes lgNumDatas) }.attrName ({ attrName =
                 ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool }.attrName :: [])))) }) },
         (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
         (addr2 idxBits) } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
         ('l'::('i'::('n'::('e'::[])))); attrType = (line lgDataBytes lgNumDatas) } :: ({ attrName =
         ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool } :: [])))), { bindex =
         ('l'::('i'::('n'::('e'::[])))); indexb =
         (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName =
           ('a'::('d'::('d'::('r'::[])))); attrType = (addr2 idxBits) }.attrName ({ attrName =
           ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
           ('l'::('i'::('n'::('e'::[])))); attrType =
           (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
           ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool }.attrName :: [])))
           (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName = ('t'::('o'::[])); attrType =
             msi }.attrName ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
             (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
             ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool }.attrName :: []))
             (indexBound_head { attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
               (line lgDataBytes lgNumDatas) }.attrName ({ attrName =
               ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool }.attrName :: [])))) }, (Var
         ((SyntaxKind (rsToP2 idxBits lgNumDatas lgDataBytes)), rs))))))) :: [])
      (icons' (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType =
        (getAttrType ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (addr2 idxBits) } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
          ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) } :: ({ attrName = ('i'::('s'::('V'::('o'::('l'::[])))));
          attrType = Bool } :: [])))) { bindex = ('l'::('i'::('n'::('e'::[])))); indexb =
          (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName =
            ('a'::('d'::('d'::('r'::[])))); attrType = (addr2 idxBits) }.attrName ({ attrName =
            ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
            ('l'::('i'::('n'::('e'::[])))); attrType =
            (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
            ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool }.attrName :: [])))
            (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName = ('t'::('o'::[]));
              attrType = msi }.attrName ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
              (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
              ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool }.attrName :: []))
              (indexBound_head { attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
                (line lgDataBytes lgNumDatas) }.attrName ({ attrName =
                ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool }.attrName :: [])))) }) },
        (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr2 idxBits) } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
        ('l'::('i'::('n'::('e'::[])))); attrType = (line lgDataBytes lgNumDatas) } :: ({ attrName =
        ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool } :: [])))), { bindex =
        ('l'::('i'::('n'::('e'::[])))); indexb =
        (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName = ('a'::('d'::('d'::('r'::[]))));
          attrType = (addr2 idxBits) }.attrName ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
          (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
          ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool }.attrName :: [])))
          (indexBound_tail ('l'::('i'::('n'::('e'::[])))) { attrName = ('t'::('o'::[])); attrType =
            msi }.attrName ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
            (line lgDataBytes lgNumDatas) }.attrName :: ({ attrName =
            ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool }.attrName :: []))
            (indexBound_head { attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
              (line lgDataBytes lgNumDatas) }.attrName ({ attrName =
              ('i'::('s'::('V'::('o'::('l'::[]))))); attrType = Bool }.attrName :: [])))) }, (Var
        ((SyntaxKind (rsToP2 idxBits lgNumDatas lgDataBytes)), rs)))))) [] Inil)))), (fun x0 ->
    SReturn (Const (void, (getDefaultConst void)))))), (SReturn (Const (void,
    (getDefaultConst void)))), (fun x0 -> SReturn (Const (void,
    (getDefaultConst void)))))))))))))))))))))))))), { nameVal =
    ('d'::('w'::('n'::('R'::('s'::[]))))) }))), (ConsInMetaModule ((MMERule (OneRule ((fun _ ->
    SReadReg ({ nameVal = ('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[])))))))) }, (SyntaxKind
    Bool), (fun valid -> SAssert_ ((Var ((SyntaxKind Bool), valid)), (SMCall ({ nameVal =
    (rqFromCPop idxBits lgNumChildren id).attrName },
    (rqFromCPop idxBits lgNumChildren id).attrType, (Const
    ((rqFromCPop idxBits lgNumChildren id).attrType.arg,
    (getDefaultConst (rqFromCPop idxBits lgNumChildren id).attrType.arg))), (fun rqChild -> SLet_
    ((SyntaxKind
    (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
      (rqToP (addr2 idxBits) id) } :: [])) { bindex = ('c'::('h'::('i'::('l'::('d'::[])))));
      indexb =
      (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
        (rqToP (addr2 idxBits) id) }.attrName :: [])) })), (ReadField (({ attrName =
    ('c'::('h'::('i'::('l'::('d'::[]))))); attrType = (child lgNumChildren) } :: ({ attrName =
    ('r'::('q'::[])); attrType = (rqToP (addr2 idxBits) id) } :: [])), { bindex =
    ('c'::('h'::('i'::('l'::('d'::[]))))); indexb =
    (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
      (rqToP (addr2 idxBits) id) }.attrName :: [])) }, (Var ((SyntaxKind
    (rqFromCPop idxBits lgNumChildren id).attrType.ret), rqChild)))), (fun c -> SLet_ ((SyntaxKind
    (rqToP2 idxBits id)), (ReadField (({ attrName = ('c'::('h'::('i'::('l'::('d'::[])))));
    attrType = (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
    (rqToP (addr2 idxBits) id) } :: [])), { bindex = ('r'::('q'::[])); indexb =
    (indexBound_tail ('r'::('q'::[])) { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
      (rqToP (addr2 idxBits) id) }.attrName :: [])
      (indexBound_head { attrName = ('r'::('q'::[])); attrType =
        (rqToP (addr2 idxBits) id) }.attrName [])) }, (Var ((SyntaxKind
    (rqFromCPop idxBits lgNumChildren id).attrType.ret), rqChild)))), (fun rq -> SLet_ ((SyntaxKind
    (idx0 idxBits)),
    (getIdx0 idxBits (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
      msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('i'::('d'::[]));
      attrType = id } :: [])))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
      (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
        msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
        ('i'::('d'::[])); attrType = id }.attrName :: [])))) }, (Var ((SyntaxKind
      (rqToP2 idxBits id)), rq))))), (fun idx1 -> SMCall ({ nameVal =
    (readDir idxBits lgNumChildren).attrName }, (readDir idxBits lgNumChildren).attrType, (Var
    ((SyntaxKind (idx0 idxBits)), idx1)), (fun dir0 -> SAssert_ ((UniBool (Neg, (BinBitBool
    ((Pervasives.succ (Pervasives.succ 0)), (Pervasives.succ (Pervasives.succ 0)), (Lt
    (Pervasives.succ (Pervasives.succ 0))), (ReadField (({ attrName =
    ('a'::('d'::('d'::('r'::[])))); attrType = (addr2 idxBits) } :: ({ attrName =
    ('f'::('r'::('o'::('m'::[])))); attrType = msi } :: ({ attrName = ('t'::('o'::[])); attrType =
    msi } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: [])))), { bindex =
    ('f'::('r'::('o'::('m'::[])))); indexb =
    (indexBound_tail ('f'::('r'::('o'::('m'::[])))) { attrName = ('a'::('d'::('d'::('r'::[]))));
      attrType = (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
      msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
      ('i'::('d'::[])); attrType = id }.attrName :: [])))
      (indexBound_head { attrName = ('f'::('r'::('o'::('m'::[])))); attrType = msi }.attrName
        ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName = ('i'::('d'::[]));
        attrType = id }.attrName :: [])))) }, (Var ((SyntaxKind (rqToP2 idxBits id)), rq)))),
    (ReadIndex (lgNumChildren, msi, (Var ((SyntaxKind
    (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
      (rqToP (addr2 idxBits) id) } :: [])) { bindex = ('c'::('h'::('i'::('l'::('d'::[])))));
      indexb =
      (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
        (rqToP (addr2 idxBits) id) }.attrName :: [])) })), c)), (Var ((SyntaxKind
    (readDir idxBits lgNumChildren).attrType.ret), dir0)))))))), (SAssert_
    ((othersCompat lgNumChildren (Var ((SyntaxKind
       (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
         (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
         (rqToP (addr2 idxBits) id) } :: [])) { bindex = ('c'::('h'::('i'::('l'::('d'::[])))));
         indexb =
         (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
           (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
           (rqToP (addr2 idxBits) id) }.attrName :: [])) })), c)) (ReadField (({ attrName =
       ('a'::('d'::('d'::('r'::[])))); attrType = (addr2 idxBits) } :: ({ attrName =
       ('f'::('r'::('o'::('m'::[])))); attrType = msi } :: ({ attrName = ('t'::('o'::[]));
       attrType = msi } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: [])))), { bindex =
       ('t'::('o'::[])); indexb =
       (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
         (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
         msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
         msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))
         (indexBound_tail ('t'::('o'::[])) { attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
           msi }.attrName ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
           ('i'::('d'::[])); attrType = id }.attrName :: []))
           (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName ({ attrName =
             ('i'::('d'::[])); attrType = id }.attrName :: [])))) }, (Var ((SyntaxKind
       (rqToP2 idxBits id)), rq)))) (Var ((SyntaxKind (readDir idxBits lgNumChildren).attrType.ret),
       dir0))), (SMCall ({ nameVal = (readLine0 idxBits lgNumDatas lgDataBytes).attrName },
    (readLine0 idxBits lgNumDatas lgDataBytes).attrType, (Var ((SyntaxKind (idx0 idxBits)), idx1)),
    (fun line2 -> SLet_ ((SyntaxKind (fromP2 idxBits lgNumDatas lgDataBytes id)), (BuildStruct
    (((projT1 (ExistT ({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType = Bool }, (Const (Bool,
        (ConstBool false)))))) :: ((projT1 (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[]))));
                                     attrType =
                                     (getAttrType ({ attrName = ('a'::('d'::('d'::('r'::[]))));
                                       attrType = (addr2 idxBits) } :: ({ attrName =
                                       ('f'::('r'::('o'::('m'::[])))); attrType =
                                       msi } :: ({ attrName = ('t'::('o'::[])); attrType =
                                       msi } :: ({ attrName = ('i'::('d'::[])); attrType =
                                       id } :: [])))) { bindex = ('a'::('d'::('d'::('r'::[]))));
                                       indexb =
                                       (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[]))));
                                         attrType = (addr2 idxBits) }.attrName ({ attrName =
                                         ('f'::('r'::('o'::('m'::[])))); attrType =
                                         msi }.attrName :: ({ attrName = ('t'::('o'::[]));
                                         attrType = msi }.attrName :: ({ attrName =
                                         ('i'::('d'::[])); attrType = id }.attrName :: [])))) }) },
                                     (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[]))));
                                     attrType = (addr2 idxBits) } :: ({ attrName =
                                     ('f'::('r'::('o'::('m'::[])))); attrType =
                                     msi } :: ({ attrName = ('t'::('o'::[])); attrType =
                                     msi } :: ({ attrName = ('i'::('d'::[])); attrType =
                                     id } :: [])))), { bindex = ('a'::('d'::('d'::('r'::[]))));
                                     indexb =
                                     (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[]))));
                                       attrType = (addr2 idxBits) }.attrName ({ attrName =
                                       ('f'::('r'::('o'::('m'::[])))); attrType =
                                       msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
                                       msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
                                       id }.attrName :: [])))) }, (Var ((SyntaxKind
                                     (rqToP2 idxBits id)), rq))))))) :: ((projT1 (ExistT
                                                                           ({ attrName =
                                                                           ('t'::('o'::[]));
                                                                           attrType =
                                                                           (getAttrType
                                                                             ({ attrName =
                                                                             ('a'::('d'::('d'::('r'::[]))));
                                                                             attrType =
                                                                             (addr2 idxBits) } :: ({ attrName =
                                                                             ('f'::('r'::('o'::('m'::[]))));
                                                                             attrType =
                                                                             msi } :: ({ attrName =
                                                                             ('t'::('o'::[]));
                                                                             attrType =
                                                                             msi } :: ({ attrName =
                                                                             ('i'::('d'::[]));
                                                                             attrType =
                                                                             id } :: []))))
                                                                             { bindex =
                                                                             ('t'::('o'::[]));
                                                                             indexb =
                                                                             (indexBound_tail
                                                                               ('t'::('o'::[]))
                                                                               { attrName =
                                                                               ('a'::('d'::('d'::('r'::[]))));
                                                                               attrType =
                                                                               (addr2 idxBits) }.attrName
                                                                               ({ attrName =
                                                                               ('f'::('r'::('o'::('m'::[]))));
                                                                               attrType =
                                                                               msi }.attrName :: ({ attrName =
                                                                               ('t'::('o'::[]));
                                                                               attrType =
                                                                               msi }.attrName :: ({ attrName =
                                                                               ('i'::('d'::[]));
                                                                               attrType =
                                                                               id }.attrName :: [])))
                                                                               (indexBound_tail
                                                                                 ('t'::('o'::[]))
                                                                                 { attrName =
                                                                                 ('f'::('r'::('o'::('m'::[]))));
                                                                                 attrType =
                                                                                 msi }.attrName
                                                                                 ({ attrName =
                                                                                 ('t'::('o'::[]));
                                                                                 attrType =
                                                                                 msi }.attrName :: ({ attrName =
                                                                                 ('i'::('d'::[]));
                                                                                 attrType =
                                                                                 id }.attrName :: []))
                                                                                 (indexBound_head
                                                                                   { attrName =
                                                                                   ('t'::('o'::[]));
                                                                                   attrType =
                                                                                   msi }.attrName
                                                                                   ({ attrName =
                                                                                   ('i'::('d'::[]));
                                                                                   attrType =
                                                                                   id }.attrName :: [])))) }) },
                                                                           (ReadField (({ attrName =
                                                                           ('a'::('d'::('d'::('r'::[]))));
                                                                           attrType =
                                                                           (addr2 idxBits) } :: ({ attrName =
                                                                           ('f'::('r'::('o'::('m'::[]))));
                                                                           attrType =
                                                                           msi } :: ({ attrName =
                                                                           ('t'::('o'::[]));
                                                                           attrType =
                                                                           msi } :: ({ attrName =
                                                                           ('i'::('d'::[]));
                                                                           attrType =
                                                                           id } :: [])))),
                                                                           { bindex =
                                                                           ('t'::('o'::[]));
                                                                           indexb =
                                                                           (indexBound_tail
                                                                             ('t'::('o'::[]))
                                                                             { attrName =
                                                                             ('a'::('d'::('d'::('r'::[]))));
                                                                             attrType =
                                                                             (addr2 idxBits) }.attrName
                                                                             ({ attrName =
                                                                             ('f'::('r'::('o'::('m'::[]))));
                                                                             attrType =
                                                                             msi }.attrName :: ({ attrName =
                                                                             ('t'::('o'::[]));
                                                                             attrType =
                                                                             msi }.attrName :: ({ attrName =
                                                                             ('i'::('d'::[]));
                                                                             attrType =
                                                                             id }.attrName :: [])))
                                                                             (indexBound_tail
                                                                               ('t'::('o'::[]))
                                                                               { attrName =
                                                                               ('f'::('r'::('o'::('m'::[]))));
                                                                               attrType =
                                                                               msi }.attrName
                                                                               ({ attrName =
                                                                               ('t'::('o'::[]));
                                                                               attrType =
                                                                               msi }.attrName :: ({ attrName =
                                                                               ('i'::('d'::[]));
                                                                               attrType =
                                                                               id }.attrName :: []))
                                                                               (indexBound_head
                                                                                 { attrName =
                                                                                 ('t'::('o'::[]));
                                                                                 attrType =
                                                                                 msi }.attrName
                                                                                 ({ attrName =
                                                                                 ('i'::('d'::[]));
                                                                                 attrType =
                                                                                 id }.attrName :: [])))) },
                                                                           (Var ((SyntaxKind
                                                                           (rqToP2 idxBits id)),
                                                                           rq))))))) :: ((projT1
                                                                                           (ExistT
                                                                                           ({ attrName =
                                                                                           ('l'::('i'::('n'::('e'::[]))));
                                                                                           attrType =
                                                                                           (readLine0
                                                                                           idxBits
                                                                                           lgNumDatas
                                                                                           lgDataBytes).attrType.ret },
                                                                                           (Var
                                                                                           ((SyntaxKind
                                                                                           (readLine0
                                                                                           idxBits
                                                                                           lgNumDatas
                                                                                           lgDataBytes).attrType.ret),
                                                                                           line2))))) :: (
    (projT1 (ExistT ({ attrName = ('i'::('d'::[])); attrType =
      (getAttrType ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
        msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('i'::('d'::[]));
        attrType = id } :: [])))) { bindex = ('i'::('d'::[])); indexb =
        (indexBound_tail ('i'::('d'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
          msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))
          (indexBound_tail ('i'::('d'::[])) { attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
            msi }.attrName ({ attrName = ('t'::('o'::[])); attrType =
            msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: []))
            (indexBound_tail ('i'::('d'::[])) { attrName = ('t'::('o'::[])); attrType =
              msi }.attrName ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])
              (indexBound_head { attrName = ('i'::('d'::[])); attrType = id }.attrName [])))) }) },
      (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
      msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('i'::('d'::[]));
      attrType = id } :: [])))), { bindex = ('i'::('d'::[])); indexb =
      (indexBound_tail ('i'::('d'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
        msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
        ('i'::('d'::[])); attrType = id }.attrName :: [])))
        (indexBound_tail ('i'::('d'::[])) { attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
          msi }.attrName ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
          ('i'::('d'::[])); attrType = id }.attrName :: []))
          (indexBound_tail ('i'::('d'::[])) { attrName = ('t'::('o'::[])); attrType = msi }.attrName
            ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])
            (indexBound_head { attrName = ('i'::('d'::[])); attrType = id }.attrName [])))) }, (Var
      ((SyntaxKind (rqToP2 idxBits id)), rq))))))) :: []))))),
    (icons' (ExistT ({ attrName = ('i'::('s'::('R'::('q'::[])))); attrType = Bool }, (Const (Bool,
      (ConstBool false)))))
      ((projT1 (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
         (getAttrType ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
           (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
           msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
           ('i'::('d'::[])); attrType = id } :: [])))) { bindex = ('a'::('d'::('d'::('r'::[]))));
           indexb =
           (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
             (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
             msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
             msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))) }) },
         (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
         (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
         msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
         ('i'::('d'::[])); attrType = id } :: [])))), { bindex = ('a'::('d'::('d'::('r'::[]))));
         indexb =
         (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
           (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
           msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
           msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))) },
         (Var ((SyntaxKind (rqToP2 idxBits id)), rq))))))) :: ((projT1 (ExistT ({ attrName =
                                                                 ('t'::('o'::[])); attrType =
                                                                 (getAttrType ({ attrName =
                                                                   ('a'::('d'::('d'::('r'::[]))));
                                                                   attrType =
                                                                   (addr2 idxBits) } :: ({ attrName =
                                                                   ('f'::('r'::('o'::('m'::[]))));
                                                                   attrType = msi } :: ({ attrName =
                                                                   ('t'::('o'::[])); attrType =
                                                                   msi } :: ({ attrName =
                                                                   ('i'::('d'::[])); attrType =
                                                                   id } :: [])))) { bindex =
                                                                   ('t'::('o'::[])); indexb =
                                                                   (indexBound_tail ('t'::('o'::[]))
                                                                     { attrName =
                                                                     ('a'::('d'::('d'::('r'::[]))));
                                                                     attrType =
                                                                     (addr2 idxBits) }.attrName
                                                                     ({ attrName =
                                                                     ('f'::('r'::('o'::('m'::[]))));
                                                                     attrType =
                                                                     msi }.attrName :: ({ attrName =
                                                                     ('t'::('o'::[])); attrType =
                                                                     msi }.attrName :: ({ attrName =
                                                                     ('i'::('d'::[])); attrType =
                                                                     id }.attrName :: [])))
                                                                     (indexBound_tail
                                                                       ('t'::('o'::[])) { attrName =
                                                                       ('f'::('r'::('o'::('m'::[]))));
                                                                       attrType = msi }.attrName
                                                                       ({ attrName =
                                                                       ('t'::('o'::[])); attrType =
                                                                       msi }.attrName :: ({ attrName =
                                                                       ('i'::('d'::[])); attrType =
                                                                       id }.attrName :: []))
                                                                       (indexBound_head { attrName =
                                                                         ('t'::('o'::[]));
                                                                         attrType = msi }.attrName
                                                                         ({ attrName =
                                                                         ('i'::('d'::[]));
                                                                         attrType =
                                                                         id }.attrName :: [])))) }) },
                                                                 (ReadField (({ attrName =
                                                                 ('a'::('d'::('d'::('r'::[]))));
                                                                 attrType =
                                                                 (addr2 idxBits) } :: ({ attrName =
                                                                 ('f'::('r'::('o'::('m'::[]))));
                                                                 attrType = msi } :: ({ attrName =
                                                                 ('t'::('o'::[])); attrType =
                                                                 msi } :: ({ attrName =
                                                                 ('i'::('d'::[])); attrType =
                                                                 id } :: [])))), { bindex =
                                                                 ('t'::('o'::[])); indexb =
                                                                 (indexBound_tail ('t'::('o'::[]))
                                                                   { attrName =
                                                                   ('a'::('d'::('d'::('r'::[]))));
                                                                   attrType =
                                                                   (addr2 idxBits) }.attrName
                                                                   ({ attrName =
                                                                   ('f'::('r'::('o'::('m'::[]))));
                                                                   attrType =
                                                                   msi }.attrName :: ({ attrName =
                                                                   ('t'::('o'::[])); attrType =
                                                                   msi }.attrName :: ({ attrName =
                                                                   ('i'::('d'::[])); attrType =
                                                                   id }.attrName :: [])))
                                                                   (indexBound_tail ('t'::('o'::[]))
                                                                     { attrName =
                                                                     ('f'::('r'::('o'::('m'::[]))));
                                                                     attrType = msi }.attrName
                                                                     ({ attrName = ('t'::('o'::[]));
                                                                     attrType =
                                                                     msi }.attrName :: ({ attrName =
                                                                     ('i'::('d'::[])); attrType =
                                                                     id }.attrName :: []))
                                                                     (indexBound_head { attrName =
                                                                       ('t'::('o'::[])); attrType =
                                                                       msi }.attrName ({ attrName =
                                                                       ('i'::('d'::[])); attrType =
                                                                       id }.attrName :: [])))) },
                                                                 (Var ((SyntaxKind
                                                                 (rqToP2 idxBits id)), rq))))))) :: (
      (projT1 (ExistT ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
        (readLine0 idxBits lgNumDatas lgDataBytes).attrType.ret }, (Var ((SyntaxKind
        (readLine0 idxBits lgNumDatas lgDataBytes).attrType.ret), line2))))) :: ((projT1 (ExistT
                                                                                   ({ attrName =
                                                                                   ('i'::('d'::[]));
                                                                                   attrType =
                                                                                   (getAttrType
                                                                                     ({ attrName =
                                                                                     ('a'::('d'::('d'::('r'::[]))));
                                                                                     attrType =
                                                                                     (addr2 idxBits) } :: ({ attrName =
                                                                                     ('f'::('r'::('o'::('m'::[]))));
                                                                                     attrType =
                                                                                     msi } :: ({ attrName =
                                                                                     ('t'::('o'::[]));
                                                                                     attrType =
                                                                                     msi } :: ({ attrName =
                                                                                     ('i'::('d'::[]));
                                                                                     attrType =
                                                                                     id } :: []))))
                                                                                     { bindex =
                                                                                     ('i'::('d'::[]));
                                                                                     indexb =
                                                                                     (indexBound_tail
                                                                                       ('i'::('d'::[]))
                                                                                       { attrName =
                                                                                       ('a'::('d'::('d'::('r'::[]))));
                                                                                       attrType =
                                                                                       (addr2
                                                                                         idxBits) }.attrName
                                                                                       ({ attrName =
                                                                                       ('f'::('r'::('o'::('m'::[]))));
                                                                                       attrType =
                                                                                       msi }.attrName :: ({ attrName =
                                                                                       ('t'::('o'::[]));
                                                                                       attrType =
                                                                                       msi }.attrName :: ({ attrName =
                                                                                       ('i'::('d'::[]));
                                                                                       attrType =
                                                                                       id }.attrName :: [])))
                                                                                       (indexBound_tail
                                                                                         ('i'::('d'::[]))
                                                                                         { attrName =
                                                                                         ('f'::('r'::('o'::('m'::[]))));
                                                                                         attrType =
                                                                                         msi }.attrName
                                                                                         ({ attrName =
                                                                                         ('t'::('o'::[]));
                                                                                         attrType =
                                                                                         msi }.attrName :: ({ attrName =
                                                                                         ('i'::('d'::[]));
                                                                                         attrType =
                                                                                         id }.attrName :: []))
                                                                                         (indexBound_tail
                                                                                           ('i'::('d'::[]))
                                                                                           { attrName =
                                                                                           ('t'::('o'::[]));
                                                                                           attrType =
                                                                                           msi }.attrName
                                                                                           ({ attrName =
                                                                                           ('i'::('d'::[]));
                                                                                           attrType =
                                                                                           id }.attrName :: [])
                                                                                           (indexBound_head
                                                                                           { attrName =
                                                                                           ('i'::('d'::[]));
                                                                                           attrType =
                                                                                           id }.attrName
                                                                                           [])))) }) },
                                                                                   (ReadField
                                                                                   (({ attrName =
                                                                                   ('a'::('d'::('d'::('r'::[]))));
                                                                                   attrType =
                                                                                   (addr2 idxBits) } :: ({ attrName =
                                                                                   ('f'::('r'::('o'::('m'::[]))));
                                                                                   attrType =
                                                                                   msi } :: ({ attrName =
                                                                                   ('t'::('o'::[]));
                                                                                   attrType =
                                                                                   msi } :: ({ attrName =
                                                                                   ('i'::('d'::[]));
                                                                                   attrType =
                                                                                   id } :: [])))),
                                                                                   { bindex =
                                                                                   ('i'::('d'::[]));
                                                                                   indexb =
                                                                                   (indexBound_tail
                                                                                     ('i'::('d'::[]))
                                                                                     { attrName =
                                                                                     ('a'::('d'::('d'::('r'::[]))));
                                                                                     attrType =
                                                                                     (addr2 idxBits) }.attrName
                                                                                     ({ attrName =
                                                                                     ('f'::('r'::('o'::('m'::[]))));
                                                                                     attrType =
                                                                                     msi }.attrName :: ({ attrName =
                                                                                     ('t'::('o'::[]));
                                                                                     attrType =
                                                                                     msi }.attrName :: ({ attrName =
                                                                                     ('i'::('d'::[]));
                                                                                     attrType =
                                                                                     id }.attrName :: [])))
                                                                                     (indexBound_tail
                                                                                       ('i'::('d'::[]))
                                                                                       { attrName =
                                                                                       ('f'::('r'::('o'::('m'::[]))));
                                                                                       attrType =
                                                                                       msi }.attrName
                                                                                       ({ attrName =
                                                                                       ('t'::('o'::[]));
                                                                                       attrType =
                                                                                       msi }.attrName :: ({ attrName =
                                                                                       ('i'::('d'::[]));
                                                                                       attrType =
                                                                                       id }.attrName :: []))
                                                                                       (indexBound_tail
                                                                                         ('i'::('d'::[]))
                                                                                         { attrName =
                                                                                         ('t'::('o'::[]));
                                                                                         attrType =
                                                                                         msi }.attrName
                                                                                         ({ attrName =
                                                                                         ('i'::('d'::[]));
                                                                                         attrType =
                                                                                         id }.attrName :: [])
                                                                                         (indexBound_head
                                                                                           { attrName =
                                                                                           ('i'::('d'::[]));
                                                                                           attrType =
                                                                                           id }.attrName
                                                                                           [])))) },
                                                                                   (Var ((SyntaxKind
                                                                                   (rqToP2 idxBits
                                                                                     id)), rq))))))) :: []))))
      (icons' (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (getAttrType ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
          msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
          ('i'::('d'::[])); attrType = id } :: [])))) { bindex = ('a'::('d'::('d'::('r'::[]))));
          indexb =
          (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
            (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
            msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
            msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))) }) },
        (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
        (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
        msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName = ('i'::('d'::[]));
        attrType = id } :: [])))), { bindex = ('a'::('d'::('d'::('r'::[])))); indexb =
        (indexBound_head { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
          msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
          msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))) },
        (Var ((SyntaxKind (rqToP2 idxBits id)), rq))))))
        ((projT1 (ExistT ({ attrName = ('t'::('o'::[])); attrType =
           (getAttrType ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
             (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
             msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
             ('i'::('d'::[])); attrType = id } :: [])))) { bindex = ('t'::('o'::[])); indexb =
             (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[]))));
               attrType = (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[]))));
               attrType = msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
               msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))
               (indexBound_tail ('t'::('o'::[])) { attrName = ('f'::('r'::('o'::('m'::[]))));
                 attrType = msi }.attrName ({ attrName = ('t'::('o'::[])); attrType =
                 msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: []))
                 (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName
                   ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))) }) },
           (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
           (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
           msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
           ('i'::('d'::[])); attrType = id } :: [])))), { bindex = ('t'::('o'::[])); indexb =
           (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
             (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
             msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
             msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))
             (indexBound_tail ('t'::('o'::[])) { attrName = ('f'::('r'::('o'::('m'::[]))));
               attrType = msi }.attrName ({ attrName = ('t'::('o'::[])); attrType =
               msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: []))
               (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName
                 ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))) }, (Var
           ((SyntaxKind (rqToP2 idxBits id)), rq))))))) :: ((projT1 (ExistT ({ attrName =
                                                              ('l'::('i'::('n'::('e'::[]))));
                                                              attrType =
                                                              (readLine0 idxBits lgNumDatas
                                                                lgDataBytes).attrType.ret }, (Var
                                                              ((SyntaxKind
                                                              (readLine0 idxBits lgNumDatas
                                                                lgDataBytes).attrType.ret),
                                                              line2))))) :: ((projT1 (ExistT
                                                                               ({ attrName =
                                                                               ('i'::('d'::[]));
                                                                               attrType =
                                                                               (getAttrType
                                                                                 ({ attrName =
                                                                                 ('a'::('d'::('d'::('r'::[]))));
                                                                                 attrType =
                                                                                 (addr2 idxBits) } :: ({ attrName =
                                                                                 ('f'::('r'::('o'::('m'::[]))));
                                                                                 attrType =
                                                                                 msi } :: ({ attrName =
                                                                                 ('t'::('o'::[]));
                                                                                 attrType =
                                                                                 msi } :: ({ attrName =
                                                                                 ('i'::('d'::[]));
                                                                                 attrType =
                                                                                 id } :: []))))
                                                                                 { bindex =
                                                                                 ('i'::('d'::[]));
                                                                                 indexb =
                                                                                 (indexBound_tail
                                                                                   ('i'::('d'::[]))
                                                                                   { attrName =
                                                                                   ('a'::('d'::('d'::('r'::[]))));
                                                                                   attrType =
                                                                                   (addr2 idxBits) }.attrName
                                                                                   ({ attrName =
                                                                                   ('f'::('r'::('o'::('m'::[]))));
                                                                                   attrType =
                                                                                   msi }.attrName :: ({ attrName =
                                                                                   ('t'::('o'::[]));
                                                                                   attrType =
                                                                                   msi }.attrName :: ({ attrName =
                                                                                   ('i'::('d'::[]));
                                                                                   attrType =
                                                                                   id }.attrName :: [])))
                                                                                   (indexBound_tail
                                                                                     ('i'::('d'::[]))
                                                                                     { attrName =
                                                                                     ('f'::('r'::('o'::('m'::[]))));
                                                                                     attrType =
                                                                                     msi }.attrName
                                                                                     ({ attrName =
                                                                                     ('t'::('o'::[]));
                                                                                     attrType =
                                                                                     msi }.attrName :: ({ attrName =
                                                                                     ('i'::('d'::[]));
                                                                                     attrType =
                                                                                     id }.attrName :: []))
                                                                                     (indexBound_tail
                                                                                       ('i'::('d'::[]))
                                                                                       { attrName =
                                                                                       ('t'::('o'::[]));
                                                                                       attrType =
                                                                                       msi }.attrName
                                                                                       ({ attrName =
                                                                                       ('i'::('d'::[]));
                                                                                       attrType =
                                                                                       id }.attrName :: [])
                                                                                       (indexBound_head
                                                                                         { attrName =
                                                                                         ('i'::('d'::[]));
                                                                                         attrType =
                                                                                         id }.attrName
                                                                                         [])))) }) },
                                                                               (ReadField
                                                                               (({ attrName =
                                                                               ('a'::('d'::('d'::('r'::[]))));
                                                                               attrType =
                                                                               (addr2 idxBits) } :: ({ attrName =
                                                                               ('f'::('r'::('o'::('m'::[]))));
                                                                               attrType =
                                                                               msi } :: ({ attrName =
                                                                               ('t'::('o'::[]));
                                                                               attrType =
                                                                               msi } :: ({ attrName =
                                                                               ('i'::('d'::[]));
                                                                               attrType =
                                                                               id } :: [])))),
                                                                               { bindex =
                                                                               ('i'::('d'::[]));
                                                                               indexb =
                                                                               (indexBound_tail
                                                                                 ('i'::('d'::[]))
                                                                                 { attrName =
                                                                                 ('a'::('d'::('d'::('r'::[]))));
                                                                                 attrType =
                                                                                 (addr2 idxBits) }.attrName
                                                                                 ({ attrName =
                                                                                 ('f'::('r'::('o'::('m'::[]))));
                                                                                 attrType =
                                                                                 msi }.attrName :: ({ attrName =
                                                                                 ('t'::('o'::[]));
                                                                                 attrType =
                                                                                 msi }.attrName :: ({ attrName =
                                                                                 ('i'::('d'::[]));
                                                                                 attrType =
                                                                                 id }.attrName :: [])))
                                                                                 (indexBound_tail
                                                                                   ('i'::('d'::[]))
                                                                                   { attrName =
                                                                                   ('f'::('r'::('o'::('m'::[]))));
                                                                                   attrType =
                                                                                   msi }.attrName
                                                                                   ({ attrName =
                                                                                   ('t'::('o'::[]));
                                                                                   attrType =
                                                                                   msi }.attrName :: ({ attrName =
                                                                                   ('i'::('d'::[]));
                                                                                   attrType =
                                                                                   id }.attrName :: []))
                                                                                   (indexBound_tail
                                                                                     ('i'::('d'::[]))
                                                                                     { attrName =
                                                                                     ('t'::('o'::[]));
                                                                                     attrType =
                                                                                     msi }.attrName
                                                                                     ({ attrName =
                                                                                     ('i'::('d'::[]));
                                                                                     attrType =
                                                                                     id }.attrName :: [])
                                                                                     (indexBound_head
                                                                                       { attrName =
                                                                                       ('i'::('d'::[]));
                                                                                       attrType =
                                                                                       id }.attrName
                                                                                       [])))) },
                                                                               (Var ((SyntaxKind
                                                                               (rqToP2 idxBits id)),
                                                                               rq))))))) :: [])))
        (icons' (ExistT ({ attrName = ('t'::('o'::[])); attrType =
          (getAttrType ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
            (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
            msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
            ('i'::('d'::[])); attrType = id } :: [])))) { bindex = ('t'::('o'::[])); indexb =
            (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[]))));
              attrType = (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[]))));
              attrType = msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
              msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))
              (indexBound_tail ('t'::('o'::[])) { attrName = ('f'::('r'::('o'::('m'::[]))));
                attrType = msi }.attrName ({ attrName = ('t'::('o'::[])); attrType =
                msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: []))
                (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName
                  ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))) }) },
          (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
          (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
          msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
          ('i'::('d'::[])); attrType = id } :: [])))), { bindex = ('t'::('o'::[])); indexb =
          (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
            (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
            msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
            msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))
            (indexBound_tail ('t'::('o'::[])) { attrName = ('f'::('r'::('o'::('m'::[]))));
              attrType = msi }.attrName ({ attrName = ('t'::('o'::[])); attrType =
              msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: []))
              (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName
                ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))) }, (Var
          ((SyntaxKind (rqToP2 idxBits id)), rq))))))
          ((projT1 (ExistT ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
             (readLine0 idxBits lgNumDatas lgDataBytes).attrType.ret }, (Var ((SyntaxKind
             (readLine0 idxBits lgNumDatas lgDataBytes).attrType.ret), line2))))) :: ((projT1
                                                                                        (ExistT
                                                                                        ({ attrName =
                                                                                        ('i'::('d'::[]));
                                                                                        attrType =
                                                                                        (getAttrType
                                                                                          ({ attrName =
                                                                                          ('a'::('d'::('d'::('r'::[]))));
                                                                                          attrType =
                                                                                          (addr2
                                                                                           idxBits) } :: ({ attrName =
                                                                                          ('f'::('r'::('o'::('m'::[]))));
                                                                                          attrType =
                                                                                          msi } :: ({ attrName =
                                                                                          ('t'::('o'::[]));
                                                                                          attrType =
                                                                                          msi } :: ({ attrName =
                                                                                          ('i'::('d'::[]));
                                                                                          attrType =
                                                                                          id } :: []))))
                                                                                          { bindex =
                                                                                          ('i'::('d'::[]));
                                                                                          indexb =
                                                                                          (indexBound_tail
                                                                                           ('i'::('d'::[]))
                                                                                           { attrName =
                                                                                           ('a'::('d'::('d'::('r'::[]))));
                                                                                           attrType =
                                                                                           (addr2
                                                                                           idxBits) }.attrName
                                                                                           ({ attrName =
                                                                                           ('f'::('r'::('o'::('m'::[]))));
                                                                                           attrType =
                                                                                           msi }.attrName :: ({ attrName =
                                                                                           ('t'::('o'::[]));
                                                                                           attrType =
                                                                                           msi }.attrName :: ({ attrName =
                                                                                           ('i'::('d'::[]));
                                                                                           attrType =
                                                                                           id }.attrName :: [])))
                                                                                           (indexBound_tail
                                                                                           ('i'::('d'::[]))
                                                                                           { attrName =
                                                                                           ('f'::('r'::('o'::('m'::[]))));
                                                                                           attrType =
                                                                                           msi }.attrName
                                                                                           ({ attrName =
                                                                                           ('t'::('o'::[]));
                                                                                           attrType =
                                                                                           msi }.attrName :: ({ attrName =
                                                                                           ('i'::('d'::[]));
                                                                                           attrType =
                                                                                           id }.attrName :: []))
                                                                                           (indexBound_tail
                                                                                           ('i'::('d'::[]))
                                                                                           { attrName =
                                                                                           ('t'::('o'::[]));
                                                                                           attrType =
                                                                                           msi }.attrName
                                                                                           ({ attrName =
                                                                                           ('i'::('d'::[]));
                                                                                           attrType =
                                                                                           id }.attrName :: [])
                                                                                           (indexBound_head
                                                                                           { attrName =
                                                                                           ('i'::('d'::[]));
                                                                                           attrType =
                                                                                           id }.attrName
                                                                                           [])))) }) },
                                                                                        (ReadField
                                                                                        (({ attrName =
                                                                                        ('a'::('d'::('d'::('r'::[]))));
                                                                                        attrType =
                                                                                        (addr2
                                                                                          idxBits) } :: ({ attrName =
                                                                                        ('f'::('r'::('o'::('m'::[]))));
                                                                                        attrType =
                                                                                        msi } :: ({ attrName =
                                                                                        ('t'::('o'::[]));
                                                                                        attrType =
                                                                                        msi } :: ({ attrName =
                                                                                        ('i'::('d'::[]));
                                                                                        attrType =
                                                                                        id } :: [])))),
                                                                                        { bindex =
                                                                                        ('i'::('d'::[]));
                                                                                        indexb =
                                                                                        (indexBound_tail
                                                                                          ('i'::('d'::[]))
                                                                                          { attrName =
                                                                                          ('a'::('d'::('d'::('r'::[]))));
                                                                                          attrType =
                                                                                          (addr2
                                                                                           idxBits) }.attrName
                                                                                          ({ attrName =
                                                                                          ('f'::('r'::('o'::('m'::[]))));
                                                                                          attrType =
                                                                                          msi }.attrName :: ({ attrName =
                                                                                          ('t'::('o'::[]));
                                                                                          attrType =
                                                                                          msi }.attrName :: ({ attrName =
                                                                                          ('i'::('d'::[]));
                                                                                          attrType =
                                                                                          id }.attrName :: [])))
                                                                                          (indexBound_tail
                                                                                           ('i'::('d'::[]))
                                                                                           { attrName =
                                                                                           ('f'::('r'::('o'::('m'::[]))));
                                                                                           attrType =
                                                                                           msi }.attrName
                                                                                           ({ attrName =
                                                                                           ('t'::('o'::[]));
                                                                                           attrType =
                                                                                           msi }.attrName :: ({ attrName =
                                                                                           ('i'::('d'::[]));
                                                                                           attrType =
                                                                                           id }.attrName :: []))
                                                                                           (indexBound_tail
                                                                                           ('i'::('d'::[]))
                                                                                           { attrName =
                                                                                           ('t'::('o'::[]));
                                                                                           attrType =
                                                                                           msi }.attrName
                                                                                           ({ attrName =
                                                                                           ('i'::('d'::[]));
                                                                                           attrType =
                                                                                           id }.attrName :: [])
                                                                                           (indexBound_head
                                                                                           { attrName =
                                                                                           ('i'::('d'::[]));
                                                                                           attrType =
                                                                                           id }.attrName
                                                                                           [])))) },
                                                                                        (Var
                                                                                        ((SyntaxKind
                                                                                        (rqToP2
                                                                                          idxBits
                                                                                          id)),
                                                                                        rq))))))) :: []))
          (icons' (ExistT ({ attrName = ('l'::('i'::('n'::('e'::[])))); attrType =
            (readLine0 idxBits lgNumDatas lgDataBytes).attrType.ret }, (Var ((SyntaxKind
            (readLine0 idxBits lgNumDatas lgDataBytes).attrType.ret), line2))))
            ((projT1 (ExistT ({ attrName = ('i'::('d'::[])); attrType =
               (getAttrType ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
                 (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
                 msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
                 ('i'::('d'::[])); attrType = id } :: [])))) { bindex = ('i'::('d'::[])); indexb =
                 (indexBound_tail ('i'::('d'::[])) { attrName = ('a'::('d'::('d'::('r'::[]))));
                   attrType = (addr2 idxBits) }.attrName ({ attrName =
                   ('f'::('r'::('o'::('m'::[])))); attrType = msi }.attrName :: ({ attrName =
                   ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName = ('i'::('d'::[]));
                   attrType = id }.attrName :: [])))
                   (indexBound_tail ('i'::('d'::[])) { attrName = ('f'::('r'::('o'::('m'::[]))));
                     attrType = msi }.attrName ({ attrName = ('t'::('o'::[])); attrType =
                     msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
                     id }.attrName :: []))
                     (indexBound_tail ('i'::('d'::[])) { attrName = ('t'::('o'::[])); attrType =
                       msi }.attrName ({ attrName = ('i'::('d'::[])); attrType =
                       id }.attrName :: [])
                       (indexBound_head { attrName = ('i'::('d'::[])); attrType = id }.attrName [])))) }) },
               (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
               (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
               msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
               ('i'::('d'::[])); attrType = id } :: [])))), { bindex = ('i'::('d'::[])); indexb =
               (indexBound_tail ('i'::('d'::[])) { attrName = ('a'::('d'::('d'::('r'::[]))));
                 attrType = (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[]))));
                 attrType = msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
                 msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))
                 (indexBound_tail ('i'::('d'::[])) { attrName = ('f'::('r'::('o'::('m'::[]))));
                   attrType = msi }.attrName ({ attrName = ('t'::('o'::[])); attrType =
                   msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
                   id }.attrName :: []))
                   (indexBound_tail ('i'::('d'::[])) { attrName = ('t'::('o'::[])); attrType =
                     msi }.attrName ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])
                     (indexBound_head { attrName = ('i'::('d'::[])); attrType = id }.attrName [])))) },
               (Var ((SyntaxKind (rqToP2 idxBits id)), rq))))))) :: [])
            (icons' (ExistT ({ attrName = ('i'::('d'::[])); attrType =
              (getAttrType ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
                (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
                msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
                ('i'::('d'::[])); attrType = id } :: [])))) { bindex = ('i'::('d'::[])); indexb =
                (indexBound_tail ('i'::('d'::[])) { attrName = ('a'::('d'::('d'::('r'::[]))));
                  attrType = (addr2 idxBits) }.attrName ({ attrName =
                  ('f'::('r'::('o'::('m'::[])))); attrType = msi }.attrName :: ({ attrName =
                  ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName = ('i'::('d'::[]));
                  attrType = id }.attrName :: [])))
                  (indexBound_tail ('i'::('d'::[])) { attrName = ('f'::('r'::('o'::('m'::[]))));
                    attrType = msi }.attrName ({ attrName = ('t'::('o'::[])); attrType =
                    msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType =
                    id }.attrName :: []))
                    (indexBound_tail ('i'::('d'::[])) { attrName = ('t'::('o'::[])); attrType =
                      msi }.attrName ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])
                      (indexBound_head { attrName = ('i'::('d'::[])); attrType = id }.attrName [])))) }) },
              (ReadField (({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
              (addr2 idxBits) } :: ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
              msi } :: ({ attrName = ('t'::('o'::[])); attrType = msi } :: ({ attrName =
              ('i'::('d'::[])); attrType = id } :: [])))), { bindex = ('i'::('d'::[])); indexb =
              (indexBound_tail ('i'::('d'::[])) { attrName = ('a'::('d'::('d'::('r'::[]))));
                attrType = (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[]))));
                attrType = msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType =
                msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])))
                (indexBound_tail ('i'::('d'::[])) { attrName = ('f'::('r'::('o'::('m'::[]))));
                  attrType = msi }.attrName ({ attrName = ('t'::('o'::[])); attrType =
                  msi }.attrName :: ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: []))
                  (indexBound_tail ('i'::('d'::[])) { attrName = ('t'::('o'::[])); attrType =
                    msi }.attrName ({ attrName = ('i'::('d'::[])); attrType = id }.attrName :: [])
                    (indexBound_head { attrName = ('i'::('d'::[])); attrType = id }.attrName [])))) },
              (Var ((SyntaxKind (rqToP2 idxBits id)), rq)))))) [] Inil))))))), (fun rs -> SMCall
    ({ nameVal = (toCEnq idxBits lgNumDatas lgDataBytes lgNumChildren id).attrName },
    (toCEnq idxBits lgNumDatas lgDataBytes lgNumChildren id).attrType, (BuildStruct
    (((projT1 (ExistT ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
          (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
          (rqToP (addr2 idxBits) id) } :: [])) { bindex = ('c'::('h'::('i'::('l'::('d'::[])))));
          indexb =
          (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
            (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
            (rqToP (addr2 idxBits) id) }.attrName :: [])) }) }, (Var ((SyntaxKind
        (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
          (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
          (rqToP (addr2 idxBits) id) } :: [])) { bindex = ('c'::('h'::('i'::('l'::('d'::[])))));
          indexb =
          (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
            (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
            (rqToP (addr2 idxBits) id) }.attrName :: [])) })), c))))) :: ((projT1 (ExistT
                                                                            ({ attrName =
                                                                            ('m'::('s'::('g'::[])));
                                                                            attrType =
                                                                            (fromP2 idxBits
                                                                              lgNumDatas lgDataBytes
                                                                              id) }, (Var
                                                                            ((SyntaxKind
                                                                            (fromP2 idxBits
                                                                              lgNumDatas lgDataBytes
                                                                              id)), rs))))) :: [])),
    (icons' (ExistT ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
        (rqToP (addr2 idxBits) id) } :: [])) { bindex = ('c'::('h'::('i'::('l'::('d'::[])))));
        indexb =
        (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
          (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
          (rqToP (addr2 idxBits) id) }.attrName :: [])) }) }, (Var ((SyntaxKind
      (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
        (rqToP (addr2 idxBits) id) } :: [])) { bindex = ('c'::('h'::('i'::('l'::('d'::[])))));
        indexb =
        (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
          (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
          (rqToP (addr2 idxBits) id) }.attrName :: [])) })), c))))
      ((projT1 (ExistT ({ attrName = ('m'::('s'::('g'::[]))); attrType =
         (fromP2 idxBits lgNumDatas lgDataBytes id) }, (Var ((SyntaxKind
         (fromP2 idxBits lgNumDatas lgDataBytes id)), rs))))) :: [])
      (icons' (ExistT ({ attrName = ('m'::('s'::('g'::[]))); attrType =
        (fromP2 idxBits lgNumDatas lgDataBytes id) }, (Var ((SyntaxKind
        (fromP2 idxBits lgNumDatas lgDataBytes id)), rs)))) [] Inil)))), (fun x -> SLet_
    ((SyntaxKind (Vector (msi, lgNumChildren))), (UpdateVector (lgNumChildren, msi, (Var
    ((SyntaxKind (readDir idxBits lgNumChildren).attrType.ret), dir0)), (Var ((SyntaxKind
    (getAttrType ({ attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
      (child lgNumChildren) } :: ({ attrName = ('r'::('q'::[])); attrType =
      (rqToP (addr2 idxBits) id) } :: [])) { bindex = ('c'::('h'::('i'::('l'::('d'::[])))));
      indexb =
      (indexBound_head { attrName = ('c'::('h'::('i'::('l'::('d'::[]))))); attrType =
        (child lgNumChildren) }.attrName ({ attrName = ('r'::('q'::[])); attrType =
        (rqToP (addr2 idxBits) id) }.attrName :: [])) })), c)), (ReadField (({ attrName =
    ('a'::('d'::('d'::('r'::[])))); attrType = (addr2 idxBits) } :: ({ attrName =
    ('f'::('r'::('o'::('m'::[])))); attrType = msi } :: ({ attrName = ('t'::('o'::[])); attrType =
    msi } :: ({ attrName = ('i'::('d'::[])); attrType = id } :: [])))), { bindex = ('t'::('o'::[]));
    indexb =
    (indexBound_tail ('t'::('o'::[])) { attrName = ('a'::('d'::('d'::('r'::[])))); attrType =
      (addr2 idxBits) }.attrName ({ attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
      msi }.attrName :: ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
      ('i'::('d'::[])); attrType = id }.attrName :: [])))
      (indexBound_tail ('t'::('o'::[])) { attrName = ('f'::('r'::('o'::('m'::[])))); attrType =
        msi }.attrName ({ attrName = ('t'::('o'::[])); attrType = msi }.attrName :: ({ attrName =
        ('i'::('d'::[])); attrType = id }.attrName :: []))
        (indexBound_head { attrName = ('t'::('o'::[])); attrType = msi }.attrName ({ attrName =
          ('i'::('d'::[])); attrType = id }.attrName :: [])))) }, (Var ((SyntaxKind
    (rqToP2 idxBits id)), rq)))))), (fun dir' -> SMCall ({ nameVal =
    (writeDir idxBits lgNumChildren).attrName }, (writeDir idxBits lgNumChildren).attrType,
    (BuildStruct
    (((projT1 (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx0 idxBits) },
        (Var ((SyntaxKind (idx0 idxBits)), idx1))))) :: ((projT1 (ExistT ({ attrName =
                                                           ('d'::('a'::('t'::('a'::[]))));
                                                           attrType = (Vector (msi,
                                                           lgNumChildren)) }, (Var ((SyntaxKind
                                                           (Vector (msi, lgNumChildren))), dir'))))) :: [])),
    (icons' (ExistT ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (idx0 idxBits) }, (Var
      ((SyntaxKind (idx0 idxBits)), idx1))))
      ((projT1 (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType = (Vector (msi,
         lgNumChildren)) }, (Var ((SyntaxKind (Vector (msi, lgNumChildren))), dir'))))) :: [])
      (icons' (ExistT ({ attrName = ('d'::('a'::('t'::('a'::[])))); attrType = (Vector (msi,
        lgNumChildren)) }, (Var ((SyntaxKind (Vector (msi, lgNumChildren))), dir')))) [] Inil)))),
    (fun x0 -> SWriteReg ({ nameVal = ('c'::('R'::('q'::('V'::('a'::('l'::('i'::('d'::[])))))))) },
    (SyntaxKind Bool), (Const (Bool, (ConstBool false))), (SReturn (Const (void,
    (getDefaultConst void)))))))))))))))))))))))))))))))))), { nameVal =
    ('d'::('e'::('f'::('e'::('r'::('r'::('e'::('d'::[])))))))) }))), NilInMetaModule))))))))))))

(** val enqS : char list -> int -> kind -> 'a1 -> 'a1 sinActionT **)

let enqS fifoName sz dType d =
  SReadReg ({ nameVal = (withPrefix fifoName ('f'::('u'::('l'::('l'::[]))))) }, (SyntaxKind Bool),
    (fun isFull -> SAssert_ ((UniBool (Neg, (Var ((SyntaxKind Bool), isFull)))), (SReadReg
    ({ nameVal = (withPrefix fifoName ('e'::('l'::('t'::[])))) }, (SyntaxKind (Vector (dType, sz))),
    (fun elt -> SReadReg ({ nameVal = (withPrefix fifoName ('e'::('n'::('q'::('P'::[]))))) },
    (SyntaxKind (Bit sz)), (fun enqP -> SReadReg ({ nameVal =
    (withPrefix fifoName ('d'::('e'::('q'::('P'::[]))))) }, (SyntaxKind (Bit sz)), (fun deqP ->
    SWriteReg ({ nameVal = (withPrefix fifoName ('e'::('l'::('t'::[])))) }, (SyntaxKind (Vector
    (dType, sz))), (UpdateVector (sz, dType, (Var ((SyntaxKind (Vector (dType, sz))), elt)), (Var
    ((SyntaxKind (Bit sz)), enqP)), (Var ((SyntaxKind dType), (Obj.magic d))))), (SWriteReg
    ({ nameVal = (withPrefix fifoName ('e'::('m'::('p'::('t'::('y'::[])))))) }, (SyntaxKind Bool),
    (Const (Bool, (ConstBool false))), (SLet_ ((SyntaxKind (Bit sz)), (BinBit (sz, sz, sz, (Add sz),
    (Var ((SyntaxKind (Bit sz)), enqP)), (Const ((Bit sz), (ConstBit (sz,
    (natToWord sz (Pervasives.succ 0)))))))), (fun next_enqP -> SWriteReg ({ nameVal =
    (withPrefix fifoName ('f'::('u'::('l'::('l'::[]))))) }, (SyntaxKind Bool), (Eq ((Bit sz), (Var
    ((SyntaxKind (Bit sz)), deqP)), (Var ((SyntaxKind (Bit sz)), next_enqP)))), (SWriteReg
    ({ nameVal = (withPrefix fifoName ('e'::('n'::('q'::('P'::[]))))) }, (SyntaxKind (Bit sz)), (Var
    ((SyntaxKind (Bit sz)), next_enqP)), (SReturn (Const (void,
    (getDefaultConst void)))))))))))))))))))))))

(** val deqS : char list -> int -> kind -> 'a1 sinActionT **)

let deqS fifoName sz dType =
  SReadReg ({ nameVal = (withPrefix fifoName ('e'::('m'::('p'::('t'::('y'::[])))))) }, (SyntaxKind
    Bool), (fun isEmpty -> SAssert_ ((UniBool (Neg, (Var ((SyntaxKind Bool), isEmpty)))), (SReadReg
    ({ nameVal = (withPrefix fifoName ('e'::('l'::('t'::[])))) }, (SyntaxKind (Vector (dType, sz))),
    (fun elt -> SReadReg ({ nameVal = (withPrefix fifoName ('e'::('n'::('q'::('P'::[]))))) },
    (SyntaxKind (Bit sz)), (fun enqP -> SReadReg ({ nameVal =
    (withPrefix fifoName ('d'::('e'::('q'::('P'::[]))))) }, (SyntaxKind (Bit sz)), (fun deqP ->
    SWriteReg ({ nameVal = (withPrefix fifoName ('f'::('u'::('l'::('l'::[]))))) }, (SyntaxKind
    Bool), (Const (Bool, (ConstBool false))), (SLet_ ((SyntaxKind (Bit sz)), (BinBit (sz, sz, sz,
    (Add sz), (Var ((SyntaxKind (Bit sz)), deqP)), (Const ((Bit sz), (ConstBit (sz,
    (natToWord sz (Pervasives.succ 0)))))))), (fun next_deqP -> SWriteReg ({ nameVal =
    (withPrefix fifoName ('e'::('m'::('p'::('t'::('y'::[])))))) }, (SyntaxKind Bool), (Eq ((Bit sz),
    (Var ((SyntaxKind (Bit sz)), enqP)), (Var ((SyntaxKind (Bit sz)), next_deqP)))), (SWriteReg
    ({ nameVal = (withPrefix fifoName ('d'::('e'::('q'::('P'::[]))))) }, (SyntaxKind (Bit sz)), (Var
    ((SyntaxKind (Bit sz)), next_deqP)), (SReturn (ReadIndex (sz, dType, (Var ((SyntaxKind (Bit
    sz)), deqP)), (Var ((SyntaxKind (Vector (dType, sz))), elt))))))))))))))))))))))

(** val firstEltS : char list -> int -> kind -> 'a1 sinActionT **)

let firstEltS fifoName sz dType =
  SReadReg ({ nameVal = (withPrefix fifoName ('e'::('m'::('p'::('t'::('y'::[])))))) }, (SyntaxKind
    Bool), (fun isEmpty -> SAssert_ ((UniBool (Neg, (Var ((SyntaxKind Bool), isEmpty)))), (SReadReg
    ({ nameVal = (withPrefix fifoName ('e'::('l'::('t'::[])))) }, (SyntaxKind (Vector (dType, sz))),
    (fun elt -> SReadReg ({ nameVal = (withPrefix fifoName ('d'::('e'::('q'::('P'::[]))))) },
    (SyntaxKind (Bit sz)), (fun deqP -> SReturn (ReadIndex (sz, dType, (Var ((SyntaxKind (Bit sz)),
    deqP)), (Var ((SyntaxKind (Vector (dType, sz))), elt))))))))))))

(** val fifoM : char list -> int -> kind -> metaModule **)

let fifoM fifoName sz dType =
  makeMetaModule (ConsInMetaModule ((MMERegister (OneReg ((ExistT ((SyntaxKind (Vector (dType,
    sz))), (makeConst (Vector (dType, sz)) (getDefaultConst (Vector (dType, sz)))))), { nameVal =
    (withPrefix fifoName ('e'::('l'::('t'::[])))) }))), (ConsInMetaModule ((MMERegister (OneReg
    ((ExistT ((SyntaxKind (Bit sz)), (makeConst (Bit sz) (getDefaultConst (Bit sz))))), { nameVal =
    (withPrefix fifoName ('e'::('n'::('q'::('P'::[]))))) }))), (ConsInMetaModule ((MMERegister
    (OneReg ((ExistT ((SyntaxKind (Bit sz)), (makeConst (Bit sz) (getDefaultConst (Bit sz))))),
    { nameVal = (withPrefix fifoName ('d'::('e'::('q'::('P'::[]))))) }))), (ConsInMetaModule
    ((MMERegister (OneReg ((ExistT ((SyntaxKind Bool), (makeConst Bool (ConstBool true)))),
    { nameVal = (withPrefix fifoName ('e'::('m'::('p'::('t'::('y'::[])))))) }))), (ConsInMetaModule
    ((MMERegister (OneReg ((ExistT ((SyntaxKind Bool), (makeConst Bool (getDefaultConst Bool)))),
    { nameVal = (withPrefix fifoName ('f'::('u'::('l'::('l'::[]))))) }))), (ConsInMetaModule
    ((MMEMeth (OneMeth ((ExistT ({ arg = dType; ret = void }, (fun _ d ->
    enqS fifoName sz dType d))), { nameVal = (withPrefix fifoName ('e'::('n'::('q'::[])))) }))),
    (ConsInMetaModule ((MMEMeth (OneMeth ((ExistT ({ arg = void; ret = dType }, (fun _ x ->
    deqS fifoName sz dType))), { nameVal = (withPrefix fifoName ('d'::('e'::('q'::[])))) }))),
    (ConsInMetaModule ((MMEMeth (OneMeth ((ExistT ({ arg = void; ret = dType }, (fun _ x ->
    firstEltS fifoName sz dType))), { nameVal =
    (withPrefix fifoName ('f'::('i'::('r'::('s'::('t'::('E'::('l'::('t'::[]))))))))) }))),
    NilInMetaModule))))))))))))))))

(** val simpleFifoS : char list -> int -> kind -> int sinModule **)

let simpleFifoS fifoName sz dType =
  makeSinModule (ConsInSinModule ((SMERegister { regGen = (fun x -> ExistT ((SyntaxKind (Vector
    (dType, sz))), (makeConst (Vector (dType, sz)) (getDefaultConst (Vector (dType, sz))))));
    regName = { nameVal = (withPrefix fifoName ('e'::('l'::('t'::[])))) } }), (ConsInSinModule
    ((SMERegister { regGen = (fun x -> ExistT ((SyntaxKind (Bit sz)),
    (makeConst (Bit sz) (getDefaultConst (Bit sz))))); regName = { nameVal =
    (withPrefix fifoName ('e'::('n'::('q'::('P'::[]))))) } }), (ConsInSinModule ((SMERegister
    { regGen = (fun x -> ExistT ((SyntaxKind (Bit sz)),
    (makeConst (Bit sz) (getDefaultConst (Bit sz))))); regName = { nameVal =
    (withPrefix fifoName ('d'::('e'::('q'::('P'::[]))))) } }), (ConsInSinModule ((SMERegister
    { regGen = (fun x -> ExistT ((SyntaxKind Bool), (makeConst Bool (ConstBool true)))); regName =
    { nameVal = (withPrefix fifoName ('e'::('m'::('p'::('t'::('y'::[])))))) } }), (ConsInSinModule
    ((SMERegister { regGen = (fun x -> ExistT ((SyntaxKind Bool),
    (makeConst Bool (getDefaultConst Bool)))); regName = { nameVal =
    (withPrefix fifoName ('f'::('u'::('l'::('l'::[]))))) } }), (ConsInSinModule ((SMEMeth
    { methGen = (ExistT ({ arg = dType; ret = void }, (fun _ d -> enqS fifoName sz dType d)));
    methName = { nameVal = (withPrefix fifoName ('e'::('n'::('q'::[])))) } }), (ConsInSinModule
    ((SMEMeth { methGen = (ExistT ({ arg = void; ret = dType }, (fun _ x ->
    deqS fifoName sz dType))); methName = { nameVal =
    (withPrefix fifoName ('d'::('e'::('q'::[])))) } }), NilInSinModule))))))))))))))

(** val simpleFifoM : char list -> int -> kind -> metaModule **)

let simpleFifoM fifoName sz dType =
  makeMetaModule (ConsInMetaModule ((MMERegister (OneReg ((ExistT ((SyntaxKind (Vector (dType,
    sz))), (makeConst (Vector (dType, sz)) (getDefaultConst (Vector (dType, sz)))))), { nameVal =
    (withPrefix fifoName ('e'::('l'::('t'::[])))) }))), (ConsInMetaModule ((MMERegister (OneReg
    ((ExistT ((SyntaxKind (Bit sz)), (makeConst (Bit sz) (getDefaultConst (Bit sz))))), { nameVal =
    (withPrefix fifoName ('e'::('n'::('q'::('P'::[]))))) }))), (ConsInMetaModule ((MMERegister
    (OneReg ((ExistT ((SyntaxKind (Bit sz)), (makeConst (Bit sz) (getDefaultConst (Bit sz))))),
    { nameVal = (withPrefix fifoName ('d'::('e'::('q'::('P'::[]))))) }))), (ConsInMetaModule
    ((MMERegister (OneReg ((ExistT ((SyntaxKind Bool), (makeConst Bool (ConstBool true)))),
    { nameVal = (withPrefix fifoName ('e'::('m'::('p'::('t'::('y'::[])))))) }))), (ConsInMetaModule
    ((MMERegister (OneReg ((ExistT ((SyntaxKind Bool), (makeConst Bool (getDefaultConst Bool)))),
    { nameVal = (withPrefix fifoName ('f'::('u'::('l'::('l'::[]))))) }))), (ConsInMetaModule
    ((MMEMeth (OneMeth ((ExistT ({ arg = dType; ret = void }, (fun _ d ->
    enqS fifoName sz dType d))), { nameVal = (withPrefix fifoName ('e'::('n'::('q'::[])))) }))),
    (ConsInMetaModule ((MMEMeth (OneMeth ((ExistT ({ arg = void; ret = dType }, (fun _ x ->
    deqS fifoName sz dType))), { nameVal = (withPrefix fifoName ('d'::('e'::('q'::[])))) }))),
    NilInMetaModule))))))))))))))

(** val rsz : int -> int **)

let rsz sz =
  Pervasives.succ sz

(** val l1Cache0 : int -> int -> int -> int -> kind -> int -> metaModule **)

let l1Cache0 idxBits tagBits lgNumDatas lgDataBytes id lgNumChildren =
  getMetaFromSinNat lgNumChildren (l1Cache idxBits tagBits lgNumDatas lgDataBytes id)

(** val l1cs : int -> int -> metaModule **)

let l1cs idxBits lgNumChildren =
  getMetaFromSinNat lgNumChildren
    (regFileS ('c'::('s'::[])) idxBits msi (getDefaultConst (dataArray idxBits msi)))

(** val l1tag : int -> int -> int -> metaModule **)

let l1tag idxBits tagBits lgNumChildren =
  getMetaFromSinNat lgNumChildren
    (regFileS ('t'::('a'::('g'::[]))) idxBits (tag tagBits)
      (getDefaultConst (dataArray idxBits (tag tagBits))))

(** val l1line : int -> int -> int -> int -> metaModule **)

let l1line idxBits lgNumDatas lgDataBytes lgNumChildren =
  getMetaFromSinNat lgNumChildren
    (regFileS ('l'::('i'::('n'::('e'::[])))) idxBits (line0 lgNumDatas lgDataBytes)
      (getDefaultConst (dataArray idxBits (line0 lgNumDatas lgDataBytes))))

(** val mIdxBits : int -> int -> int **)

let mIdxBits idxBits tagBits =
  plus tagBits idxBits

(** val fifoRqToP : int -> int -> kind -> int -> int -> metaModule **)

let fifoRqToP idxBits tagBits id fifoSize lgNumChildren =
  getMetaFromSinNat lgNumChildren
    (simpleFifoS ('r'::('q'::('T'::('o'::('P'::('a'::('r'::('e'::('n'::('t'::[]))))))))))
      (rsz fifoSize) (rqToP2 (mIdxBits idxBits tagBits) id))

(** val fifoRsToP : int -> int -> int -> int -> int -> int -> metaModule **)

let fifoRsToP idxBits tagBits lgNumDatas lgDataBytes fifoSize lgNumChildren =
  getMetaFromSinNat lgNumChildren
    (simpleFifoS ('r'::('s'::('T'::('o'::('P'::('a'::('r'::('e'::('n'::('t'::[]))))))))))
      (rsz fifoSize) (rsToP2 (mIdxBits idxBits tagBits) lgNumDatas lgDataBytes))

(** val fifoFromP : int -> int -> int -> int -> kind -> int -> int -> metaModule **)

let fifoFromP idxBits tagBits lgNumDatas lgDataBytes id fifoSize lgNumChildren =
  getMetaFromSinNat lgNumChildren
    (simpleFifoS ('f'::('r'::('o'::('m'::('P'::('a'::('r'::('e'::('n'::('t'::[]))))))))))
      (rsz fifoSize) (fromP2 (mIdxBits idxBits tagBits) lgNumDatas lgDataBytes id))

(** val childParent0 : int -> int -> int -> int -> kind -> int -> metaModule **)

let childParent0 idxBits tagBits lgNumDatas lgDataBytes id lgNumChildren =
  childParent (mIdxBits idxBits tagBits) lgNumDatas lgDataBytes lgNumChildren id

(** val fifoRqFromC : int -> int -> kind -> int -> int -> metaModule **)

let fifoRqFromC idxBits tagBits id fifoSize lgNumChildren =
  fifoM ('r'::('q'::('F'::('r'::('o'::('m'::('C'::('h'::('i'::('l'::('d'::[])))))))))))
    (rsz fifoSize) (rqFromC1 (mIdxBits idxBits tagBits) lgNumChildren id)

(** val fifoRsFromC : int -> int -> int -> int -> int -> int -> metaModule **)

let fifoRsFromC idxBits tagBits lgNumDatas lgDataBytes fifoSize lgNumChildren =
  simpleFifoM ('r'::('s'::('F'::('r'::('o'::('m'::('C'::('h'::('i'::('l'::('d'::[])))))))))))
    (rsz fifoSize) (rsFromC1 (mIdxBits idxBits tagBits) lgNumDatas lgDataBytes lgNumChildren)

(** val fifoToC : int -> int -> int -> int -> kind -> int -> int -> metaModule **)

let fifoToC idxBits tagBits lgNumDatas lgDataBytes id fifoSize lgNumChildren =
  simpleFifoM ('t'::('o'::('C'::('h'::('i'::('l'::('d'::[]))))))) (rsz fifoSize)
    (toC1 (mIdxBits idxBits tagBits) lgNumDatas lgDataBytes lgNumChildren id)

(** val memDir0 : int -> int -> int -> int -> kind -> int -> metaModule **)

let memDir0 idxBits tagBits lgNumDatas lgDataBytes id lgNumChildren =
  memDir (mIdxBits idxBits tagBits) lgNumDatas lgDataBytes lgNumChildren id

(** val mline : int -> int -> int -> int -> metaModule **)

let mline idxBits tagBits lgNumDatas lgDataBytes =
  regFileM ('m'::('l'::('i'::('n'::('e'::[]))))) (mIdxBits idxBits tagBits)
    (line1 lgNumDatas lgDataBytes)
    (getDefaultConst (dataArray (mIdxBits idxBits tagBits) (line1 lgNumDatas lgDataBytes)))

(** val mdir : int -> int -> int -> metaModule **)

let mdir idxBits tagBits lgNumChildren =
  regFileM ('m'::('c'::('s'::[]))) (mIdxBits idxBits tagBits) (dir lgNumChildren)
    (getDefaultConst (dataArray (mIdxBits idxBits tagBits) (dir lgNumChildren)))

(** val l1Con : modules **)

let l1Con =
  ConcatMod
    ((modFromMeta
       (l1Cache0 (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0))
         (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0)) (Bit
         (Pervasives.succ 0)) (Pervasives.succ 0))), (ConcatMod ((ConcatMod
    ((modFromMeta (l1cs (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ 0))), (ConcatMod
    ((modFromMeta
       (l1tag (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0))
         (Pervasives.succ 0))),
    (modFromMeta
      (l1line (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0))
        (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ 0))))))), (ConcatMod
    ((modFromMeta
       (fifoRqToP (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0)) (Bit
         (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ 0))),
    (ConcatMod
    ((modFromMeta
       (fifoRsToP (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0))
         (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0))
         (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ 0))),
    (modFromMeta
      (fifoFromP (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0))
        (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0)) (Bit
        (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ 0))))))))))

(** val memDirCCon : modules **)

let memDirCCon =
  ConcatMod
    ((modFromMeta
       (memDir0 (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0))
         (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0)) (Bit
         (Pervasives.succ 0)) (Pervasives.succ 0))), (ConcatMod
    ((modFromMeta
       (mline (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0))
         (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0)))),
    (modFromMeta
      (mdir (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0))
        (Pervasives.succ 0))))))

(** val childParentCCon : modules **)

let childParentCCon =
  ConcatMod
    ((modFromMeta
       (childParent0 (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0))
         (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0)) (Bit
         (Pervasives.succ 0)) (Pervasives.succ 0))), (ConcatMod
    ((modFromMeta
       (fifoRqFromC (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0)) (Bit
         (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ 0))),
    (ConcatMod
    ((modFromMeta
       (fifoRsFromC (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0))
         (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0))
         (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ 0))),
    (modFromMeta
      (fifoToC (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0))
        (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0)) (Bit
        (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ 0))))))))

(** val targetM : modules **)

let targetM =
  ConcatMod (l1Con, (ConcatMod (childParentCCon, memDirCCon)))

(** val targetS : modulesS **)

let targetS =
  getModuleS targetM

(** val targetB : bModule list option **)

let targetB =
  modulesSToBModules targetS

