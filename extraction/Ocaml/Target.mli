type __ = Obj.t

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2

type 'a exc = 'a option

val value : 'a1 -> 'a1 option

val error : 'a1 option

val plus : int -> int -> int

val mult : int -> int -> int

val nth_error : 'a1 list -> int -> 'a1 exc

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val div2 : int -> int

val append : char list -> char list -> char list

type ('a, 'b) ilist =
| Icons of 'a * 'a list * 'b * ('a, 'b) ilist
| Inil

val imap : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> ('a1, 'a2) ilist -> ('a1, 'a3) ilist

type word =
| WO
| WS of bool * int * word

val wordToNat : int -> word -> int

val mod2 : int -> bool

val natToWord : int -> int -> word

val wones : int -> word

type 'a indexBound = { ibound : int }

val ibound : 'a1 -> 'a1 list -> 'a1 indexBound -> int

val indexBound_head : 'a1 -> 'a1 list -> 'a1 indexBound

val indexBound_tail : 'a1 -> 'a1 -> 'a1 list -> 'a1 indexBound -> 'a1 indexBound

type 'a boundedIndex = { bindex : 'a; indexb : 'a indexBound }

val bindex : 'a1 list -> 'a1 boundedIndex -> 'a1

val indexb : 'a1 list -> 'a1 boundedIndex -> 'a1 indexBound

val none_neq_Some : 'a1 -> 'a2

val nth_Bounded' : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a1

val nth_Bounded : ('a1 -> 'a2) -> 'a1 list -> 'a2 boundedIndex -> 'a1

type 'kind attribute = { attrName : char list; attrType : 'kind }

val attrName : 'a1 attribute -> char list

val attrType : 'a1 attribute -> 'a1

type 'kind boundedIndexFull = char list boundedIndex

val getAttr : 'a1 attribute list -> 'a1 boundedIndexFull -> 'a1 attribute

val getAttrType : 'a1 attribute list -> 'a1 boundedIndexFull -> 'a1

val string_of_nat : int -> char list

val indexSymbol : char list

val prefixSymbol : char list

val addIndexToStr : ('a1 -> char list) -> 'a1 -> char list -> char list

val withPrefix : char list -> char list -> char list

val getDefaultConstBit : int -> word

type 'a vec =
| Vec0 of 'a
| VecNext of int * 'a vec * 'a vec

val replicate : 'a1 -> int -> 'a1 vec

val mapVec : ('a1 -> 'a2) -> int -> 'a1 vec -> 'a2 vec

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

val getDefaultConst : kind -> constT

type signatureT = { arg : kind; ret : kind }

val arg : signatureT -> kind

val ret : signatureT -> kind

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

val void : kind

type modules =
| Mod of regInitT list * action attribute list * defMethT list
| ConcatMod of modules * modules

val concat : 'a1 list list -> 'a1 list

type nameRec = { nameVal : char list }

val nameVal : nameRec -> char list

type nameRecIdx = { isRep : bool; nameRec0 : nameRec }

val isRep : nameRecIdx -> bool

val nameRec0 : nameRecIdx -> nameRec

val convNameRec : bool -> nameRec -> nameRecIdx

type 'ty genActionT =
| GMCall of nameRecIdx * signatureT * 'ty expr * ('ty -> 'ty genActionT)
| GIndex of ('ty -> 'ty genActionT)
| GLet_ of fullKind * 'ty expr * ('ty fullType -> 'ty genActionT)
| GReadReg of nameRecIdx * fullKind * ('ty fullType -> 'ty genActionT)
| GWriteReg of nameRecIdx * fullKind * 'ty expr * 'ty genActionT
| GIfElse of 'ty expr * kind * 'ty genActionT * 'ty genActionT * ('ty -> 'ty genActionT)
| GAssert_ of 'ty expr * 'ty genActionT
| GReturn of 'ty expr

val strFromName : ('a1 -> char list) -> 'a1 -> nameRecIdx -> char list

val getGenAction :
  ('a1 -> char list) -> kind -> ('a1 -> constT) -> 'a1 -> kind -> 'a2 genActionT -> 'a2 actionT

type genAction = __ -> __ genActionT

type genMethodT = __ -> __ -> __ genActionT

val getActionFromGen :
  ('a1 -> char list) -> kind -> ('a1 -> constT) -> genAction -> 'a1 -> 'a2 actionT

val getMethFromGen :
  ('a1 -> char list) -> kind -> ('a1 -> constT) -> (signatureT, genMethodT) sigT -> 'a1 ->
  (signatureT, __ -> __ -> __ actionT) sigT

type 'ty sinActionT =
| SMCall of nameRec * signatureT * 'ty expr * ('ty -> 'ty sinActionT)
| SLet_ of fullKind * 'ty expr * ('ty fullType -> 'ty sinActionT)
| SReadReg of nameRec * fullKind * ('ty fullType -> 'ty sinActionT)
| SWriteReg of nameRec * fullKind * 'ty expr * 'ty sinActionT
| SIfElse of 'ty expr * kind * 'ty sinActionT * 'ty sinActionT * ('ty -> 'ty sinActionT)
| SAssert_ of 'ty expr * 'ty sinActionT
| SReturn of 'ty expr

val convSinToGen : bool -> kind -> kind -> 'a1 sinActionT -> 'a1 genActionT

val getSinAction : kind -> 'a1 sinActionT -> 'a1 actionT

type sinAction = __ -> __ sinActionT

type sinMethodT = __ -> __ -> __ sinActionT

val getActionFromSin : sinAction -> 'a1 actionT

val getMethFromSin : (signatureT, sinMethodT) sigT -> (signatureT, __ -> __ -> __ actionT) sigT

val getListFromRep :
  ('a1 -> char list) -> ('a1 -> 'a2) -> char list -> 'a1 list -> 'a2 attribute list

val repRule :
  ('a1 -> char list) -> kind -> ('a1 -> constT) -> genAction -> char list -> 'a1 list -> (__ -> __
  actionT) attribute list

val repMeth :
  ('a1 -> char list) -> kind -> ('a1 -> constT) -> (signatureT, genMethodT) sigT -> char list -> 'a1
  list -> (signatureT, __ -> __ -> __ actionT) sigT attribute list

type metaReg =
| OneReg of (fullKind, constFullT) sigT * nameRec
| RepReg of (__ -> char list) * (__ -> (fullKind, constFullT) sigT) * nameRec * __ list

val getListFromMetaReg : metaReg -> (fullKind, constFullT) sigT attribute list

type metaRule =
| OneRule of sinAction * nameRec
| RepRule of (__ -> char list) * kind * (__ -> constT) * genAction * nameRec * __ list

val getListFromMetaRule : metaRule -> (__ -> __ actionT) attribute list

type metaMeth =
| OneMeth of (signatureT, sinMethodT) sigT * nameRec
| RepMeth of (__ -> char list) * kind * (__ -> constT) * (signatureT, genMethodT) sigT * nameRec
   * __ list

val getListFromMetaMeth : metaMeth -> (signatureT, __ -> __ -> __ actionT) sigT attribute list

type metaModule = { metaRegs : metaReg list; metaRules : metaRule list; metaMeths : metaMeth list }

val metaRegs : metaModule -> metaReg list

val metaRules : metaModule -> metaRule list

val metaMeths : metaModule -> metaMeth list

val modFromMeta : metaModule -> modules

val getNatListToN : int -> int list

val natToWordConst : int -> int -> constT

type 'a sinReg = { regGen : ('a -> (fullKind, constFullT) sigT); regName : nameRec }

type sinRule = { ruleGen : sinAction; ruleName : nameRec }

type sinMeth = { methGen : (signatureT, sinMethodT) sigT; methName : nameRec }

type 'a sinModule = { sinRegs : 'a sinReg list; sinRules : sinRule list; sinMeths : sinMeth list }

val sinRegs : 'a1 sinModule -> 'a1 sinReg list

val sinRules : 'a1 sinModule -> sinRule list

val sinMeths : 'a1 sinModule -> sinMeth list

val regsToRep : ('a1 -> char list) -> 'a1 list -> 'a1 sinReg list -> metaReg list

val rulesToRep :
  ('a1 -> char list) -> kind -> ('a1 -> constT) -> 'a1 list -> sinRule list -> metaRule list

val methsToRep :
  ('a1 -> char list) -> kind -> ('a1 -> constT) -> 'a1 list -> sinMeth list -> metaMeth list

val getMetaFromSin :
  ('a1 -> char list) -> kind -> ('a1 -> constT) -> 'a1 list -> 'a1 sinModule -> metaModule

val getMetaFromSinNat : int -> int sinModule -> metaModule

val icons' :
  (kind attribute, 'a1 expr) sigT -> kind attribute list -> (kind attribute, 'a1 expr) ilist ->
  (kind attribute, 'a1 expr) ilist

val maybe : kind -> kind

val makeConst : kind -> constT -> constFullT

type metaModuleElt =
| MMERegister of metaReg
| MMERule of metaRule
| MMEMeth of metaMeth

type inMetaModule =
| NilInMetaModule
| ConsInMetaModule of metaModuleElt * inMetaModule

val makeMetaModule : inMetaModule -> metaModule

type sinModuleElt =
| SMERegister of int sinReg
| SMERule of sinRule
| SMEMeth of sinMeth

type inSinModule =
| NilInSinModule
| ConsInSinModule of sinModuleElt * inSinModule

val makeSinModule : inSinModule -> int sinModule

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

val getActionS : int -> kind -> tyS actionT -> int * actionS

type methodTS = actionS

type defMethTS = (signatureT, methodTS) sigT attribute

type modulesS =
| ModS of regInitT list * actionS attribute list * defMethTS list
| ConcatModsS of modulesS * modulesS

val getMethS : (signatureT, methodT) sigT -> (signatureT, methodTS) sigT

val getModuleS : modules -> modulesS

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

val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option

val bindVec : int -> 'a1 option vec -> 'a1 vec option

val bindList :
  kind attribute list -> (kind attribute, bExpr option) ilist -> (kind attribute, bExpr) ilist
  option

val exprSToBExpr : fullKind -> exprS -> bExpr option

val actionSToBAction : kind -> actionS -> bAction list option

val rulesToBRules : actionS attribute list -> bAction list attribute list option

val methsToBMethods : defMethTS list -> bMethod list option

val modulesSToBModules : modulesS -> bModule list option

val msi : kind

val mod0 : int

val sh : int

val inv : int

val toCompat : 'a1 expr -> 'a1 expr

val isCompat : 'a1 expr -> 'a1 expr -> 'a1 expr

val memOp : kind

val child : int -> kind

val data : int -> kind

val line : int -> int -> kind

val rqFromProc : int -> kind -> kind

val rsToProc : int -> kind

val fromP : int -> int -> kind -> kind -> kind

val rqToP : kind -> kind -> kind

val rsToP : int -> int -> kind -> kind

val rqFromC : int -> kind -> kind -> kind

val rsFromC : int -> int -> int -> kind -> kind

val toC : int -> int -> int -> kind -> kind -> kind

val dataArray : int -> kind -> kind

val addr : int -> kind

val writePort : int -> kind -> kind

val regFileS : char list -> int -> kind -> constT -> int sinModule

val regFileM : char list -> int -> kind -> constT -> metaModule

val addrBits : int -> int -> int -> int

val addr0 : int -> int -> int -> kind

val tag : int -> kind

val idx : int -> kind

val tagIdx : int -> int -> kind

val data0 : int -> kind

val offset : int -> kind

val line0 : int -> int -> kind

val rqFromProc0 : int -> int -> int -> int -> kind

val rsToProc0 : int -> kind

val fromP0 : int -> int -> int -> int -> kind -> kind

val rqToP0 : int -> int -> kind -> kind

val rsToP0 : int -> int -> int -> int -> kind

val rqFromProcPop : int -> int -> int -> int -> signatureT attribute

val rqFromProcFirst : int -> int -> int -> int -> signatureT attribute

val fromPPop : int -> int -> int -> int -> kind -> signatureT attribute

val rsToProcEnq : int -> signatureT attribute

val rqToPEnq : int -> int -> kind -> signatureT attribute

val rsToPEnq : int -> int -> int -> int -> signatureT attribute

val readLine : int -> int -> int -> signatureT attribute

val writeLine : int -> int -> int -> signatureT attribute

val readTag : int -> int -> signatureT attribute

val writeTag : int -> int -> signatureT attribute

val readCs : int -> signatureT attribute

val writeCs : int -> signatureT attribute

val getTagIdx : int -> int -> int -> 'a1 expr -> 'a1 expr

val getTag : int -> int -> int -> 'a1 expr -> 'a1 expr

val getIdx : int -> int -> int -> 'a1 expr -> 'a1 expr

val getOffset : int -> int -> int -> 'a1 expr -> 'a1 expr

val makeTagIdx : int -> int -> 'a1 expr -> 'a1 expr -> 'a1 expr

val getIdxFromTagIdx : int -> int -> 'a1 expr -> 'a1 expr

val getTagFromTagIdx : int -> int -> 'a1 expr -> 'a1 expr

val l1Cache : int -> int -> int -> int -> kind -> int sinModule

val addrBits0 : int -> int

val addr1 : int -> kind

val rqToP1 : int -> kind -> kind

val rqFromC0 : int -> int -> kind -> kind

val rsToP1 : int -> int -> int -> kind

val rsFromC0 : int -> int -> int -> int -> kind

val fromP1 : int -> int -> int -> kind -> kind

val toC0 : int -> int -> int -> int -> kind -> kind

val rqToPPop : int -> kind -> signatureT attribute

val rqFromCEnq : int -> int -> kind -> signatureT attribute

val rsToPPop : int -> int -> int -> signatureT attribute

val rsFromCEnq : int -> int -> int -> int -> signatureT attribute

val toCPop : int -> int -> int -> int -> kind -> signatureT attribute

val fromPEnq : int -> int -> int -> kind -> signatureT attribute

val childParent : int -> int -> int -> int -> kind -> metaModule

val foldInc' : kind -> int -> ('a1 expr -> 'a1 expr -> 'a1 expr) -> 'a1 expr -> int -> 'a1 expr

val foldInc : kind -> int -> ('a1 expr -> 'a1 expr -> 'a1 expr) -> 'a1 expr -> 'a1 expr

val addrBits1 : int -> int

val addr2 : int -> kind

val idx0 : int -> kind

val data1 : int -> kind

val line1 : int -> int -> kind

val rqToP2 : int -> kind -> kind

val rqFromC1 : int -> int -> kind -> kind

val rsToP2 : int -> int -> int -> kind

val rsFromC1 : int -> int -> int -> int -> kind

val fromP2 : int -> int -> int -> kind -> kind

val toC1 : int -> int -> int -> int -> kind -> kind

val rqFromCPop : int -> int -> kind -> signatureT attribute

val rqFromCFirst : int -> int -> kind -> signatureT attribute

val rsFromCPop : int -> int -> int -> int -> signatureT attribute

val toCEnq : int -> int -> int -> int -> kind -> signatureT attribute

val dir : int -> kind

val dirw : int -> kind

val readLine0 : int -> int -> int -> signatureT attribute

val writeLine0 : int -> int -> int -> signatureT attribute

val readDir : int -> int -> signatureT attribute

val writeDir : int -> int -> signatureT attribute

val child0 : int -> kind

val getIdx0 : int -> 'a1 expr -> 'a1 expr

val othersCompat : int -> 'a1 expr -> 'a1 expr -> 'a1 expr -> 'a1 expr

val findIncompat : int -> 'a1 expr -> 'a1 expr -> 'a1 expr -> 'a1 expr -> 'a1 expr

val dirwInit : int -> constT

val memDir : int -> int -> int -> int -> kind -> metaModule

val enqS : char list -> int -> kind -> 'a1 -> 'a1 sinActionT

val deqS : char list -> int -> kind -> 'a1 sinActionT

val firstEltS : char list -> int -> kind -> 'a1 sinActionT

val fifoM : char list -> int -> kind -> metaModule

val simpleFifoS : char list -> int -> kind -> int sinModule

val simpleFifoM : char list -> int -> kind -> metaModule

val rsz : int -> int

val l1Cache0 : int -> int -> int -> int -> kind -> int -> metaModule

val l1cs : int -> int -> metaModule

val l1tag : int -> int -> int -> metaModule

val l1line : int -> int -> int -> int -> metaModule

val mIdxBits : int -> int -> int

val fifoRqToP : int -> int -> kind -> int -> int -> metaModule

val fifoRsToP : int -> int -> int -> int -> int -> int -> metaModule

val fifoFromP : int -> int -> int -> int -> kind -> int -> int -> metaModule

val childParent0 : int -> int -> int -> int -> kind -> int -> metaModule

val fifoRqFromC : int -> int -> kind -> int -> int -> metaModule

val fifoRsFromC : int -> int -> int -> int -> int -> int -> metaModule

val fifoToC : int -> int -> int -> int -> kind -> int -> int -> metaModule

val memDir0 : int -> int -> int -> int -> kind -> int -> metaModule

val mline : int -> int -> int -> int -> metaModule

val mdir : int -> int -> int -> metaModule

val l1Con : modules

val memDirCCon : modules

val childParentCCon : modules

val targetM : modules

val targetS : modulesS

val targetB : bModule list option

