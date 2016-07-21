type __ = Obj.t

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type ('a, 'b) ilist =
| Icons of 'a * 'a list * 'b * ('a, 'b) ilist
| Inil

type word =
| WO
| WS of bool * int * word

type 'kind attribute = { attrName : char list; attrType : 'kind }

type 'a vec =
| Vec0 of 'a
| VecNext of int * 'a vec * 'a vec

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

type signatureT = { arg : kind; ret : kind }

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

type regInitT = (fullKind, constFullT) sigT attribute

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

type bModules = bModule list

