open Prims
type decl =
  | DGlobal of (flag Prims.list* (Prims.string Prims.list* Prims.string)*
  typ* expr)
  | DFunction of (cc option* flag Prims.list* Prims.int* typ* (Prims.string
  Prims.list* Prims.string)* binder Prims.list* expr)
  | DTypeAlias of ((Prims.string Prims.list* Prims.string)* Prims.int* typ)
  | DTypeFlat of ((Prims.string Prims.list* Prims.string)* Prims.int*
  (Prims.string* (typ* Prims.bool)) Prims.list)
  | DExternal of (cc option* (Prims.string Prims.list* Prims.string)* typ)
  | DTypeVariant of ((Prims.string Prims.list* Prims.string)* Prims.int*
  (Prims.string* (Prims.string* (typ* Prims.bool)) Prims.list) Prims.list)
and cc =
  | StdCall
  | CDecl
  | FastCall
and flag =
  | Private
  | NoExtract
  | CInline
  | Substitute
and lifetime =
  | Eternal
  | Stack
and expr =
  | EBound of Prims.int
  | EQualified of (Prims.string Prims.list* Prims.string)
  | EConstant of (width* Prims.string)
  | EUnit
  | EApp of (expr* expr Prims.list)
  | ELet of (binder* expr* expr)
  | EIfThenElse of (expr* expr* expr)
  | ESequence of expr Prims.list
  | EAssign of (expr* expr)
  | EBufCreate of (lifetime* expr* expr)
  | EBufRead of (expr* expr)
  | EBufWrite of (expr* expr* expr)
  | EBufSub of (expr* expr)
  | EBufBlit of (expr* expr* expr* expr* expr)
  | EMatch of (expr* (pattern* expr) Prims.list)
  | EOp of (op* width)
  | ECast of (expr* typ)
  | EPushFrame
  | EPopFrame
  | EBool of Prims.bool
  | EAny
  | EAbort
  | EReturn of expr
  | EFlat of (typ* (Prims.string* expr) Prims.list)
  | EField of (typ* expr* Prims.string)
  | EWhile of (expr* expr)
  | EBufCreateL of (lifetime* expr Prims.list)
  | ETuple of expr Prims.list
  | ECons of (typ* Prims.string* expr Prims.list)
  | EBufFill of (expr* expr* expr)
  | EString of Prims.string
  | EFun of (binder Prims.list* expr)
and op =
  | Add
  | AddW
  | Sub
  | SubW
  | Div
  | DivW
  | Mult
  | MultW
  | Mod
  | BOr
  | BAnd
  | BXor
  | BShiftL
  | BShiftR
  | BNot
  | Eq
  | Neq
  | Lt
  | Lte
  | Gt
  | Gte
  | And
  | Or
  | Xor
  | Not
and pattern =
  | PUnit
  | PBool of Prims.bool
  | PVar of binder
  | PCons of (Prims.string* pattern Prims.list)
  | PTuple of pattern Prims.list
  | PRecord of (Prims.string* pattern) Prims.list
and width =
  | UInt8
  | UInt16
  | UInt32
  | UInt64
  | Int8
  | Int16
  | Int32
  | Int64
  | Bool
  | Int
  | UInt
and binder = {
  name: Prims.string;
  typ: typ;
  mut: Prims.bool;}
and typ =
  | TInt of width
  | TBuf of typ
  | TUnit
  | TQualified of (Prims.string Prims.list* Prims.string)
  | TBool
  | TAny
  | TArrow of (typ* typ)
  | TZ
  | TBound of Prims.int
  | TApp of ((Prims.string Prims.list* Prims.string)* typ Prims.list)
  | TTuple of typ Prims.list
let uu___is_DGlobal: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DGlobal _0 -> true | uu____300 -> false
let __proj__DGlobal__item___0:
  decl ->
    (flag Prims.list* (Prims.string Prims.list* Prims.string)* typ* expr)
  = fun projectee  -> match projectee with | DGlobal _0 -> _0
let uu___is_DFunction: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____349 -> false
let __proj__DFunction__item___0:
  decl ->
    (cc option* flag Prims.list* Prims.int* typ* (Prims.string Prims.list*
      Prims.string)* binder Prims.list* expr)
  = fun projectee  -> match projectee with | DFunction _0 -> _0
let uu___is_DTypeAlias: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____406 -> false
let __proj__DTypeAlias__item___0:
  decl -> ((Prims.string Prims.list* Prims.string)* Prims.int* typ) =
  fun projectee  -> match projectee with | DTypeAlias _0 -> _0
let uu___is_DTypeFlat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____447 -> false
let __proj__DTypeFlat__item___0:
  decl ->
    ((Prims.string Prims.list* Prims.string)* Prims.int* (Prims.string* (typ*
      Prims.bool)) Prims.list)
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0
let uu___is_DExternal: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____499 -> false
let __proj__DExternal__item___0:
  decl -> (cc option* (Prims.string Prims.list* Prims.string)* typ) =
  fun projectee  -> match projectee with | DExternal _0 -> _0
let uu___is_DTypeVariant: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____546 -> false
let __proj__DTypeVariant__item___0:
  decl ->
    ((Prims.string Prims.list* Prims.string)* Prims.int* (Prims.string*
      (Prims.string* (typ* Prims.bool)) Prims.list) Prims.list)
  = fun projectee  -> match projectee with | DTypeVariant _0 -> _0
let uu___is_StdCall: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____599 -> false
let uu___is_CDecl: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____603 -> false
let uu___is_FastCall: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____607 -> false
let uu___is_Private: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____611 -> false
let uu___is_NoExtract: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____615 -> false
let uu___is_CInline: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____619 -> false
let uu___is_Substitute: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____623 -> false
let uu___is_Eternal: lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____627 -> false
let uu___is_Stack: lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____631 -> false
let uu___is_EBound: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____636 -> false
let __proj__EBound__item___0: expr -> Prims.int =
  fun projectee  -> match projectee with | EBound _0 -> _0
let uu___is_EQualified: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____651 -> false
let __proj__EQualified__item___0:
  expr -> (Prims.string Prims.list* Prims.string) =
  fun projectee  -> match projectee with | EQualified _0 -> _0
let uu___is_EConstant: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____674 -> false
let __proj__EConstant__item___0: expr -> (width* Prims.string) =
  fun projectee  -> match projectee with | EConstant _0 -> _0
let uu___is_EUnit: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____691 -> false
let uu___is_EApp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____699 -> false
let __proj__EApp__item___0: expr -> (expr* expr Prims.list) =
  fun projectee  -> match projectee with | EApp _0 -> _0
let uu___is_ELet: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____723 -> false
let __proj__ELet__item___0: expr -> (binder* expr* expr) =
  fun projectee  -> match projectee with | ELet _0 -> _0
let uu___is_EIfThenElse: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____747 -> false
let __proj__EIfThenElse__item___0: expr -> (expr* expr* expr) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0
let uu___is_ESequence: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____769 -> false
let __proj__ESequence__item___0: expr -> expr Prims.list =
  fun projectee  -> match projectee with | ESequence _0 -> _0
let uu___is_EAssign: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____786 -> false
let __proj__EAssign__item___0: expr -> (expr* expr) =
  fun projectee  -> match projectee with | EAssign _0 -> _0
let uu___is_EBufCreate: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____807 -> false
let __proj__EBufCreate__item___0: expr -> (lifetime* expr* expr) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0
let uu___is_EBufRead: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____830 -> false
let __proj__EBufRead__item___0: expr -> (expr* expr) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0
let uu___is_EBufWrite: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____851 -> false
let __proj__EBufWrite__item___0: expr -> (expr* expr* expr) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0
let uu___is_EBufSub: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____874 -> false
let __proj__EBufSub__item___0: expr -> (expr* expr) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0
let uu___is_EBufBlit: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____897 -> false
let __proj__EBufBlit__item___0: expr -> (expr* expr* expr* expr* expr) =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0
let uu___is_EMatch: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____929 -> false
let __proj__EMatch__item___0: expr -> (expr* (pattern* expr) Prims.list) =
  fun projectee  -> match projectee with | EMatch _0 -> _0
let uu___is_EOp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____958 -> false
let __proj__EOp__item___0: expr -> (op* width) =
  fun projectee  -> match projectee with | EOp _0 -> _0
let uu___is_ECast: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____978 -> false
let __proj__ECast__item___0: expr -> (expr* typ) =
  fun projectee  -> match projectee with | ECast _0 -> _0
let uu___is_EPushFrame: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____995 -> false
let uu___is_EPopFrame: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____999 -> false
let uu___is_EBool: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1004 -> false
let __proj__EBool__item___0: expr -> Prims.bool =
  fun projectee  -> match projectee with | EBool _0 -> _0
let uu___is_EAny: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1015 -> false
let uu___is_EAbort: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1019 -> false
let uu___is_EReturn: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1024 -> false
let __proj__EReturn__item___0: expr -> expr =
  fun projectee  -> match projectee with | EReturn _0 -> _0
let uu___is_EFlat: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1041 -> false
let __proj__EFlat__item___0: expr -> (typ* (Prims.string* expr) Prims.list) =
  fun projectee  -> match projectee with | EFlat _0 -> _0
let uu___is_EField: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____1071 -> false
let __proj__EField__item___0: expr -> (typ* expr* Prims.string) =
  fun projectee  -> match projectee with | EField _0 -> _0
let uu___is_EWhile: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____1094 -> false
let __proj__EWhile__item___0: expr -> (expr* expr) =
  fun projectee  -> match projectee with | EWhile _0 -> _0
let uu___is_EBufCreateL: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____1115 -> false
let __proj__EBufCreateL__item___0: expr -> (lifetime* expr Prims.list) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0
let uu___is_ETuple: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____1137 -> false
let __proj__ETuple__item___0: expr -> expr Prims.list =
  fun projectee  -> match projectee with | ETuple _0 -> _0
let uu___is_ECons: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____1156 -> false
let __proj__ECons__item___0: expr -> (typ* Prims.string* expr Prims.list) =
  fun projectee  -> match projectee with | ECons _0 -> _0
let uu___is_EBufFill: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____1183 -> false
let __proj__EBufFill__item___0: expr -> (expr* expr* expr) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0
let uu___is_EString: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____1204 -> false
let __proj__EString__item___0: expr -> Prims.string =
  fun projectee  -> match projectee with | EString _0 -> _0
let uu___is_EFun: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____1219 -> false
let __proj__EFun__item___0: expr -> (binder Prims.list* expr) =
  fun projectee  -> match projectee with | EFun _0 -> _0
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____1239 -> false
let uu___is_AddW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____1243 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____1247 -> false
let uu___is_SubW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____1251 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____1255 -> false
let uu___is_DivW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____1259 -> false
let uu___is_Mult: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____1263 -> false
let uu___is_MultW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____1267 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____1271 -> false
let uu___is_BOr: op -> Prims.bool =
  fun projectee  -> match projectee with | BOr  -> true | uu____1275 -> false
let uu___is_BAnd: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____1279 -> false
let uu___is_BXor: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____1283 -> false
let uu___is_BShiftL: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____1287 -> false
let uu___is_BShiftR: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____1291 -> false
let uu___is_BNot: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____1295 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____1299 -> false
let uu___is_Neq: op -> Prims.bool =
  fun projectee  -> match projectee with | Neq  -> true | uu____1303 -> false
let uu___is_Lt: op -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____1307 -> false
let uu___is_Lte: op -> Prims.bool =
  fun projectee  -> match projectee with | Lte  -> true | uu____1311 -> false
let uu___is_Gt: op -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____1315 -> false
let uu___is_Gte: op -> Prims.bool =
  fun projectee  -> match projectee with | Gte  -> true | uu____1319 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____1323 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____1327 -> false
let uu___is_Xor: op -> Prims.bool =
  fun projectee  -> match projectee with | Xor  -> true | uu____1331 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____1335 -> false
let uu___is_PUnit: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____1339 -> false
let uu___is_PBool: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____1344 -> false
let __proj__PBool__item___0: pattern -> Prims.bool =
  fun projectee  -> match projectee with | PBool _0 -> _0
let uu___is_PVar: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____1356 -> false
let __proj__PVar__item___0: pattern -> binder =
  fun projectee  -> match projectee with | PVar _0 -> _0
let uu___is_PCons: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____1371 -> false
let __proj__PCons__item___0: pattern -> (Prims.string* pattern Prims.list) =
  fun projectee  -> match projectee with | PCons _0 -> _0
let uu___is_PTuple: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____1393 -> false
let __proj__PTuple__item___0: pattern -> pattern Prims.list =
  fun projectee  -> match projectee with | PTuple _0 -> _0
let uu___is_PRecord: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____1411 -> false
let __proj__PRecord__item___0: pattern -> (Prims.string* pattern) Prims.list
  = fun projectee  -> match projectee with | PRecord _0 -> _0
let uu___is_UInt8: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____1431 -> false
let uu___is_UInt16: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____1435 -> false
let uu___is_UInt32: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____1439 -> false
let uu___is_UInt64: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____1443 -> false
let uu___is_Int8: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____1447 -> false
let uu___is_Int16: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____1451 -> false
let uu___is_Int32: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____1455 -> false
let uu___is_Int64: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____1459 -> false
let uu___is_Bool: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____1463 -> false
let uu___is_Int: width -> Prims.bool =
  fun projectee  -> match projectee with | Int  -> true | uu____1467 -> false
let uu___is_UInt: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt  -> true | uu____1471 -> false
let uu___is_TInt: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____1488 -> false
let __proj__TInt__item___0: typ -> width =
  fun projectee  -> match projectee with | TInt _0 -> _0
let uu___is_TBuf: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____1500 -> false
let __proj__TBuf__item___0: typ -> typ =
  fun projectee  -> match projectee with | TBuf _0 -> _0
let uu___is_TUnit: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____1511 -> false
let uu___is_TQualified: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____1519 -> false
let __proj__TQualified__item___0:
  typ -> (Prims.string Prims.list* Prims.string) =
  fun projectee  -> match projectee with | TQualified _0 -> _0
let uu___is_TBool: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____1539 -> false
let uu___is_TAny: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____1543 -> false
let uu___is_TArrow: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____1550 -> false
let __proj__TArrow__item___0: typ -> (typ* typ) =
  fun projectee  -> match projectee with | TArrow _0 -> _0
let uu___is_TZ: typ -> Prims.bool =
  fun projectee  -> match projectee with | TZ  -> true | uu____1567 -> false
let uu___is_TBound: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____1572 -> false
let __proj__TBound__item___0: typ -> Prims.int =
  fun projectee  -> match projectee with | TBound _0 -> _0
let uu___is_TApp: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____1590 -> false
let __proj__TApp__item___0:
  typ -> ((Prims.string Prims.list* Prims.string)* typ Prims.list) =
  fun projectee  -> match projectee with | TApp _0 -> _0
let uu___is_TTuple: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____1621 -> false
let __proj__TTuple__item___0: typ -> typ Prims.list =
  fun projectee  -> match projectee with | TTuple _0 -> _0
type program = decl Prims.list
type ident = Prims.string
type fields_t = (Prims.string* (typ* Prims.bool)) Prims.list
type branches_t =
  (Prims.string* (Prims.string* (typ* Prims.bool)) Prims.list) Prims.list
type branch = (pattern* expr)
type branches = (pattern* expr) Prims.list
type constant = (width* Prims.string)
type var = Prims.int
type lident = (Prims.string Prims.list* Prims.string)
type version = Prims.int
let current_version: Prims.int = Prims.parse_int "20"
type file = (Prims.string* program)
type binary_format = (version* file Prims.list)
let fst3 uu____1674 = match uu____1674 with | (x,uu____1679,uu____1680) -> x
let snd3 uu____1694 = match uu____1694 with | (uu____1698,x,uu____1700) -> x
let thd3 uu____1714 = match uu____1714 with | (uu____1718,uu____1719,x) -> x
let mk_width: Prims.string -> width option =
  fun uu___119_1724  ->
    match uu___119_1724 with
    | "UInt8" -> Some UInt8
    | "UInt16" -> Some UInt16
    | "UInt32" -> Some UInt32
    | "UInt64" -> Some UInt64
    | "Int8" -> Some Int8
    | "Int16" -> Some Int16
    | "Int32" -> Some Int32
    | "Int64" -> Some Int64
    | uu____1726 -> None
let mk_bool_op: Prims.string -> op option =
  fun uu___120_1730  ->
    match uu___120_1730 with
    | "op_Negation" -> Some Not
    | "op_AmpAmp" -> Some And
    | "op_BarBar" -> Some Or
    | "op_Equality" -> Some Eq
    | "op_disEquality" -> Some Neq
    | uu____1732 -> None
let is_bool_op: Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> None
let mk_op: Prims.string -> op option =
  fun uu___121_1740  ->
    match uu___121_1740 with
    | "add"|"op_Plus_Hat" -> Some Add
    | "add_mod"|"op_Plus_Percent_Hat" -> Some AddW
    | "sub"|"op_Subtraction_Hat" -> Some Sub
    | "sub_mod"|"op_Subtraction_Percent_Hat" -> Some SubW
    | "mul"|"op_Star_Hat" -> Some Mult
    | "mul_mod"|"op_Star_Percent_Hat" -> Some MultW
    | "div"|"op_Slash_Hat" -> Some Div
    | "div_mod"|"op_Slash_Percent_Hat" -> Some DivW
    | "rem"|"op_Percent_Hat" -> Some Mod
    | "logor"|"op_Bar_Hat" -> Some BOr
    | "logxor"|"op_Hat_Hat" -> Some BXor
    | "logand"|"op_Amp_Hat" -> Some BAnd
    | "lognot" -> Some BNot
    | "shift_right"|"op_Greater_Greater_Hat" -> Some BShiftR
    | "shift_left"|"op_Less_Less_Hat" -> Some BShiftL
    | "eq"|"op_Equals_Hat" -> Some Eq
    | "op_Greater_Hat"|"gt" -> Some Gt
    | "op_Greater_Equals_Hat"|"gte" -> Some Gte
    | "op_Less_Hat"|"lt" -> Some Lt
    | "op_Less_Equals_Hat"|"lte" -> Some Lte
    | uu____1742 -> None
let is_op: Prims.string -> Prims.bool = fun op  -> (mk_op op) <> None
let is_machine_int: Prims.string -> Prims.bool =
  fun m  -> (mk_width m) <> None
type env =
  {
  names: name Prims.list;
  names_t: Prims.string Prims.list;
  module_name: Prims.string Prims.list;}
and name = {
  pretty: Prims.string;
  mut: Prims.bool;}
let empty: Prims.string Prims.list -> env =
  fun module_name  -> { names = []; names_t = []; module_name }
let extend: env -> Prims.string -> Prims.bool -> env =
  fun env  ->
    fun x  ->
      fun is_mut  ->
        let uu___126_1809 = env in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___126_1809.names_t);
          module_name = (uu___126_1809.module_name)
        }
let extend_t: env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___127_1816 = env in
      {
        names = (uu___127_1816.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___127_1816.module_name)
      }
let find_name: env -> Prims.string -> name =
  fun env  ->
    fun x  ->
      let uu____1823 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names in
      match uu____1823 with
      | Some name -> name
      | None  -> failwith "internal error: name not found"
let is_mutable: env -> Prims.string -> Prims.bool =
  fun env  -> fun x  -> let uu____1833 = find_name env x in uu____1833.mut
let find: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____1843 ->
          let uu____1844 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____1844
let find_t: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____1854 ->
          let uu____1855 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____1855
let add_binders env binders =
  FStar_List.fold_left
    (fun env1  ->
       fun uu____1885  ->
         match uu____1885 with
         | ((name,uu____1891),uu____1892) -> extend env1 name false) env
    binders
let rec translate: FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____1983  ->
    match uu____1983 with
    | FStar_Extraction_ML_Syntax.MLLib modules1 ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____2014 = m in
               match uu____2014 with
               | ((prefix1,final),uu____2026,uu____2027) ->
                   FStar_String.concat "."
                     (FStar_List.append prefix1 [final]) in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____2043 = translate_module m in Some uu____2043)
             with
             | e ->
                 ((let uu____2048 = FStar_Util.print_exn e in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____2048);
                  None)) modules1
and translate_module:
  ((Prims.string Prims.list* Prims.string)*
    (FStar_Extraction_ML_Syntax.mlsig* FStar_Extraction_ML_Syntax.mlmodule)
    option* FStar_Extraction_ML_Syntax.mllib) -> file
  =
  fun uu____2049  ->
    match uu____2049 with
    | (module_name,modul,uu____2061) ->
        let module_name1 =
          FStar_List.append (fst module_name) [snd module_name] in
        let program =
          match modul with
          | Some (_signature,decls) ->
              FStar_List.filter_map (translate_decl (empty module_name1))
                decls
          | uu____2085 ->
              failwith "Unexpected standalone interface or nested modules" in
        ((FStar_String.concat "_" module_name1), program)
and translate_flags:
  FStar_Extraction_ML_Syntax.c_flag Prims.list -> flag Prims.list =
  fun flags  ->
    FStar_List.choose
      (fun uu___122_2093  ->
         match uu___122_2093 with
         | FStar_Extraction_ML_Syntax.Private  -> Some Private
         | FStar_Extraction_ML_Syntax.NoExtract  -> Some NoExtract
         | FStar_Extraction_ML_Syntax.Attribute "c_inline" -> Some CInline
         | FStar_Extraction_ML_Syntax.Attribute "substitute" ->
             Some Substitute
         | FStar_Extraction_ML_Syntax.Attribute a ->
             (FStar_Util.print1_warning "Warning: unrecognized attribute %s"
                a;
              None)
         | uu____2097 -> None) flags
and translate_decl:
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl option =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let
        (flavor,flags,{ FStar_Extraction_ML_Syntax.mllb_name = (name,_);
                        FStar_Extraction_ML_Syntax.mllb_tysc = Some
                          (tvars,t0);
                        FStar_Extraction_ML_Syntax.mllb_add_unit = _;
                        FStar_Extraction_ML_Syntax.mllb_def =
                          {
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                            FStar_Extraction_ML_Syntax.mlty = _;
                            FStar_Extraction_ML_Syntax.loc = _;_};
                        FStar_Extraction_ML_Syntax.print_typ = _;_}::[])
        |FStar_Extraction_ML_Syntax.MLM_Let
        (flavor,flags,{ FStar_Extraction_ML_Syntax.mllb_name = (name,_);
                        FStar_Extraction_ML_Syntax.mllb_tysc = Some
                          (tvars,t0);
                        FStar_Extraction_ML_Syntax.mllb_add_unit = _;
                        FStar_Extraction_ML_Syntax.mllb_def =
                          {
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Coerce
                              ({
                                 FStar_Extraction_ML_Syntax.expr =
                                   FStar_Extraction_ML_Syntax.MLE_Fun
                                   (args,body);
                                 FStar_Extraction_ML_Syntax.mlty = _;
                                 FStar_Extraction_ML_Syntax.loc = _;_},_,_);
                            FStar_Extraction_ML_Syntax.mlty = _;
                            FStar_Extraction_ML_Syntax.loc = _;_};
                        FStar_Extraction_ML_Syntax.print_typ = _;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___123_2142  ->
                 match uu___123_2142 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____2143 -> false) flags in
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun uu____2150  ->
                   match uu____2150 with
                   | (name1,uu____2154) -> extend_t env2 name1) env1 tvars in
          let rec find_return_type uu___124_2158 =
            match uu___124_2158 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2159,uu____2160,t)
                -> find_return_type t
            | t -> t in
          let t =
            let uu____2164 = find_return_type t0 in
            translate_type env2 uu____2164 in
          let binders = translate_binders env2 args in
          let env3 = add_binders env2 args in
          let name1 = ((env3.module_name), name) in
          let flags1 = translate_flags flags in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
               let uu____2179 =
                 let uu____2180 =
                   let uu____2188 = translate_type env3 t0 in
                   (None, name1, uu____2188) in
                 DExternal uu____2180 in
               Some uu____2179
             else None)
          else
            (try
               let body1 = translate_expr env3 body in
               Some
                 (DFunction
                    (None, flags1, (FStar_List.length tvars), t, name1,
                      binders, body1))
             with
             | e ->
                 ((let uu____2211 = FStar_Util.print_exn e in
                   FStar_Util.print2 "Warning: writing a stub for %s (%s)\n"
                     (snd name1) uu____2211);
                  Some
                    (DFunction
                       (None, flags1, (FStar_List.length tvars), t, name1,
                         binders, EAbort))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____2224);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some ([],t);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2226;
                          FStar_Extraction_ML_Syntax.mllb_def = expr;
                          FStar_Extraction_ML_Syntax.print_typ = uu____2228;_}::[])
          ->
          let flags1 = translate_flags flags in
          let t1 = translate_type env t in
          let name1 = ((env.module_name), name) in
          (try
             let expr1 = translate_expr env expr in
             Some (DGlobal (flags1, name1, t1, expr1))
           with
           | e ->
               ((let uu____2254 = FStar_Util.print_exn e in
                 FStar_Util.print2
                   "Warning: not translating definition for %s (%s)\n"
                   (snd name1) uu____2254);
                Some (DGlobal (flags1, name1, t1, EAny))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (uu____2260,uu____2261,{
                                   FStar_Extraction_ML_Syntax.mllb_name =
                                     (name,uu____2263);
                                   FStar_Extraction_ML_Syntax.mllb_tysc = ts;
                                   FStar_Extraction_ML_Syntax.mllb_add_unit =
                                     uu____2265;
                                   FStar_Extraction_ML_Syntax.mllb_def =
                                     uu____2266;
                                   FStar_Extraction_ML_Syntax.print_typ =
                                     uu____2267;_}::uu____2268)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           (match ts with
            | Some (idents,t) ->
                let uu____2278 =
                  let uu____2279 = FStar_List.map FStar_Pervasives.fst idents in
                  FStar_String.concat ", " uu____2279 in
                let uu____2283 =
                  FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                  uu____2278 uu____2283
            | None  -> ());
           None)
      | FStar_Extraction_ML_Syntax.MLM_Let uu____2285 ->
          failwith "impossible"
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____2287 -> None
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((assumed,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_Abbrev t))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____2319  ->
                   match uu____2319 with
                   | (name2,uu____2323) -> extend_t env1 name2) env args in
          if assumed
          then None
          else
            (let uu____2326 =
               let uu____2327 =
                 let uu____2334 = translate_type env1 t in
                 (name1, (FStar_List.length args), uu____2334) in
               DTypeAlias uu____2327 in
             Some uu____2326)
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2340,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_Record fields))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____2374  ->
                   match uu____2374 with
                   | (name2,uu____2378) -> extend_t env1 name2) env args in
          let uu____2379 =
            let uu____2380 =
              let uu____2392 =
                FStar_List.map
                  (fun uu____2404  ->
                     match uu____2404 with
                     | (f,t) ->
                         let uu____2413 =
                           let uu____2416 = translate_type env1 t in
                           (uu____2416, false) in
                         (f, uu____2413)) fields in
              (name1, (FStar_List.length args), uu____2392) in
            DTypeFlat uu____2380 in
          Some uu____2379
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2429,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_DType branches))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____2464  ->
                   match uu____2464 with
                   | (name2,uu____2468) -> extend_t env1 name2) env args in
          let uu____2469 =
            let uu____2470 =
              let uu____2485 =
                FStar_List.mapi
                  (fun i  ->
                     fun uu____2505  ->
                       match uu____2505 with
                       | (cons1,ts) ->
                           let uu____2520 =
                             FStar_List.mapi
                               (fun j  ->
                                  fun t  ->
                                    let uu____2532 =
                                      let uu____2533 =
                                        FStar_Util.string_of_int i in
                                      let uu____2534 =
                                        FStar_Util.string_of_int j in
                                      FStar_Util.format2 "x%s%s" uu____2533
                                        uu____2534 in
                                    let uu____2535 =
                                      let uu____2538 = translate_type env1 t in
                                      (uu____2538, false) in
                                    (uu____2532, uu____2535)) ts in
                           (cons1, uu____2520)) branches in
              (name1, (FStar_List.length args), uu____2485) in
            DTypeVariant uu____2470 in
          Some uu____2469
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2559,name,_mangled_name,uu____2562,uu____2563)::uu____2564)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           None)
      | FStar_Extraction_ML_Syntax.MLM_Ty [] ->
          (FStar_Util.print_string
             "Impossible!! Empty block of mutually recursive type declarations";
           None)
      | FStar_Extraction_ML_Syntax.MLM_Top uu____2586 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____2588 ->
          failwith "todo: translate_decl [MLM_Exn]"
and translate_type: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple []
        |FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var (name,uu____2596) ->
          let uu____2597 = find_t env name in TBound uu____2597
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____2599,t2) ->
          let uu____2601 =
            let uu____2604 = translate_type env t1 in
            let uu____2605 = translate_type env t2 in
            (uu____2604, uu____2605) in
          TArrow uu____2601
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____2608 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2608 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____2611 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2611 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____2618 = FStar_Util.must (mk_width m) in TInt uu____2618
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____2625 = FStar_Util.must (mk_width m) in TInt uu____2625
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____2629 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2629 = "FStar.Buffer.buffer" ->
          let uu____2630 = translate_type env arg in TBuf uu____2630
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____2631::[],p) when
          let uu____2634 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2634 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____2656 = FStar_List.map (translate_type env) args in
          TTuple uu____2656
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____2665 =
              let uu____2672 = FStar_List.map (translate_type env) args in
              (lid, uu____2672) in
            TApp uu____2665
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____2678 = FStar_List.map (translate_type env) ts in
          TTuple uu____2678
and translate_binders:
  env ->
    (FStar_Extraction_ML_Syntax.mlident* FStar_Extraction_ML_Syntax.mlty)
      Prims.list -> binder Prims.list
  = fun env  -> fun args  -> FStar_List.map (translate_binder env) args
and translate_binder:
  env ->
    (FStar_Extraction_ML_Syntax.mlident* FStar_Extraction_ML_Syntax.mlty) ->
      binder
  =
  fun env  ->
    fun uu____2688  ->
      match uu____2688 with
      | ((name,uu____2692),typ) ->
          let uu____2696 = translate_type env typ in
          { name; typ = uu____2696; mut = false }
and translate_expr: env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____2701) ->
          let uu____2702 = find env name in EBound uu____2702
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____2706 =
            let uu____2709 = FStar_Util.must (mk_op op) in
            let uu____2710 = FStar_Util.must (mk_width m) in
            (uu____2709, uu____2710) in
          EOp uu____2706
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____2713 =
            let uu____2716 = FStar_Util.must (mk_bool_op op) in
            (uu____2716, Bool) in
          EOp uu____2713
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags,{
                           FStar_Extraction_ML_Syntax.mllb_name =
                             (name,uu____2721);
                           FStar_Extraction_ML_Syntax.mllb_tysc = Some
                             ([],typ);
                           FStar_Extraction_ML_Syntax.mllb_add_unit =
                             add_unit;
                           FStar_Extraction_ML_Syntax.mllb_def = body;
                           FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let is_mut =
            FStar_Util.for_some
              (fun uu___125_2737  ->
                 match uu___125_2737 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____2738 -> false) flags in
          let uu____2739 =
            if is_mut
            then
              let uu____2744 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____2748 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____2748 = "FStar.ST.stackref" -> t
                | uu____2749 ->
                    let uu____2750 =
                      let uu____2751 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____2751 in
                    failwith uu____2750 in
              let uu____2753 =
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
                      (uu____2754,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____2756;
                    FStar_Extraction_ML_Syntax.loc = uu____2757;_} -> body1
                | uu____2759 ->
                    failwith "unexpected: bad desugaring of Mutable" in
              (uu____2744, uu____2753)
            else (typ, body) in
          (match uu____2739 with
           | (typ1,body1) ->
               let binder =
                 let uu____2764 = translate_type env typ1 in
                 { name; typ = uu____2764; mut = is_mut } in
               let body2 = translate_expr env body1 in
               let env1 = extend env name is_mut in
               let continuation1 = translate_expr env1 continuation in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____2780 =
            let uu____2786 = translate_expr env expr in
            let uu____2787 = translate_branches env branches in
            (uu____2786, uu____2787) in
          EMatch uu____2780
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2795;
             FStar_Extraction_ML_Syntax.loc = uu____2796;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____2798);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____2799;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____2800;_}::[])
          when
          (let uu____2802 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____2802 = "FStar.ST.op_Bang") && (is_mutable env v1)
          -> let uu____2803 = find env v1 in EBound uu____2803
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2805;
             FStar_Extraction_ML_Syntax.loc = uu____2806;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____2808);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____2809;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____2810;_}::e1::[])
          when
          (let uu____2813 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____2813 = "FStar.ST.op_Colon_Equals") && (is_mutable env v1)
          ->
          let uu____2814 =
            let uu____2817 =
              let uu____2818 = find env v1 in EBound uu____2818 in
            let uu____2819 = translate_expr env e1 in
            (uu____2817, uu____2819) in
          EAssign uu____2814
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2821;
             FStar_Extraction_ML_Syntax.loc = uu____2822;_},e1::e2::[])
          when
          (let uu____2826 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____2826 = "FStar.Buffer.index") ||
            (let uu____2827 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____2827 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____2828 =
            let uu____2831 = translate_expr env e1 in
            let uu____2832 = translate_expr env e2 in
            (uu____2831, uu____2832) in
          EBufRead uu____2828
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2834;
             FStar_Extraction_ML_Syntax.loc = uu____2835;_},e1::e2::[])
          when
          let uu____2839 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2839 = "FStar.Buffer.create" ->
          let uu____2840 =
            let uu____2844 = translate_expr env e1 in
            let uu____2845 = translate_expr env e2 in
            (Stack, uu____2844, uu____2845) in
          EBufCreate uu____2840
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2847;
             FStar_Extraction_ML_Syntax.loc = uu____2848;_},_e0::e1::e2::[])
          when
          let uu____2853 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2853 = "FStar.Buffer.rcreate" ->
          let uu____2854 =
            let uu____2858 = translate_expr env e1 in
            let uu____2859 = translate_expr env e2 in
            (Eternal, uu____2858, uu____2859) in
          EBufCreate uu____2854
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2861;
             FStar_Extraction_ML_Syntax.loc = uu____2862;_},e2::[])
          when
          let uu____2865 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2865 = "FStar.Buffer.createL" ->
          let rec list_elements1 acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements1 (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____2889 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!" in
          let list_elements2 = list_elements1 [] in
          let uu____2895 =
            let uu____2899 =
              let uu____2901 = list_elements2 e2 in
              FStar_List.map (translate_expr env) uu____2901 in
            (Stack, uu____2899) in
          EBufCreateL uu____2895
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2905;
             FStar_Extraction_ML_Syntax.loc = uu____2906;_},e1::e2::_e3::[])
          when
          let uu____2911 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2911 = "FStar.Buffer.sub" ->
          let uu____2912 =
            let uu____2915 = translate_expr env e1 in
            let uu____2916 = translate_expr env e2 in
            (uu____2915, uu____2916) in
          EBufSub uu____2912
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2918;
             FStar_Extraction_ML_Syntax.loc = uu____2919;_},e1::e2::[])
          when
          let uu____2923 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2923 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2925;
             FStar_Extraction_ML_Syntax.loc = uu____2926;_},e1::e2::[])
          when
          let uu____2930 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2930 = "FStar.Buffer.offset" ->
          let uu____2931 =
            let uu____2934 = translate_expr env e1 in
            let uu____2935 = translate_expr env e2 in
            (uu____2934, uu____2935) in
          EBufSub uu____2931
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2937;
             FStar_Extraction_ML_Syntax.loc = uu____2938;_},e1::e2::e3::[])
          when
          (let uu____2943 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____2943 = "FStar.Buffer.upd") ||
            (let uu____2944 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____2944 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____2945 =
            let uu____2949 = translate_expr env e1 in
            let uu____2950 = translate_expr env e2 in
            let uu____2951 = translate_expr env e3 in
            (uu____2949, uu____2950, uu____2951) in
          EBufWrite uu____2945
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2953;
             FStar_Extraction_ML_Syntax.loc = uu____2954;_},uu____2955::[])
          when
          let uu____2957 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2957 = "FStar.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2959;
             FStar_Extraction_ML_Syntax.loc = uu____2960;_},uu____2961::[])
          when
          let uu____2963 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2963 = "FStar.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2965;
             FStar_Extraction_ML_Syntax.loc = uu____2966;_},e1::e2::e3::e4::e5::[])
          when
          let uu____2973 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2973 = "FStar.Buffer.blit" ->
          let uu____2974 =
            let uu____2980 = translate_expr env e1 in
            let uu____2981 = translate_expr env e2 in
            let uu____2982 = translate_expr env e3 in
            let uu____2983 = translate_expr env e4 in
            let uu____2984 = translate_expr env e5 in
            (uu____2980, uu____2981, uu____2982, uu____2983, uu____2984) in
          EBufBlit uu____2974
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2986;
             FStar_Extraction_ML_Syntax.loc = uu____2987;_},e1::e2::e3::[])
          when
          let uu____2992 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2992 = "FStar.Buffer.fill" ->
          let uu____2993 =
            let uu____2997 = translate_expr env e1 in
            let uu____2998 = translate_expr env e2 in
            let uu____2999 = translate_expr env e3 in
            (uu____2997, uu____2998, uu____2999) in
          EBufFill uu____2993
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3001;
             FStar_Extraction_ML_Syntax.loc = uu____3002;_},uu____3003::[])
          when
          let uu____3005 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3005 = "FStar.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3007;
             FStar_Extraction_ML_Syntax.loc = uu____3008;_},e1::[])
          when
          let uu____3011 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3011 = "Obj.repr" ->
          let uu____3012 =
            let uu____3015 = translate_expr env e1 in (uu____3015, TAny) in
          ECast uu____3012
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____3018;
             FStar_Extraction_ML_Syntax.loc = uu____3019;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____3024 = FStar_Util.must (mk_width m) in
          let uu____3025 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____3024 uu____3025 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____3027;
             FStar_Extraction_ML_Syntax.loc = uu____3028;_},args)
          when is_bool_op op ->
          let uu____3033 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____3033 args
      | FStar_Extraction_ML_Syntax.MLE_App
        ({
           FStar_Extraction_ML_Syntax.expr =
             FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],"int_to_t");
           FStar_Extraction_ML_Syntax.mlty = _;
           FStar_Extraction_ML_Syntax.loc = _;_},{
                                                   FStar_Extraction_ML_Syntax.expr
                                                     =
                                                     FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_Int
                                                     (c,None ));
                                                   FStar_Extraction_ML_Syntax.mlty
                                                     = _;
                                                   FStar_Extraction_ML_Syntax.loc
                                                     = _;_}::[])
        |FStar_Extraction_ML_Syntax.MLE_App
        ({
           FStar_Extraction_ML_Syntax.expr =
             FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],"uint_to_t");
           FStar_Extraction_ML_Syntax.mlty = _;
           FStar_Extraction_ML_Syntax.loc = _;_},{
                                                   FStar_Extraction_ML_Syntax.expr
                                                     =
                                                     FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_Int
                                                     (c,None ));
                                                   FStar_Extraction_ML_Syntax.mlty
                                                     = _;
                                                   FStar_Extraction_ML_Syntax.loc
                                                     = _;_}::[])
          when is_machine_int m ->
          let uu____3058 =
            let uu____3061 = FStar_Util.must (mk_width m) in (uu____3061, c) in
          EConstant uu____3058
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____3062;
             FStar_Extraction_ML_Syntax.loc = uu____3063;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3065;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3066;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____3070 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____3072;
             FStar_Extraction_ML_Syntax.loc = uu____3073;_},arg::[])
          ->
          let is_known_type =
            (((((((FStar_Util.starts_with c "uint8") ||
                    (FStar_Util.starts_with c "uint16"))
                   || (FStar_Util.starts_with c "uint32"))
                  || (FStar_Util.starts_with c "uint64"))
                 || (FStar_Util.starts_with c "int8"))
                || (FStar_Util.starts_with c "int16"))
               || (FStar_Util.starts_with c "int32"))
              || (FStar_Util.starts_with c "int64") in
          if (FStar_Util.ends_with c "uint64") && is_known_type
          then
            let uu____3078 =
              let uu____3081 = translate_expr env arg in
              (uu____3081, (TInt UInt64)) in
            ECast uu____3078
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____3083 =
                 let uu____3086 = translate_expr env arg in
                 (uu____3086, (TInt UInt32)) in
               ECast uu____3083)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____3088 =
                   let uu____3091 = translate_expr env arg in
                   (uu____3091, (TInt UInt16)) in
                 ECast uu____3088)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____3093 =
                     let uu____3096 = translate_expr env arg in
                     (uu____3096, (TInt UInt8)) in
                   ECast uu____3093)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____3098 =
                       let uu____3101 = translate_expr env arg in
                       (uu____3101, (TInt Int64)) in
                     ECast uu____3098)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____3103 =
                         let uu____3106 = translate_expr env arg in
                         (uu____3106, (TInt Int32)) in
                       ECast uu____3103)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____3108 =
                           let uu____3111 = translate_expr env arg in
                           (uu____3111, (TInt Int16)) in
                         ECast uu____3108)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____3113 =
                             let uu____3116 = translate_expr env arg in
                             (uu____3116, (TInt Int8)) in
                           ECast uu____3113)
                        else
                          (let uu____3118 =
                             let uu____3122 =
                               let uu____3124 = translate_expr env arg in
                               [uu____3124] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____3122) in
                           EApp uu____3118)
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name (path,function_name);
             FStar_Extraction_ML_Syntax.mlty = uu____3129;
             FStar_Extraction_ML_Syntax.loc = uu____3130;_},args)
          ->
          let uu____3136 =
            let uu____3140 = FStar_List.map (translate_expr env) args in
            ((EQualified (path, function_name)), uu____3140) in
          EApp uu____3136
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Var (name,uu____3145);
             FStar_Extraction_ML_Syntax.mlty = uu____3146;
             FStar_Extraction_ML_Syntax.loc = uu____3147;_},args)
          ->
          let uu____3151 =
            let uu____3155 =
              let uu____3156 = find env name in EBound uu____3156 in
            let uu____3157 = FStar_List.map (translate_expr env) args in
            (uu____3155, uu____3157) in
          EApp uu____3151
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____3163 =
            let uu____3166 = translate_expr env e1 in
            let uu____3167 = translate_type env t_to in
            (uu____3166, uu____3167) in
          ECast uu____3163
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____3168,fields) ->
          let uu____3178 =
            let uu____3184 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____3185 =
              FStar_List.map
                (fun uu____3193  ->
                   match uu____3193 with
                   | (field,expr) ->
                       let uu____3200 = translate_expr env expr in
                       (field, uu____3200)) fields in
            (uu____3184, uu____3185) in
          EFlat uu____3178
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____3206 =
            let uu____3210 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____3211 = translate_expr env e1 in
            (uu____3210, uu____3211, (snd path)) in
          EField uu____3206
      | FStar_Extraction_ML_Syntax.MLE_Let uu____3213 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____3221) ->
          let uu____3224 =
            let uu____3225 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1 in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____3225 in
          failwith uu____3224
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____3229 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____3229
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____3233 = FStar_List.map (translate_expr env) es in
          ETuple uu____3233
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____3235,cons1),es) ->
          let uu____3245 =
            let uu____3250 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____3251 = FStar_List.map (translate_expr env) es in
            (uu____3250, cons1, uu____3251) in
          ECons uu____3245
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args in
          let env1 = add_binders env args in
          let uu____3265 =
            let uu____3269 = translate_expr env1 body in
            (binders, uu____3269) in
          EFun uu____3265
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____3276 =
            let uu____3280 = translate_expr env e1 in
            let uu____3281 = translate_expr env e2 in
            let uu____3282 =
              match e3 with
              | None  -> EUnit
              | Some e31 -> translate_expr env e31 in
            (uu____3280, uu____3281, uu____3282) in
          EIfThenElse uu____3276
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____3284 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____3288 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____3296 ->
          failwith "todo: translate_expr [MLE_Coerce]"
and assert_lid: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____3309 =
              let uu____3316 = FStar_List.map (translate_type env) ts in
              (lid, uu____3316) in
            TApp uu____3309
          else TQualified lid
      | uu____3320 -> failwith "invalid argument: assert_lid"
and translate_branches:
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern* FStar_Extraction_ML_Syntax.mlexpr
      option* FStar_Extraction_ML_Syntax.mlexpr) Prims.list ->
      (pattern* expr) Prims.list
  =
  fun env  -> fun branches  -> FStar_List.map (translate_branch env) branches
and translate_branch:
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern* FStar_Extraction_ML_Syntax.mlexpr
      option* FStar_Extraction_ML_Syntax.mlexpr) -> (pattern* expr)
  =
  fun env  ->
    fun uu____3335  ->
      match uu____3335 with
      | (pat,guard,expr) ->
          if guard = None
          then
            let uu____3350 = translate_pat env pat in
            (match uu____3350 with
             | (env1,pat1) ->
                 let uu____3357 = translate_expr env1 expr in
                 (pat1, uu____3357))
          else failwith "todo: translate_branch"
and translate_pat:
  env -> FStar_Extraction_ML_Syntax.mlpattern -> (env* pattern) =
  fun env  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Unit ) -> (env, PUnit)
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Bool b) -> (env, (PBool b))
      | FStar_Extraction_ML_Syntax.MLP_Var (name,uu____3367) ->
          let env1 = extend env name false in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_" false in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____3370,cons1),ps) ->
          let uu____3380 =
            FStar_List.fold_left
              (fun uu____3387  ->
                 fun p1  ->
                   match uu____3387 with
                   | (env1,acc) ->
                       let uu____3399 = translate_pat env1 p1 in
                       (match uu____3399 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____3380 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____3416,ps) ->
          let uu____3426 =
            FStar_List.fold_left
              (fun uu____3439  ->
                 fun uu____3440  ->
                   match (uu____3439, uu____3440) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____3477 = translate_pat env1 p1 in
                       (match uu____3477 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps in
          (match uu____3426 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____3511 =
            FStar_List.fold_left
              (fun uu____3518  ->
                 fun p1  ->
                   match uu____3518 with
                   | (env1,acc) ->
                       let uu____3530 = translate_pat env1 p1 in
                       (match uu____3530 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____3511 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____3546 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____3549 ->
          failwith "todo: translate_pat [MLP_Branch]"
and translate_constant: FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_Int (s,Some uu____3556) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____3564 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____3565 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____3566 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____3567 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (uu____3569,None ) ->
        failwith "todo: translate_expr [MLC_Int]"
and mk_op_app:
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr
  =
  fun env  ->
    fun w  ->
      fun op  ->
        fun args  ->
          let uu____3580 =
            let uu____3584 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____3584) in
          EApp uu____3580