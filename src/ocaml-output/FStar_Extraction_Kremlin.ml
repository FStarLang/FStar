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
    | "add" -> Some Add
    | "op_Plus_Hat" -> Some Add
    | "add_mod" -> Some AddW
    | "op_Plus_Percent_Hat" -> Some AddW
    | "sub" -> Some Sub
    | "op_Subtraction_Hat" -> Some Sub
    | "sub_mod" -> Some SubW
    | "op_Subtraction_Percent_Hat" -> Some SubW
    | "mul" -> Some Mult
    | "op_Star_Hat" -> Some Mult
    | "mul_mod" -> Some MultW
    | "op_Star_Percent_Hat" -> Some MultW
    | "div" -> Some Div
    | "op_Slash_Hat" -> Some Div
    | "div_mod" -> Some DivW
    | "op_Slash_Percent_Hat" -> Some DivW
    | "rem" -> Some Mod
    | "op_Percent_Hat" -> Some Mod
    | "logor" -> Some BOr
    | "op_Bar_Hat" -> Some BOr
    | "logxor" -> Some BXor
    | "op_Hat_Hat" -> Some BXor
    | "logand" -> Some BAnd
    | "op_Amp_Hat" -> Some BAnd
    | "lognot" -> Some BNot
    | "shift_right" -> Some BShiftR
    | "op_Greater_Greater_Hat" -> Some BShiftR
    | "shift_left" -> Some BShiftL
    | "op_Less_Less_Hat" -> Some BShiftL
    | "eq" -> Some Eq
    | "op_Equals_Hat" -> Some Eq
    | "op_Greater_Hat" -> Some Gt
    | "gt" -> Some Gt
    | "op_Greater_Equals_Hat" -> Some Gte
    | "gte" -> Some Gte
    | "op_Less_Hat" -> Some Lt
    | "lt" -> Some Lt
    | "op_Less_Equals_Hat" -> Some Lte
    | "lte" -> Some Lte
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
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____2105);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some
                            (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2108;
                          FStar_Extraction_ML_Syntax.mllb_def =
                            {
                              FStar_Extraction_ML_Syntax.expr =
                                FStar_Extraction_ML_Syntax.MLE_Fun
                                (args,body);
                              FStar_Extraction_ML_Syntax.mlty = uu____2111;
                              FStar_Extraction_ML_Syntax.loc = uu____2112;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____2113;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___123_2124  ->
                 match uu___123_2124 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____2125 -> false) flags in
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun uu____2132  ->
                   match uu____2132 with
                   | (name1,uu____2136) -> extend_t env2 name1) env1 tvars in
          let rec find_return_type uu___124_2140 =
            match uu___124_2140 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2141,uu____2142,t)
                -> find_return_type t
            | t -> t in
          let t =
            let uu____2146 = find_return_type t0 in
            translate_type env2 uu____2146 in
          let binders = translate_binders env2 args in
          let env3 = add_binders env2 args in
          let name1 = ((env3.module_name), name) in
          let flags1 = translate_flags flags in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
               let uu____2163 =
                 let uu____2164 =
                   let uu____2172 = translate_type env3 t0 in
                   (None, name1, uu____2172) in
                 DExternal uu____2164 in
               Some uu____2163
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
                 ((let uu____2197 = FStar_Util.print_exn e in
                   FStar_Util.print2 "Warning: writing a stub for %s (%s)\n"
                     (snd name1) uu____2197);
                  Some
                    (DFunction
                       (None, flags1, (FStar_List.length tvars), t, name1,
                         binders, EAbort))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____2212);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some
                            (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2215;
                          FStar_Extraction_ML_Syntax.mllb_def =
                            {
                              FStar_Extraction_ML_Syntax.expr =
                                FStar_Extraction_ML_Syntax.MLE_Coerce
                                ({
                                   FStar_Extraction_ML_Syntax.expr =
                                     FStar_Extraction_ML_Syntax.MLE_Fun
                                     (args,body);
                                   FStar_Extraction_ML_Syntax.mlty =
                                     uu____2218;
                                   FStar_Extraction_ML_Syntax.loc =
                                     uu____2219;_},uu____2220,uu____2221);
                              FStar_Extraction_ML_Syntax.mlty = uu____2222;
                              FStar_Extraction_ML_Syntax.loc = uu____2223;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____2224;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___123_2235  ->
                 match uu___123_2235 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____2236 -> false) flags in
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun uu____2243  ->
                   match uu____2243 with
                   | (name1,uu____2247) -> extend_t env2 name1) env1 tvars in
          let rec find_return_type uu___124_2251 =
            match uu___124_2251 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2252,uu____2253,t)
                -> find_return_type t
            | t -> t in
          let t =
            let uu____2257 = find_return_type t0 in
            translate_type env2 uu____2257 in
          let binders = translate_binders env2 args in
          let env3 = add_binders env2 args in
          let name1 = ((env3.module_name), name) in
          let flags1 = translate_flags flags in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
               let uu____2274 =
                 let uu____2275 =
                   let uu____2283 = translate_type env3 t0 in
                   (None, name1, uu____2283) in
                 DExternal uu____2275 in
               Some uu____2274
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
                 ((let uu____2308 = FStar_Util.print_exn e in
                   FStar_Util.print2 "Warning: writing a stub for %s (%s)\n"
                     (snd name1) uu____2308);
                  Some
                    (DFunction
                       (None, flags1, (FStar_List.length tvars), t, name1,
                         binders, EAbort))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____2323);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some ([],t);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2325;
                          FStar_Extraction_ML_Syntax.mllb_def = expr;
                          FStar_Extraction_ML_Syntax.print_typ = uu____2327;_}::[])
          ->
          let flags1 = translate_flags flags in
          let t1 = translate_type env t in
          let name1 = ((env.module_name), name) in
          (try
             let expr1 = translate_expr env expr in
             Some (DGlobal (flags1, name1, t1, expr1))
           with
           | e ->
               ((let uu____2353 = FStar_Util.print_exn e in
                 FStar_Util.print2
                   "Warning: not translating definition for %s (%s)\n"
                   (snd name1) uu____2353);
                Some (DGlobal (flags1, name1, t1, EAny))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (uu____2359,uu____2360,{
                                   FStar_Extraction_ML_Syntax.mllb_name =
                                     (name,uu____2362);
                                   FStar_Extraction_ML_Syntax.mllb_tysc = ts;
                                   FStar_Extraction_ML_Syntax.mllb_add_unit =
                                     uu____2364;
                                   FStar_Extraction_ML_Syntax.mllb_def =
                                     uu____2365;
                                   FStar_Extraction_ML_Syntax.print_typ =
                                     uu____2366;_}::uu____2367)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           (match ts with
            | Some (idents,t) ->
                let uu____2377 =
                  let uu____2378 = FStar_List.map FStar_Pervasives.fst idents in
                  FStar_String.concat ", " uu____2378 in
                let uu____2382 =
                  FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                  uu____2377 uu____2382
            | None  -> ());
           None)
      | FStar_Extraction_ML_Syntax.MLM_Let uu____2384 ->
          failwith "impossible"
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____2386 -> None
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((assumed,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_Abbrev t))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____2418  ->
                   match uu____2418 with
                   | (name2,uu____2422) -> extend_t env1 name2) env args in
          if assumed
          then None
          else
            (let uu____2425 =
               let uu____2426 =
                 let uu____2433 = translate_type env1 t in
                 (name1, (FStar_List.length args), uu____2433) in
               DTypeAlias uu____2426 in
             Some uu____2425)
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2441,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_Record fields))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____2475  ->
                   match uu____2475 with
                   | (name2,uu____2479) -> extend_t env1 name2) env args in
          let uu____2480 =
            let uu____2481 =
              let uu____2493 =
                FStar_List.map
                  (fun uu____2505  ->
                     match uu____2505 with
                     | (f,t) ->
                         let uu____2514 =
                           let uu____2517 = translate_type env1 t in
                           (uu____2517, false) in
                         (f, uu____2514)) fields in
              (name1, (FStar_List.length args), uu____2493) in
            DTypeFlat uu____2481 in
          Some uu____2480
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2532,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_DType branches))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____2567  ->
                   match uu____2567 with
                   | (name2,uu____2571) -> extend_t env1 name2) env args in
          let uu____2572 =
            let uu____2573 =
              let uu____2588 =
                FStar_List.mapi
                  (fun i  ->
                     fun uu____2608  ->
                       match uu____2608 with
                       | (cons1,ts) ->
                           let uu____2623 =
                             FStar_List.mapi
                               (fun j  ->
                                  fun t  ->
                                    let uu____2635 =
                                      let uu____2636 =
                                        FStar_Util.string_of_int i in
                                      let uu____2637 =
                                        FStar_Util.string_of_int j in
                                      FStar_Util.format2 "x%s%s" uu____2636
                                        uu____2637 in
                                    let uu____2638 =
                                      let uu____2641 = translate_type env1 t in
                                      (uu____2641, false) in
                                    (uu____2635, uu____2638)) ts in
                           (cons1, uu____2623)) branches in
              (name1, (FStar_List.length args), uu____2588) in
            DTypeVariant uu____2573 in
          Some uu____2572
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2664,name,_mangled_name,uu____2667,uu____2668)::uu____2669)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           None)
      | FStar_Extraction_ML_Syntax.MLM_Ty [] ->
          (FStar_Util.print_string
             "Impossible!! Empty block of mutually recursive type declarations";
           None)
      | FStar_Extraction_ML_Syntax.MLM_Top uu____2691 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____2693 ->
          failwith "todo: translate_decl [MLM_Exn]"
and translate_type: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var (name,uu____2701) ->
          let uu____2702 = find_t env name in TBound uu____2702
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____2704,t2) ->
          let uu____2706 =
            let uu____2709 = translate_type env t1 in
            let uu____2710 = translate_type env t2 in
            (uu____2709, uu____2710) in
          TArrow uu____2706
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____2713 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2713 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____2716 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2716 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____2723 = FStar_Util.must (mk_width m) in TInt uu____2723
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____2730 = FStar_Util.must (mk_width m) in TInt uu____2730
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____2734 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2734 = "FStar.Buffer.buffer" ->
          let uu____2735 = translate_type env arg in TBuf uu____2735
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____2736::[],p) when
          let uu____2739 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2739 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____2761 = FStar_List.map (translate_type env) args in
          TTuple uu____2761
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____2773 =
              let uu____2780 = FStar_List.map (translate_type env) args in
              (lid, uu____2780) in
            TApp uu____2773
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____2786 = FStar_List.map (translate_type env) ts in
          TTuple uu____2786
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
    fun uu____2796  ->
      match uu____2796 with
      | ((name,uu____2800),typ) ->
          let uu____2804 = translate_type env typ in
          { name; typ = uu____2804; mut = false }
and translate_expr: env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____2809) ->
          let uu____2810 = find env name in EBound uu____2810
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____2814 =
            let uu____2817 = FStar_Util.must (mk_op op) in
            let uu____2818 = FStar_Util.must (mk_width m) in
            (uu____2817, uu____2818) in
          EOp uu____2814
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____2821 =
            let uu____2824 = FStar_Util.must (mk_bool_op op) in
            (uu____2824, Bool) in
          EOp uu____2821
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags,{
                           FStar_Extraction_ML_Syntax.mllb_name =
                             (name,uu____2829);
                           FStar_Extraction_ML_Syntax.mllb_tysc = Some
                             ([],typ);
                           FStar_Extraction_ML_Syntax.mllb_add_unit =
                             add_unit;
                           FStar_Extraction_ML_Syntax.mllb_def = body;
                           FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let is_mut =
            FStar_Util.for_some
              (fun uu___125_2845  ->
                 match uu___125_2845 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____2846 -> false) flags in
          let uu____2847 =
            if is_mut
            then
              let uu____2852 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____2856 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____2856 = "FStar.ST.stackref" -> t
                | uu____2857 ->
                    let uu____2858 =
                      let uu____2859 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____2859 in
                    failwith uu____2858 in
              let uu____2861 =
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
                      (uu____2862,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____2864;
                    FStar_Extraction_ML_Syntax.loc = uu____2865;_} -> body1
                | uu____2867 ->
                    failwith "unexpected: bad desugaring of Mutable" in
              (uu____2852, uu____2861)
            else (typ, body) in
          (match uu____2847 with
           | (typ1,body1) ->
               let binder =
                 let uu____2872 = translate_type env typ1 in
                 { name; typ = uu____2872; mut = is_mut } in
               let body2 = translate_expr env body1 in
               let env1 = extend env name is_mut in
               let continuation1 = translate_expr env1 continuation in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____2888 =
            let uu____2894 = translate_expr env expr in
            let uu____2895 = translate_branches env branches in
            (uu____2894, uu____2895) in
          EMatch uu____2888
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2903;
             FStar_Extraction_ML_Syntax.loc = uu____2904;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____2906);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____2907;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____2908;_}::[])
          when
          (let uu____2910 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____2910 = "FStar.ST.op_Bang") && (is_mutable env v1)
          -> let uu____2911 = find env v1 in EBound uu____2911
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2913;
             FStar_Extraction_ML_Syntax.loc = uu____2914;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____2916);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____2917;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____2918;_}::e1::[])
          when
          (let uu____2921 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____2921 = "FStar.ST.op_Colon_Equals") && (is_mutable env v1)
          ->
          let uu____2922 =
            let uu____2925 =
              let uu____2926 = find env v1 in EBound uu____2926 in
            let uu____2927 = translate_expr env e1 in
            (uu____2925, uu____2927) in
          EAssign uu____2922
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2929;
             FStar_Extraction_ML_Syntax.loc = uu____2930;_},e1::e2::[])
          when
          (let uu____2934 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____2934 = "FStar.Buffer.index") ||
            (let uu____2935 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____2935 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____2936 =
            let uu____2939 = translate_expr env e1 in
            let uu____2940 = translate_expr env e2 in
            (uu____2939, uu____2940) in
          EBufRead uu____2936
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2942;
             FStar_Extraction_ML_Syntax.loc = uu____2943;_},e1::e2::[])
          when
          let uu____2947 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2947 = "FStar.Buffer.create" ->
          let uu____2948 =
            let uu____2952 = translate_expr env e1 in
            let uu____2953 = translate_expr env e2 in
            (Stack, uu____2952, uu____2953) in
          EBufCreate uu____2948
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2955;
             FStar_Extraction_ML_Syntax.loc = uu____2956;_},_e0::e1::e2::[])
          when
          let uu____2961 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2961 = "FStar.Buffer.rcreate" ->
          let uu____2962 =
            let uu____2966 = translate_expr env e1 in
            let uu____2967 = translate_expr env e2 in
            (Eternal, uu____2966, uu____2967) in
          EBufCreate uu____2962
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____2969;
             FStar_Extraction_ML_Syntax.loc = uu____2970;_},e2::[])
          when
          let uu____2973 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2973 = "FStar.Buffer.createL" ->
          let rec list_elements1 acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements1 (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____2997 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!" in
          let list_elements2 = list_elements1 [] in
          let uu____3003 =
            let uu____3007 =
              let uu____3009 = list_elements2 e2 in
              FStar_List.map (translate_expr env) uu____3009 in
            (Stack, uu____3007) in
          EBufCreateL uu____3003
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3013;
             FStar_Extraction_ML_Syntax.loc = uu____3014;_},e1::e2::_e3::[])
          when
          let uu____3019 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3019 = "FStar.Buffer.sub" ->
          let uu____3020 =
            let uu____3023 = translate_expr env e1 in
            let uu____3024 = translate_expr env e2 in
            (uu____3023, uu____3024) in
          EBufSub uu____3020
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3026;
             FStar_Extraction_ML_Syntax.loc = uu____3027;_},e1::e2::[])
          when
          let uu____3031 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3031 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3033;
             FStar_Extraction_ML_Syntax.loc = uu____3034;_},e1::e2::[])
          when
          let uu____3038 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3038 = "FStar.Buffer.offset" ->
          let uu____3039 =
            let uu____3042 = translate_expr env e1 in
            let uu____3043 = translate_expr env e2 in
            (uu____3042, uu____3043) in
          EBufSub uu____3039
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3045;
             FStar_Extraction_ML_Syntax.loc = uu____3046;_},e1::e2::e3::[])
          when
          (let uu____3051 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____3051 = "FStar.Buffer.upd") ||
            (let uu____3052 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____3052 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____3053 =
            let uu____3057 = translate_expr env e1 in
            let uu____3058 = translate_expr env e2 in
            let uu____3059 = translate_expr env e3 in
            (uu____3057, uu____3058, uu____3059) in
          EBufWrite uu____3053
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3061;
             FStar_Extraction_ML_Syntax.loc = uu____3062;_},uu____3063::[])
          when
          let uu____3065 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3065 = "FStar.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3067;
             FStar_Extraction_ML_Syntax.loc = uu____3068;_},uu____3069::[])
          when
          let uu____3071 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3071 = "FStar.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3073;
             FStar_Extraction_ML_Syntax.loc = uu____3074;_},e1::e2::e3::e4::e5::[])
          when
          let uu____3081 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3081 = "FStar.Buffer.blit" ->
          let uu____3082 =
            let uu____3088 = translate_expr env e1 in
            let uu____3089 = translate_expr env e2 in
            let uu____3090 = translate_expr env e3 in
            let uu____3091 = translate_expr env e4 in
            let uu____3092 = translate_expr env e5 in
            (uu____3088, uu____3089, uu____3090, uu____3091, uu____3092) in
          EBufBlit uu____3082
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3094;
             FStar_Extraction_ML_Syntax.loc = uu____3095;_},e1::e2::e3::[])
          when
          let uu____3100 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3100 = "FStar.Buffer.fill" ->
          let uu____3101 =
            let uu____3105 = translate_expr env e1 in
            let uu____3106 = translate_expr env e2 in
            let uu____3107 = translate_expr env e3 in
            (uu____3105, uu____3106, uu____3107) in
          EBufFill uu____3101
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3109;
             FStar_Extraction_ML_Syntax.loc = uu____3110;_},uu____3111::[])
          when
          let uu____3113 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3113 = "FStar.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3115;
             FStar_Extraction_ML_Syntax.loc = uu____3116;_},e1::[])
          when
          let uu____3119 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3119 = "Obj.repr" ->
          let uu____3120 =
            let uu____3123 = translate_expr env e1 in (uu____3123, TAny) in
          ECast uu____3120
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____3126;
             FStar_Extraction_ML_Syntax.loc = uu____3127;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____3132 = FStar_Util.must (mk_width m) in
          let uu____3133 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____3132 uu____3133 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____3135;
             FStar_Extraction_ML_Syntax.loc = uu____3136;_},args)
          when is_bool_op op ->
          let uu____3141 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____3141 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____3143;
             FStar_Extraction_ML_Syntax.loc = uu____3144;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,None ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3146;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3147;_}::[])
          when is_machine_int m ->
          let uu____3155 =
            let uu____3158 = FStar_Util.must (mk_width m) in (uu____3158, c) in
          EConstant uu____3155
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____3160;
             FStar_Extraction_ML_Syntax.loc = uu____3161;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,None ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3163;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3164;_}::[])
          when is_machine_int m ->
          let uu____3172 =
            let uu____3175 = FStar_Util.must (mk_width m) in (uu____3175, c) in
          EConstant uu____3172
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____3176;
             FStar_Extraction_ML_Syntax.loc = uu____3177;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3179;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3180;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____3184 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____3186;
             FStar_Extraction_ML_Syntax.loc = uu____3187;_},arg::[])
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
            let uu____3192 =
              let uu____3195 = translate_expr env arg in
              (uu____3195, (TInt UInt64)) in
            ECast uu____3192
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____3197 =
                 let uu____3200 = translate_expr env arg in
                 (uu____3200, (TInt UInt32)) in
               ECast uu____3197)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____3202 =
                   let uu____3205 = translate_expr env arg in
                   (uu____3205, (TInt UInt16)) in
                 ECast uu____3202)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____3207 =
                     let uu____3210 = translate_expr env arg in
                     (uu____3210, (TInt UInt8)) in
                   ECast uu____3207)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____3212 =
                       let uu____3215 = translate_expr env arg in
                       (uu____3215, (TInt Int64)) in
                     ECast uu____3212)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____3217 =
                         let uu____3220 = translate_expr env arg in
                         (uu____3220, (TInt Int32)) in
                       ECast uu____3217)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____3222 =
                           let uu____3225 = translate_expr env arg in
                           (uu____3225, (TInt Int16)) in
                         ECast uu____3222)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____3227 =
                             let uu____3230 = translate_expr env arg in
                             (uu____3230, (TInt Int8)) in
                           ECast uu____3227)
                        else
                          (let uu____3232 =
                             let uu____3236 =
                               let uu____3238 = translate_expr env arg in
                               [uu____3238] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____3236) in
                           EApp uu____3232)
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name (path,function_name);
             FStar_Extraction_ML_Syntax.mlty = uu____3243;
             FStar_Extraction_ML_Syntax.loc = uu____3244;_},args)
          ->
          let uu____3250 =
            let uu____3254 = FStar_List.map (translate_expr env) args in
            ((EQualified (path, function_name)), uu____3254) in
          EApp uu____3250
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Var (name,uu____3259);
             FStar_Extraction_ML_Syntax.mlty = uu____3260;
             FStar_Extraction_ML_Syntax.loc = uu____3261;_},args)
          ->
          let uu____3265 =
            let uu____3269 =
              let uu____3270 = find env name in EBound uu____3270 in
            let uu____3271 = FStar_List.map (translate_expr env) args in
            (uu____3269, uu____3271) in
          EApp uu____3265
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____3277 =
            let uu____3280 = translate_expr env e1 in
            let uu____3281 = translate_type env t_to in
            (uu____3280, uu____3281) in
          ECast uu____3277
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____3282,fields) ->
          let uu____3292 =
            let uu____3298 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____3299 =
              FStar_List.map
                (fun uu____3307  ->
                   match uu____3307 with
                   | (field,expr) ->
                       let uu____3314 = translate_expr env expr in
                       (field, uu____3314)) fields in
            (uu____3298, uu____3299) in
          EFlat uu____3292
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____3320 =
            let uu____3324 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____3325 = translate_expr env e1 in
            (uu____3324, uu____3325, (snd path)) in
          EField uu____3320
      | FStar_Extraction_ML_Syntax.MLE_Let uu____3327 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____3335) ->
          let uu____3338 =
            let uu____3339 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1 in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____3339 in
          failwith uu____3338
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____3343 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____3343
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____3347 = FStar_List.map (translate_expr env) es in
          ETuple uu____3347
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____3349,cons1),es) ->
          let uu____3359 =
            let uu____3364 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____3365 = FStar_List.map (translate_expr env) es in
            (uu____3364, cons1, uu____3365) in
          ECons uu____3359
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args in
          let env1 = add_binders env args in
          let uu____3379 =
            let uu____3383 = translate_expr env1 body in
            (binders, uu____3383) in
          EFun uu____3379
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____3390 =
            let uu____3394 = translate_expr env e1 in
            let uu____3395 = translate_expr env e2 in
            let uu____3396 =
              match e3 with
              | None  -> EUnit
              | Some e31 -> translate_expr env e31 in
            (uu____3394, uu____3395, uu____3396) in
          EIfThenElse uu____3390
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____3398 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____3402 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____3410 ->
          failwith "todo: translate_expr [MLE_Coerce]"
and assert_lid: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____3426 =
              let uu____3433 = FStar_List.map (translate_type env) ts in
              (lid, uu____3433) in
            TApp uu____3426
          else TQualified lid
      | uu____3437 -> failwith "invalid argument: assert_lid"
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
    fun uu____3452  ->
      match uu____3452 with
      | (pat,guard,expr) ->
          if guard = None
          then
            let uu____3467 = translate_pat env pat in
            (match uu____3467 with
             | (env1,pat1) ->
                 let uu____3474 = translate_expr env1 expr in
                 (pat1, uu____3474))
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
      | FStar_Extraction_ML_Syntax.MLP_Var (name,uu____3484) ->
          let env1 = extend env name false in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_" false in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____3487,cons1),ps) ->
          let uu____3497 =
            FStar_List.fold_left
              (fun uu____3504  ->
                 fun p1  ->
                   match uu____3504 with
                   | (env1,acc) ->
                       let uu____3516 = translate_pat env1 p1 in
                       (match uu____3516 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____3497 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____3533,ps) ->
          let uu____3543 =
            FStar_List.fold_left
              (fun uu____3556  ->
                 fun uu____3557  ->
                   match (uu____3556, uu____3557) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____3594 = translate_pat env1 p1 in
                       (match uu____3594 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps in
          (match uu____3543 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____3628 =
            FStar_List.fold_left
              (fun uu____3635  ->
                 fun p1  ->
                   match uu____3635 with
                   | (env1,acc) ->
                       let uu____3647 = translate_pat env1 p1 in
                       (match uu____3647 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____3628 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____3663 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____3666 ->
          failwith "todo: translate_pat [MLP_Branch]"
and translate_constant: FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_Int (s,Some uu____3673) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____3681 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____3682 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____3683 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____3684 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (uu____3686,None ) ->
        failwith "todo: translate_expr [MLC_Int]"
and mk_op_app:
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr
  =
  fun env  ->
    fun w  ->
      fun op  ->
        fun args  ->
          let uu____3697 =
            let uu____3701 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____3701) in
          EApp uu____3697