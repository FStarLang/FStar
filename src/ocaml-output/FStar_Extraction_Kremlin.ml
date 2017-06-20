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
    match projectee with | DGlobal _0 -> true | uu____348 -> false
let __proj__DGlobal__item___0:
  decl ->
    (flag Prims.list* (Prims.string Prims.list* Prims.string)* typ* expr)
  = fun projectee  -> match projectee with | DGlobal _0 -> _0
let uu___is_DFunction: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____397 -> false
let __proj__DFunction__item___0:
  decl ->
    (cc option* flag Prims.list* Prims.int* typ* (Prims.string Prims.list*
      Prims.string)* binder Prims.list* expr)
  = fun projectee  -> match projectee with | DFunction _0 -> _0
let uu___is_DTypeAlias: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____454 -> false
let __proj__DTypeAlias__item___0:
  decl -> ((Prims.string Prims.list* Prims.string)* Prims.int* typ) =
  fun projectee  -> match projectee with | DTypeAlias _0 -> _0
let uu___is_DTypeFlat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____495 -> false
let __proj__DTypeFlat__item___0:
  decl ->
    ((Prims.string Prims.list* Prims.string)* Prims.int* (Prims.string* (typ*
      Prims.bool)) Prims.list)
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0
let uu___is_DExternal: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____547 -> false
let __proj__DExternal__item___0:
  decl -> (cc option* (Prims.string Prims.list* Prims.string)* typ) =
  fun projectee  -> match projectee with | DExternal _0 -> _0
let uu___is_DTypeVariant: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____594 -> false
let __proj__DTypeVariant__item___0:
  decl ->
    ((Prims.string Prims.list* Prims.string)* Prims.int* (Prims.string*
      (Prims.string* (typ* Prims.bool)) Prims.list) Prims.list)
  = fun projectee  -> match projectee with | DTypeVariant _0 -> _0
let uu___is_StdCall: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____647 -> false
let uu___is_CDecl: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____651 -> false
let uu___is_FastCall: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____655 -> false
let uu___is_Private: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____659 -> false
let uu___is_NoExtract: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____663 -> false
let uu___is_CInline: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____667 -> false
let uu___is_Substitute: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____671 -> false
let uu___is_Eternal: lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____675 -> false
let uu___is_Stack: lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____679 -> false
let uu___is_EBound: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____684 -> false
let __proj__EBound__item___0: expr -> Prims.int =
  fun projectee  -> match projectee with | EBound _0 -> _0
let uu___is_EQualified: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____699 -> false
let __proj__EQualified__item___0:
  expr -> (Prims.string Prims.list* Prims.string) =
  fun projectee  -> match projectee with | EQualified _0 -> _0
let uu___is_EConstant: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____722 -> false
let __proj__EConstant__item___0: expr -> (width* Prims.string) =
  fun projectee  -> match projectee with | EConstant _0 -> _0
let uu___is_EUnit: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____739 -> false
let uu___is_EApp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____747 -> false
let __proj__EApp__item___0: expr -> (expr* expr Prims.list) =
  fun projectee  -> match projectee with | EApp _0 -> _0
let uu___is_ELet: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____771 -> false
let __proj__ELet__item___0: expr -> (binder* expr* expr) =
  fun projectee  -> match projectee with | ELet _0 -> _0
let uu___is_EIfThenElse: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____795 -> false
let __proj__EIfThenElse__item___0: expr -> (expr* expr* expr) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0
let uu___is_ESequence: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____817 -> false
let __proj__ESequence__item___0: expr -> expr Prims.list =
  fun projectee  -> match projectee with | ESequence _0 -> _0
let uu___is_EAssign: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____834 -> false
let __proj__EAssign__item___0: expr -> (expr* expr) =
  fun projectee  -> match projectee with | EAssign _0 -> _0
let uu___is_EBufCreate: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____855 -> false
let __proj__EBufCreate__item___0: expr -> (lifetime* expr* expr) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0
let uu___is_EBufRead: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____878 -> false
let __proj__EBufRead__item___0: expr -> (expr* expr) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0
let uu___is_EBufWrite: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____899 -> false
let __proj__EBufWrite__item___0: expr -> (expr* expr* expr) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0
let uu___is_EBufSub: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____922 -> false
let __proj__EBufSub__item___0: expr -> (expr* expr) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0
let uu___is_EBufBlit: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____945 -> false
let __proj__EBufBlit__item___0: expr -> (expr* expr* expr* expr* expr) =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0
let uu___is_EMatch: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____977 -> false
let __proj__EMatch__item___0: expr -> (expr* (pattern* expr) Prims.list) =
  fun projectee  -> match projectee with | EMatch _0 -> _0
let uu___is_EOp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1006 -> false
let __proj__EOp__item___0: expr -> (op* width) =
  fun projectee  -> match projectee with | EOp _0 -> _0
let uu___is_ECast: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1026 -> false
let __proj__ECast__item___0: expr -> (expr* typ) =
  fun projectee  -> match projectee with | ECast _0 -> _0
let uu___is_EPushFrame: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1043 -> false
let uu___is_EPopFrame: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1047 -> false
let uu___is_EBool: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1052 -> false
let __proj__EBool__item___0: expr -> Prims.bool =
  fun projectee  -> match projectee with | EBool _0 -> _0
let uu___is_EAny: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1063 -> false
let uu___is_EAbort: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1067 -> false
let uu___is_EReturn: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1072 -> false
let __proj__EReturn__item___0: expr -> expr =
  fun projectee  -> match projectee with | EReturn _0 -> _0
let uu___is_EFlat: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1089 -> false
let __proj__EFlat__item___0: expr -> (typ* (Prims.string* expr) Prims.list) =
  fun projectee  -> match projectee with | EFlat _0 -> _0
let uu___is_EField: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____1119 -> false
let __proj__EField__item___0: expr -> (typ* expr* Prims.string) =
  fun projectee  -> match projectee with | EField _0 -> _0
let uu___is_EWhile: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____1142 -> false
let __proj__EWhile__item___0: expr -> (expr* expr) =
  fun projectee  -> match projectee with | EWhile _0 -> _0
let uu___is_EBufCreateL: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____1163 -> false
let __proj__EBufCreateL__item___0: expr -> (lifetime* expr Prims.list) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0
let uu___is_ETuple: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____1185 -> false
let __proj__ETuple__item___0: expr -> expr Prims.list =
  fun projectee  -> match projectee with | ETuple _0 -> _0
let uu___is_ECons: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____1204 -> false
let __proj__ECons__item___0: expr -> (typ* Prims.string* expr Prims.list) =
  fun projectee  -> match projectee with | ECons _0 -> _0
let uu___is_EBufFill: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____1231 -> false
let __proj__EBufFill__item___0: expr -> (expr* expr* expr) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0
let uu___is_EString: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____1252 -> false
let __proj__EString__item___0: expr -> Prims.string =
  fun projectee  -> match projectee with | EString _0 -> _0
let uu___is_EFun: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____1267 -> false
let __proj__EFun__item___0: expr -> (binder Prims.list* expr) =
  fun projectee  -> match projectee with | EFun _0 -> _0
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____1287 -> false
let uu___is_AddW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____1291 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____1295 -> false
let uu___is_SubW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____1299 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____1303 -> false
let uu___is_DivW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____1307 -> false
let uu___is_Mult: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____1311 -> false
let uu___is_MultW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____1315 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____1319 -> false
let uu___is_BOr: op -> Prims.bool =
  fun projectee  -> match projectee with | BOr  -> true | uu____1323 -> false
let uu___is_BAnd: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____1327 -> false
let uu___is_BXor: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____1331 -> false
let uu___is_BShiftL: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____1335 -> false
let uu___is_BShiftR: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____1339 -> false
let uu___is_BNot: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____1343 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____1347 -> false
let uu___is_Neq: op -> Prims.bool =
  fun projectee  -> match projectee with | Neq  -> true | uu____1351 -> false
let uu___is_Lt: op -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____1355 -> false
let uu___is_Lte: op -> Prims.bool =
  fun projectee  -> match projectee with | Lte  -> true | uu____1359 -> false
let uu___is_Gt: op -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____1363 -> false
let uu___is_Gte: op -> Prims.bool =
  fun projectee  -> match projectee with | Gte  -> true | uu____1367 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____1371 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____1375 -> false
let uu___is_Xor: op -> Prims.bool =
  fun projectee  -> match projectee with | Xor  -> true | uu____1379 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____1383 -> false
let uu___is_PUnit: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____1387 -> false
let uu___is_PBool: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____1392 -> false
let __proj__PBool__item___0: pattern -> Prims.bool =
  fun projectee  -> match projectee with | PBool _0 -> _0
let uu___is_PVar: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____1404 -> false
let __proj__PVar__item___0: pattern -> binder =
  fun projectee  -> match projectee with | PVar _0 -> _0
let uu___is_PCons: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____1419 -> false
let __proj__PCons__item___0: pattern -> (Prims.string* pattern Prims.list) =
  fun projectee  -> match projectee with | PCons _0 -> _0
let uu___is_PTuple: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____1441 -> false
let __proj__PTuple__item___0: pattern -> pattern Prims.list =
  fun projectee  -> match projectee with | PTuple _0 -> _0
let uu___is_PRecord: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____1459 -> false
let __proj__PRecord__item___0: pattern -> (Prims.string* pattern) Prims.list
  = fun projectee  -> match projectee with | PRecord _0 -> _0
let uu___is_UInt8: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____1479 -> false
let uu___is_UInt16: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____1483 -> false
let uu___is_UInt32: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____1487 -> false
let uu___is_UInt64: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____1491 -> false
let uu___is_Int8: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____1495 -> false
let uu___is_Int16: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____1499 -> false
let uu___is_Int32: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____1503 -> false
let uu___is_Int64: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____1507 -> false
let uu___is_Bool: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____1511 -> false
let uu___is_Int: width -> Prims.bool =
  fun projectee  -> match projectee with | Int  -> true | uu____1515 -> false
let uu___is_UInt: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt  -> true | uu____1519 -> false
let uu___is_TInt: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____1536 -> false
let __proj__TInt__item___0: typ -> width =
  fun projectee  -> match projectee with | TInt _0 -> _0
let uu___is_TBuf: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____1548 -> false
let __proj__TBuf__item___0: typ -> typ =
  fun projectee  -> match projectee with | TBuf _0 -> _0
let uu___is_TUnit: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____1559 -> false
let uu___is_TQualified: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____1567 -> false
let __proj__TQualified__item___0:
  typ -> (Prims.string Prims.list* Prims.string) =
  fun projectee  -> match projectee with | TQualified _0 -> _0
let uu___is_TBool: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____1587 -> false
let uu___is_TAny: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____1591 -> false
let uu___is_TArrow: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____1598 -> false
let __proj__TArrow__item___0: typ -> (typ* typ) =
  fun projectee  -> match projectee with | TArrow _0 -> _0
let uu___is_TZ: typ -> Prims.bool =
  fun projectee  -> match projectee with | TZ  -> true | uu____1615 -> false
let uu___is_TBound: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____1620 -> false
let __proj__TBound__item___0: typ -> Prims.int =
  fun projectee  -> match projectee with | TBound _0 -> _0
let uu___is_TApp: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____1638 -> false
let __proj__TApp__item___0:
  typ -> ((Prims.string Prims.list* Prims.string)* typ Prims.list) =
  fun projectee  -> match projectee with | TApp _0 -> _0
let uu___is_TTuple: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____1669 -> false
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
let fst3 uu____1722 = match uu____1722 with | (x,uu____1727,uu____1728) -> x
let snd3 uu____1742 = match uu____1742 with | (uu____1746,x,uu____1748) -> x
let thd3 uu____1762 = match uu____1762 with | (uu____1766,uu____1767,x) -> x
let mk_width: Prims.string -> width option =
  fun uu___118_1772  ->
    match uu___118_1772 with
    | "UInt8" -> Some UInt8
    | "UInt16" -> Some UInt16
    | "UInt32" -> Some UInt32
    | "UInt64" -> Some UInt64
    | "Int8" -> Some Int8
    | "Int16" -> Some Int16
    | "Int32" -> Some Int32
    | "Int64" -> Some Int64
    | uu____1774 -> None
let mk_bool_op: Prims.string -> op option =
  fun uu___119_1778  ->
    match uu___119_1778 with
    | "op_Negation" -> Some Not
    | "op_AmpAmp" -> Some And
    | "op_BarBar" -> Some Or
    | "op_Equality" -> Some Eq
    | "op_disEquality" -> Some Neq
    | uu____1780 -> None
let is_bool_op: Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> None
let mk_op: Prims.string -> op option =
  fun uu___120_1788  ->
    match uu___120_1788 with
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
    | uu____1790 -> None
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
        let uu___125_1862 = env in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___125_1862.names_t);
          module_name = (uu___125_1862.module_name)
        }
let extend_t: env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___126_1869 = env in
      {
        names = (uu___126_1869.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___126_1869.module_name)
      }
let find_name: env -> Prims.string -> name =
  fun env  ->
    fun x  ->
      let uu____1876 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names in
      match uu____1876 with
      | Some name -> name
      | None  -> failwith "internal error: name not found"
let is_mutable: env -> Prims.string -> Prims.bool =
  fun env  -> fun x  -> let uu____1887 = find_name env x in uu____1887.mut
let find: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____1902 ->
          let uu____1903 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____1903
let find_t: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____1918 ->
          let uu____1919 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____1919
let add_binders env binders =
  FStar_List.fold_left
    (fun env1  ->
       fun uu____1954  ->
         match uu____1954 with
         | ((name,uu____1960),uu____1961) -> extend env1 name false) env
    binders
let rec translate: FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____2052  ->
    match uu____2052 with
    | FStar_Extraction_ML_Syntax.MLLib modules1 ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____2085 = m in
               match uu____2085 with
               | ((prefix1,final),uu____2097,uu____2098) ->
                   FStar_String.concat "."
                     (FStar_List.append prefix1 [final]) in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____2117 = translate_module m in Some uu____2117)
             with
             | e ->
                 ((let uu____2125 = FStar_Util.print_exn e in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____2125);
                  None)) modules1
and translate_module:
  ((Prims.string Prims.list* Prims.string)*
    (FStar_Extraction_ML_Syntax.mlsig* FStar_Extraction_ML_Syntax.mlmodule)
    option* FStar_Extraction_ML_Syntax.mllib) -> file
  =
  fun uu____2126  ->
    match uu____2126 with
    | (module_name,modul,uu____2138) ->
        let module_name1 =
          FStar_List.append (fst module_name) [snd module_name] in
        let program =
          match modul with
          | Some (_signature,decls) ->
              FStar_List.filter_map (translate_decl (empty module_name1))
                decls
          | uu____2162 ->
              failwith "Unexpected standalone interface or nested modules" in
        ((FStar_String.concat "_" module_name1), program)
and translate_flags:
  FStar_Extraction_ML_Syntax.c_flag Prims.list -> flag Prims.list =
  fun flags  ->
    FStar_List.choose
      (fun uu___121_2171  ->
         match uu___121_2171 with
         | FStar_Extraction_ML_Syntax.Private  -> Some Private
         | FStar_Extraction_ML_Syntax.NoExtract  -> Some NoExtract
         | FStar_Extraction_ML_Syntax.Attribute "c_inline" -> Some CInline
         | FStar_Extraction_ML_Syntax.Attribute "substitute" ->
             Some Substitute
         | FStar_Extraction_ML_Syntax.Attribute a ->
             (FStar_Util.print1_warning "Warning: unrecognized attribute %s"
                a;
              None)
         | uu____2175 -> None) flags
and translate_decl:
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl option =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____2182);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some
                            (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2185;
                          FStar_Extraction_ML_Syntax.mllb_def =
                            {
                              FStar_Extraction_ML_Syntax.expr =
                                FStar_Extraction_ML_Syntax.MLE_Fun
                                (args,body);
                              FStar_Extraction_ML_Syntax.mlty = uu____2188;
                              FStar_Extraction_ML_Syntax.loc = uu____2189;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____2190;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___122_2202  ->
                 match uu___122_2202 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____2203 -> false) flags in
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun uu____2214  ->
                   match uu____2214 with
                   | (name1,uu____2218) -> extend_t env2 name1) env1 tvars in
          let rec find_return_type uu___123_2222 =
            match uu___123_2222 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2223,uu____2224,t)
                -> find_return_type t
            | t -> t in
          let t =
            let uu____2228 = find_return_type t0 in
            translate_type env2 uu____2228 in
          let binders = translate_binders env2 args in
          let env3 = add_binders env2 args in
          let name1 = ((env3.module_name), name) in
          let flags1 = translate_flags flags in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
               let uu____2243 =
                 let uu____2244 =
                   let uu____2252 = translate_type env3 t0 in
                   (None, name1, uu____2252) in
                 DExternal uu____2244 in
               Some uu____2243
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
                 ((let uu____2280 = FStar_Util.print_exn e in
                   FStar_Util.print2 "Warning: writing a stub for %s (%s)\n"
                     (snd name1) uu____2280);
                  Some
                    (DFunction
                       (None, flags1, (FStar_List.length tvars), t, name1,
                         binders, EAbort))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____2293);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some
                            (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2296;
                          FStar_Extraction_ML_Syntax.mllb_def =
                            {
                              FStar_Extraction_ML_Syntax.expr =
                                FStar_Extraction_ML_Syntax.MLE_Coerce
                                ({
                                   FStar_Extraction_ML_Syntax.expr =
                                     FStar_Extraction_ML_Syntax.MLE_Fun
                                     (args,body);
                                   FStar_Extraction_ML_Syntax.mlty =
                                     uu____2299;
                                   FStar_Extraction_ML_Syntax.loc =
                                     uu____2300;_},uu____2301,uu____2302);
                              FStar_Extraction_ML_Syntax.mlty = uu____2303;
                              FStar_Extraction_ML_Syntax.loc = uu____2304;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____2305;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___122_2317  ->
                 match uu___122_2317 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____2318 -> false) flags in
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun uu____2329  ->
                   match uu____2329 with
                   | (name1,uu____2333) -> extend_t env2 name1) env1 tvars in
          let rec find_return_type uu___123_2337 =
            match uu___123_2337 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2338,uu____2339,t)
                -> find_return_type t
            | t -> t in
          let t =
            let uu____2343 = find_return_type t0 in
            translate_type env2 uu____2343 in
          let binders = translate_binders env2 args in
          let env3 = add_binders env2 args in
          let name1 = ((env3.module_name), name) in
          let flags1 = translate_flags flags in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
               let uu____2358 =
                 let uu____2359 =
                   let uu____2367 = translate_type env3 t0 in
                   (None, name1, uu____2367) in
                 DExternal uu____2359 in
               Some uu____2358
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
                 ((let uu____2395 = FStar_Util.print_exn e in
                   FStar_Util.print2 "Warning: writing a stub for %s (%s)\n"
                     (snd name1) uu____2395);
                  Some
                    (DFunction
                       (None, flags1, (FStar_List.length tvars), t, name1,
                         binders, EAbort))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____2408);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some ([],t);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2410;
                          FStar_Extraction_ML_Syntax.mllb_def = expr;
                          FStar_Extraction_ML_Syntax.print_typ = uu____2412;_}::[])
          ->
          let flags1 = translate_flags flags in
          let t1 = translate_type env t in
          let name1 = ((env.module_name), name) in
          (try
             let expr1 = translate_expr env expr in
             Some (DGlobal (flags1, name1, t1, expr1))
           with
           | e ->
               ((let uu____2443 = FStar_Util.print_exn e in
                 FStar_Util.print2
                   "Warning: not translating definition for %s (%s)\n"
                   (snd name1) uu____2443);
                Some (DGlobal (flags1, name1, t1, EAny))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (uu____2449,uu____2450,{
                                   FStar_Extraction_ML_Syntax.mllb_name =
                                     (name,uu____2452);
                                   FStar_Extraction_ML_Syntax.mllb_tysc = ts;
                                   FStar_Extraction_ML_Syntax.mllb_add_unit =
                                     uu____2454;
                                   FStar_Extraction_ML_Syntax.mllb_def =
                                     uu____2455;
                                   FStar_Extraction_ML_Syntax.print_typ =
                                     uu____2456;_}::uu____2457)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           (match ts with
            | Some (idents,t) ->
                let uu____2467 =
                  let uu____2468 = FStar_List.map FStar_Pervasives.fst idents in
                  FStar_String.concat ", " uu____2468 in
                let uu____2472 =
                  FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                  uu____2467 uu____2472
            | None  -> ());
           None)
      | FStar_Extraction_ML_Syntax.MLM_Let uu____2474 ->
          failwith "impossible"
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____2476 -> None
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((assumed,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_Abbrev t))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____2512  ->
                   match uu____2512 with
                   | (name2,uu____2516) -> extend_t env1 name2) env args in
          if assumed
          then None
          else
            (let uu____2519 =
               let uu____2520 =
                 let uu____2527 = translate_type env1 t in
                 (name1, (FStar_List.length args), uu____2527) in
               DTypeAlias uu____2520 in
             Some uu____2519)
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2533,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_Record fields))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____2571  ->
                   match uu____2571 with
                   | (name2,uu____2575) -> extend_t env1 name2) env args in
          let uu____2576 =
            let uu____2577 =
              let uu____2589 =
                FStar_List.map
                  (fun uu____2605  ->
                     match uu____2605 with
                     | (f,t) ->
                         let uu____2614 =
                           let uu____2617 = translate_type env1 t in
                           (uu____2617, false) in
                         (f, uu____2614)) fields in
              (name1, (FStar_List.length args), uu____2589) in
            DTypeFlat uu____2577 in
          Some uu____2576
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2630,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_DType branches))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____2671  ->
                   match uu____2671 with
                   | (name2,uu____2675) -> extend_t env1 name2) env args in
          let uu____2676 =
            let uu____2677 =
              let uu____2692 =
                FStar_List.map
                  (fun uu____2717  ->
                     match uu____2717 with
                     | (cons1,ts) ->
                         let uu____2738 =
                           FStar_List.map
                             (fun uu____2754  ->
                                match uu____2754 with
                                | (name2,t) ->
                                    let uu____2763 =
                                      let uu____2766 = translate_type env1 t in
                                      (uu____2766, false) in
                                    (name2, uu____2763)) ts in
                         (cons1, uu____2738)) branches in
              (name1, (FStar_List.length args), uu____2692) in
            DTypeVariant uu____2677 in
          Some uu____2676
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2787,name,_mangled_name,uu____2790,uu____2791)::uu____2792)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           None)
      | FStar_Extraction_ML_Syntax.MLM_Ty [] ->
          (FStar_Util.print_string
             "Impossible!! Empty block of mutually recursive type declarations";
           None)
      | FStar_Extraction_ML_Syntax.MLM_Top uu____2814 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____2816 ->
          failwith "todo: translate_decl [MLM_Exn]"
and translate_type: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var (name,uu____2826) ->
          let uu____2827 = find_t env name in TBound uu____2827
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____2829,t2) ->
          let uu____2831 =
            let uu____2834 = translate_type env t1 in
            let uu____2835 = translate_type env t2 in
            (uu____2834, uu____2835) in
          TArrow uu____2831
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____2838 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2838 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____2841 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2841 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____2848 = FStar_Util.must (mk_width m) in TInt uu____2848
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____2855 = FStar_Util.must (mk_width m) in TInt uu____2855
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____2859 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2859 = "FStar.Buffer.buffer" ->
          let uu____2860 = translate_type env arg in TBuf uu____2860
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____2861::[],p) when
          let uu____2864 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2864 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____2886 = FStar_List.map (translate_type env) args in
          TTuple uu____2886
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____2895 =
              let uu____2902 = FStar_List.map (translate_type env) args in
              (lid, uu____2902) in
            TApp uu____2895
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____2908 = FStar_List.map (translate_type env) ts in
          TTuple uu____2908
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
    fun uu____2918  ->
      match uu____2918 with
      | ((name,uu____2922),typ) ->
          let uu____2926 = translate_type env typ in
          { name; typ = uu____2926; mut = false }
and translate_expr: env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____2931) ->
          let uu____2932 = find env name in EBound uu____2932
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____2936 =
            let uu____2939 = FStar_Util.must (mk_op op) in
            let uu____2940 = FStar_Util.must (mk_width m) in
            (uu____2939, uu____2940) in
          EOp uu____2936
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____2943 =
            let uu____2946 = FStar_Util.must (mk_bool_op op) in
            (uu____2946, Bool) in
          EOp uu____2943
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags,{
                           FStar_Extraction_ML_Syntax.mllb_name =
                             (name,uu____2951);
                           FStar_Extraction_ML_Syntax.mllb_tysc = Some
                             ([],typ);
                           FStar_Extraction_ML_Syntax.mllb_add_unit =
                             add_unit;
                           FStar_Extraction_ML_Syntax.mllb_def = body;
                           FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let is_mut =
            FStar_Util.for_some
              (fun uu___124_2968  ->
                 match uu___124_2968 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____2969 -> false) flags in
          let uu____2970 =
            if is_mut
            then
              let uu____2975 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____2979 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____2979 = "FStar.ST.stackref" -> t
                | uu____2980 ->
                    let uu____2981 =
                      let uu____2982 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____2982 in
                    failwith uu____2981 in
              let uu____2984 =
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
                      (uu____2985,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____2987;
                    FStar_Extraction_ML_Syntax.loc = uu____2988;_} -> body1
                | uu____2990 ->
                    failwith "unexpected: bad desugaring of Mutable" in
              (uu____2975, uu____2984)
            else (typ, body) in
          (match uu____2970 with
           | (typ1,body1) ->
               let binder =
                 let uu____2995 = translate_type env typ1 in
                 { name; typ = uu____2995; mut = is_mut } in
               let body2 = translate_expr env body1 in
               let env1 = extend env name is_mut in
               let continuation1 = translate_expr env1 continuation in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____3011 =
            let uu____3017 = translate_expr env expr in
            let uu____3018 = translate_branches env branches in
            (uu____3017, uu____3018) in
          EMatch uu____3011
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3026;
             FStar_Extraction_ML_Syntax.loc = uu____3027;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____3029);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3030;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3031;_}::[])
          when
          (let uu____3035 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____3035 = "FStar.ST.op_Bang") && (is_mutable env v1)
          -> let uu____3036 = find env v1 in EBound uu____3036
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3038;
             FStar_Extraction_ML_Syntax.loc = uu____3039;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____3041);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3042;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3043;_}::e1::[])
          when
          (let uu____3048 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____3048 = "FStar.ST.op_Colon_Equals") && (is_mutable env v1)
          ->
          let uu____3049 =
            let uu____3052 =
              let uu____3053 = find env v1 in EBound uu____3053 in
            let uu____3054 = translate_expr env e1 in
            (uu____3052, uu____3054) in
          EAssign uu____3049
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3056;
             FStar_Extraction_ML_Syntax.loc = uu____3057;_},e1::e2::[])
          when
          (let uu____3063 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____3063 = "FStar.Buffer.index") ||
            (let uu____3065 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____3065 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____3066 =
            let uu____3069 = translate_expr env e1 in
            let uu____3070 = translate_expr env e2 in
            (uu____3069, uu____3070) in
          EBufRead uu____3066
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3072;
             FStar_Extraction_ML_Syntax.loc = uu____3073;_},e1::e2::[])
          when
          let uu____3077 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3077 = "FStar.Buffer.create" ->
          let uu____3078 =
            let uu____3082 = translate_expr env e1 in
            let uu____3083 = translate_expr env e2 in
            (Stack, uu____3082, uu____3083) in
          EBufCreate uu____3078
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3085;
             FStar_Extraction_ML_Syntax.loc = uu____3086;_},_e0::e1::e2::[])
          when
          let uu____3091 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3091 = "FStar.Buffer.rcreate" ->
          let uu____3092 =
            let uu____3096 = translate_expr env e1 in
            let uu____3097 = translate_expr env e2 in
            (Eternal, uu____3096, uu____3097) in
          EBufCreate uu____3092
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3099;
             FStar_Extraction_ML_Syntax.loc = uu____3100;_},e2::[])
          when
          let uu____3103 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3103 = "FStar.Buffer.createL" ->
          let rec list_elements1 acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements1 (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____3127 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!" in
          let list_elements2 = list_elements1 [] in
          let uu____3133 =
            let uu____3137 =
              let uu____3139 = list_elements2 e2 in
              FStar_List.map (translate_expr env) uu____3139 in
            (Stack, uu____3137) in
          EBufCreateL uu____3133
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3143;
             FStar_Extraction_ML_Syntax.loc = uu____3144;_},e1::e2::_e3::[])
          when
          let uu____3149 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3149 = "FStar.Buffer.sub" ->
          let uu____3150 =
            let uu____3153 = translate_expr env e1 in
            let uu____3154 = translate_expr env e2 in
            (uu____3153, uu____3154) in
          EBufSub uu____3150
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3156;
             FStar_Extraction_ML_Syntax.loc = uu____3157;_},e1::e2::[])
          when
          let uu____3161 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3161 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3163;
             FStar_Extraction_ML_Syntax.loc = uu____3164;_},e1::e2::[])
          when
          let uu____3168 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3168 = "FStar.Buffer.offset" ->
          let uu____3169 =
            let uu____3172 = translate_expr env e1 in
            let uu____3173 = translate_expr env e2 in
            (uu____3172, uu____3173) in
          EBufSub uu____3169
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3175;
             FStar_Extraction_ML_Syntax.loc = uu____3176;_},e1::e2::e3::[])
          when
          (let uu____3183 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____3183 = "FStar.Buffer.upd") ||
            (let uu____3185 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____3185 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____3186 =
            let uu____3190 = translate_expr env e1 in
            let uu____3191 = translate_expr env e2 in
            let uu____3192 = translate_expr env e3 in
            (uu____3190, uu____3191, uu____3192) in
          EBufWrite uu____3186
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3194;
             FStar_Extraction_ML_Syntax.loc = uu____3195;_},uu____3196::[])
          when
          let uu____3198 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3198 = "FStar.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3200;
             FStar_Extraction_ML_Syntax.loc = uu____3201;_},uu____3202::[])
          when
          let uu____3204 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3204 = "FStar.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3206;
             FStar_Extraction_ML_Syntax.loc = uu____3207;_},e1::e2::e3::e4::e5::[])
          when
          let uu____3214 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3214 = "FStar.Buffer.blit" ->
          let uu____3215 =
            let uu____3221 = translate_expr env e1 in
            let uu____3222 = translate_expr env e2 in
            let uu____3223 = translate_expr env e3 in
            let uu____3224 = translate_expr env e4 in
            let uu____3225 = translate_expr env e5 in
            (uu____3221, uu____3222, uu____3223, uu____3224, uu____3225) in
          EBufBlit uu____3215
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3227;
             FStar_Extraction_ML_Syntax.loc = uu____3228;_},e1::e2::e3::[])
          when
          let uu____3233 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3233 = "FStar.Buffer.fill" ->
          let uu____3234 =
            let uu____3238 = translate_expr env e1 in
            let uu____3239 = translate_expr env e2 in
            let uu____3240 = translate_expr env e3 in
            (uu____3238, uu____3239, uu____3240) in
          EBufFill uu____3234
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3242;
             FStar_Extraction_ML_Syntax.loc = uu____3243;_},uu____3244::[])
          when
          let uu____3246 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3246 = "FStar.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3248;
             FStar_Extraction_ML_Syntax.loc = uu____3249;_},e1::[])
          when
          let uu____3252 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3252 = "Obj.repr" ->
          let uu____3253 =
            let uu____3256 = translate_expr env e1 in (uu____3256, TAny) in
          ECast uu____3253
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____3259;
             FStar_Extraction_ML_Syntax.loc = uu____3260;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____3265 = FStar_Util.must (mk_width m) in
          let uu____3266 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____3265 uu____3266 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____3268;
             FStar_Extraction_ML_Syntax.loc = uu____3269;_},args)
          when is_bool_op op ->
          let uu____3274 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____3274 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____3276;
             FStar_Extraction_ML_Syntax.loc = uu____3277;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,None ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3279;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3280;_}::[])
          when is_machine_int m ->
          let uu____3288 =
            let uu____3291 = FStar_Util.must (mk_width m) in (uu____3291, c) in
          EConstant uu____3288
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____3293;
             FStar_Extraction_ML_Syntax.loc = uu____3294;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,None ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3296;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3297;_}::[])
          when is_machine_int m ->
          let uu____3305 =
            let uu____3308 = FStar_Util.must (mk_width m) in (uu____3308, c) in
          EConstant uu____3305
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____3309;
             FStar_Extraction_ML_Syntax.loc = uu____3310;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3312;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3313;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____3317 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____3319;
             FStar_Extraction_ML_Syntax.loc = uu____3320;_},arg::[])
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
            let uu____3325 =
              let uu____3328 = translate_expr env arg in
              (uu____3328, (TInt UInt64)) in
            ECast uu____3325
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____3330 =
                 let uu____3333 = translate_expr env arg in
                 (uu____3333, (TInt UInt32)) in
               ECast uu____3330)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____3335 =
                   let uu____3338 = translate_expr env arg in
                   (uu____3338, (TInt UInt16)) in
                 ECast uu____3335)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____3340 =
                     let uu____3343 = translate_expr env arg in
                     (uu____3343, (TInt UInt8)) in
                   ECast uu____3340)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____3345 =
                       let uu____3348 = translate_expr env arg in
                       (uu____3348, (TInt Int64)) in
                     ECast uu____3345)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____3350 =
                         let uu____3353 = translate_expr env arg in
                         (uu____3353, (TInt Int32)) in
                       ECast uu____3350)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____3355 =
                           let uu____3358 = translate_expr env arg in
                           (uu____3358, (TInt Int16)) in
                         ECast uu____3355)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____3360 =
                             let uu____3363 = translate_expr env arg in
                             (uu____3363, (TInt Int8)) in
                           ECast uu____3360)
                        else
                          (let uu____3365 =
                             let uu____3369 =
                               let uu____3371 = translate_expr env arg in
                               [uu____3371] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____3369) in
                           EApp uu____3365)
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name (path,function_name);
             FStar_Extraction_ML_Syntax.mlty = uu____3376;
             FStar_Extraction_ML_Syntax.loc = uu____3377;_},args)
          ->
          let uu____3383 =
            let uu____3387 = FStar_List.map (translate_expr env) args in
            ((EQualified (path, function_name)), uu____3387) in
          EApp uu____3383
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Var (name,uu____3392);
             FStar_Extraction_ML_Syntax.mlty = uu____3393;
             FStar_Extraction_ML_Syntax.loc = uu____3394;_},args)
          ->
          let uu____3398 =
            let uu____3402 =
              let uu____3403 = find env name in EBound uu____3403 in
            let uu____3404 = FStar_List.map (translate_expr env) args in
            (uu____3402, uu____3404) in
          EApp uu____3398
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____3410 =
            let uu____3413 = translate_expr env e1 in
            let uu____3414 = translate_type env t_to in
            (uu____3413, uu____3414) in
          ECast uu____3410
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____3415,fields) ->
          let uu____3425 =
            let uu____3431 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____3432 =
              FStar_List.map
                (fun uu____3444  ->
                   match uu____3444 with
                   | (field,expr) ->
                       let uu____3451 = translate_expr env expr in
                       (field, uu____3451)) fields in
            (uu____3431, uu____3432) in
          EFlat uu____3425
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____3457 =
            let uu____3461 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____3462 = translate_expr env e1 in
            (uu____3461, uu____3462, (snd path)) in
          EField uu____3457
      | FStar_Extraction_ML_Syntax.MLE_Let uu____3464 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____3472) ->
          let uu____3475 =
            let uu____3476 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1 in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____3476 in
          failwith uu____3475
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____3480 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____3480
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____3484 = FStar_List.map (translate_expr env) es in
          ETuple uu____3484
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____3486,cons1),es) ->
          let uu____3496 =
            let uu____3501 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____3502 = FStar_List.map (translate_expr env) es in
            (uu____3501, cons1, uu____3502) in
          ECons uu____3496
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args in
          let env1 = add_binders env args in
          let uu____3516 =
            let uu____3520 = translate_expr env1 body in
            (binders, uu____3520) in
          EFun uu____3516
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____3527 =
            let uu____3531 = translate_expr env e1 in
            let uu____3532 = translate_expr env e2 in
            let uu____3533 =
              match e3 with
              | None  -> EUnit
              | Some e31 -> translate_expr env e31 in
            (uu____3531, uu____3532, uu____3533) in
          EIfThenElse uu____3527
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____3535 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____3539 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____3547 ->
          failwith "todo: translate_expr [MLE_Coerce]"
and assert_lid: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____3560 =
              let uu____3567 = FStar_List.map (translate_type env) ts in
              (lid, uu____3567) in
            TApp uu____3560
          else TQualified lid
      | uu____3571 -> failwith "invalid argument: assert_lid"
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
    fun uu____3586  ->
      match uu____3586 with
      | (pat,guard,expr) ->
          if guard = None
          then
            let uu____3601 = translate_pat env pat in
            (match uu____3601 with
             | (env1,pat1) ->
                 let uu____3608 = translate_expr env1 expr in
                 (pat1, uu____3608))
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
      | FStar_Extraction_ML_Syntax.MLP_Var (name,uu____3618) ->
          let env1 = extend env name false in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_" false in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____3621,cons1),ps) ->
          let uu____3631 =
            FStar_List.fold_left
              (fun uu____3645  ->
                 fun p1  ->
                   match uu____3645 with
                   | (env1,acc) ->
                       let uu____3657 = translate_pat env1 p1 in
                       (match uu____3657 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____3631 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____3674,ps) ->
          let uu____3684 =
            FStar_List.fold_left
              (fun uu____3706  ->
                 fun uu____3707  ->
                   match (uu____3706, uu____3707) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____3744 = translate_pat env1 p1 in
                       (match uu____3744 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps in
          (match uu____3684 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____3778 =
            FStar_List.fold_left
              (fun uu____3792  ->
                 fun p1  ->
                   match uu____3792 with
                   | (env1,acc) ->
                       let uu____3804 = translate_pat env1 p1 in
                       (match uu____3804 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____3778 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____3820 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____3823 ->
          failwith "todo: translate_pat [MLP_Branch]"
and translate_constant: FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_Int (s,Some uu____3830) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____3838 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____3839 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____3840 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____3841 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (uu____3843,None ) ->
        failwith "todo: translate_expr [MLC_Int]"
and mk_op_app:
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr
  =
  fun env  ->
    fun w  ->
      fun op  ->
        fun args  ->
          let uu____3854 =
            let uu____3858 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____3858) in
          EApp uu____3854