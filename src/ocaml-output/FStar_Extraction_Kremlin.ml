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
    match projectee with | DGlobal _0 -> true | uu____349 -> false
let __proj__DGlobal__item___0:
  decl ->
    (flag Prims.list* (Prims.string Prims.list* Prims.string)* typ* expr)
  = fun projectee  -> match projectee with | DGlobal _0 -> _0
let uu___is_DFunction: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____400 -> false
let __proj__DFunction__item___0:
  decl ->
    (cc option* flag Prims.list* Prims.int* typ* (Prims.string Prims.list*
      Prims.string)* binder Prims.list* expr)
  = fun projectee  -> match projectee with | DFunction _0 -> _0
let uu___is_DTypeAlias: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____459 -> false
let __proj__DTypeAlias__item___0:
  decl -> ((Prims.string Prims.list* Prims.string)* Prims.int* typ) =
  fun projectee  -> match projectee with | DTypeAlias _0 -> _0
let uu___is_DTypeFlat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____502 -> false
let __proj__DTypeFlat__item___0:
  decl ->
    ((Prims.string Prims.list* Prims.string)* Prims.int* (Prims.string* (typ*
      Prims.bool)) Prims.list)
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0
let uu___is_DExternal: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____556 -> false
let __proj__DExternal__item___0:
  decl -> (cc option* (Prims.string Prims.list* Prims.string)* typ) =
  fun projectee  -> match projectee with | DExternal _0 -> _0
let uu___is_DTypeVariant: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____605 -> false
let __proj__DTypeVariant__item___0:
  decl ->
    ((Prims.string Prims.list* Prims.string)* Prims.int* (Prims.string*
      (Prims.string* (typ* Prims.bool)) Prims.list) Prims.list)
  = fun projectee  -> match projectee with | DTypeVariant _0 -> _0
let uu___is_StdCall: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____660 -> false
let uu___is_CDecl: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____665 -> false
let uu___is_FastCall: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____670 -> false
let uu___is_Private: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____675 -> false
let uu___is_NoExtract: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____680 -> false
let uu___is_CInline: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____685 -> false
let uu___is_Substitute: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____690 -> false
let uu___is_Eternal: lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____695 -> false
let uu___is_Stack: lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____700 -> false
let uu___is_EBound: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____706 -> false
let __proj__EBound__item___0: expr -> Prims.int =
  fun projectee  -> match projectee with | EBound _0 -> _0
let uu___is_EQualified: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____723 -> false
let __proj__EQualified__item___0:
  expr -> (Prims.string Prims.list* Prims.string) =
  fun projectee  -> match projectee with | EQualified _0 -> _0
let uu___is_EConstant: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____748 -> false
let __proj__EConstant__item___0: expr -> (width* Prims.string) =
  fun projectee  -> match projectee with | EConstant _0 -> _0
let uu___is_EUnit: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____767 -> false
let uu___is_EApp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____776 -> false
let __proj__EApp__item___0: expr -> (expr* expr Prims.list) =
  fun projectee  -> match projectee with | EApp _0 -> _0
let uu___is_ELet: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____802 -> false
let __proj__ELet__item___0: expr -> (binder* expr* expr) =
  fun projectee  -> match projectee with | ELet _0 -> _0
let uu___is_EIfThenElse: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____828 -> false
let __proj__EIfThenElse__item___0: expr -> (expr* expr* expr) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0
let uu___is_ESequence: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____852 -> false
let __proj__ESequence__item___0: expr -> expr Prims.list =
  fun projectee  -> match projectee with | ESequence _0 -> _0
let uu___is_EAssign: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____871 -> false
let __proj__EAssign__item___0: expr -> (expr* expr) =
  fun projectee  -> match projectee with | EAssign _0 -> _0
let uu___is_EBufCreate: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____894 -> false
let __proj__EBufCreate__item___0: expr -> (lifetime* expr* expr) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0
let uu___is_EBufRead: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____919 -> false
let __proj__EBufRead__item___0: expr -> (expr* expr) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0
let uu___is_EBufWrite: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____942 -> false
let __proj__EBufWrite__item___0: expr -> (expr* expr* expr) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0
let uu___is_EBufSub: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____967 -> false
let __proj__EBufSub__item___0: expr -> (expr* expr) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0
let uu___is_EBufBlit: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____992 -> false
let __proj__EBufBlit__item___0: expr -> (expr* expr* expr* expr* expr) =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0
let uu___is_EMatch: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____1026 -> false
let __proj__EMatch__item___0: expr -> (expr* (pattern* expr) Prims.list) =
  fun projectee  -> match projectee with | EMatch _0 -> _0
let uu___is_EOp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1057 -> false
let __proj__EOp__item___0: expr -> (op* width) =
  fun projectee  -> match projectee with | EOp _0 -> _0
let uu___is_ECast: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1079 -> false
let __proj__ECast__item___0: expr -> (expr* typ) =
  fun projectee  -> match projectee with | ECast _0 -> _0
let uu___is_EPushFrame: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1098 -> false
let uu___is_EPopFrame: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1103 -> false
let uu___is_EBool: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1109 -> false
let __proj__EBool__item___0: expr -> Prims.bool =
  fun projectee  -> match projectee with | EBool _0 -> _0
let uu___is_EAny: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1122 -> false
let uu___is_EAbort: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1127 -> false
let uu___is_EReturn: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1133 -> false
let __proj__EReturn__item___0: expr -> expr =
  fun projectee  -> match projectee with | EReturn _0 -> _0
let uu___is_EFlat: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1152 -> false
let __proj__EFlat__item___0: expr -> (typ* (Prims.string* expr) Prims.list) =
  fun projectee  -> match projectee with | EFlat _0 -> _0
let uu___is_EField: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____1184 -> false
let __proj__EField__item___0: expr -> (typ* expr* Prims.string) =
  fun projectee  -> match projectee with | EField _0 -> _0
let uu___is_EWhile: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____1209 -> false
let __proj__EWhile__item___0: expr -> (expr* expr) =
  fun projectee  -> match projectee with | EWhile _0 -> _0
let uu___is_EBufCreateL: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____1232 -> false
let __proj__EBufCreateL__item___0: expr -> (lifetime* expr Prims.list) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0
let uu___is_ETuple: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____1256 -> false
let __proj__ETuple__item___0: expr -> expr Prims.list =
  fun projectee  -> match projectee with | ETuple _0 -> _0
let uu___is_ECons: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____1277 -> false
let __proj__ECons__item___0: expr -> (typ* Prims.string* expr Prims.list) =
  fun projectee  -> match projectee with | ECons _0 -> _0
let uu___is_EBufFill: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____1306 -> false
let __proj__EBufFill__item___0: expr -> (expr* expr* expr) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0
let uu___is_EString: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____1329 -> false
let __proj__EString__item___0: expr -> Prims.string =
  fun projectee  -> match projectee with | EString _0 -> _0
let uu___is_EFun: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____1346 -> false
let __proj__EFun__item___0: expr -> (binder Prims.list* expr) =
  fun projectee  -> match projectee with | EFun _0 -> _0
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____1368 -> false
let uu___is_AddW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____1373 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____1378 -> false
let uu___is_SubW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____1383 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____1388 -> false
let uu___is_DivW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____1393 -> false
let uu___is_Mult: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____1398 -> false
let uu___is_MultW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____1403 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____1408 -> false
let uu___is_BOr: op -> Prims.bool =
  fun projectee  -> match projectee with | BOr  -> true | uu____1413 -> false
let uu___is_BAnd: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____1418 -> false
let uu___is_BXor: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____1423 -> false
let uu___is_BShiftL: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____1428 -> false
let uu___is_BShiftR: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____1433 -> false
let uu___is_BNot: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____1438 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____1443 -> false
let uu___is_Neq: op -> Prims.bool =
  fun projectee  -> match projectee with | Neq  -> true | uu____1448 -> false
let uu___is_Lt: op -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____1453 -> false
let uu___is_Lte: op -> Prims.bool =
  fun projectee  -> match projectee with | Lte  -> true | uu____1458 -> false
let uu___is_Gt: op -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____1463 -> false
let uu___is_Gte: op -> Prims.bool =
  fun projectee  -> match projectee with | Gte  -> true | uu____1468 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____1473 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____1478 -> false
let uu___is_Xor: op -> Prims.bool =
  fun projectee  -> match projectee with | Xor  -> true | uu____1483 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____1488 -> false
let uu___is_PUnit: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____1493 -> false
let uu___is_PBool: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____1499 -> false
let __proj__PBool__item___0: pattern -> Prims.bool =
  fun projectee  -> match projectee with | PBool _0 -> _0
let uu___is_PVar: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____1513 -> false
let __proj__PVar__item___0: pattern -> binder =
  fun projectee  -> match projectee with | PVar _0 -> _0
let uu___is_PCons: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____1530 -> false
let __proj__PCons__item___0: pattern -> (Prims.string* pattern Prims.list) =
  fun projectee  -> match projectee with | PCons _0 -> _0
let uu___is_PTuple: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____1554 -> false
let __proj__PTuple__item___0: pattern -> pattern Prims.list =
  fun projectee  -> match projectee with | PTuple _0 -> _0
let uu___is_PRecord: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____1574 -> false
let __proj__PRecord__item___0: pattern -> (Prims.string* pattern) Prims.list
  = fun projectee  -> match projectee with | PRecord _0 -> _0
let uu___is_UInt8: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____1596 -> false
let uu___is_UInt16: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____1601 -> false
let uu___is_UInt32: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____1606 -> false
let uu___is_UInt64: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____1611 -> false
let uu___is_Int8: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____1616 -> false
let uu___is_Int16: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____1621 -> false
let uu___is_Int32: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____1626 -> false
let uu___is_Int64: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____1631 -> false
let uu___is_Bool: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____1636 -> false
let uu___is_Int: width -> Prims.bool =
  fun projectee  -> match projectee with | Int  -> true | uu____1641 -> false
let uu___is_UInt: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt  -> true | uu____1646 -> false
let uu___is_TInt: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____1667 -> false
let __proj__TInt__item___0: typ -> width =
  fun projectee  -> match projectee with | TInt _0 -> _0
let uu___is_TBuf: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____1681 -> false
let __proj__TBuf__item___0: typ -> typ =
  fun projectee  -> match projectee with | TBuf _0 -> _0
let uu___is_TUnit: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____1694 -> false
let uu___is_TQualified: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____1703 -> false
let __proj__TQualified__item___0:
  typ -> (Prims.string Prims.list* Prims.string) =
  fun projectee  -> match projectee with | TQualified _0 -> _0
let uu___is_TBool: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____1725 -> false
let uu___is_TAny: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____1730 -> false
let uu___is_TArrow: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____1738 -> false
let __proj__TArrow__item___0: typ -> (typ* typ) =
  fun projectee  -> match projectee with | TArrow _0 -> _0
let uu___is_TZ: typ -> Prims.bool =
  fun projectee  -> match projectee with | TZ  -> true | uu____1757 -> false
let uu___is_TBound: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____1763 -> false
let __proj__TBound__item___0: typ -> Prims.int =
  fun projectee  -> match projectee with | TBound _0 -> _0
let uu___is_TApp: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____1783 -> false
let __proj__TApp__item___0:
  typ -> ((Prims.string Prims.list* Prims.string)* typ Prims.list) =
  fun projectee  -> match projectee with | TApp _0 -> _0
let uu___is_TTuple: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____1816 -> false
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
let fst3 uu____1874 = match uu____1874 with | (x,uu____1879,uu____1880) -> x
let snd3 uu____1898 = match uu____1898 with | (uu____1902,x,uu____1904) -> x
let thd3 uu____1922 = match uu____1922 with | (uu____1926,uu____1927,x) -> x
let mk_width: Prims.string -> width option =
  fun uu___119_1933  ->
    match uu___119_1933 with
    | "UInt8" -> Some UInt8
    | "UInt16" -> Some UInt16
    | "UInt32" -> Some UInt32
    | "UInt64" -> Some UInt64
    | "Int8" -> Some Int8
    | "Int16" -> Some Int16
    | "Int32" -> Some Int32
    | "Int64" -> Some Int64
    | uu____1935 -> None
let mk_bool_op: Prims.string -> op option =
  fun uu___120_1940  ->
    match uu___120_1940 with
    | "op_Negation" -> Some Not
    | "op_AmpAmp" -> Some And
    | "op_BarBar" -> Some Or
    | "op_Equality" -> Some Eq
    | "op_disEquality" -> Some Neq
    | uu____1942 -> None
let is_bool_op: Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> None
let mk_op: Prims.string -> op option =
  fun uu___121_1952  ->
    match uu___121_1952 with
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
    | uu____1954 -> None
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
        let uu___126_2037 = env in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___126_2037.names_t);
          module_name = (uu___126_2037.module_name)
        }
let extend_t: env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___127_2046 = env in
      {
        names = (uu___127_2046.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___127_2046.module_name)
      }
let find_name: env -> Prims.string -> name =
  fun env  ->
    fun x  ->
      let uu____2055 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names in
      match uu____2055 with
      | Some name -> name
      | None  -> failwith "internal error: name not found"
let is_mutable: env -> Prims.string -> Prims.bool =
  fun env  -> fun x  -> let uu____2067 = find_name env x in uu____2067.mut
let find: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____2079 ->
          let uu____2080 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____2080
let find_t: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____2092 ->
          let uu____2093 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____2093
let add_binders env binders =
  FStar_List.fold_left
    (fun env1  ->
       fun uu____2127  ->
         match uu____2127 with
         | ((name,uu____2133),uu____2134) -> extend env1 name false) env
    binders
let rec translate: FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____2225  ->
    match uu____2225 with
    | FStar_Extraction_ML_Syntax.MLLib modules1 ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____2256 = m in
               match uu____2256 with
               | ((prefix1,final),uu____2268,uu____2269) ->
                   FStar_String.concat "."
                     (FStar_List.append prefix1 [final]) in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____2285 = translate_module m in Some uu____2285)
             with
             | e ->
                 ((let uu____2290 = FStar_Util.print_exn e in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____2290);
                  None)) modules1
and translate_module:
  ((Prims.string Prims.list* Prims.string)*
    (FStar_Extraction_ML_Syntax.mlsig* FStar_Extraction_ML_Syntax.mlmodule)
    option* FStar_Extraction_ML_Syntax.mllib) -> file
  =
  fun uu____2291  ->
    match uu____2291 with
    | (module_name,modul,uu____2303) ->
        let module_name1 =
          FStar_List.append (fst module_name) [snd module_name] in
        let program =
          match modul with
          | Some (_signature,decls) ->
              FStar_List.filter_map (translate_decl (empty module_name1))
                decls
          | uu____2327 ->
              failwith "Unexpected standalone interface or nested modules" in
        ((FStar_String.concat "_" module_name1), program)
and translate_flags:
  FStar_Extraction_ML_Syntax.c_flag Prims.list -> flag Prims.list =
  fun flags  ->
    FStar_List.choose
      (fun uu___122_2335  ->
         match uu___122_2335 with
         | FStar_Extraction_ML_Syntax.Private  -> Some Private
         | FStar_Extraction_ML_Syntax.NoExtract  -> Some NoExtract
         | FStar_Extraction_ML_Syntax.Attribute "c_inline" -> Some CInline
         | FStar_Extraction_ML_Syntax.Attribute "substitute" ->
             Some Substitute
         | FStar_Extraction_ML_Syntax.Attribute a ->
             (FStar_Util.print1_warning "Warning: unrecognized attribute %s"
                a;
              None)
         | uu____2339 -> None) flags
and translate_decl:
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl option =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____2347);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some
                            (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2350;
                          FStar_Extraction_ML_Syntax.mllb_def =
                            {
                              FStar_Extraction_ML_Syntax.expr =
                                FStar_Extraction_ML_Syntax.MLE_Fun
                                (args,body);
                              FStar_Extraction_ML_Syntax.mlty = uu____2353;
                              FStar_Extraction_ML_Syntax.loc = uu____2354;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____2355;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___123_2366  ->
                 match uu___123_2366 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____2367 -> false) flags in
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun uu____2374  ->
                   match uu____2374 with
                   | (name1,uu____2378) -> extend_t env2 name1) env1 tvars in
          let rec find_return_type uu___124_2382 =
            match uu___124_2382 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2383,uu____2384,t)
                -> find_return_type t
            | t -> t in
          let t =
            let uu____2388 = find_return_type t0 in
            translate_type env2 uu____2388 in
          let binders = translate_binders env2 args in
          let env3 = add_binders env2 args in
          let name1 = ((env3.module_name), name) in
          let flags1 = translate_flags flags in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
               let uu____2405 =
                 let uu____2406 =
                   let uu____2414 = translate_type env3 t0 in
                   (None, name1, uu____2414) in
                 DExternal uu____2406 in
               Some uu____2405
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
                 ((let uu____2439 = FStar_Util.print_exn e in
                   FStar_Util.print2 "Warning: writing a stub for %s (%s)\n"
                     (snd name1) uu____2439);
                  Some
                    (DFunction
                       (None, flags1, (FStar_List.length tvars), t, name1,
                         binders, EAbort))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____2454);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some
                            (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2457;
                          FStar_Extraction_ML_Syntax.mllb_def =
                            {
                              FStar_Extraction_ML_Syntax.expr =
                                FStar_Extraction_ML_Syntax.MLE_Coerce
                                ({
                                   FStar_Extraction_ML_Syntax.expr =
                                     FStar_Extraction_ML_Syntax.MLE_Fun
                                     (args,body);
                                   FStar_Extraction_ML_Syntax.mlty =
                                     uu____2460;
                                   FStar_Extraction_ML_Syntax.loc =
                                     uu____2461;_},uu____2462,uu____2463);
                              FStar_Extraction_ML_Syntax.mlty = uu____2464;
                              FStar_Extraction_ML_Syntax.loc = uu____2465;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____2466;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___123_2477  ->
                 match uu___123_2477 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____2478 -> false) flags in
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun uu____2485  ->
                   match uu____2485 with
                   | (name1,uu____2489) -> extend_t env2 name1) env1 tvars in
          let rec find_return_type uu___124_2493 =
            match uu___124_2493 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2494,uu____2495,t)
                -> find_return_type t
            | t -> t in
          let t =
            let uu____2499 = find_return_type t0 in
            translate_type env2 uu____2499 in
          let binders = translate_binders env2 args in
          let env3 = add_binders env2 args in
          let name1 = ((env3.module_name), name) in
          let flags1 = translate_flags flags in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
               let uu____2516 =
                 let uu____2517 =
                   let uu____2525 = translate_type env3 t0 in
                   (None, name1, uu____2525) in
                 DExternal uu____2517 in
               Some uu____2516
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
                 ((let uu____2550 = FStar_Util.print_exn e in
                   FStar_Util.print2 "Warning: writing a stub for %s (%s)\n"
                     (snd name1) uu____2550);
                  Some
                    (DFunction
                       (None, flags1, (FStar_List.length tvars), t, name1,
                         binders, EAbort))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____2565);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some ([],t);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2567;
                          FStar_Extraction_ML_Syntax.mllb_def = expr;
                          FStar_Extraction_ML_Syntax.print_typ = uu____2569;_}::[])
          ->
          let flags1 = translate_flags flags in
          let t1 = translate_type env t in
          let name1 = ((env.module_name), name) in
          (try
             let expr1 = translate_expr env expr in
             Some (DGlobal (flags1, name1, t1, expr1))
           with
           | e ->
               ((let uu____2595 = FStar_Util.print_exn e in
                 FStar_Util.print2
                   "Warning: not translating definition for %s (%s)\n"
                   (snd name1) uu____2595);
                Some (DGlobal (flags1, name1, t1, EAny))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (uu____2601,uu____2602,{
                                   FStar_Extraction_ML_Syntax.mllb_name =
                                     (name,uu____2604);
                                   FStar_Extraction_ML_Syntax.mllb_tysc = ts;
                                   FStar_Extraction_ML_Syntax.mllb_add_unit =
                                     uu____2606;
                                   FStar_Extraction_ML_Syntax.mllb_def =
                                     uu____2607;
                                   FStar_Extraction_ML_Syntax.print_typ =
                                     uu____2608;_}::uu____2609)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           (match ts with
            | Some (idents,t) ->
                let uu____2619 =
                  let uu____2620 = FStar_List.map FStar_Pervasives.fst idents in
                  FStar_String.concat ", " uu____2620 in
                let uu____2624 =
                  FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                  uu____2619 uu____2624
            | None  -> ());
           None)
      | FStar_Extraction_ML_Syntax.MLM_Let uu____2626 ->
          failwith "impossible"
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____2628 -> None
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((assumed,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_Abbrev t))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____2660  ->
                   match uu____2660 with
                   | (name2,uu____2664) -> extend_t env1 name2) env args in
          if assumed
          then None
          else
            (let uu____2667 =
               let uu____2668 =
                 let uu____2675 = translate_type env1 t in
                 (name1, (FStar_List.length args), uu____2675) in
               DTypeAlias uu____2668 in
             Some uu____2667)
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2683,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_Record fields))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____2717  ->
                   match uu____2717 with
                   | (name2,uu____2721) -> extend_t env1 name2) env args in
          let uu____2722 =
            let uu____2723 =
              let uu____2735 =
                FStar_List.map
                  (fun uu____2747  ->
                     match uu____2747 with
                     | (f,t) ->
                         let uu____2756 =
                           let uu____2759 = translate_type env1 t in
                           (uu____2759, false) in
                         (f, uu____2756)) fields in
              (name1, (FStar_List.length args), uu____2735) in
            DTypeFlat uu____2723 in
          Some uu____2722
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2774,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_DType branches))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____2811  ->
                   match uu____2811 with
                   | (name2,uu____2815) -> extend_t env1 name2) env args in
          let uu____2816 =
            let uu____2817 =
              let uu____2832 =
                FStar_List.map
                  (fun uu____2853  ->
                     match uu____2853 with
                     | (cons1,ts) ->
                         let uu____2874 =
                           FStar_List.map
                             (fun uu____2886  ->
                                match uu____2886 with
                                | (name2,t) ->
                                    let uu____2895 =
                                      let uu____2898 = translate_type env1 t in
                                      (uu____2898, false) in
                                    (name2, uu____2895)) ts in
                         (cons1, uu____2874)) branches in
              (name1, (FStar_List.length args), uu____2832) in
            DTypeVariant uu____2817 in
          Some uu____2816
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2921,name,_mangled_name,uu____2924,uu____2925)::uu____2926)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           None)
      | FStar_Extraction_ML_Syntax.MLM_Ty [] ->
          (FStar_Util.print_string
             "Impossible!! Empty block of mutually recursive type declarations";
           None)
      | FStar_Extraction_ML_Syntax.MLM_Top uu____2948 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____2950 ->
          failwith "todo: translate_decl [MLM_Exn]"
and translate_type: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var (name,uu____2960) ->
          let uu____2961 = find_t env name in TBound uu____2961
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____2963,t2) ->
          let uu____2965 =
            let uu____2968 = translate_type env t1 in
            let uu____2969 = translate_type env t2 in
            (uu____2968, uu____2969) in
          TArrow uu____2965
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____2972 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2972 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____2975 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2975 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____2982 = FStar_Util.must (mk_width m) in TInt uu____2982
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____2989 = FStar_Util.must (mk_width m) in TInt uu____2989
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____2993 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2993 = "FStar.Buffer.buffer" ->
          let uu____2994 = translate_type env arg in TBuf uu____2994
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____2995::[],p) when
          let uu____2998 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2998 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____3020 = FStar_List.map (translate_type env) args in
          TTuple uu____3020
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____3032 =
              let uu____3039 = FStar_List.map (translate_type env) args in
              (lid, uu____3039) in
            TApp uu____3032
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____3045 = FStar_List.map (translate_type env) ts in
          TTuple uu____3045
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
    fun uu____3055  ->
      match uu____3055 with
      | ((name,uu____3059),typ) ->
          let uu____3063 = translate_type env typ in
          { name; typ = uu____3063; mut = false }
and translate_expr: env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____3068) ->
          let uu____3069 = find env name in EBound uu____3069
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____3073 =
            let uu____3076 = FStar_Util.must (mk_op op) in
            let uu____3077 = FStar_Util.must (mk_width m) in
            (uu____3076, uu____3077) in
          EOp uu____3073
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____3080 =
            let uu____3083 = FStar_Util.must (mk_bool_op op) in
            (uu____3083, Bool) in
          EOp uu____3080
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags,{
                           FStar_Extraction_ML_Syntax.mllb_name =
                             (name,uu____3088);
                           FStar_Extraction_ML_Syntax.mllb_tysc = Some
                             ([],typ);
                           FStar_Extraction_ML_Syntax.mllb_add_unit =
                             add_unit;
                           FStar_Extraction_ML_Syntax.mllb_def = body;
                           FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let is_mut =
            FStar_Util.for_some
              (fun uu___125_3104  ->
                 match uu___125_3104 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____3105 -> false) flags in
          let uu____3106 =
            if is_mut
            then
              let uu____3111 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____3115 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____3115 = "FStar.ST.stackref" -> t
                | uu____3116 ->
                    let uu____3117 =
                      let uu____3118 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____3118 in
                    failwith uu____3117 in
              let uu____3120 =
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
                      (uu____3121,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____3123;
                    FStar_Extraction_ML_Syntax.loc = uu____3124;_} -> body1
                | uu____3126 ->
                    failwith "unexpected: bad desugaring of Mutable" in
              (uu____3111, uu____3120)
            else (typ, body) in
          (match uu____3106 with
           | (typ1,body1) ->
               let binder =
                 let uu____3131 = translate_type env typ1 in
                 { name; typ = uu____3131; mut = is_mut } in
               let body2 = translate_expr env body1 in
               let env1 = extend env name is_mut in
               let continuation1 = translate_expr env1 continuation in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____3147 =
            let uu____3153 = translate_expr env expr in
            let uu____3154 = translate_branches env branches in
            (uu____3153, uu____3154) in
          EMatch uu____3147
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3162;
             FStar_Extraction_ML_Syntax.loc = uu____3163;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____3165);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3166;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3167;_}::[])
          when
          (let uu____3169 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____3169 = "FStar.ST.op_Bang") && (is_mutable env v1)
          -> let uu____3170 = find env v1 in EBound uu____3170
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3172;
             FStar_Extraction_ML_Syntax.loc = uu____3173;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____3175);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3176;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3177;_}::e1::[])
          when
          (let uu____3180 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____3180 = "FStar.ST.op_Colon_Equals") && (is_mutable env v1)
          ->
          let uu____3181 =
            let uu____3184 =
              let uu____3185 = find env v1 in EBound uu____3185 in
            let uu____3186 = translate_expr env e1 in
            (uu____3184, uu____3186) in
          EAssign uu____3181
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3188;
             FStar_Extraction_ML_Syntax.loc = uu____3189;_},e1::e2::[])
          when
          (let uu____3193 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____3193 = "FStar.Buffer.index") ||
            (let uu____3194 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____3194 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____3195 =
            let uu____3198 = translate_expr env e1 in
            let uu____3199 = translate_expr env e2 in
            (uu____3198, uu____3199) in
          EBufRead uu____3195
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3201;
             FStar_Extraction_ML_Syntax.loc = uu____3202;_},e1::e2::[])
          when
          let uu____3206 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3206 = "FStar.Buffer.create" ->
          let uu____3207 =
            let uu____3211 = translate_expr env e1 in
            let uu____3212 = translate_expr env e2 in
            (Stack, uu____3211, uu____3212) in
          EBufCreate uu____3207
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3214;
             FStar_Extraction_ML_Syntax.loc = uu____3215;_},_e0::e1::e2::[])
          when
          let uu____3220 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3220 = "FStar.Buffer.rcreate" ->
          let uu____3221 =
            let uu____3225 = translate_expr env e1 in
            let uu____3226 = translate_expr env e2 in
            (Eternal, uu____3225, uu____3226) in
          EBufCreate uu____3221
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3228;
             FStar_Extraction_ML_Syntax.loc = uu____3229;_},e2::[])
          when
          let uu____3232 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3232 = "FStar.Buffer.createL" ->
          let rec list_elements1 acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements1 (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____3256 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!" in
          let list_elements2 = list_elements1 [] in
          let uu____3262 =
            let uu____3266 =
              let uu____3268 = list_elements2 e2 in
              FStar_List.map (translate_expr env) uu____3268 in
            (Stack, uu____3266) in
          EBufCreateL uu____3262
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3272;
             FStar_Extraction_ML_Syntax.loc = uu____3273;_},e1::e2::_e3::[])
          when
          let uu____3278 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3278 = "FStar.Buffer.sub" ->
          let uu____3279 =
            let uu____3282 = translate_expr env e1 in
            let uu____3283 = translate_expr env e2 in
            (uu____3282, uu____3283) in
          EBufSub uu____3279
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3285;
             FStar_Extraction_ML_Syntax.loc = uu____3286;_},e1::e2::[])
          when
          let uu____3290 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3290 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3292;
             FStar_Extraction_ML_Syntax.loc = uu____3293;_},e1::e2::[])
          when
          let uu____3297 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3297 = "FStar.Buffer.offset" ->
          let uu____3298 =
            let uu____3301 = translate_expr env e1 in
            let uu____3302 = translate_expr env e2 in
            (uu____3301, uu____3302) in
          EBufSub uu____3298
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3304;
             FStar_Extraction_ML_Syntax.loc = uu____3305;_},e1::e2::e3::[])
          when
          (let uu____3310 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____3310 = "FStar.Buffer.upd") ||
            (let uu____3311 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____3311 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____3312 =
            let uu____3316 = translate_expr env e1 in
            let uu____3317 = translate_expr env e2 in
            let uu____3318 = translate_expr env e3 in
            (uu____3316, uu____3317, uu____3318) in
          EBufWrite uu____3312
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3320;
             FStar_Extraction_ML_Syntax.loc = uu____3321;_},uu____3322::[])
          when
          let uu____3324 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3324 = "FStar.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3326;
             FStar_Extraction_ML_Syntax.loc = uu____3327;_},uu____3328::[])
          when
          let uu____3330 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3330 = "FStar.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3332;
             FStar_Extraction_ML_Syntax.loc = uu____3333;_},e1::e2::e3::e4::e5::[])
          when
          let uu____3340 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3340 = "FStar.Buffer.blit" ->
          let uu____3341 =
            let uu____3347 = translate_expr env e1 in
            let uu____3348 = translate_expr env e2 in
            let uu____3349 = translate_expr env e3 in
            let uu____3350 = translate_expr env e4 in
            let uu____3351 = translate_expr env e5 in
            (uu____3347, uu____3348, uu____3349, uu____3350, uu____3351) in
          EBufBlit uu____3341
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3353;
             FStar_Extraction_ML_Syntax.loc = uu____3354;_},e1::e2::e3::[])
          when
          let uu____3359 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3359 = "FStar.Buffer.fill" ->
          let uu____3360 =
            let uu____3364 = translate_expr env e1 in
            let uu____3365 = translate_expr env e2 in
            let uu____3366 = translate_expr env e3 in
            (uu____3364, uu____3365, uu____3366) in
          EBufFill uu____3360
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3368;
             FStar_Extraction_ML_Syntax.loc = uu____3369;_},uu____3370::[])
          when
          let uu____3372 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3372 = "FStar.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____3374;
             FStar_Extraction_ML_Syntax.loc = uu____3375;_},e1::[])
          when
          let uu____3378 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3378 = "Obj.repr" ->
          let uu____3379 =
            let uu____3382 = translate_expr env e1 in (uu____3382, TAny) in
          ECast uu____3379
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____3385;
             FStar_Extraction_ML_Syntax.loc = uu____3386;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____3391 = FStar_Util.must (mk_width m) in
          let uu____3392 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____3391 uu____3392 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____3394;
             FStar_Extraction_ML_Syntax.loc = uu____3395;_},args)
          when is_bool_op op ->
          let uu____3400 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____3400 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____3402;
             FStar_Extraction_ML_Syntax.loc = uu____3403;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,None ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3405;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3406;_}::[])
          when is_machine_int m ->
          let uu____3414 =
            let uu____3417 = FStar_Util.must (mk_width m) in (uu____3417, c) in
          EConstant uu____3414
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____3419;
             FStar_Extraction_ML_Syntax.loc = uu____3420;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,None ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3422;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3423;_}::[])
          when is_machine_int m ->
          let uu____3431 =
            let uu____3434 = FStar_Util.must (mk_width m) in (uu____3434, c) in
          EConstant uu____3431
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____3435;
             FStar_Extraction_ML_Syntax.loc = uu____3436;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3438;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3439;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____3443 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____3445;
             FStar_Extraction_ML_Syntax.loc = uu____3446;_},arg::[])
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
            let uu____3451 =
              let uu____3454 = translate_expr env arg in
              (uu____3454, (TInt UInt64)) in
            ECast uu____3451
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____3456 =
                 let uu____3459 = translate_expr env arg in
                 (uu____3459, (TInt UInt32)) in
               ECast uu____3456)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____3461 =
                   let uu____3464 = translate_expr env arg in
                   (uu____3464, (TInt UInt16)) in
                 ECast uu____3461)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____3466 =
                     let uu____3469 = translate_expr env arg in
                     (uu____3469, (TInt UInt8)) in
                   ECast uu____3466)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____3471 =
                       let uu____3474 = translate_expr env arg in
                       (uu____3474, (TInt Int64)) in
                     ECast uu____3471)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____3476 =
                         let uu____3479 = translate_expr env arg in
                         (uu____3479, (TInt Int32)) in
                       ECast uu____3476)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____3481 =
                           let uu____3484 = translate_expr env arg in
                           (uu____3484, (TInt Int16)) in
                         ECast uu____3481)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____3486 =
                             let uu____3489 = translate_expr env arg in
                             (uu____3489, (TInt Int8)) in
                           ECast uu____3486)
                        else
                          (let uu____3491 =
                             let uu____3495 =
                               let uu____3497 = translate_expr env arg in
                               [uu____3497] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____3495) in
                           EApp uu____3491)
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name (path,function_name);
             FStar_Extraction_ML_Syntax.mlty = uu____3502;
             FStar_Extraction_ML_Syntax.loc = uu____3503;_},args)
          ->
          let uu____3509 =
            let uu____3513 = FStar_List.map (translate_expr env) args in
            ((EQualified (path, function_name)), uu____3513) in
          EApp uu____3509
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Var (name,uu____3518);
             FStar_Extraction_ML_Syntax.mlty = uu____3519;
             FStar_Extraction_ML_Syntax.loc = uu____3520;_},args)
          ->
          let uu____3524 =
            let uu____3528 =
              let uu____3529 = find env name in EBound uu____3529 in
            let uu____3530 = FStar_List.map (translate_expr env) args in
            (uu____3528, uu____3530) in
          EApp uu____3524
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____3536 =
            let uu____3539 = translate_expr env e1 in
            let uu____3540 = translate_type env t_to in
            (uu____3539, uu____3540) in
          ECast uu____3536
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____3541,fields) ->
          let uu____3551 =
            let uu____3557 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____3558 =
              FStar_List.map
                (fun uu____3566  ->
                   match uu____3566 with
                   | (field,expr) ->
                       let uu____3573 = translate_expr env expr in
                       (field, uu____3573)) fields in
            (uu____3557, uu____3558) in
          EFlat uu____3551
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____3579 =
            let uu____3583 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____3584 = translate_expr env e1 in
            (uu____3583, uu____3584, (snd path)) in
          EField uu____3579
      | FStar_Extraction_ML_Syntax.MLE_Let uu____3586 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____3594) ->
          let uu____3597 =
            let uu____3598 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1 in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____3598 in
          failwith uu____3597
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____3602 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____3602
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____3606 = FStar_List.map (translate_expr env) es in
          ETuple uu____3606
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____3608,cons1),es) ->
          let uu____3618 =
            let uu____3623 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____3624 = FStar_List.map (translate_expr env) es in
            (uu____3623, cons1, uu____3624) in
          ECons uu____3618
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args in
          let env1 = add_binders env args in
          let uu____3638 =
            let uu____3642 = translate_expr env1 body in
            (binders, uu____3642) in
          EFun uu____3638
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____3649 =
            let uu____3653 = translate_expr env e1 in
            let uu____3654 = translate_expr env e2 in
            let uu____3655 =
              match e3 with
              | None  -> EUnit
              | Some e31 -> translate_expr env e31 in
            (uu____3653, uu____3654, uu____3655) in
          EIfThenElse uu____3649
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____3657 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____3661 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____3669 ->
          failwith "todo: translate_expr [MLE_Coerce]"
and assert_lid: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____3685 =
              let uu____3692 = FStar_List.map (translate_type env) ts in
              (lid, uu____3692) in
            TApp uu____3685
          else TQualified lid
      | uu____3696 -> failwith "invalid argument: assert_lid"
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
    fun uu____3711  ->
      match uu____3711 with
      | (pat,guard,expr) ->
          if guard = None
          then
            let uu____3726 = translate_pat env pat in
            (match uu____3726 with
             | (env1,pat1) ->
                 let uu____3733 = translate_expr env1 expr in
                 (pat1, uu____3733))
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
      | FStar_Extraction_ML_Syntax.MLP_Var (name,uu____3743) ->
          let env1 = extend env name false in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_" false in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____3746,cons1),ps) ->
          let uu____3756 =
            FStar_List.fold_left
              (fun uu____3763  ->
                 fun p1  ->
                   match uu____3763 with
                   | (env1,acc) ->
                       let uu____3775 = translate_pat env1 p1 in
                       (match uu____3775 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____3756 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____3792,ps) ->
          let uu____3802 =
            FStar_List.fold_left
              (fun uu____3815  ->
                 fun uu____3816  ->
                   match (uu____3815, uu____3816) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____3853 = translate_pat env1 p1 in
                       (match uu____3853 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps in
          (match uu____3802 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____3887 =
            FStar_List.fold_left
              (fun uu____3894  ->
                 fun p1  ->
                   match uu____3894 with
                   | (env1,acc) ->
                       let uu____3906 = translate_pat env1 p1 in
                       (match uu____3906 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____3887 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____3922 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____3925 ->
          failwith "todo: translate_pat [MLP_Branch]"
and translate_constant: FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_Int (s,Some uu____3932) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____3940 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____3941 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____3942 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____3943 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (uu____3945,None ) ->
        failwith "todo: translate_expr [MLC_Int]"
and mk_op_app:
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr
  =
  fun env  ->
    fun w  ->
      fun op  ->
        fun args  ->
          let uu____3956 =
            let uu____3960 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____3960) in
          EApp uu____3956