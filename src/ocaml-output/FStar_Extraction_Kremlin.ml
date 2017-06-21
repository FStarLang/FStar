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
let __proj__Mkbinder__item__name: binder -> Prims.string =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ; mut = __fname__mut;_} ->
        __fname__name
let __proj__Mkbinder__item__typ: binder -> typ =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ; mut = __fname__mut;_} ->
        __fname__typ
let __proj__Mkbinder__item__mut: binder -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ; mut = __fname__mut;_} ->
        __fname__mut
let uu___is_TInt: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____1673 -> false
let __proj__TInt__item___0: typ -> width =
  fun projectee  -> match projectee with | TInt _0 -> _0
let uu___is_TBuf: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____1687 -> false
let __proj__TBuf__item___0: typ -> typ =
  fun projectee  -> match projectee with | TBuf _0 -> _0
let uu___is_TUnit: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____1700 -> false
let uu___is_TQualified: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____1709 -> false
let __proj__TQualified__item___0:
  typ -> (Prims.string Prims.list* Prims.string) =
  fun projectee  -> match projectee with | TQualified _0 -> _0
let uu___is_TBool: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____1731 -> false
let uu___is_TAny: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____1736 -> false
let uu___is_TArrow: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____1744 -> false
let __proj__TArrow__item___0: typ -> (typ* typ) =
  fun projectee  -> match projectee with | TArrow _0 -> _0
let uu___is_TZ: typ -> Prims.bool =
  fun projectee  -> match projectee with | TZ  -> true | uu____1763 -> false
let uu___is_TBound: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____1769 -> false
let __proj__TBound__item___0: typ -> Prims.int =
  fun projectee  -> match projectee with | TBound _0 -> _0
let uu___is_TApp: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____1789 -> false
let __proj__TApp__item___0:
  typ -> ((Prims.string Prims.list* Prims.string)* typ Prims.list) =
  fun projectee  -> match projectee with | TApp _0 -> _0
let uu___is_TTuple: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____1822 -> false
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
let fst3 uu____1880 = match uu____1880 with | (x,uu____1885,uu____1886) -> x
let snd3 uu____1904 = match uu____1904 with | (uu____1908,x,uu____1910) -> x
let thd3 uu____1928 = match uu____1928 with | (uu____1932,uu____1933,x) -> x
let mk_width: Prims.string -> width option =
  fun uu___119_1939  ->
    match uu___119_1939 with
    | "UInt8" -> Some UInt8
    | "UInt16" -> Some UInt16
    | "UInt32" -> Some UInt32
    | "UInt64" -> Some UInt64
    | "Int8" -> Some Int8
    | "Int16" -> Some Int16
    | "Int32" -> Some Int32
    | "Int64" -> Some Int64
    | uu____1941 -> None
let mk_bool_op: Prims.string -> op option =
  fun uu___120_1946  ->
    match uu___120_1946 with
    | "op_Negation" -> Some Not
    | "op_AmpAmp" -> Some And
    | "op_BarBar" -> Some Or
    | "op_Equality" -> Some Eq
    | "op_disEquality" -> Some Neq
    | uu____1948 -> None
let is_bool_op: Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> None
let mk_op: Prims.string -> op option =
  fun uu___121_1958  ->
    match uu___121_1958 with
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
    | uu____1960 -> None
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
let __proj__Mkenv__item__names: env -> name Prims.list =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__names
let __proj__Mkenv__item__names_t: env -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__names_t
let __proj__Mkenv__item__module_name: env -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__module_name
let __proj__Mkname__item__pretty: name -> Prims.string =
  fun projectee  ->
    match projectee with
    | { pretty = __fname__pretty; mut = __fname__mut;_} -> __fname__pretty
let __proj__Mkname__item__mut: name -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { pretty = __fname__pretty; mut = __fname__mut;_} -> __fname__mut
let empty: Prims.string Prims.list -> env =
  fun module_name  -> { names = []; names_t = []; module_name }
let extend: env -> Prims.string -> Prims.bool -> env =
  fun env  ->
    fun x  ->
      fun is_mut  ->
        let uu___126_2060 = env in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___126_2060.names_t);
          module_name = (uu___126_2060.module_name)
        }
let extend_t: env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___127_2069 = env in
      {
        names = (uu___127_2069.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___127_2069.module_name)
      }
let find_name: env -> Prims.string -> name =
  fun env  ->
    fun x  ->
      let uu____2078 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names in
      match uu____2078 with
      | Some name -> name
      | None  -> failwith "internal error: name not found"
let is_mutable: env -> Prims.string -> Prims.bool =
<<<<<<< HEAD
  fun env  -> fun x  -> let uu____1887 = find_name env x in uu____1887.mut
=======
  fun env  -> fun x  -> let uu____2090 = find_name env x in uu____2090.mut
>>>>>>> origin/guido_tactics
let find: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
<<<<<<< HEAD
      | uu____1902 ->
          let uu____1903 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____1903
=======
      | uu____2102 ->
          let uu____2103 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____2103
>>>>>>> origin/guido_tactics
let find_t: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
<<<<<<< HEAD
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
=======
      | uu____2115 ->
          let uu____2116 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____2116
let add_binders env binders =
  FStar_List.fold_left
    (fun env1  ->
       fun uu____2150  ->
         match uu____2150 with
         | ((name,uu____2156),uu____2157) -> extend env1 name false) env
    binders
let rec translate: FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____2248  ->
    match uu____2248 with
>>>>>>> origin/guido_tactics
    | FStar_Extraction_ML_Syntax.MLLib modules1 ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
<<<<<<< HEAD
               let uu____2085 = m in
               match uu____2085 with
               | ((prefix1,final),uu____2097,uu____2098) ->
=======
               let uu____2279 = m in
               match uu____2279 with
               | ((prefix1,final),uu____2291,uu____2292) ->
>>>>>>> origin/guido_tactics
                   FStar_String.concat "."
                     (FStar_List.append prefix1 [final]) in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
<<<<<<< HEAD
               (let uu____2117 = translate_module m in Some uu____2117)
             with
             | e ->
                 ((let uu____2125 = FStar_Util.print_exn e in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____2125);
=======
               (let uu____2308 = translate_module m in Some uu____2308)
             with
             | e ->
                 ((let uu____2313 = FStar_Util.print_exn e in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____2313);
>>>>>>> origin/guido_tactics
                  None)) modules1
and translate_module:
  ((Prims.string Prims.list* Prims.string)*
    (FStar_Extraction_ML_Syntax.mlsig* FStar_Extraction_ML_Syntax.mlmodule)
    option* FStar_Extraction_ML_Syntax.mllib) -> file
  =
<<<<<<< HEAD
  fun uu____2126  ->
    match uu____2126 with
    | (module_name,modul,uu____2138) ->
=======
  fun uu____2314  ->
    match uu____2314 with
    | (module_name,modul,uu____2326) ->
>>>>>>> origin/guido_tactics
        let module_name1 =
          FStar_List.append (fst module_name) [snd module_name] in
        let program =
          match modul with
          | Some (_signature,decls) ->
              FStar_List.filter_map (translate_decl (empty module_name1))
                decls
<<<<<<< HEAD
          | uu____2162 ->
=======
          | uu____2350 ->
>>>>>>> origin/guido_tactics
              failwith "Unexpected standalone interface or nested modules" in
        ((FStar_String.concat "_" module_name1), program)
and translate_flags:
  FStar_Extraction_ML_Syntax.c_flag Prims.list -> flag Prims.list =
  fun flags  ->
    FStar_List.choose
<<<<<<< HEAD
      (fun uu___121_2171  ->
         match uu___121_2171 with
=======
      (fun uu___122_2358  ->
         match uu___122_2358 with
>>>>>>> origin/guido_tactics
         | FStar_Extraction_ML_Syntax.Private  -> Some Private
         | FStar_Extraction_ML_Syntax.NoExtract  -> Some NoExtract
         | FStar_Extraction_ML_Syntax.Attribute "c_inline" -> Some CInline
         | FStar_Extraction_ML_Syntax.Attribute "substitute" ->
             Some Substitute
         | FStar_Extraction_ML_Syntax.Attribute a ->
             (FStar_Util.print1_warning "Warning: unrecognized attribute %s"
                a;
              None)
<<<<<<< HEAD
         | uu____2175 -> None) flags
=======
         | uu____2362 -> None) flags
>>>>>>> origin/guido_tactics
and translate_decl:
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl option =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
<<<<<<< HEAD
                            (name,uu____2182);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some
                            (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2185;
=======
                            (name,uu____2370);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some
                            (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2373;
>>>>>>> origin/guido_tactics
                          FStar_Extraction_ML_Syntax.mllb_def =
                            {
                              FStar_Extraction_ML_Syntax.expr =
                                FStar_Extraction_ML_Syntax.MLE_Fun
                                (args,body);
<<<<<<< HEAD
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
=======
                              FStar_Extraction_ML_Syntax.mlty = uu____2376;
                              FStar_Extraction_ML_Syntax.loc = uu____2377;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____2378;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___123_2389  ->
                 match uu___123_2389 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____2390 -> false) flags in
>>>>>>> origin/guido_tactics
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
<<<<<<< HEAD
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
=======
                 fun uu____2397  ->
                   match uu____2397 with
                   | (name1,uu____2401) -> extend_t env2 name1) env1 tvars in
          let rec find_return_type uu___124_2405 =
            match uu___124_2405 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2406,uu____2407,t)
                -> find_return_type t
            | t -> t in
          let t =
            let uu____2411 = find_return_type t0 in
            translate_type env2 uu____2411 in
>>>>>>> origin/guido_tactics
          let binders = translate_binders env2 args in
          let env3 = add_binders env2 args in
          let name1 = ((env3.module_name), name) in
          let flags1 = translate_flags flags in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
<<<<<<< HEAD
               let uu____2243 =
                 let uu____2244 =
                   let uu____2252 = translate_type env3 t0 in
                   (None, name1, uu____2252) in
                 DExternal uu____2244 in
               Some uu____2243
=======
               let uu____2428 =
                 let uu____2429 =
                   let uu____2437 = translate_type env3 t0 in
                   (None, name1, uu____2437) in
                 DExternal uu____2429 in
               Some uu____2428
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                 ((let uu____2280 = FStar_Util.print_exn e in
                   FStar_Util.print2 "Warning: writing a stub for %s (%s)\n"
                     (snd name1) uu____2280);
=======
                 ((let uu____2462 = FStar_Util.print_exn e in
                   FStar_Util.print2 "Warning: writing a stub for %s (%s)\n"
                     (snd name1) uu____2462);
>>>>>>> origin/guido_tactics
                  Some
                    (DFunction
                       (None, flags1, (FStar_List.length tvars), t, name1,
                         binders, EAbort))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
<<<<<<< HEAD
                            (name,uu____2293);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some
                            (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2296;
=======
                            (name,uu____2477);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some
                            (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2480;
>>>>>>> origin/guido_tactics
                          FStar_Extraction_ML_Syntax.mllb_def =
                            {
                              FStar_Extraction_ML_Syntax.expr =
                                FStar_Extraction_ML_Syntax.MLE_Coerce
                                ({
                                   FStar_Extraction_ML_Syntax.expr =
                                     FStar_Extraction_ML_Syntax.MLE_Fun
                                     (args,body);
                                   FStar_Extraction_ML_Syntax.mlty =
<<<<<<< HEAD
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
=======
                                     uu____2483;
                                   FStar_Extraction_ML_Syntax.loc =
                                     uu____2484;_},uu____2485,uu____2486);
                              FStar_Extraction_ML_Syntax.mlty = uu____2487;
                              FStar_Extraction_ML_Syntax.loc = uu____2488;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____2489;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___123_2500  ->
                 match uu___123_2500 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____2501 -> false) flags in
>>>>>>> origin/guido_tactics
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
<<<<<<< HEAD
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
=======
                 fun uu____2508  ->
                   match uu____2508 with
                   | (name1,uu____2512) -> extend_t env2 name1) env1 tvars in
          let rec find_return_type uu___124_2516 =
            match uu___124_2516 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____2517,uu____2518,t)
                -> find_return_type t
            | t -> t in
          let t =
            let uu____2522 = find_return_type t0 in
            translate_type env2 uu____2522 in
>>>>>>> origin/guido_tactics
          let binders = translate_binders env2 args in
          let env3 = add_binders env2 args in
          let name1 = ((env3.module_name), name) in
          let flags1 = translate_flags flags in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
<<<<<<< HEAD
               let uu____2358 =
                 let uu____2359 =
                   let uu____2367 = translate_type env3 t0 in
                   (None, name1, uu____2367) in
                 DExternal uu____2359 in
               Some uu____2358
=======
               let uu____2539 =
                 let uu____2540 =
                   let uu____2548 = translate_type env3 t0 in
                   (None, name1, uu____2548) in
                 DExternal uu____2540 in
               Some uu____2539
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                 ((let uu____2395 = FStar_Util.print_exn e in
                   FStar_Util.print2 "Warning: writing a stub for %s (%s)\n"
                     (snd name1) uu____2395);
=======
                 ((let uu____2573 = FStar_Util.print_exn e in
                   FStar_Util.print2 "Warning: writing a stub for %s (%s)\n"
                     (snd name1) uu____2573);
>>>>>>> origin/guido_tactics
                  Some
                    (DFunction
                       (None, flags1, (FStar_List.length tvars), t, name1,
                         binders, EAbort))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
<<<<<<< HEAD
                            (name,uu____2408);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some ([],t);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2410;
                          FStar_Extraction_ML_Syntax.mllb_def = expr;
                          FStar_Extraction_ML_Syntax.print_typ = uu____2412;_}::[])
=======
                            (name,uu____2588);
                          FStar_Extraction_ML_Syntax.mllb_tysc = Some ([],t);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____2590;
                          FStar_Extraction_ML_Syntax.mllb_def = expr;
                          FStar_Extraction_ML_Syntax.print_typ = uu____2592;_}::[])
>>>>>>> origin/guido_tactics
          ->
          let flags1 = translate_flags flags in
          let t1 = translate_type env t in
          let name1 = ((env.module_name), name) in
          (try
             let expr1 = translate_expr env expr in
             Some (DGlobal (flags1, name1, t1, expr1))
           with
           | e ->
<<<<<<< HEAD
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
=======
               ((let uu____2618 = FStar_Util.print_exn e in
                 FStar_Util.print2
                   "Warning: not translating definition for %s (%s)\n"
                   (snd name1) uu____2618);
                Some (DGlobal (flags1, name1, t1, EAny))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (uu____2624,uu____2625,{
                                   FStar_Extraction_ML_Syntax.mllb_name =
                                     (name,uu____2627);
                                   FStar_Extraction_ML_Syntax.mllb_tysc = ts;
                                   FStar_Extraction_ML_Syntax.mllb_add_unit =
                                     uu____2629;
                                   FStar_Extraction_ML_Syntax.mllb_def =
                                     uu____2630;
                                   FStar_Extraction_ML_Syntax.print_typ =
                                     uu____2631;_}::uu____2632)
>>>>>>> origin/guido_tactics
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           (match ts with
            | Some (idents,t) ->
<<<<<<< HEAD
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
=======
                let uu____2642 =
                  let uu____2643 = FStar_List.map FStar_Pervasives.fst idents in
                  FStar_String.concat ", " uu____2643 in
                let uu____2647 =
                  FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                  uu____2642 uu____2647
            | None  -> ());
           None)
      | FStar_Extraction_ML_Syntax.MLM_Let uu____2649 ->
          failwith "impossible"
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____2651 -> None
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((assumed,name,_mangled_name,args,Some
            (FStar_Extraction_ML_Syntax.MLTD_Abbrev t))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
<<<<<<< HEAD
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
=======
                 fun uu____2683  ->
                   match uu____2683 with
                   | (name2,uu____2687) -> extend_t env1 name2) env args in
          if assumed
          then None
          else
            (let uu____2690 =
               let uu____2691 =
                 let uu____2698 = translate_type env1 t in
                 (name1, (FStar_List.length args), uu____2698) in
               DTypeAlias uu____2691 in
             Some uu____2690)
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2706,name,_mangled_name,args,Some
>>>>>>> origin/guido_tactics
            (FStar_Extraction_ML_Syntax.MLTD_Record fields))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
<<<<<<< HEAD
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
=======
                 fun uu____2740  ->
                   match uu____2740 with
                   | (name2,uu____2744) -> extend_t env1 name2) env args in
          let uu____2745 =
            let uu____2746 =
              let uu____2758 =
                FStar_List.map
                  (fun uu____2770  ->
                     match uu____2770 with
                     | (f,t) ->
                         let uu____2779 =
                           let uu____2782 = translate_type env1 t in
                           (uu____2782, false) in
                         (f, uu____2779)) fields in
              (name1, (FStar_List.length args), uu____2758) in
            DTypeFlat uu____2746 in
          Some uu____2745
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2797,name,_mangled_name,args,Some
>>>>>>> origin/guido_tactics
            (FStar_Extraction_ML_Syntax.MLTD_DType branches))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
<<<<<<< HEAD
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
=======
                 fun uu____2834  ->
                   match uu____2834 with
                   | (name2,uu____2838) -> extend_t env1 name2) env args in
          let uu____2839 =
            let uu____2840 =
              let uu____2855 =
                FStar_List.map
                  (fun uu____2876  ->
                     match uu____2876 with
                     | (cons1,ts) ->
                         let uu____2897 =
                           FStar_List.map
                             (fun uu____2909  ->
                                match uu____2909 with
                                | (name2,t) ->
                                    let uu____2918 =
                                      let uu____2921 = translate_type env1 t in
                                      (uu____2921, false) in
                                    (name2, uu____2918)) ts in
                         (cons1, uu____2897)) branches in
              (name1, (FStar_List.length args), uu____2855) in
            DTypeVariant uu____2840 in
          Some uu____2839
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____2944,name,_mangled_name,uu____2947,uu____2948)::uu____2949)
>>>>>>> origin/guido_tactics
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           None)
      | FStar_Extraction_ML_Syntax.MLM_Ty [] ->
          (FStar_Util.print_string
             "Impossible!! Empty block of mutually recursive type declarations";
           None)
<<<<<<< HEAD
      | FStar_Extraction_ML_Syntax.MLM_Top uu____2814 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____2816 ->
=======
      | FStar_Extraction_ML_Syntax.MLM_Top uu____2971 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____2973 ->
>>>>>>> origin/guido_tactics
          failwith "todo: translate_decl [MLM_Exn]"
and translate_type: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
<<<<<<< HEAD
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
=======
      | FStar_Extraction_ML_Syntax.MLTY_Var (name,uu____2983) ->
          let uu____2984 = find_t env name in TBound uu____2984
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____2986,t2) ->
          let uu____2988 =
            let uu____2991 = translate_type env t1 in
            let uu____2992 = translate_type env t2 in
            (uu____2991, uu____2992) in
          TArrow uu____2988
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____2995 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2995 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____2998 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____2998 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____3005 = FStar_Util.must (mk_width m) in TInt uu____3005
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____3012 = FStar_Util.must (mk_width m) in TInt uu____3012
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____3016 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3016 = "FStar.Buffer.buffer" ->
          let uu____3017 = translate_type env arg in TBuf uu____3017
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____3018::[],p) when
          let uu____3021 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3021 = "FStar.Ghost.erased" -> TAny
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
<<<<<<< HEAD
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
=======
          let uu____3043 = FStar_List.map (translate_type env) args in
          TTuple uu____3043
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____3055 =
              let uu____3062 = FStar_List.map (translate_type env) args in
              (lid, uu____3062) in
            TApp uu____3055
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____3068 = FStar_List.map (translate_type env) ts in
          TTuple uu____3068
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
    fun uu____2918  ->
      match uu____2918 with
      | ((name,uu____2922),typ) ->
          let uu____2926 = translate_type env typ in
          { name; typ = uu____2926; mut = false }
=======
    fun uu____3078  ->
      match uu____3078 with
      | ((name,uu____3082),typ) ->
          let uu____3086 = translate_type env typ in
          { name; typ = uu____3086; mut = false }
>>>>>>> origin/guido_tactics
and translate_expr: env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
<<<<<<< HEAD
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
=======
      | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____3091) ->
          let uu____3092 = find env name in EBound uu____3092
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____3096 =
            let uu____3099 = FStar_Util.must (mk_op op) in
            let uu____3100 = FStar_Util.must (mk_width m) in
            (uu____3099, uu____3100) in
          EOp uu____3096
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____3103 =
            let uu____3106 = FStar_Util.must (mk_bool_op op) in
            (uu____3106, Bool) in
          EOp uu____3103
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags,{
                           FStar_Extraction_ML_Syntax.mllb_name =
<<<<<<< HEAD
                             (name,uu____2951);
=======
                             (name,uu____3111);
>>>>>>> origin/guido_tactics
                           FStar_Extraction_ML_Syntax.mllb_tysc = Some
                             ([],typ);
                           FStar_Extraction_ML_Syntax.mllb_add_unit =
                             add_unit;
                           FStar_Extraction_ML_Syntax.mllb_def = body;
                           FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let is_mut =
            FStar_Util.for_some
<<<<<<< HEAD
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
=======
              (fun uu___125_3127  ->
                 match uu___125_3127 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____3128 -> false) flags in
          let uu____3129 =
            if is_mut
            then
              let uu____3134 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____3138 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____3138 = "FStar.ST.stackref" -> t
                | uu____3139 ->
                    let uu____3140 =
                      let uu____3141 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____3141 in
                    failwith uu____3140 in
              let uu____3143 =
>>>>>>> origin/guido_tactics
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
<<<<<<< HEAD
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
=======
                      (uu____3144,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____3146;
                    FStar_Extraction_ML_Syntax.loc = uu____3147;_} -> body1
                | uu____3149 ->
                    failwith "unexpected: bad desugaring of Mutable" in
              (uu____3134, uu____3143)
            else (typ, body) in
          (match uu____3129 with
           | (typ1,body1) ->
               let binder =
                 let uu____3154 = translate_type env typ1 in
                 { name; typ = uu____3154; mut = is_mut } in
>>>>>>> origin/guido_tactics
               let body2 = translate_expr env body1 in
               let env1 = extend env name is_mut in
               let continuation1 = translate_expr env1 continuation in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
<<<<<<< HEAD
          let uu____3011 =
            let uu____3017 = translate_expr env expr in
            let uu____3018 = translate_branches env branches in
            (uu____3017, uu____3018) in
          EMatch uu____3011
=======
          let uu____3170 =
            let uu____3176 = translate_expr env expr in
            let uu____3177 = translate_branches env branches in
            (uu____3176, uu____3177) in
          EMatch uu____3170
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
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
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3185;
             FStar_Extraction_ML_Syntax.loc = uu____3186;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____3188);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3189;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3190;_}::[])
          when
          (let uu____3192 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____3192 = "FStar.ST.op_Bang") && (is_mutable env v1)
          -> let uu____3193 = find env v1 in EBound uu____3193
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
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
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3195;
             FStar_Extraction_ML_Syntax.loc = uu____3196;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____3198);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3199;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3200;_}::e1::[])
          when
          (let uu____3203 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____3203 = "FStar.ST.op_Colon_Equals") && (is_mutable env v1)
          ->
          let uu____3204 =
            let uu____3207 =
              let uu____3208 = find env v1 in EBound uu____3208 in
            let uu____3209 = translate_expr env e1 in
            (uu____3207, uu____3209) in
          EAssign uu____3204
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
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
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3211;
             FStar_Extraction_ML_Syntax.loc = uu____3212;_},e1::e2::[])
          when
          (let uu____3216 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____3216 = "FStar.Buffer.index") ||
            (let uu____3217 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____3217 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____3218 =
            let uu____3221 = translate_expr env e1 in
            let uu____3222 = translate_expr env e2 in
            (uu____3221, uu____3222) in
          EBufRead uu____3218
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
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
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3224;
             FStar_Extraction_ML_Syntax.loc = uu____3225;_},e1::e2::[])
          when
          let uu____3229 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3229 = "FStar.Buffer.create" ->
          let uu____3230 =
            let uu____3234 = translate_expr env e1 in
            let uu____3235 = translate_expr env e2 in
            (Stack, uu____3234, uu____3235) in
          EBufCreate uu____3230
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
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
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3237;
             FStar_Extraction_ML_Syntax.loc = uu____3238;_},_e0::e1::e2::[])
          when
          let uu____3243 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3243 = "FStar.Buffer.rcreate" ->
          let uu____3244 =
            let uu____3248 = translate_expr env e1 in
            let uu____3249 = translate_expr env e2 in
            (Eternal, uu____3248, uu____3249) in
          EBufCreate uu____3244
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____3099;
             FStar_Extraction_ML_Syntax.loc = uu____3100;_},e2::[])
          when
          let uu____3103 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3103 = "FStar.Buffer.createL" ->
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3251;
             FStar_Extraction_ML_Syntax.loc = uu____3252;_},e2::[])
          when
          let uu____3255 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3255 = "FStar.Buffer.createL" ->
>>>>>>> origin/guido_tactics
          let rec list_elements1 acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements1 (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
<<<<<<< HEAD
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
=======
            | uu____3279 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!" in
          let list_elements2 = list_elements1 [] in
          let uu____3285 =
            let uu____3289 =
              let uu____3291 = list_elements2 e2 in
              FStar_List.map (translate_expr env) uu____3291 in
            (Stack, uu____3289) in
          EBufCreateL uu____3285
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
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
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3295;
             FStar_Extraction_ML_Syntax.loc = uu____3296;_},e1::e2::_e3::[])
          when
          let uu____3301 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3301 = "FStar.Buffer.sub" ->
          let uu____3302 =
            let uu____3305 = translate_expr env e1 in
            let uu____3306 = translate_expr env e2 in
            (uu____3305, uu____3306) in
          EBufSub uu____3302
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____3156;
             FStar_Extraction_ML_Syntax.loc = uu____3157;_},e1::e2::[])
          when
          let uu____3161 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3161 = "FStar.Buffer.join" -> translate_expr env e1
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3308;
             FStar_Extraction_ML_Syntax.loc = uu____3309;_},e1::e2::[])
          when
          let uu____3313 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3313 = "FStar.Buffer.join" -> translate_expr env e1
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
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
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3315;
             FStar_Extraction_ML_Syntax.loc = uu____3316;_},e1::e2::[])
          when
          let uu____3320 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3320 = "FStar.Buffer.offset" ->
          let uu____3321 =
            let uu____3324 = translate_expr env e1 in
            let uu____3325 = translate_expr env e2 in
            (uu____3324, uu____3325) in
          EBufSub uu____3321
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
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
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3327;
             FStar_Extraction_ML_Syntax.loc = uu____3328;_},e1::e2::e3::[])
          when
          (let uu____3333 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____3333 = "FStar.Buffer.upd") ||
            (let uu____3334 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____3334 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____3335 =
            let uu____3339 = translate_expr env e1 in
            let uu____3340 = translate_expr env e2 in
            let uu____3341 = translate_expr env e3 in
            (uu____3339, uu____3340, uu____3341) in
          EBufWrite uu____3335
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____3194;
             FStar_Extraction_ML_Syntax.loc = uu____3195;_},uu____3196::[])
          when
          let uu____3198 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3198 = "FStar.ST.push_frame" -> EPushFrame
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3343;
             FStar_Extraction_ML_Syntax.loc = uu____3344;_},uu____3345::[])
          when
          let uu____3347 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3347 = "FStar.ST.push_frame" -> EPushFrame
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____3200;
             FStar_Extraction_ML_Syntax.loc = uu____3201;_},uu____3202::[])
          when
          let uu____3204 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3204 = "FStar.ST.pop_frame" -> EPopFrame
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3349;
             FStar_Extraction_ML_Syntax.loc = uu____3350;_},uu____3351::[])
          when
          let uu____3353 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3353 = "FStar.ST.pop_frame" -> EPopFrame
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
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
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3355;
             FStar_Extraction_ML_Syntax.loc = uu____3356;_},e1::e2::e3::e4::e5::[])
          when
          let uu____3363 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3363 = "FStar.Buffer.blit" ->
          let uu____3364 =
            let uu____3370 = translate_expr env e1 in
            let uu____3371 = translate_expr env e2 in
            let uu____3372 = translate_expr env e3 in
            let uu____3373 = translate_expr env e4 in
            let uu____3374 = translate_expr env e5 in
            (uu____3370, uu____3371, uu____3372, uu____3373, uu____3374) in
          EBufBlit uu____3364
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
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
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3376;
             FStar_Extraction_ML_Syntax.loc = uu____3377;_},e1::e2::e3::[])
          when
          let uu____3382 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3382 = "FStar.Buffer.fill" ->
          let uu____3383 =
            let uu____3387 = translate_expr env e1 in
            let uu____3388 = translate_expr env e2 in
            let uu____3389 = translate_expr env e3 in
            (uu____3387, uu____3388, uu____3389) in
          EBufFill uu____3383
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____3242;
             FStar_Extraction_ML_Syntax.loc = uu____3243;_},uu____3244::[])
          when
          let uu____3246 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3246 = "FStar.ST.get" -> EUnit
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3391;
             FStar_Extraction_ML_Syntax.loc = uu____3392;_},uu____3393::[])
          when
          let uu____3395 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3395 = "FStar.ST.get" -> EUnit
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____3248;
             FStar_Extraction_ML_Syntax.loc = uu____3249;_},e1::[])
          when
          let uu____3252 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3252 = "Obj.repr" ->
          let uu____3253 =
            let uu____3256 = translate_expr env e1 in (uu____3256, TAny) in
          ECast uu____3253
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3397;
             FStar_Extraction_ML_Syntax.loc = uu____3398;_},e1::[])
          when
          let uu____3401 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____3401 = "Obj.repr" ->
          let uu____3402 =
            let uu____3405 = translate_expr env e1 in (uu____3405, TAny) in
          ECast uu____3402
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____3259;
             FStar_Extraction_ML_Syntax.loc = uu____3260;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____3265 = FStar_Util.must (mk_width m) in
          let uu____3266 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____3265 uu____3266 args
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3408;
             FStar_Extraction_ML_Syntax.loc = uu____3409;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____3414 = FStar_Util.must (mk_width m) in
          let uu____3415 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____3414 uu____3415 args
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____3268;
             FStar_Extraction_ML_Syntax.loc = uu____3269;_},args)
          when is_bool_op op ->
          let uu____3274 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____3274 args
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3417;
             FStar_Extraction_ML_Syntax.loc = uu____3418;_},args)
          when is_bool_op op ->
          let uu____3423 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____3423 args
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____3276;
             FStar_Extraction_ML_Syntax.loc = uu____3277;_},{
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3425;
             FStar_Extraction_ML_Syntax.loc = uu____3426;_},{
>>>>>>> origin/guido_tactics
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,None ));
                                                              FStar_Extraction_ML_Syntax.mlty
<<<<<<< HEAD
                                                                = uu____3279;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3280;_}::[])
          when is_machine_int m ->
          let uu____3288 =
            let uu____3291 = FStar_Util.must (mk_width m) in (uu____3291, c) in
          EConstant uu____3288
=======
                                                                = uu____3428;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3429;_}::[])
          when is_machine_int m ->
          let uu____3437 =
            let uu____3440 = FStar_Util.must (mk_width m) in (uu____3440, c) in
          EConstant uu____3437
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____3293;
             FStar_Extraction_ML_Syntax.loc = uu____3294;_},{
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3442;
             FStar_Extraction_ML_Syntax.loc = uu____3443;_},{
>>>>>>> origin/guido_tactics
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,None ));
                                                              FStar_Extraction_ML_Syntax.mlty
<<<<<<< HEAD
                                                                = uu____3296;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3297;_}::[])
          when is_machine_int m ->
          let uu____3305 =
            let uu____3308 = FStar_Util.must (mk_width m) in (uu____3308, c) in
          EConstant uu____3305
=======
                                                                = uu____3445;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3446;_}::[])
          when is_machine_int m ->
          let uu____3454 =
            let uu____3457 = FStar_Util.must (mk_width m) in (uu____3457, c) in
          EConstant uu____3454
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____3309;
             FStar_Extraction_ML_Syntax.loc = uu____3310;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3312;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3313;_}::[])
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3458;
             FStar_Extraction_ML_Syntax.loc = uu____3459;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____3461;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____3462;_}::[])
>>>>>>> origin/guido_tactics
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
<<<<<<< HEAD
           | uu____3317 ->
=======
           | uu____3466 ->
>>>>>>> origin/guido_tactics
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____3319;
             FStar_Extraction_ML_Syntax.loc = uu____3320;_},arg::[])
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3468;
             FStar_Extraction_ML_Syntax.loc = uu____3469;_},arg::[])
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
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
=======
            let uu____3474 =
              let uu____3477 = translate_expr env arg in
              (uu____3477, (TInt UInt64)) in
            ECast uu____3474
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____3479 =
                 let uu____3482 = translate_expr env arg in
                 (uu____3482, (TInt UInt32)) in
               ECast uu____3479)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____3484 =
                   let uu____3487 = translate_expr env arg in
                   (uu____3487, (TInt UInt16)) in
                 ECast uu____3484)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____3489 =
                     let uu____3492 = translate_expr env arg in
                     (uu____3492, (TInt UInt8)) in
                   ECast uu____3489)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____3494 =
                       let uu____3497 = translate_expr env arg in
                       (uu____3497, (TInt Int64)) in
                     ECast uu____3494)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____3499 =
                         let uu____3502 = translate_expr env arg in
                         (uu____3502, (TInt Int32)) in
                       ECast uu____3499)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____3504 =
                           let uu____3507 = translate_expr env arg in
                           (uu____3507, (TInt Int16)) in
                         ECast uu____3504)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____3509 =
                             let uu____3512 = translate_expr env arg in
                             (uu____3512, (TInt Int8)) in
                           ECast uu____3509)
                        else
                          (let uu____3514 =
                             let uu____3518 =
                               let uu____3520 = translate_expr env arg in
                               [uu____3520] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____3518) in
                           EApp uu____3514)
>>>>>>> origin/guido_tactics
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name (path,function_name);
<<<<<<< HEAD
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
=======
             FStar_Extraction_ML_Syntax.mlty = uu____3525;
             FStar_Extraction_ML_Syntax.loc = uu____3526;_},args)
          ->
          let uu____3532 =
            let uu____3536 = FStar_List.map (translate_expr env) args in
            ((EQualified (path, function_name)), uu____3536) in
          EApp uu____3532
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Var (name,uu____3541);
             FStar_Extraction_ML_Syntax.mlty = uu____3542;
             FStar_Extraction_ML_Syntax.loc = uu____3543;_},args)
          ->
          let uu____3547 =
            let uu____3551 =
              let uu____3552 = find env name in EBound uu____3552 in
            let uu____3553 = FStar_List.map (translate_expr env) args in
            (uu____3551, uu____3553) in
          EApp uu____3547
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____3559 =
            let uu____3562 = translate_expr env e1 in
            let uu____3563 = translate_type env t_to in
            (uu____3562, uu____3563) in
          ECast uu____3559
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____3564,fields) ->
          let uu____3574 =
            let uu____3580 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____3581 =
              FStar_List.map
                (fun uu____3589  ->
                   match uu____3589 with
                   | (field,expr) ->
                       let uu____3596 = translate_expr env expr in
                       (field, uu____3596)) fields in
            (uu____3580, uu____3581) in
          EFlat uu____3574
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____3602 =
            let uu____3606 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____3607 = translate_expr env e1 in
            (uu____3606, uu____3607, (snd path)) in
          EField uu____3602
      | FStar_Extraction_ML_Syntax.MLE_Let uu____3609 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____3617) ->
          let uu____3620 =
            let uu____3621 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1 in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____3621 in
          failwith uu____3620
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____3625 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____3625
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____3629 = FStar_List.map (translate_expr env) es in
          ETuple uu____3629
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____3631,cons1),es) ->
          let uu____3641 =
            let uu____3646 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____3647 = FStar_List.map (translate_expr env) es in
            (uu____3646, cons1, uu____3647) in
          ECons uu____3641
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args in
          let env1 = add_binders env args in
          let uu____3661 =
            let uu____3665 = translate_expr env1 body in
            (binders, uu____3665) in
          EFun uu____3661
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____3672 =
            let uu____3676 = translate_expr env e1 in
            let uu____3677 = translate_expr env e2 in
            let uu____3678 =
              match e3 with
              | None  -> EUnit
              | Some e31 -> translate_expr env e31 in
            (uu____3676, uu____3677, uu____3678) in
          EIfThenElse uu____3672
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____3680 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____3684 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____3692 ->
>>>>>>> origin/guido_tactics
          failwith "todo: translate_expr [MLE_Coerce]"
and assert_lid: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
<<<<<<< HEAD
            let uu____3560 =
              let uu____3567 = FStar_List.map (translate_type env) ts in
              (lid, uu____3567) in
            TApp uu____3560
          else TQualified lid
      | uu____3571 -> failwith "invalid argument: assert_lid"
=======
            let uu____3708 =
              let uu____3715 = FStar_List.map (translate_type env) ts in
              (lid, uu____3715) in
            TApp uu____3708
          else TQualified lid
      | uu____3719 -> failwith "invalid argument: assert_lid"
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
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
=======
    fun uu____3734  ->
      match uu____3734 with
      | (pat,guard,expr) ->
          if guard = None
          then
            let uu____3749 = translate_pat env pat in
            (match uu____3749 with
             | (env1,pat1) ->
                 let uu____3756 = translate_expr env1 expr in
                 (pat1, uu____3756))
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      | FStar_Extraction_ML_Syntax.MLP_Var (name,uu____3618) ->
=======
      | FStar_Extraction_ML_Syntax.MLP_Var (name,uu____3766) ->
>>>>>>> origin/guido_tactics
          let env1 = extend env name false in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_" false in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
<<<<<<< HEAD
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
=======
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____3769,cons1),ps) ->
          let uu____3779 =
            FStar_List.fold_left
              (fun uu____3786  ->
                 fun p1  ->
                   match uu____3786 with
                   | (env1,acc) ->
                       let uu____3798 = translate_pat env1 p1 in
                       (match uu____3798 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____3779 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____3815,ps) ->
          let uu____3825 =
            FStar_List.fold_left
              (fun uu____3838  ->
                 fun uu____3839  ->
                   match (uu____3838, uu____3839) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____3876 = translate_pat env1 p1 in
                       (match uu____3876 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps in
          (match uu____3825 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____3910 =
            FStar_List.fold_left
              (fun uu____3917  ->
                 fun p1  ->
                   match uu____3917 with
                   | (env1,acc) ->
                       let uu____3929 = translate_pat env1 p1 in
                       (match uu____3929 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____3910 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____3945 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____3948 ->
>>>>>>> origin/guido_tactics
          failwith "todo: translate_pat [MLP_Branch]"
and translate_constant: FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
<<<<<<< HEAD
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
=======
    | FStar_Extraction_ML_Syntax.MLC_Int (s,Some uu____3955) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____3963 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____3964 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____3965 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____3966 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (uu____3968,None ) ->
>>>>>>> origin/guido_tactics
        failwith "todo: translate_expr [MLC_Int]"
and mk_op_app:
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr
  =
  fun env  ->
    fun w  ->
      fun op  ->
        fun args  ->
<<<<<<< HEAD
          let uu____3854 =
            let uu____3858 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____3858) in
          EApp uu____3854
=======
          let uu____3979 =
            let uu____3983 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____3983) in
          EApp uu____3979
>>>>>>> origin/guido_tactics
