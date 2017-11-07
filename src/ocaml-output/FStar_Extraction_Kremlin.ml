open Prims
type decl =
  | DGlobal of
  (flag Prims.list,(Prims.string Prims.list,Prims.string)
                     FStar_Pervasives_Native.tuple2,typ,expr)
  FStar_Pervasives_Native.tuple4
  | DFunction of
  (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,(Prims.string
                                                                    Prims.list,
                                                                    Prims.string)
                                                                    FStar_Pervasives_Native.tuple2,
  binder Prims.list,expr) FStar_Pervasives_Native.tuple7
  | DTypeAlias of
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
  Prims.int,typ) FStar_Pervasives_Native.tuple3
  | DTypeFlat of
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
  Prims.int,(Prims.string,(typ,Prims.bool) FStar_Pervasives_Native.tuple2)
              FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple3
  | DExternal of
  (cc FStar_Pervasives_Native.option,(Prims.string Prims.list,Prims.string)
                                       FStar_Pervasives_Native.tuple2,
  typ) FStar_Pervasives_Native.tuple3
  | DTypeVariant of
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
  flag Prims.list,Prims.int,(Prims.string,(Prims.string,(typ,Prims.bool)
                                                          FStar_Pervasives_Native.tuple2)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list)
                              FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple4[@@deriving show]
and cc =
  | StdCall
  | CDecl
  | FastCall[@@deriving show]
and flag =
  | Private
  | NoExtract
  | CInline
  | Substitute
  | GCType
  | Comment of Prims.string[@@deriving show]
and lifetime =
  | Eternal
  | Stack[@@deriving show]
and expr =
  | EBound of Prims.int
  | EQualified of (Prims.string Prims.list,Prims.string)
  FStar_Pervasives_Native.tuple2
  | EConstant of (width,Prims.string) FStar_Pervasives_Native.tuple2
  | EUnit
  | EApp of (expr,expr Prims.list) FStar_Pervasives_Native.tuple2
  | ETypApp of (expr,typ Prims.list) FStar_Pervasives_Native.tuple2
  | ELet of (binder,expr,expr) FStar_Pervasives_Native.tuple3
  | EIfThenElse of (expr,expr,expr) FStar_Pervasives_Native.tuple3
  | ESequence of expr Prims.list
  | EAssign of (expr,expr) FStar_Pervasives_Native.tuple2
  | EBufCreate of (lifetime,expr,expr) FStar_Pervasives_Native.tuple3
  | EBufRead of (expr,expr) FStar_Pervasives_Native.tuple2
  | EBufWrite of (expr,expr,expr) FStar_Pervasives_Native.tuple3
  | EBufSub of (expr,expr) FStar_Pervasives_Native.tuple2
  | EBufBlit of (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5
  | EMatch of (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2
  | EOp of (op,width) FStar_Pervasives_Native.tuple2
  | ECast of (expr,typ) FStar_Pervasives_Native.tuple2
  | EPushFrame
  | EPopFrame
  | EBool of Prims.bool
  | EAny
  | EAbort
  | EReturn of expr
  | EFlat of
  (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2
  | EField of (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3
  | EWhile of (expr,expr) FStar_Pervasives_Native.tuple2
  | EBufCreateL of (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2
  | ETuple of expr Prims.list
  | ECons of (typ,Prims.string,expr Prims.list)
  FStar_Pervasives_Native.tuple3
  | EBufFill of (expr,expr,expr) FStar_Pervasives_Native.tuple3
  | EString of Prims.string
  | EFun of (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3
  | EAbortS of Prims.string[@@deriving show]
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
  | Not[@@deriving show]
and pattern =
  | PUnit
  | PBool of Prims.bool
  | PVar of binder
  | PCons of (Prims.string,pattern Prims.list)
  FStar_Pervasives_Native.tuple2
  | PTuple of pattern Prims.list
  | PRecord of (Prims.string,pattern) FStar_Pervasives_Native.tuple2
  Prims.list[@@deriving show]
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
  | CInt[@@deriving show]
and binder = {
  name: Prims.string;
  typ: typ;
  mut: Prims.bool;}[@@deriving show]
and typ =
  | TInt of width
  | TBuf of typ
  | TUnit
  | TQualified of (Prims.string Prims.list,Prims.string)
  FStar_Pervasives_Native.tuple2
  | TBool
  | TAny
  | TArrow of (typ,typ) FStar_Pervasives_Native.tuple2
  | TBound of Prims.int
  | TApp of
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
  typ Prims.list) FStar_Pervasives_Native.tuple2
  | TTuple of typ Prims.list[@@deriving show]
let uu___is_DGlobal: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DGlobal _0 -> true | uu____523 -> false
let __proj__DGlobal__item___0:
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,typ,expr)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DGlobal _0 -> _0
let uu___is_DFunction: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____609 -> false
let __proj__DFunction__item___0:
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr) FStar_Pervasives_Native.tuple7
  = fun projectee  -> match projectee with | DFunction _0 -> _0
let uu___is_DTypeAlias: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____711 -> false
let __proj__DTypeAlias__item___0:
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      Prims.int,typ) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0
let uu___is_DTypeFlat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____781 -> false
let __proj__DTypeFlat__item___0:
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      Prims.int,(Prims.string,(typ,Prims.bool) FStar_Pervasives_Native.tuple2)
                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0
let uu___is_DExternal: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____873 -> false
let __proj__DExternal__item___0:
  decl ->
    (cc FStar_Pervasives_Native.option,(Prims.string Prims.list,Prims.string)
                                         FStar_Pervasives_Native.tuple2,
      typ) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DExternal _0 -> _0
let uu___is_DTypeVariant: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____959 -> false
let __proj__DTypeVariant__item___0:
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,(Prims.string,(Prims.string,(typ,Prims.bool)
                                                              FStar_Pervasives_Native.tuple2)
                                                FStar_Pervasives_Native.tuple2
                                                Prims.list)
                                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DTypeVariant _0 -> _0
let uu___is_StdCall: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1066 -> false
let uu___is_CDecl: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1070 -> false
let uu___is_FastCall: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1074 -> false
let uu___is_Private: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1078 -> false
let uu___is_NoExtract: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____1082 -> false
let uu___is_CInline: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1086 -> false
let uu___is_Substitute: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1090 -> false
let uu___is_GCType: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1094 -> false
let uu___is_Comment: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1099 -> false
let __proj__Comment__item___0: flag -> Prims.string =
  fun projectee  -> match projectee with | Comment _0 -> _0
let uu___is_Eternal: lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1110 -> false
let uu___is_Stack: lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1114 -> false
let uu___is_EBound: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1119 -> false
let __proj__EBound__item___0: expr -> Prims.int =
  fun projectee  -> match projectee with | EBound _0 -> _0
let uu___is_EQualified: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1137 -> false
let __proj__EQualified__item___0:
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EQualified _0 -> _0
let uu___is_EConstant: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1171 -> false
let __proj__EConstant__item___0:
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EConstant _0 -> _0
let uu___is_EUnit: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1194 -> false
let uu___is_EApp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1205 -> false
let __proj__EApp__item___0:
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EApp _0 -> _0
let uu___is_ETypApp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1241 -> false
let __proj__ETypApp__item___0:
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ETypApp _0 -> _0
let uu___is_ELet: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1277 -> false
let __proj__ELet__item___0:
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ELet _0 -> _0
let uu___is_EIfThenElse: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1313 -> false
let __proj__EIfThenElse__item___0:
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0
let uu___is_ESequence: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1345 -> false
let __proj__ESequence__item___0: expr -> expr Prims.list =
  fun projectee  -> match projectee with | ESequence _0 -> _0
let uu___is_EAssign: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1367 -> false
let __proj__EAssign__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EAssign _0 -> _0
let uu___is_EBufCreate: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____1397 -> false
let __proj__EBufCreate__item___0:
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0
let uu___is_EBufRead: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____1431 -> false
let __proj__EBufRead__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufRead _0 -> _0
let uu___is_EBufWrite: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____1461 -> false
let __proj__EBufWrite__item___0:
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0
let uu___is_EBufSub: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____1495 -> false
let __proj__EBufSub__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufSub _0 -> _0
let uu___is_EBufBlit: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____1529 -> false
let __proj__EBufBlit__item___0:
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5 =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0
let uu___is_EMatch: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____1581 -> false
let __proj__EMatch__item___0:
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EMatch _0 -> _0
let uu___is_EOp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1627 -> false
let __proj__EOp__item___0: expr -> (op,width) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EOp _0 -> _0
let uu___is_ECast: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1655 -> false
let __proj__ECast__item___0:
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ECast _0 -> _0
let uu___is_EPushFrame: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1678 -> false
let uu___is_EPopFrame: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1682 -> false
let uu___is_EBool: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1687 -> false
let __proj__EBool__item___0: expr -> Prims.bool =
  fun projectee  -> match projectee with | EBool _0 -> _0
let uu___is_EAny: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1698 -> false
let uu___is_EAbort: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1702 -> false
let uu___is_EReturn: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1707 -> false
let __proj__EReturn__item___0: expr -> expr =
  fun projectee  -> match projectee with | EReturn _0 -> _0
let uu___is_EFlat: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1729 -> false
let __proj__EFlat__item___0:
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EFlat _0 -> _0
let uu___is_EField: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____1777 -> false
let __proj__EField__item___0:
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EField _0 -> _0
let uu___is_EWhile: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____1811 -> false
let __proj__EWhile__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EWhile _0 -> _0
let uu___is_EBufCreateL: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____1841 -> false
let __proj__EBufCreateL__item___0:
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0
let uu___is_ETuple: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____1873 -> false
let __proj__ETuple__item___0: expr -> expr Prims.list =
  fun projectee  -> match projectee with | ETuple _0 -> _0
let uu___is_ECons: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____1899 -> false
let __proj__ECons__item___0:
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ECons _0 -> _0
let uu___is_EBufFill: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____1941 -> false
let __proj__EBufFill__item___0:
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufFill _0 -> _0
let uu___is_EString: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____1971 -> false
let __proj__EString__item___0: expr -> Prims.string =
  fun projectee  -> match projectee with | EString _0 -> _0
let uu___is_EFun: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____1991 -> false
let __proj__EFun__item___0:
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EFun _0 -> _0
let uu___is_EAbortS: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2027 -> false
let __proj__EAbortS__item___0: expr -> Prims.string =
  fun projectee  -> match projectee with | EAbortS _0 -> _0
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____2038 -> false
let uu___is_AddW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2042 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____2046 -> false
let uu___is_SubW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2050 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____2054 -> false
let uu___is_DivW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2058 -> false
let uu___is_Mult: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2062 -> false
let uu___is_MultW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2066 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____2070 -> false
let uu___is_BOr: op -> Prims.bool =
  fun projectee  -> match projectee with | BOr  -> true | uu____2074 -> false
let uu___is_BAnd: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2078 -> false
let uu___is_BXor: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2082 -> false
let uu___is_BShiftL: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2086 -> false
let uu___is_BShiftR: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2090 -> false
let uu___is_BNot: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2094 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2098 -> false
let uu___is_Neq: op -> Prims.bool =
  fun projectee  -> match projectee with | Neq  -> true | uu____2102 -> false
let uu___is_Lt: op -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2106 -> false
let uu___is_Lte: op -> Prims.bool =
  fun projectee  -> match projectee with | Lte  -> true | uu____2110 -> false
let uu___is_Gt: op -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2114 -> false
let uu___is_Gte: op -> Prims.bool =
  fun projectee  -> match projectee with | Gte  -> true | uu____2118 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____2122 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____2126 -> false
let uu___is_Xor: op -> Prims.bool =
  fun projectee  -> match projectee with | Xor  -> true | uu____2130 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____2134 -> false
let uu___is_PUnit: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2138 -> false
let uu___is_PBool: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2143 -> false
let __proj__PBool__item___0: pattern -> Prims.bool =
  fun projectee  -> match projectee with | PBool _0 -> _0
let uu___is_PVar: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2155 -> false
let __proj__PVar__item___0: pattern -> binder =
  fun projectee  -> match projectee with | PVar _0 -> _0
let uu___is_PCons: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2173 -> false
let __proj__PCons__item___0:
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PCons _0 -> _0
let uu___is_PTuple: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2205 -> false
let __proj__PTuple__item___0: pattern -> pattern Prims.list =
  fun projectee  -> match projectee with | PTuple _0 -> _0
let uu___is_PRecord: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2229 -> false
let __proj__PRecord__item___0:
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list
  = fun projectee  -> match projectee with | PRecord _0 -> _0
let uu___is_UInt8: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____2258 -> false
let uu___is_UInt16: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2262 -> false
let uu___is_UInt32: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2266 -> false
let uu___is_UInt64: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2270 -> false
let uu___is_Int8: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2274 -> false
let uu___is_Int16: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2278 -> false
let uu___is_Int32: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2282 -> false
let uu___is_Int64: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2286 -> false
let uu___is_Bool: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2290 -> false
let uu___is_CInt: width -> Prims.bool =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____2294 -> false
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
    match projectee with | TInt _0 -> true | uu____2317 -> false
let __proj__TInt__item___0: typ -> width =
  fun projectee  -> match projectee with | TInt _0 -> _0
let uu___is_TBuf: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2329 -> false
let __proj__TBuf__item___0: typ -> typ =
  fun projectee  -> match projectee with | TBuf _0 -> _0
let uu___is_TUnit: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2340 -> false
let uu___is_TQualified: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2351 -> false
let __proj__TQualified__item___0:
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TQualified _0 -> _0
let uu___is_TBool: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2380 -> false
let uu___is_TAny: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2384 -> false
let uu___is_TArrow: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2393 -> false
let __proj__TArrow__item___0: typ -> (typ,typ) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TArrow _0 -> _0
let uu___is_TBound: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2417 -> false
let __proj__TBound__item___0: typ -> Prims.int =
  fun projectee  -> match projectee with | TBound _0 -> _0
let uu___is_TApp: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2441 -> false
let __proj__TApp__item___0:
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TApp _0 -> _0
let uu___is_TTuple: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____2491 -> false
let __proj__TTuple__item___0: typ -> typ Prims.list =
  fun projectee  -> match projectee with | TTuple _0 -> _0
type program = decl Prims.list[@@deriving show]
type ident = Prims.string[@@deriving show]
type fields_t =
  (Prims.string,(typ,Prims.bool) FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
type branches_t =
  (Prims.string,(Prims.string,(typ,Prims.bool) FStar_Pervasives_Native.tuple2)
                  FStar_Pervasives_Native.tuple2 Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
type fsdoc = Prims.string[@@deriving show]
type branch = (pattern,expr) FStar_Pervasives_Native.tuple2[@@deriving show]
type branches = (pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list
[@@deriving show]
type constant = (width,Prims.string) FStar_Pervasives_Native.tuple2[@@deriving
                                                                    show]
type var = Prims.int[@@deriving show]
type lident =
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
[@@deriving show]
type version = Prims.int[@@deriving show]
let current_version: version = Prims.parse_int "24"
type file = (Prims.string,program) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
type binary_format = (version,file Prims.list) FStar_Pervasives_Native.tuple2
[@@deriving show]
let fst3:
  'Auu____2567 'Auu____2568 'Auu____2569 .
    ('Auu____2569,'Auu____2568,'Auu____2567) FStar_Pervasives_Native.tuple3
      -> 'Auu____2569
  = fun uu____2579  -> match uu____2579 with | (x,uu____2587,uu____2588) -> x
let snd3:
  'Auu____2593 'Auu____2594 'Auu____2595 .
    ('Auu____2595,'Auu____2594,'Auu____2593) FStar_Pervasives_Native.tuple3
      -> 'Auu____2594
  = fun uu____2605  -> match uu____2605 with | (uu____2612,x,uu____2614) -> x
let thd3:
  'Auu____2619 'Auu____2620 'Auu____2621 .
    ('Auu____2621,'Auu____2620,'Auu____2619) FStar_Pervasives_Native.tuple3
      -> 'Auu____2619
  = fun uu____2631  -> match uu____2631 with | (uu____2638,uu____2639,x) -> x
let mk_width: Prims.string -> width FStar_Pervasives_Native.option =
  fun uu___401_2645  ->
    match uu___401_2645 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____2648 -> FStar_Pervasives_Native.None
let mk_bool_op: Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___402_2653  ->
    match uu___402_2653 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____2656 -> FStar_Pervasives_Native.None
let is_bool_op: Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None
let mk_op: Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___403_2666  ->
    match uu___403_2666 with
    | "add" -> FStar_Pervasives_Native.Some Add
    | "op_Plus_Hat" -> FStar_Pervasives_Native.Some Add
    | "add_mod" -> FStar_Pervasives_Native.Some AddW
    | "op_Plus_Percent_Hat" -> FStar_Pervasives_Native.Some AddW
    | "sub" -> FStar_Pervasives_Native.Some Sub
    | "op_Subtraction_Hat" -> FStar_Pervasives_Native.Some Sub
    | "sub_mod" -> FStar_Pervasives_Native.Some SubW
    | "op_Subtraction_Percent_Hat" -> FStar_Pervasives_Native.Some SubW
    | "mul" -> FStar_Pervasives_Native.Some Mult
    | "op_Star_Hat" -> FStar_Pervasives_Native.Some Mult
    | "mul_mod" -> FStar_Pervasives_Native.Some MultW
    | "op_Star_Percent_Hat" -> FStar_Pervasives_Native.Some MultW
    | "div" -> FStar_Pervasives_Native.Some Div
    | "op_Slash_Hat" -> FStar_Pervasives_Native.Some Div
    | "div_mod" -> FStar_Pervasives_Native.Some DivW
    | "op_Slash_Percent_Hat" -> FStar_Pervasives_Native.Some DivW
    | "rem" -> FStar_Pervasives_Native.Some Mod
    | "op_Percent_Hat" -> FStar_Pervasives_Native.Some Mod
    | "logor" -> FStar_Pervasives_Native.Some BOr
    | "op_Bar_Hat" -> FStar_Pervasives_Native.Some BOr
    | "logxor" -> FStar_Pervasives_Native.Some BXor
    | "op_Hat_Hat" -> FStar_Pervasives_Native.Some BXor
    | "logand" -> FStar_Pervasives_Native.Some BAnd
    | "op_Amp_Hat" -> FStar_Pervasives_Native.Some BAnd
    | "lognot" -> FStar_Pervasives_Native.Some BNot
    | "shift_right" -> FStar_Pervasives_Native.Some BShiftR
    | "op_Greater_Greater_Hat" -> FStar_Pervasives_Native.Some BShiftR
    | "shift_left" -> FStar_Pervasives_Native.Some BShiftL
    | "op_Less_Less_Hat" -> FStar_Pervasives_Native.Some BShiftL
    | "eq" -> FStar_Pervasives_Native.Some Eq
    | "op_Equals_Hat" -> FStar_Pervasives_Native.Some Eq
    | "op_Greater_Hat" -> FStar_Pervasives_Native.Some Gt
    | "gt" -> FStar_Pervasives_Native.Some Gt
    | "op_Greater_Equals_Hat" -> FStar_Pervasives_Native.Some Gte
    | "gte" -> FStar_Pervasives_Native.Some Gte
    | "op_Less_Hat" -> FStar_Pervasives_Native.Some Lt
    | "lt" -> FStar_Pervasives_Native.Some Lt
    | "op_Less_Equals_Hat" -> FStar_Pervasives_Native.Some Lte
    | "lte" -> FStar_Pervasives_Native.Some Lte
    | uu____2669 -> FStar_Pervasives_Native.None
let is_op: Prims.string -> Prims.bool =
  fun op  -> (mk_op op) <> FStar_Pervasives_Native.None
let is_machine_int: Prims.string -> Prims.bool =
  fun m  -> (mk_width m) <> FStar_Pervasives_Native.None
type env =
  {
  names: name Prims.list;
  names_t: Prims.string Prims.list;
  module_name: Prims.string Prims.list;}[@@deriving show]
and name = {
  pretty: Prims.string;
  mut: Prims.bool;}[@@deriving show]
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
        let uu___408_2780 = env in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___408_2780.names_t);
          module_name = (uu___408_2780.module_name)
        }
let extend_t: env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___409_2787 = env in
      {
        names = (uu___409_2787.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___409_2787.module_name)
      }
let find_name: env -> Prims.string -> name =
  fun env  ->
    fun x  ->
      let uu____2794 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names in
      match uu____2794 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
let is_mutable: env -> Prims.string -> Prims.bool =
  fun env  -> fun x  -> let uu____2806 = find_name env x in uu____2806.mut
let find: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____2821 ->
          let uu____2822 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____2822
let find_t: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____2837 ->
          let uu____2838 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____2838
let add_binders:
  'Auu____2842 .
    env ->
      (Prims.string,'Auu____2842) FStar_Pervasives_Native.tuple2 Prims.list
        -> env
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____2872  ->
             match uu____2872 with
             | (name,uu____2878) -> extend env1 name false) env binders
let rec translate: FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____3019  ->
    match uu____3019 with
    | FStar_Extraction_ML_Syntax.MLLib modules1 ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3079 = m in
               match uu____3079 with
               | ((prefix1,final),uu____3100,uu____3101) ->
                   FStar_String.concat "."
                     (FStar_List.append prefix1 [final]) in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____3133 = translate_module m in
                FStar_Pervasives_Native.Some uu____3133)
             with
             | e ->
                 ((let uu____3142 = FStar_Util.print_exn e in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3142);
                  FStar_Pervasives_Native.None)) modules1
and translate_module:
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
    (FStar_Extraction_ML_Syntax.mlsig,FStar_Extraction_ML_Syntax.mlmodule)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,FStar_Extraction_ML_Syntax.mllib)
    FStar_Pervasives_Native.tuple3 -> file
  =
  fun uu____3143  ->
    match uu____3143 with
    | (module_name,modul,uu____3164) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name] in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____3207 ->
              failwith "Unexpected standalone interface or nested modules" in
        ((FStar_String.concat "_" module_name1), program)
and translate_flags:
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list =
  fun flags  ->
    FStar_List.choose
      (fun uu___404_3222  ->
         match uu___404_3222 with
         | FStar_Extraction_ML_Syntax.Private  ->
             FStar_Pervasives_Native.Some Private
         | FStar_Extraction_ML_Syntax.NoExtract  ->
             FStar_Pervasives_Native.Some NoExtract
         | FStar_Extraction_ML_Syntax.CInline  ->
             FStar_Pervasives_Native.Some CInline
         | FStar_Extraction_ML_Syntax.Substitute  ->
             FStar_Pervasives_Native.Some Substitute
         | FStar_Extraction_ML_Syntax.GCType  ->
             FStar_Pervasives_Native.Some GCType
         | FStar_Extraction_ML_Syntax.Comment s ->
             FStar_Pervasives_Native.Some (Comment s)
         | uu____3226 -> FStar_Pervasives_Native.None) flags
and translate_decl:
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,flags,lbs) ->
          FStar_List.choose (translate_let env flavor flags) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3238 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3240 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____3243 ->
          failwith "todo: translate_decl [MLM_Exn]"
and translate_let:
  env ->
    FStar_Extraction_ML_Syntax.mlletflavor ->
      FStar_Extraction_ML_Syntax.metadata ->
        FStar_Extraction_ML_Syntax.mllb ->
          decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun flavor  ->
      fun flags  ->
        fun lb  ->
          match lb with
          | { FStar_Extraction_ML_Syntax.mllb_name = name;
              FStar_Extraction_ML_Syntax.mllb_tysc =
                FStar_Pervasives_Native.Some (tvars,t0);
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3265;
              FStar_Extraction_ML_Syntax.mllb_def =
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                  FStar_Extraction_ML_Syntax.mlty = uu____3268;
                  FStar_Extraction_ML_Syntax.loc = uu____3269;_};
              FStar_Extraction_ML_Syntax.print_typ = uu____3270;_} ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___405_3289  ->
                     match uu___405_3289 with
                     | FStar_Extraction_ML_Syntax.Assumed  -> true
                     | uu____3290 -> false) flags in
              let env1 =
                if flavor = FStar_Extraction_ML_Syntax.Rec
                then extend env name false
                else env in
              let env2 =
                FStar_List.fold_left
                  (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars in
              let rec find_return_type i uu___406_3304 =
                match uu___406_3304 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun
                    (uu____3305,uu____3306,t) when i > (Prims.parse_int "0")
                    -> find_return_type (i - (Prims.parse_int "1")) t
                | t -> t in
              let t =
                let uu____3310 = find_return_type (FStar_List.length args) t0 in
                translate_type env2 uu____3310 in
              let binders = translate_binders env2 args in
              let env3 = add_binders env2 args in
              let name1 = ((env3.module_name), name) in
              let flags1 =
                match t0 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun
                    (uu____3333,FStar_Extraction_ML_Syntax.E_GHOST
                     ,uu____3334)
                    ->
                    let uu____3335 = translate_flags flags in NoExtract ::
                      uu____3335
                | uu____3338 -> translate_flags flags in
              if assumed
              then
                (if (FStar_List.length tvars) = (Prims.parse_int "0")
                 then
                   let uu____3343 =
                     let uu____3344 =
                       let uu____3359 = translate_type env3 t0 in
                       (FStar_Pervasives_Native.None, name1, uu____3359) in
                     DExternal uu____3344 in
                   FStar_Pervasives_Native.Some uu____3343
                 else FStar_Pervasives_Native.None)
              else
                (try
                   let body1 = translate_expr env3 body in
                   FStar_Pervasives_Native.Some
                     (DFunction
                        (FStar_Pervasives_Native.None, flags1,
                          (FStar_List.length tvars), t, name1, binders,
                          body1))
                 with
                 | e ->
                     let msg = FStar_Util.print_exn e in
                     (FStar_Util.print2_warning
                        "Writing a stub for %s (%s)\n"
                        (FStar_Pervasives_Native.snd name1) msg;
                      (let msg1 =
                         Prims.strcat "This function was not extracted:\n"
                           msg in
                       FStar_Pervasives_Native.Some
                         (DFunction
                            (FStar_Pervasives_Native.None, flags1,
                              (FStar_List.length tvars), t, name1, binders,
                              (EAbortS msg1))))))
          | { FStar_Extraction_ML_Syntax.mllb_name = name;
              FStar_Extraction_ML_Syntax.mllb_tysc =
                FStar_Pervasives_Native.Some (tvars,t0);
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3419;
              FStar_Extraction_ML_Syntax.mllb_def =
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Coerce
                    ({
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                       FStar_Extraction_ML_Syntax.mlty = uu____3422;
                       FStar_Extraction_ML_Syntax.loc = uu____3423;_},uu____3424,uu____3425);
                  FStar_Extraction_ML_Syntax.mlty = uu____3426;
                  FStar_Extraction_ML_Syntax.loc = uu____3427;_};
              FStar_Extraction_ML_Syntax.print_typ = uu____3428;_} ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___405_3447  ->
                     match uu___405_3447 with
                     | FStar_Extraction_ML_Syntax.Assumed  -> true
                     | uu____3448 -> false) flags in
              let env1 =
                if flavor = FStar_Extraction_ML_Syntax.Rec
                then extend env name false
                else env in
              let env2 =
                FStar_List.fold_left
                  (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars in
              let rec find_return_type i uu___406_3462 =
                match uu___406_3462 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun
                    (uu____3463,uu____3464,t) when i > (Prims.parse_int "0")
                    -> find_return_type (i - (Prims.parse_int "1")) t
                | t -> t in
              let t =
                let uu____3468 = find_return_type (FStar_List.length args) t0 in
                translate_type env2 uu____3468 in
              let binders = translate_binders env2 args in
              let env3 = add_binders env2 args in
              let name1 = ((env3.module_name), name) in
              let flags1 =
                match t0 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun
                    (uu____3491,FStar_Extraction_ML_Syntax.E_GHOST
                     ,uu____3492)
                    ->
                    let uu____3493 = translate_flags flags in NoExtract ::
                      uu____3493
                | uu____3496 -> translate_flags flags in
              if assumed
              then
                (if (FStar_List.length tvars) = (Prims.parse_int "0")
                 then
                   let uu____3501 =
                     let uu____3502 =
                       let uu____3517 = translate_type env3 t0 in
                       (FStar_Pervasives_Native.None, name1, uu____3517) in
                     DExternal uu____3502 in
                   FStar_Pervasives_Native.Some uu____3501
                 else FStar_Pervasives_Native.None)
              else
                (try
                   let body1 = translate_expr env3 body in
                   FStar_Pervasives_Native.Some
                     (DFunction
                        (FStar_Pervasives_Native.None, flags1,
                          (FStar_List.length tvars), t, name1, binders,
                          body1))
                 with
                 | e ->
                     let msg = FStar_Util.print_exn e in
                     (FStar_Util.print2_warning
                        "Writing a stub for %s (%s)\n"
                        (FStar_Pervasives_Native.snd name1) msg;
                      (let msg1 =
                         Prims.strcat "This function was not extracted:\n"
                           msg in
                       FStar_Pervasives_Native.Some
                         (DFunction
                            (FStar_Pervasives_Native.None, flags1,
                              (FStar_List.length tvars), t, name1, binders,
                              (EAbortS msg1))))))
          | { FStar_Extraction_ML_Syntax.mllb_name = name;
              FStar_Extraction_ML_Syntax.mllb_tysc =
                FStar_Pervasives_Native.Some ([],t);
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3576;
              FStar_Extraction_ML_Syntax.mllb_def = expr;
              FStar_Extraction_ML_Syntax.print_typ = uu____3578;_} ->
              let flags1 = translate_flags flags in
              let t1 = translate_type env t in
              let name1 = ((env.module_name), name) in
              (try
                 let expr1 = translate_expr env expr in
                 FStar_Pervasives_Native.Some
                   (DGlobal (flags1, name1, t1, expr1))
               with
               | e ->
                   ((let uu____3624 = FStar_Util.print_exn e in
                     FStar_Util.print2_warning
                       "Not translating definition for %s (%s)\n"
                       (FStar_Pervasives_Native.snd name1) uu____3624);
                    FStar_Pervasives_Native.Some
                      (DGlobal (flags1, name1, t1, EAny))))
          | { FStar_Extraction_ML_Syntax.mllb_name = name;
              FStar_Extraction_ML_Syntax.mllb_tysc = ts;
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3637;
              FStar_Extraction_ML_Syntax.mllb_def = uu____3638;
              FStar_Extraction_ML_Syntax.print_typ = uu____3639;_} ->
              (FStar_Util.print1_warning
                 "Not translating definition for %s\n" name;
               (match ts with
                | FStar_Pervasives_Native.Some (idents,t) ->
                    let uu____3650 =
                      FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                    FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                      (FStar_String.concat ", " idents) uu____3650
                | FStar_Pervasives_Native.None  -> ());
               FStar_Pervasives_Native.None)
and translate_type_decl:
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ty  ->
      match ty with
      | (assumed,name,_mangled_name,args,uu____3661,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Abbrev t)) ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args in
          if assumed
          then FStar_Pervasives_Native.None
          else
            (let uu____3686 =
               let uu____3687 =
                 let uu____3700 = translate_type env1 t in
                 (name1, (FStar_List.length args), uu____3700) in
               DTypeAlias uu____3687 in
             FStar_Pervasives_Native.Some uu____3686)
      | (uu____3707,name,_mangled_name,args,uu____3711,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args in
          let uu____3739 =
            let uu____3740 =
              let uu____3763 =
                FStar_List.map
                  (fun uu____3790  ->
                     match uu____3790 with
                     | (f,t) ->
                         let uu____3805 =
                           let uu____3810 = translate_type env1 t in
                           (uu____3810, false) in
                         (f, uu____3805)) fields in
              (name1, (FStar_List.length args), uu____3763) in
            DTypeFlat uu____3740 in
          FStar_Pervasives_Native.Some uu____3739
      | (uu____3831,name,_mangled_name,args,attrs,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
          let name1 = ((env.module_name), name) in
          let flags = translate_flags attrs in
          let env1 = FStar_List.fold_left extend_t env args in
          let uu____3868 =
            let uu____3869 =
              let uu____3902 =
                FStar_List.map
                  (fun uu____3947  ->
                     match uu____3947 with
                     | (cons1,ts) ->
                         let uu____3986 =
                           FStar_List.map
                             (fun uu____4013  ->
                                match uu____4013 with
                                | (name2,t) ->
                                    let uu____4028 =
                                      let uu____4033 = translate_type env1 t in
                                      (uu____4033, false) in
                                    (name2, uu____4028)) ts in
                         (cons1, uu____3986)) branches in
              (name1, flags, (FStar_List.length args), uu____3902) in
            DTypeVariant uu____3869 in
          FStar_Pervasives_Native.Some uu____3868
      | (uu____4072,name,_mangled_name,uu____4075,uu____4076,uu____4077) ->
          (FStar_Util.print1_warning
             "Not translating type definition for %s\n" name;
           FStar_Pervasives_Native.None)
and translate_type: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4090 = find_t env name in TBound uu____4090
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4092,t2) ->
          let uu____4094 =
            let uu____4099 = translate_type env t1 in
            let uu____4100 = translate_type env t2 in
            (uu____4099, uu____4100) in
          TArrow uu____4094
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4104 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4104 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4108 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4108 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4120 = FStar_Util.must (mk_width m) in TInt uu____4120
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4132 = FStar_Util.must (mk_width m) in TInt uu____4132
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4137 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4137 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4142 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4142 = "FStar.Buffer.buffer" ->
          let uu____4143 = translate_type env arg in TBuf uu____4143
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4144::[],p) when
          let uu____4148 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4148 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4186 = FStar_List.map (translate_type env) args in
          TTuple uu____4186
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4195 =
              let uu____4208 = FStar_List.map (translate_type env) args in
              (lid, uu____4208) in
            TApp uu____4195
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4217 = FStar_List.map (translate_type env) ts in
          TTuple uu____4217
and translate_binders:
  env ->
    (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2 Prims.list -> binder Prims.list
  = fun env  -> fun args  -> FStar_List.map (translate_binder env) args
and translate_binder:
  env ->
    (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2 -> binder
  =
  fun env  ->
    fun uu____4233  ->
      match uu____4233 with
      | (name,typ) ->
          let uu____4240 = translate_type env typ in
          { name; typ = uu____4240; mut = false }
and translate_expr: env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____4245 = find env name in EBound uu____4245
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4250 =
            let uu____4255 = FStar_Util.must (mk_op op) in
            let uu____4256 = FStar_Util.must (mk_width m) in
            (uu____4255, uu____4256) in
          EOp uu____4250
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4260 =
            let uu____4265 = FStar_Util.must (mk_bool_op op) in
            (uu____4265, Bool) in
          EOp uu____4260
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags,{ FStar_Extraction_ML_Syntax.mllb_name = name;
                           FStar_Extraction_ML_Syntax.mllb_tysc =
                             FStar_Pervasives_Native.Some ([],typ);
                           FStar_Extraction_ML_Syntax.mllb_add_unit =
                             add_unit;
                           FStar_Extraction_ML_Syntax.mllb_def = body;
                           FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let is_mut =
            FStar_Util.for_some
              (fun uu___407_4295  ->
                 match uu___407_4295 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____4296 -> false) flags in
          let uu____4297 =
            if is_mut
            then
              let uu____4306 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____4311 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4311 = "FStar.ST.stackref" -> t
                | uu____4312 ->
                    let uu____4313 =
                      let uu____4314 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____4314 in
                    failwith uu____4313 in
              let uu____4317 =
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
                      (uu____4318,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____4320;
                    FStar_Extraction_ML_Syntax.loc = uu____4321;_} -> body1
                | uu____4324 ->
                    failwith "unexpected: bad desugaring of Mutable" in
              (uu____4306, uu____4317)
            else (typ, body) in
          (match uu____4297 with
           | (typ1,body1) ->
               let binder =
                 let uu____4329 = translate_type env typ1 in
                 { name; typ = uu____4329; mut = is_mut } in
               let body2 = translate_expr env body1 in
               let env1 = extend env name is_mut in
               let continuation1 = translate_expr env1 continuation in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4355 =
            let uu____4366 = translate_expr env expr in
            let uu____4367 = translate_branches env branches in
            (uu____4366, uu____4367) in
          EMatch uu____4355
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4381;
             FStar_Extraction_ML_Syntax.loc = uu____4382;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                v1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4384;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4385;_}::[])
          when
          (let uu____4390 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4390 = "FStar.HyperStack.ST.op_Bang") && (is_mutable env v1)
          -> let uu____4391 = find env v1 in EBound uu____4391
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4393;
             FStar_Extraction_ML_Syntax.loc = uu____4394;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                v1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4396;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4397;_}::e1::[])
          when
          (let uu____4403 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4403 = "FStar.HyperStack.ST.op_Colon_Equals") &&
            (is_mutable env v1)
          ->
          let uu____4404 =
            let uu____4409 =
              let uu____4410 = find env v1 in EBound uu____4410 in
            let uu____4411 = translate_expr env e1 in
            (uu____4409, uu____4411) in
          EAssign uu____4404
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4413;
                  FStar_Extraction_ML_Syntax.loc = uu____4414;_},uu____4415);
             FStar_Extraction_ML_Syntax.mlty = uu____4416;
             FStar_Extraction_ML_Syntax.loc = uu____4417;_},e1::e2::[])
          when
          (let uu____4428 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4428 = "FStar.Buffer.index") ||
            (let uu____4430 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4430 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____4431 =
            let uu____4436 = translate_expr env e1 in
            let uu____4437 = translate_expr env e2 in
            (uu____4436, uu____4437) in
          EBufRead uu____4431
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4439;
                  FStar_Extraction_ML_Syntax.loc = uu____4440;_},uu____4441);
             FStar_Extraction_ML_Syntax.mlty = uu____4442;
             FStar_Extraction_ML_Syntax.loc = uu____4443;_},e1::e2::[])
          when
          let uu____4452 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4452 = "FStar.Buffer.create" ->
          let uu____4453 =
            let uu____4460 = translate_expr env e1 in
            let uu____4461 = translate_expr env e2 in
            (Stack, uu____4460, uu____4461) in
          EBufCreate uu____4453
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4463;
                  FStar_Extraction_ML_Syntax.loc = uu____4464;_},uu____4465);
             FStar_Extraction_ML_Syntax.mlty = uu____4466;
             FStar_Extraction_ML_Syntax.loc = uu____4467;_},_e0::e1::e2::[])
          when
          let uu____4477 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4477 = "FStar.Buffer.rcreate" ->
          let uu____4478 =
            let uu____4485 = translate_expr env e1 in
            let uu____4486 = translate_expr env e2 in
            (Eternal, uu____4485, uu____4486) in
          EBufCreate uu____4478
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4488;
                  FStar_Extraction_ML_Syntax.loc = uu____4489;_},uu____4490);
             FStar_Extraction_ML_Syntax.mlty = uu____4491;
             FStar_Extraction_ML_Syntax.loc = uu____4492;_},e2::[])
          when
          let uu____4500 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4500 = "FStar.Buffer.createL" ->
          let rec list_elements1 acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements1 (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____4538 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!" in
          let list_elements2 = list_elements1 [] in
          let uu____4546 =
            let uu____4553 =
              let uu____4556 = list_elements2 e2 in
              FStar_List.map (translate_expr env) uu____4556 in
            (Stack, uu____4553) in
          EBufCreateL uu____4546
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4562;
                  FStar_Extraction_ML_Syntax.loc = uu____4563;_},uu____4564);
             FStar_Extraction_ML_Syntax.mlty = uu____4565;
             FStar_Extraction_ML_Syntax.loc = uu____4566;_},e1::e2::_e3::[])
          when
          let uu____4576 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4576 = "FStar.Buffer.sub" ->
          let uu____4577 =
            let uu____4582 = translate_expr env e1 in
            let uu____4583 = translate_expr env e2 in
            (uu____4582, uu____4583) in
          EBufSub uu____4577
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4585;
                  FStar_Extraction_ML_Syntax.loc = uu____4586;_},uu____4587);
             FStar_Extraction_ML_Syntax.mlty = uu____4588;
             FStar_Extraction_ML_Syntax.loc = uu____4589;_},e1::e2::[])
          when
          let uu____4598 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4598 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4600;
                  FStar_Extraction_ML_Syntax.loc = uu____4601;_},uu____4602);
             FStar_Extraction_ML_Syntax.mlty = uu____4603;
             FStar_Extraction_ML_Syntax.loc = uu____4604;_},e1::e2::[])
          when
          let uu____4613 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4613 = "FStar.Buffer.offset" ->
          let uu____4614 =
            let uu____4619 = translate_expr env e1 in
            let uu____4620 = translate_expr env e2 in
            (uu____4619, uu____4620) in
          EBufSub uu____4614
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4622;
                  FStar_Extraction_ML_Syntax.loc = uu____4623;_},uu____4624);
             FStar_Extraction_ML_Syntax.mlty = uu____4625;
             FStar_Extraction_ML_Syntax.loc = uu____4626;_},e1::e2::e3::[])
          when
          (let uu____4638 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4638 = "FStar.Buffer.upd") ||
            (let uu____4640 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4640 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____4641 =
            let uu____4648 = translate_expr env e1 in
            let uu____4649 = translate_expr env e2 in
            let uu____4650 = translate_expr env e3 in
            (uu____4648, uu____4649, uu____4650) in
          EBufWrite uu____4641
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4652;
             FStar_Extraction_ML_Syntax.loc = uu____4653;_},uu____4654::[])
          when
          let uu____4657 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4657 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4659;
             FStar_Extraction_ML_Syntax.loc = uu____4660;_},uu____4661::[])
          when
          let uu____4664 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4664 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4666;
                  FStar_Extraction_ML_Syntax.loc = uu____4667;_},uu____4668);
             FStar_Extraction_ML_Syntax.mlty = uu____4669;
             FStar_Extraction_ML_Syntax.loc = uu____4670;_},e1::e2::e3::e4::e5::[])
          when
          let uu____4682 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4682 = "FStar.Buffer.blit" ->
          let uu____4683 =
            let uu____4694 = translate_expr env e1 in
            let uu____4695 = translate_expr env e2 in
            let uu____4696 = translate_expr env e3 in
            let uu____4697 = translate_expr env e4 in
            let uu____4698 = translate_expr env e5 in
            (uu____4694, uu____4695, uu____4696, uu____4697, uu____4698) in
          EBufBlit uu____4683
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4700;
                  FStar_Extraction_ML_Syntax.loc = uu____4701;_},uu____4702);
             FStar_Extraction_ML_Syntax.mlty = uu____4703;
             FStar_Extraction_ML_Syntax.loc = uu____4704;_},e1::e2::e3::[])
          when
          let uu____4714 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4714 = "FStar.Buffer.fill" ->
          let uu____4715 =
            let uu____4722 = translate_expr env e1 in
            let uu____4723 = translate_expr env e2 in
            let uu____4724 = translate_expr env e3 in
            (uu____4722, uu____4723, uu____4724) in
          EBufFill uu____4715
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4726;
             FStar_Extraction_ML_Syntax.loc = uu____4727;_},uu____4728::[])
          when
          let uu____4731 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4731 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4733;
             FStar_Extraction_ML_Syntax.loc = uu____4734;_},e1::[])
          when
          let uu____4738 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4738 = "Obj.repr" ->
          let uu____4739 =
            let uu____4744 = translate_expr env e1 in (uu____4744, TAny) in
          ECast uu____4739
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____4747;
             FStar_Extraction_ML_Syntax.loc = uu____4748;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____4756 = FStar_Util.must (mk_width m) in
          let uu____4757 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____4756 uu____4757 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____4759;
             FStar_Extraction_ML_Syntax.loc = uu____4760;_},args)
          when is_bool_op op ->
          let uu____4768 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____4768 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____4770;
             FStar_Extraction_ML_Syntax.loc = uu____4771;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4773;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4774;_}::[])
          when is_machine_int m ->
          let uu____4789 =
            let uu____4794 = FStar_Util.must (mk_width m) in (uu____4794, c) in
          EConstant uu____4789
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____4796;
             FStar_Extraction_ML_Syntax.loc = uu____4797;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4799;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4800;_}::[])
          when is_machine_int m ->
          let uu____4815 =
            let uu____4820 = FStar_Util.must (mk_width m) in (uu____4820, c) in
          EConstant uu____4815
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____4821;
             FStar_Extraction_ML_Syntax.loc = uu____4822;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4824;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4825;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____4831 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____4832;
             FStar_Extraction_ML_Syntax.loc = uu____4833;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4835;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4836;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____4842 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____4844;
             FStar_Extraction_ML_Syntax.loc = uu____4845;_},arg::[])
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
            let uu____4852 =
              let uu____4857 = translate_expr env arg in
              (uu____4857, (TInt UInt64)) in
            ECast uu____4852
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____4859 =
                 let uu____4864 = translate_expr env arg in
                 (uu____4864, (TInt UInt32)) in
               ECast uu____4859)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____4866 =
                   let uu____4871 = translate_expr env arg in
                   (uu____4871, (TInt UInt16)) in
                 ECast uu____4866)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____4873 =
                     let uu____4878 = translate_expr env arg in
                     (uu____4878, (TInt UInt8)) in
                   ECast uu____4873)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____4880 =
                       let uu____4885 = translate_expr env arg in
                       (uu____4885, (TInt Int64)) in
                     ECast uu____4880)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____4887 =
                         let uu____4892 = translate_expr env arg in
                         (uu____4892, (TInt Int32)) in
                       ECast uu____4887)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____4894 =
                           let uu____4899 = translate_expr env arg in
                           (uu____4899, (TInt Int16)) in
                         ECast uu____4894)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____4901 =
                             let uu____4906 = translate_expr env arg in
                             (uu____4906, (TInt Int8)) in
                           ECast uu____4901)
                        else
                          (let uu____4908 =
                             let uu____4915 =
                               let uu____4918 = translate_expr env arg in
                               [uu____4918] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____4915) in
                           EApp uu____4908)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____4929 =
            let uu____4936 = translate_expr env head1 in
            let uu____4937 = FStar_List.map (translate_expr env) args in
            (uu____4936, uu____4937) in
          EApp uu____4929
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____4948 =
            let uu____4955 = translate_expr env head1 in
            let uu____4956 = FStar_List.map (translate_type env) ty_args in
            (uu____4955, uu____4956) in
          ETypApp uu____4948
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____4964 =
            let uu____4969 = translate_expr env e1 in
            let uu____4970 = translate_type env t_to in
            (uu____4969, uu____4970) in
          ECast uu____4964
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____4971,fields) ->
          let uu____4989 =
            let uu____5000 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5001 =
              FStar_List.map
                (fun uu____5020  ->
                   match uu____5020 with
                   | (field,expr) ->
                       let uu____5031 = translate_expr env expr in
                       (field, uu____5031)) fields in
            (uu____5000, uu____5001) in
          EFlat uu____4989
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5040 =
            let uu____5047 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____5048 = translate_expr env e1 in
            (uu____5047, uu____5048, (FStar_Pervasives_Native.snd path)) in
          EField uu____5040
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5051 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5065) ->
          let uu____5070 =
            let uu____5071 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1 in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5071 in
          failwith uu____5070
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5077 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____5077
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5083 = FStar_List.map (translate_expr env) es in
          ETuple uu____5083
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5086,cons1),es) ->
          let uu____5103 =
            let uu____5112 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5113 = FStar_List.map (translate_expr env) es in
            (uu____5112, cons1, uu____5113) in
          ECons uu____5103
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args in
          let env1 = add_binders env args in
          let uu____5136 =
            let uu____5145 = translate_expr env1 body in
            let uu____5146 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty in
            (binders, uu____5145, uu____5146) in
          EFun uu____5136
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5156 =
            let uu____5163 = translate_expr env e1 in
            let uu____5164 = translate_expr env e2 in
            let uu____5165 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31 in
            (uu____5163, uu____5164, uu____5165) in
          EIfThenElse uu____5156
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5167 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5174 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____5189 ->
          failwith "todo: translate_expr [MLE_Coerce]"
and assert_lid: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____5204 =
              let uu____5217 = FStar_List.map (translate_type env) ts in
              (lid, uu____5217) in
            TApp uu____5204
          else TQualified lid
      | uu____5223 -> failwith "invalid argument: assert_lid"
and translate_branches:
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern,FStar_Extraction_ML_Syntax.mlexpr
                                            FStar_Pervasives_Native.option,
      FStar_Extraction_ML_Syntax.mlexpr) FStar_Pervasives_Native.tuple3
      Prims.list -> (pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  -> fun branches  -> FStar_List.map (translate_branch env) branches
and translate_branch:
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern,FStar_Extraction_ML_Syntax.mlexpr
                                            FStar_Pervasives_Native.option,
      FStar_Extraction_ML_Syntax.mlexpr) FStar_Pervasives_Native.tuple3 ->
      (pattern,expr) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____5249  ->
      match uu____5249 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____5275 = translate_pat env pat in
            (match uu____5275 with
             | (env1,pat1) ->
                 let uu____5286 = translate_expr env1 expr in
                 (pat1, uu____5286))
          else failwith "todo: translate_branch"
and translate_pat:
  env ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      (env,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Unit ) -> (env, PUnit)
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Bool b) -> (env, (PBool b))
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name false in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_" false in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5302,cons1),ps) ->
          let uu____5319 =
            FStar_List.fold_left
              (fun uu____5339  ->
                 fun p1  ->
                   match uu____5339 with
                   | (env1,acc) ->
                       let uu____5359 = translate_pat env1 p1 in
                       (match uu____5359 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____5319 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____5388,ps) ->
          let uu____5406 =
            FStar_List.fold_left
              (fun uu____5440  ->
                 fun uu____5441  ->
                   match (uu____5440, uu____5441) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____5510 = translate_pat env1 p1 in
                       (match uu____5510 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps in
          (match uu____5406 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____5572 =
            FStar_List.fold_left
              (fun uu____5592  ->
                 fun p1  ->
                   match uu____5592 with
                   | (env1,acc) ->
                       let uu____5612 = translate_pat env1 p1 in
                       (match uu____5612 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____5572 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____5639 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____5644 ->
          failwith "todo: translate_pat [MLP_Branch]"
and translate_constant: FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____5654) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____5669 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____5670 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____5671 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____5672 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        EConstant (CInt, s)
and mk_op_app:
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr
  =
  fun env  ->
    fun w  ->
      fun op  ->
        fun args  ->
          let uu____5692 =
            let uu____5699 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____5699) in
          EApp uu____5692