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
    match projectee with | DGlobal _0 -> true | uu____524 -> false
let __proj__DGlobal__item___0:
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,typ,expr)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DGlobal _0 -> _0
let uu___is_DFunction: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____612 -> false
let __proj__DFunction__item___0:
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr) FStar_Pervasives_Native.tuple7
  = fun projectee  -> match projectee with | DFunction _0 -> _0
let uu___is_DTypeAlias: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____716 -> false
let __proj__DTypeAlias__item___0:
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      Prims.int,typ) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0
let uu___is_DTypeFlat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____788 -> false
let __proj__DTypeFlat__item___0:
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      Prims.int,(Prims.string,(typ,Prims.bool) FStar_Pervasives_Native.tuple2)
                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0
let uu___is_DExternal: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____882 -> false
let __proj__DExternal__item___0:
  decl ->
    (cc FStar_Pervasives_Native.option,(Prims.string Prims.list,Prims.string)
                                         FStar_Pervasives_Native.tuple2,
      typ) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DExternal _0 -> _0
let uu___is_DTypeVariant: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____970 -> false
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
    match projectee with | StdCall  -> true | uu____1079 -> false
let uu___is_CDecl: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1084 -> false
let uu___is_FastCall: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1089 -> false
let uu___is_Private: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1094 -> false
let uu___is_NoExtract: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____1099 -> false
let uu___is_CInline: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1104 -> false
let uu___is_Substitute: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1109 -> false
let uu___is_GCType: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1114 -> false
let uu___is_Comment: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1120 -> false
let __proj__Comment__item___0: flag -> Prims.string =
  fun projectee  -> match projectee with | Comment _0 -> _0
let uu___is_Eternal: lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1133 -> false
let uu___is_Stack: lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1138 -> false
let uu___is_EBound: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1144 -> false
let __proj__EBound__item___0: expr -> Prims.int =
  fun projectee  -> match projectee with | EBound _0 -> _0
let uu___is_EQualified: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1164 -> false
let __proj__EQualified__item___0:
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EQualified _0 -> _0
let uu___is_EConstant: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1200 -> false
let __proj__EConstant__item___0:
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EConstant _0 -> _0
let uu___is_EUnit: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1225 -> false
let uu___is_EApp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1237 -> false
let __proj__EApp__item___0:
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EApp _0 -> _0
let uu___is_ETypApp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1275 -> false
let __proj__ETypApp__item___0:
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ETypApp _0 -> _0
let uu___is_ELet: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1313 -> false
let __proj__ELet__item___0:
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ELet _0 -> _0
let uu___is_EIfThenElse: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1351 -> false
let __proj__EIfThenElse__item___0:
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0
let uu___is_ESequence: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1385 -> false
let __proj__ESequence__item___0: expr -> expr Prims.list =
  fun projectee  -> match projectee with | ESequence _0 -> _0
let uu___is_EAssign: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1409 -> false
let __proj__EAssign__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EAssign _0 -> _0
let uu___is_EBufCreate: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____1441 -> false
let __proj__EBufCreate__item___0:
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0
let uu___is_EBufRead: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____1477 -> false
let __proj__EBufRead__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufRead _0 -> _0
let uu___is_EBufWrite: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____1509 -> false
let __proj__EBufWrite__item___0:
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0
let uu___is_EBufSub: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____1545 -> false
let __proj__EBufSub__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufSub _0 -> _0
let uu___is_EBufBlit: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____1581 -> false
let __proj__EBufBlit__item___0:
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5 =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0
let uu___is_EMatch: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____1635 -> false
let __proj__EMatch__item___0:
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EMatch _0 -> _0
let uu___is_EOp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1683 -> false
let __proj__EOp__item___0: expr -> (op,width) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EOp _0 -> _0
let uu___is_ECast: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1713 -> false
let __proj__ECast__item___0:
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ECast _0 -> _0
let uu___is_EPushFrame: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1738 -> false
let uu___is_EPopFrame: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1743 -> false
let uu___is_EBool: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1749 -> false
let __proj__EBool__item___0: expr -> Prims.bool =
  fun projectee  -> match projectee with | EBool _0 -> _0
let uu___is_EAny: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1762 -> false
let uu___is_EAbort: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1767 -> false
let uu___is_EReturn: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1773 -> false
let __proj__EReturn__item___0: expr -> expr =
  fun projectee  -> match projectee with | EReturn _0 -> _0
let uu___is_EFlat: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1797 -> false
let __proj__EFlat__item___0:
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EFlat _0 -> _0
let uu___is_EField: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____1847 -> false
let __proj__EField__item___0:
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EField _0 -> _0
let uu___is_EWhile: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____1883 -> false
let __proj__EWhile__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EWhile _0 -> _0
let uu___is_EBufCreateL: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____1915 -> false
let __proj__EBufCreateL__item___0:
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0
let uu___is_ETuple: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____1949 -> false
let __proj__ETuple__item___0: expr -> expr Prims.list =
  fun projectee  -> match projectee with | ETuple _0 -> _0
let uu___is_ECons: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____1977 -> false
let __proj__ECons__item___0:
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ECons _0 -> _0
let uu___is_EBufFill: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2021 -> false
let __proj__EBufFill__item___0:
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufFill _0 -> _0
let uu___is_EString: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2053 -> false
let __proj__EString__item___0: expr -> Prims.string =
  fun projectee  -> match projectee with | EString _0 -> _0
let uu___is_EFun: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2075 -> false
let __proj__EFun__item___0:
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EFun _0 -> _0
let uu___is_EAbortS: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2113 -> false
let __proj__EAbortS__item___0: expr -> Prims.string =
  fun projectee  -> match projectee with | EAbortS _0 -> _0
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____2126 -> false
let uu___is_AddW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2131 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____2136 -> false
let uu___is_SubW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2141 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____2146 -> false
let uu___is_DivW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2151 -> false
let uu___is_Mult: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2156 -> false
let uu___is_MultW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2161 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____2166 -> false
let uu___is_BOr: op -> Prims.bool =
  fun projectee  -> match projectee with | BOr  -> true | uu____2171 -> false
let uu___is_BAnd: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2176 -> false
let uu___is_BXor: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2181 -> false
let uu___is_BShiftL: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2186 -> false
let uu___is_BShiftR: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2191 -> false
let uu___is_BNot: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2196 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2201 -> false
let uu___is_Neq: op -> Prims.bool =
  fun projectee  -> match projectee with | Neq  -> true | uu____2206 -> false
let uu___is_Lt: op -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2211 -> false
let uu___is_Lte: op -> Prims.bool =
  fun projectee  -> match projectee with | Lte  -> true | uu____2216 -> false
let uu___is_Gt: op -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2221 -> false
let uu___is_Gte: op -> Prims.bool =
  fun projectee  -> match projectee with | Gte  -> true | uu____2226 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____2231 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____2236 -> false
let uu___is_Xor: op -> Prims.bool =
  fun projectee  -> match projectee with | Xor  -> true | uu____2241 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____2246 -> false
let uu___is_PUnit: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2251 -> false
let uu___is_PBool: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2257 -> false
let __proj__PBool__item___0: pattern -> Prims.bool =
  fun projectee  -> match projectee with | PBool _0 -> _0
let uu___is_PVar: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2271 -> false
let __proj__PVar__item___0: pattern -> binder =
  fun projectee  -> match projectee with | PVar _0 -> _0
let uu___is_PCons: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2291 -> false
let __proj__PCons__item___0:
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PCons _0 -> _0
let uu___is_PTuple: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2325 -> false
let __proj__PTuple__item___0: pattern -> pattern Prims.list =
  fun projectee  -> match projectee with | PTuple _0 -> _0
let uu___is_PRecord: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2351 -> false
let __proj__PRecord__item___0:
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list
  = fun projectee  -> match projectee with | PRecord _0 -> _0
let uu___is_UInt8: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____2382 -> false
let uu___is_UInt16: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2387 -> false
let uu___is_UInt32: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2392 -> false
let uu___is_UInt64: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2397 -> false
let uu___is_Int8: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2402 -> false
let uu___is_Int16: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2407 -> false
let uu___is_Int32: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2412 -> false
let uu___is_Int64: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2417 -> false
let uu___is_Bool: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2422 -> false
let uu___is_CInt: width -> Prims.bool =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____2427 -> false
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
    match projectee with | TInt _0 -> true | uu____2454 -> false
let __proj__TInt__item___0: typ -> width =
  fun projectee  -> match projectee with | TInt _0 -> _0
let uu___is_TBuf: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2468 -> false
let __proj__TBuf__item___0: typ -> typ =
  fun projectee  -> match projectee with | TBuf _0 -> _0
let uu___is_TUnit: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2481 -> false
let uu___is_TQualified: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2493 -> false
let __proj__TQualified__item___0:
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TQualified _0 -> _0
let uu___is_TBool: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2524 -> false
let uu___is_TAny: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2529 -> false
let uu___is_TArrow: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2539 -> false
let __proj__TArrow__item___0: typ -> (typ,typ) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TArrow _0 -> _0
let uu___is_TBound: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2565 -> false
let __proj__TBound__item___0: typ -> Prims.int =
  fun projectee  -> match projectee with | TBound _0 -> _0
let uu___is_TApp: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2591 -> false
let __proj__TApp__item___0:
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TApp _0 -> _0
let uu___is_TTuple: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____2643 -> false
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
  'Auu____2724 'Auu____2725 'Auu____2726 .
    ('Auu____2726,'Auu____2725,'Auu____2724) FStar_Pervasives_Native.tuple3
      -> 'Auu____2726
  = fun uu____2736  -> match uu____2736 with | (x,uu____2744,uu____2745) -> x
let snd3:
  'Auu____2754 'Auu____2755 'Auu____2756 .
    ('Auu____2756,'Auu____2755,'Auu____2754) FStar_Pervasives_Native.tuple3
      -> 'Auu____2755
  = fun uu____2766  -> match uu____2766 with | (uu____2773,x,uu____2775) -> x
let thd3:
  'Auu____2784 'Auu____2785 'Auu____2786 .
    ('Auu____2786,'Auu____2785,'Auu____2784) FStar_Pervasives_Native.tuple3
      -> 'Auu____2784
  = fun uu____2796  -> match uu____2796 with | (uu____2803,uu____2804,x) -> x
let mk_width: Prims.string -> width FStar_Pervasives_Native.option =
  fun uu___127_2811  ->
    match uu___127_2811 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____2814 -> FStar_Pervasives_Native.None
let mk_bool_op: Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___128_2820  ->
    match uu___128_2820 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____2823 -> FStar_Pervasives_Native.None
let is_bool_op: Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None
let mk_op: Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___129_2835  ->
    match uu___129_2835 with
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
    | uu____2838 -> FStar_Pervasives_Native.None
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
        let uu___134_2960 = env in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___134_2960.names_t);
          module_name = (uu___134_2960.module_name)
        }
let extend_t: env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___135_2969 = env in
      {
        names = (uu___135_2969.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___135_2969.module_name)
      }
let find_name: env -> Prims.string -> name =
  fun env  ->
    fun x  ->
      let uu____2978 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names in
      match uu____2978 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
let is_mutable: env -> Prims.string -> Prims.bool =
  fun env  -> fun x  -> let uu____2992 = find_name env x in uu____2992.mut
let find: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____3009 ->
          let uu____3010 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____3010
let find_t: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____3027 ->
          let uu____3028 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____3028
let add_binders:
  'Auu____3037 'Auu____3038 .
    env ->
      ((Prims.string,'Auu____3038) FStar_Pervasives_Native.tuple2,'Auu____3037)
        FStar_Pervasives_Native.tuple2 Prims.list -> env
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____3081  ->
             match uu____3081 with
             | ((name,uu____3091),uu____3092) -> extend env1 name false) env
        binders
let rec translate: FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____3221  ->
    match uu____3221 with
    | FStar_Extraction_ML_Syntax.MLLib modules1 ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3281 = m in
               match uu____3281 with
               | ((prefix1,final),uu____3302,uu____3303) ->
                   FStar_String.concat "."
                     (FStar_List.append prefix1 [final]) in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____3335 = translate_module m in
                FStar_Pervasives_Native.Some uu____3335)
             with
             | e ->
                 ((let uu____3344 = FStar_Util.print_exn e in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3344);
                  FStar_Pervasives_Native.None)) modules1
and translate_module:
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
    (FStar_Extraction_ML_Syntax.mlsig,FStar_Extraction_ML_Syntax.mlmodule)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,FStar_Extraction_ML_Syntax.mllib)
    FStar_Pervasives_Native.tuple3 -> file
  =
  fun uu____3345  ->
    match uu____3345 with
    | (module_name,modul,uu____3366) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name] in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.filter_map (translate_decl (empty module_name1))
                decls
          | uu____3409 ->
              failwith "Unexpected standalone interface or nested modules" in
        ((FStar_String.concat "_" module_name1), program)
and translate_flags:
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list =
  fun flags  ->
    FStar_List.choose
      (fun uu___130_3424  ->
         match uu___130_3424 with
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
         | uu____3428 -> FStar_Pervasives_Native.None) flags
and translate_decl:
  env ->
    FStar_Extraction_ML_Syntax.mlmodule1 ->
      decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____3436);
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3439;
                          FStar_Extraction_ML_Syntax.mllb_def =
                            {
                              FStar_Extraction_ML_Syntax.expr =
                                FStar_Extraction_ML_Syntax.MLE_Fun
                                (args,body);
                              FStar_Extraction_ML_Syntax.mlty = uu____3442;
                              FStar_Extraction_ML_Syntax.loc = uu____3443;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____3444;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___131_3465  ->
                 match uu___131_3465 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____3466 -> false) flags in
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun uu____3479  ->
                   match uu____3479 with
                   | (name1,uu____3485) -> extend_t env2 name1) env1 tvars in
          let rec find_return_type i uu___132_3492 =
            match uu___132_3492 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3493,uu____3494,t)
                when i > (Prims.parse_int "0") ->
                find_return_type (i - (Prims.parse_int "1")) t
            | t -> t in
          let t =
            let uu____3498 = find_return_type (FStar_List.length args) t0 in
            translate_type env2 uu____3498 in
          let binders = translate_binders env2 args in
          let env3 = add_binders env2 args in
          let name1 = ((env3.module_name), name) in
          let flags1 =
            match t0 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun
                (uu____3521,FStar_Extraction_ML_Syntax.E_GHOST ,uu____3522)
                ->
                let uu____3523 = translate_flags flags in NoExtract ::
                  uu____3523
            | uu____3526 -> translate_flags flags in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
               let uu____3531 =
                 let uu____3532 =
                   let uu____3547 = translate_type env3 t0 in
                   (FStar_Pervasives_Native.None, name1, uu____3547) in
                 DExternal uu____3532 in
               FStar_Pervasives_Native.Some uu____3531
             else FStar_Pervasives_Native.None)
          else
            (try
               let body1 = translate_expr env3 body in
               FStar_Pervasives_Native.Some
                 (DFunction
                    (FStar_Pervasives_Native.None, flags1,
                      (FStar_List.length tvars), t, name1, binders, body1))
             with
             | e ->
                 let msg = FStar_Util.print_exn e in
                 (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n"
                    (FStar_Pervasives_Native.snd name1) msg;
                  (let msg1 =
                     Prims.strcat "This function was not extracted:\n" msg in
                   FStar_Pervasives_Native.Some
                     (DFunction
                        (FStar_Pervasives_Native.None, flags1,
                          (FStar_List.length tvars), t, name1, binders,
                          (EAbortS msg1))))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____3607);
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3610;
                          FStar_Extraction_ML_Syntax.mllb_def =
                            {
                              FStar_Extraction_ML_Syntax.expr =
                                FStar_Extraction_ML_Syntax.MLE_Coerce
                                ({
                                   FStar_Extraction_ML_Syntax.expr =
                                     FStar_Extraction_ML_Syntax.MLE_Fun
                                     (args,body);
                                   FStar_Extraction_ML_Syntax.mlty =
                                     uu____3613;
                                   FStar_Extraction_ML_Syntax.loc =
                                     uu____3614;_},uu____3615,uu____3616);
                              FStar_Extraction_ML_Syntax.mlty = uu____3617;
                              FStar_Extraction_ML_Syntax.loc = uu____3618;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____3619;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___131_3640  ->
                 match uu___131_3640 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____3641 -> false) flags in
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun uu____3654  ->
                   match uu____3654 with
                   | (name1,uu____3660) -> extend_t env2 name1) env1 tvars in
          let rec find_return_type i uu___132_3667 =
            match uu___132_3667 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3668,uu____3669,t)
                when i > (Prims.parse_int "0") ->
                find_return_type (i - (Prims.parse_int "1")) t
            | t -> t in
          let t =
            let uu____3673 = find_return_type (FStar_List.length args) t0 in
            translate_type env2 uu____3673 in
          let binders = translate_binders env2 args in
          let env3 = add_binders env2 args in
          let name1 = ((env3.module_name), name) in
          let flags1 =
            match t0 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun
                (uu____3696,FStar_Extraction_ML_Syntax.E_GHOST ,uu____3697)
                ->
                let uu____3698 = translate_flags flags in NoExtract ::
                  uu____3698
            | uu____3701 -> translate_flags flags in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
               let uu____3706 =
                 let uu____3707 =
                   let uu____3722 = translate_type env3 t0 in
                   (FStar_Pervasives_Native.None, name1, uu____3722) in
                 DExternal uu____3707 in
               FStar_Pervasives_Native.Some uu____3706
             else FStar_Pervasives_Native.None)
          else
            (try
               let body1 = translate_expr env3 body in
               FStar_Pervasives_Native.Some
                 (DFunction
                    (FStar_Pervasives_Native.None, flags1,
                      (FStar_List.length tvars), t, name1, binders, body1))
             with
             | e ->
                 let msg = FStar_Util.print_exn e in
                 (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n"
                    (FStar_Pervasives_Native.snd name1) msg;
                  (let msg1 =
                     Prims.strcat "This function was not extracted:\n" msg in
                   FStar_Pervasives_Native.Some
                     (DFunction
                        (FStar_Pervasives_Native.None, flags1,
                          (FStar_List.length tvars), t, name1, binders,
                          (EAbortS msg1))))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____3782);
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some ([],t);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3784;
                          FStar_Extraction_ML_Syntax.mllb_def = expr;
                          FStar_Extraction_ML_Syntax.print_typ = uu____3786;_}::[])
          ->
          let flags1 = translate_flags flags in
          let t1 = translate_type env t in
          let name1 = ((env.module_name), name) in
          (try
             let expr1 = translate_expr env expr in
             FStar_Pervasives_Native.Some
               (DGlobal (flags1, name1, t1, expr1))
           with
           | e ->
               ((let uu____3834 = FStar_Util.print_exn e in
                 FStar_Util.print2
                   "Warning: not translating definition for %s (%s)\n"
                   (FStar_Pervasives_Native.snd name1) uu____3834);
                FStar_Pervasives_Native.Some
                  (DGlobal (flags1, name1, t1, EAny))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (uu____3845,uu____3846,{
                                   FStar_Extraction_ML_Syntax.mllb_name =
                                     (name,uu____3848);
                                   FStar_Extraction_ML_Syntax.mllb_tysc = ts;
                                   FStar_Extraction_ML_Syntax.mllb_add_unit =
                                     uu____3850;
                                   FStar_Extraction_ML_Syntax.mllb_def =
                                     uu____3851;
                                   FStar_Extraction_ML_Syntax.print_typ =
                                     uu____3852;_}::uu____3853)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           (match ts with
            | FStar_Pervasives_Native.Some (idents,t) ->
                let uu____3868 =
                  let uu____3869 =
                    FStar_List.map FStar_Pervasives_Native.fst idents in
                  FStar_String.concat ", " uu____3869 in
                let uu____3876 =
                  FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                  uu____3868 uu____3876
            | FStar_Pervasives_Native.None  -> ());
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Let uu____3879 ->
          failwith "impossible"
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3882 ->
          FStar_Pervasives_Native.None
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((assumed,name,_mangled_name,args,uu____3887,FStar_Pervasives_Native.Some
            (FStar_Extraction_ML_Syntax.MLTD_Abbrev t))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____3946  ->
                   match uu____3946 with
                   | (name2,uu____3952) -> extend_t env1 name2) env args in
          if assumed
          then FStar_Pervasives_Native.None
          else
            (let uu____3956 =
               let uu____3957 =
                 let uu____3970 = translate_type env1 t in
                 (name1, (FStar_List.length args), uu____3970) in
               DTypeAlias uu____3957 in
             FStar_Pervasives_Native.Some uu____3956)
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____3977,name,_mangled_name,args,uu____3981,FStar_Pervasives_Native.Some
            (FStar_Extraction_ML_Syntax.MLTD_Record fields))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____4046  ->
                   match uu____4046 with
                   | (name2,uu____4052) -> extend_t env1 name2) env args in
          let uu____4053 =
            let uu____4054 =
              let uu____4077 =
                FStar_List.map
                  (fun uu____4104  ->
                     match uu____4104 with
                     | (f,t) ->
                         let uu____4119 =
                           let uu____4124 = translate_type env1 t in
                           (uu____4124, false) in
                         (f, uu____4119)) fields in
              (name1, (FStar_List.length args), uu____4077) in
            DTypeFlat uu____4054 in
          FStar_Pervasives_Native.Some uu____4053
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____4145,name,_mangled_name,args,attrs,FStar_Pervasives_Native.Some
            (FStar_Extraction_ML_Syntax.MLTD_DType branches))::[])
          ->
          let name1 = ((env.module_name), name) in
          let flags = translate_flags attrs in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____4223  ->
                   match uu____4223 with
                   | (name2,uu____4229) -> extend_t env1 name2) env args in
          let uu____4230 =
            let uu____4231 =
              let uu____4264 =
                FStar_List.map
                  (fun uu____4309  ->
                     match uu____4309 with
                     | (cons1,ts) ->
                         let uu____4348 =
                           FStar_List.map
                             (fun uu____4375  ->
                                match uu____4375 with
                                | (name2,t) ->
                                    let uu____4390 =
                                      let uu____4395 = translate_type env1 t in
                                      (uu____4395, false) in
                                    (name2, uu____4390)) ts in
                         (cons1, uu____4348)) branches in
              (name1, flags, (FStar_List.length args), uu____4264) in
            DTypeVariant uu____4231 in
          FStar_Pervasives_Native.Some uu____4230
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____4434,name,_mangled_name,uu____4437,uu____4438,uu____4439)::uu____4440)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Ty [] ->
          (FStar_Util.print_string
             "Impossible!! Empty block of mutually recursive type declarations";
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Top uu____4485 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____4488 ->
          failwith "todo: translate_decl [MLM_Exn]"
and translate_type: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var (name,uu____4504) ->
          let uu____4505 = find_t env name in TBound uu____4505
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4507,t2) ->
          let uu____4509 =
            let uu____4514 = translate_type env t1 in
            let uu____4515 = translate_type env t2 in
            (uu____4514, uu____4515) in
          TArrow uu____4509
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4519 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4519 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4523 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4523 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4535 = FStar_Util.must (mk_width m) in TInt uu____4535
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4547 = FStar_Util.must (mk_width m) in TInt uu____4547
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4552 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4552 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4557 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4557 = "FStar.Buffer.buffer" ->
          let uu____4558 = translate_type env arg in TBuf uu____4558
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4559::[],p) when
          let uu____4563 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4563 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4601 = FStar_List.map (translate_type env) args in
          TTuple uu____4601
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4610 =
              let uu____4623 = FStar_List.map (translate_type env) args in
              (lid, uu____4623) in
            TApp uu____4610
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4632 = FStar_List.map (translate_type env) ts in
          TTuple uu____4632
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
    fun uu____4648  ->
      match uu____4648 with
      | ((name,uu____4654),typ) ->
          let uu____4660 = translate_type env typ in
          { name; typ = uu____4660; mut = false }
and translate_expr: env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____4665) ->
          let uu____4666 = find env name in EBound uu____4666
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4671 =
            let uu____4676 = FStar_Util.must (mk_op op) in
            let uu____4677 = FStar_Util.must (mk_width m) in
            (uu____4676, uu____4677) in
          EOp uu____4671
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4681 =
            let uu____4686 = FStar_Util.must (mk_bool_op op) in
            (uu____4686, Bool) in
          EOp uu____4681
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags,{
                           FStar_Extraction_ML_Syntax.mllb_name =
                             (name,uu____4691);
                           FStar_Extraction_ML_Syntax.mllb_tysc =
                             FStar_Pervasives_Native.Some ([],typ);
                           FStar_Extraction_ML_Syntax.mllb_add_unit =
                             add_unit;
                           FStar_Extraction_ML_Syntax.mllb_def = body;
                           FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let is_mut =
            FStar_Util.for_some
              (fun uu___133_4717  ->
                 match uu___133_4717 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____4718 -> false) flags in
          let uu____4719 =
            if is_mut
            then
              let uu____4728 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____4733 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4733 = "FStar.ST.stackref" -> t
                | uu____4734 ->
                    let uu____4735 =
                      let uu____4736 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____4736 in
                    failwith uu____4735 in
              let uu____4739 =
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
                      (uu____4740,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____4742;
                    FStar_Extraction_ML_Syntax.loc = uu____4743;_} -> body1
                | uu____4746 ->
                    failwith "unexpected: bad desugaring of Mutable" in
              (uu____4728, uu____4739)
            else (typ, body) in
          (match uu____4719 with
           | (typ1,body1) ->
               let binder =
                 let uu____4751 = translate_type env typ1 in
                 { name; typ = uu____4751; mut = is_mut } in
               let body2 = translate_expr env body1 in
               let env1 = extend env name is_mut in
               let continuation1 = translate_expr env1 continuation in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4777 =
            let uu____4788 = translate_expr env expr in
            let uu____4789 = translate_branches env branches in
            (uu____4788, uu____4789) in
          EMatch uu____4777
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4803;
             FStar_Extraction_ML_Syntax.loc = uu____4804;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____4806);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4807;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4808;_}::[])
          when
          (let uu____4813 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4813 = "FStar.HyperStack.ST.op_Bang") && (is_mutable env v1)
          -> let uu____4814 = find env v1 in EBound uu____4814
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4816;
             FStar_Extraction_ML_Syntax.loc = uu____4817;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____4819);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4820;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4821;_}::e1::[])
          when
          (let uu____4827 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4827 = "FStar.HyperStack.ST.op_Colon_Equals") &&
            (is_mutable env v1)
          ->
          let uu____4828 =
            let uu____4833 =
              let uu____4834 = find env v1 in EBound uu____4834 in
            let uu____4835 = translate_expr env e1 in
            (uu____4833, uu____4835) in
          EAssign uu____4828
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4837;
                  FStar_Extraction_ML_Syntax.loc = uu____4838;_},uu____4839);
             FStar_Extraction_ML_Syntax.mlty = uu____4840;
             FStar_Extraction_ML_Syntax.loc = uu____4841;_},e1::e2::[])
          when
          (let uu____4852 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4852 = "FStar.Buffer.index") ||
            (let uu____4854 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4854 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____4855 =
            let uu____4860 = translate_expr env e1 in
            let uu____4861 = translate_expr env e2 in
            (uu____4860, uu____4861) in
          EBufRead uu____4855
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4863;
                  FStar_Extraction_ML_Syntax.loc = uu____4864;_},uu____4865);
             FStar_Extraction_ML_Syntax.mlty = uu____4866;
             FStar_Extraction_ML_Syntax.loc = uu____4867;_},e1::e2::[])
          when
          let uu____4876 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4876 = "FStar.Buffer.create" ->
          let uu____4877 =
            let uu____4884 = translate_expr env e1 in
            let uu____4885 = translate_expr env e2 in
            (Stack, uu____4884, uu____4885) in
          EBufCreate uu____4877
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4887;
                  FStar_Extraction_ML_Syntax.loc = uu____4888;_},uu____4889);
             FStar_Extraction_ML_Syntax.mlty = uu____4890;
             FStar_Extraction_ML_Syntax.loc = uu____4891;_},_e0::e1::e2::[])
          when
          let uu____4901 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4901 = "FStar.Buffer.rcreate" ->
          let uu____4902 =
            let uu____4909 = translate_expr env e1 in
            let uu____4910 = translate_expr env e2 in
            (Eternal, uu____4909, uu____4910) in
          EBufCreate uu____4902
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4912;
                  FStar_Extraction_ML_Syntax.loc = uu____4913;_},uu____4914);
             FStar_Extraction_ML_Syntax.mlty = uu____4915;
             FStar_Extraction_ML_Syntax.loc = uu____4916;_},e2::[])
          when
          let uu____4924 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4924 = "FStar.Buffer.createL" ->
          let rec list_elements1 acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements1 (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____4962 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!" in
          let list_elements2 = list_elements1 [] in
          let uu____4970 =
            let uu____4977 =
              let uu____4980 = list_elements2 e2 in
              FStar_List.map (translate_expr env) uu____4980 in
            (Stack, uu____4977) in
          EBufCreateL uu____4970
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4986;
                  FStar_Extraction_ML_Syntax.loc = uu____4987;_},uu____4988);
             FStar_Extraction_ML_Syntax.mlty = uu____4989;
             FStar_Extraction_ML_Syntax.loc = uu____4990;_},e1::e2::_e3::[])
          when
          let uu____5000 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5000 = "FStar.Buffer.sub" ->
          let uu____5001 =
            let uu____5006 = translate_expr env e1 in
            let uu____5007 = translate_expr env e2 in
            (uu____5006, uu____5007) in
          EBufSub uu____5001
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5009;
                  FStar_Extraction_ML_Syntax.loc = uu____5010;_},uu____5011);
             FStar_Extraction_ML_Syntax.mlty = uu____5012;
             FStar_Extraction_ML_Syntax.loc = uu____5013;_},e1::e2::[])
          when
          let uu____5022 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5022 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5024;
                  FStar_Extraction_ML_Syntax.loc = uu____5025;_},uu____5026);
             FStar_Extraction_ML_Syntax.mlty = uu____5027;
             FStar_Extraction_ML_Syntax.loc = uu____5028;_},e1::e2::[])
          when
          let uu____5037 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5037 = "FStar.Buffer.offset" ->
          let uu____5038 =
            let uu____5043 = translate_expr env e1 in
            let uu____5044 = translate_expr env e2 in
            (uu____5043, uu____5044) in
          EBufSub uu____5038
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5046;
                  FStar_Extraction_ML_Syntax.loc = uu____5047;_},uu____5048);
             FStar_Extraction_ML_Syntax.mlty = uu____5049;
             FStar_Extraction_ML_Syntax.loc = uu____5050;_},e1::e2::e3::[])
          when
          (let uu____5062 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5062 = "FStar.Buffer.upd") ||
            (let uu____5064 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5064 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____5065 =
            let uu____5072 = translate_expr env e1 in
            let uu____5073 = translate_expr env e2 in
            let uu____5074 = translate_expr env e3 in
            (uu____5072, uu____5073, uu____5074) in
          EBufWrite uu____5065
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5076;
             FStar_Extraction_ML_Syntax.loc = uu____5077;_},uu____5078::[])
          when
          let uu____5081 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5081 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5083;
             FStar_Extraction_ML_Syntax.loc = uu____5084;_},uu____5085::[])
          when
          let uu____5088 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5088 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5090;
                  FStar_Extraction_ML_Syntax.loc = uu____5091;_},uu____5092);
             FStar_Extraction_ML_Syntax.mlty = uu____5093;
             FStar_Extraction_ML_Syntax.loc = uu____5094;_},e1::e2::e3::e4::e5::[])
          when
          let uu____5106 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5106 = "FStar.Buffer.blit" ->
          let uu____5107 =
            let uu____5118 = translate_expr env e1 in
            let uu____5119 = translate_expr env e2 in
            let uu____5120 = translate_expr env e3 in
            let uu____5121 = translate_expr env e4 in
            let uu____5122 = translate_expr env e5 in
            (uu____5118, uu____5119, uu____5120, uu____5121, uu____5122) in
          EBufBlit uu____5107
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5124;
                  FStar_Extraction_ML_Syntax.loc = uu____5125;_},uu____5126);
             FStar_Extraction_ML_Syntax.mlty = uu____5127;
             FStar_Extraction_ML_Syntax.loc = uu____5128;_},e1::e2::e3::[])
          when
          let uu____5138 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5138 = "FStar.Buffer.fill" ->
          let uu____5139 =
            let uu____5146 = translate_expr env e1 in
            let uu____5147 = translate_expr env e2 in
            let uu____5148 = translate_expr env e3 in
            (uu____5146, uu____5147, uu____5148) in
          EBufFill uu____5139
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5150;
             FStar_Extraction_ML_Syntax.loc = uu____5151;_},uu____5152::[])
          when
          let uu____5155 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5155 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5157;
             FStar_Extraction_ML_Syntax.loc = uu____5158;_},e1::[])
          when
          let uu____5162 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5162 = "Obj.repr" ->
          let uu____5163 =
            let uu____5168 = translate_expr env e1 in (uu____5168, TAny) in
          ECast uu____5163
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5171;
             FStar_Extraction_ML_Syntax.loc = uu____5172;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5180 = FStar_Util.must (mk_width m) in
          let uu____5181 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____5180 uu____5181 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5183;
             FStar_Extraction_ML_Syntax.loc = uu____5184;_},args)
          when is_bool_op op ->
          let uu____5192 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____5192 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5194;
             FStar_Extraction_ML_Syntax.loc = uu____5195;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5197;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5198;_}::[])
          when is_machine_int m ->
          let uu____5213 =
            let uu____5218 = FStar_Util.must (mk_width m) in (uu____5218, c) in
          EConstant uu____5213
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5220;
             FStar_Extraction_ML_Syntax.loc = uu____5221;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5223;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5224;_}::[])
          when is_machine_int m ->
          let uu____5239 =
            let uu____5244 = FStar_Util.must (mk_width m) in (uu____5244, c) in
          EConstant uu____5239
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5245;
             FStar_Extraction_ML_Syntax.loc = uu____5246;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5248;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5249;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5255 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5257;
             FStar_Extraction_ML_Syntax.loc = uu____5258;_},arg::[])
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
            let uu____5265 =
              let uu____5270 = translate_expr env arg in
              (uu____5270, (TInt UInt64)) in
            ECast uu____5265
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5272 =
                 let uu____5277 = translate_expr env arg in
                 (uu____5277, (TInt UInt32)) in
               ECast uu____5272)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5279 =
                   let uu____5284 = translate_expr env arg in
                   (uu____5284, (TInt UInt16)) in
                 ECast uu____5279)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5286 =
                     let uu____5291 = translate_expr env arg in
                     (uu____5291, (TInt UInt8)) in
                   ECast uu____5286)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5293 =
                       let uu____5298 = translate_expr env arg in
                       (uu____5298, (TInt Int64)) in
                     ECast uu____5293)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5300 =
                         let uu____5305 = translate_expr env arg in
                         (uu____5305, (TInt Int32)) in
                       ECast uu____5300)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5307 =
                           let uu____5312 = translate_expr env arg in
                           (uu____5312, (TInt Int16)) in
                         ECast uu____5307)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5314 =
                             let uu____5319 = translate_expr env arg in
                             (uu____5319, (TInt Int8)) in
                           ECast uu____5314)
                        else
                          (let uu____5321 =
                             let uu____5328 =
                               let uu____5331 = translate_expr env arg in
                               [uu____5331] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5328) in
                           EApp uu____5321)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5342 =
            let uu____5349 = translate_expr env head1 in
            let uu____5350 = FStar_List.map (translate_expr env) args in
            (uu____5349, uu____5350) in
          EApp uu____5342
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5361 =
            let uu____5368 = translate_expr env head1 in
            let uu____5369 = FStar_List.map (translate_type env) ty_args in
            (uu____5368, uu____5369) in
          ETypApp uu____5361
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5377 =
            let uu____5382 = translate_expr env e1 in
            let uu____5383 = translate_type env t_to in
            (uu____5382, uu____5383) in
          ECast uu____5377
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5384,fields) ->
          let uu____5402 =
            let uu____5413 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5414 =
              FStar_List.map
                (fun uu____5433  ->
                   match uu____5433 with
                   | (field,expr) ->
                       let uu____5444 = translate_expr env expr in
                       (field, uu____5444)) fields in
            (uu____5413, uu____5414) in
          EFlat uu____5402
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5453 =
            let uu____5460 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____5461 = translate_expr env e1 in
            (uu____5460, uu____5461, (FStar_Pervasives_Native.snd path)) in
          EField uu____5453
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5464 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5478) ->
          let uu____5483 =
            let uu____5484 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1 in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5484 in
          failwith uu____5483
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5490 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____5490
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5496 = FStar_List.map (translate_expr env) es in
          ETuple uu____5496
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5499,cons1),es) ->
          let uu____5516 =
            let uu____5525 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5526 = FStar_List.map (translate_expr env) es in
            (uu____5525, cons1, uu____5526) in
          ECons uu____5516
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args in
          let env1 = add_binders env args in
          let uu____5549 =
            let uu____5558 = translate_expr env1 body in
            let uu____5559 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty in
            (binders, uu____5558, uu____5559) in
          EFun uu____5549
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5569 =
            let uu____5576 = translate_expr env e1 in
            let uu____5577 = translate_expr env e2 in
            let uu____5578 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31 in
            (uu____5576, uu____5577, uu____5578) in
          EIfThenElse uu____5569
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5580 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5587 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____5602 ->
          failwith "todo: translate_expr [MLE_Coerce]"
and assert_lid: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____5617 =
              let uu____5630 = FStar_List.map (translate_type env) ts in
              (lid, uu____5630) in
            TApp uu____5617
          else TQualified lid
      | uu____5636 -> failwith "invalid argument: assert_lid"
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
    fun uu____5662  ->
      match uu____5662 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____5688 = translate_pat env pat in
            (match uu____5688 with
             | (env1,pat1) ->
                 let uu____5699 = translate_expr env1 expr in
                 (pat1, uu____5699))
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
      | FStar_Extraction_ML_Syntax.MLP_Var (name,uu____5713) ->
          let env1 = extend env name false in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_" false in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5716,cons1),ps) ->
          let uu____5733 =
            FStar_List.fold_left
              (fun uu____5753  ->
                 fun p1  ->
                   match uu____5753 with
                   | (env1,acc) ->
                       let uu____5773 = translate_pat env1 p1 in
                       (match uu____5773 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____5733 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____5802,ps) ->
          let uu____5820 =
            FStar_List.fold_left
              (fun uu____5854  ->
                 fun uu____5855  ->
                   match (uu____5854, uu____5855) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____5924 = translate_pat env1 p1 in
                       (match uu____5924 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps in
          (match uu____5820 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____5986 =
            FStar_List.fold_left
              (fun uu____6006  ->
                 fun p1  ->
                   match uu____6006 with
                   | (env1,acc) ->
                       let uu____6026 = translate_pat env1 p1 in
                       (match uu____6026 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____5986 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6053 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6058 ->
          failwith "todo: translate_pat [MLP_Branch]"
and translate_constant: FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6068) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6083 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____6084 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____6085 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6086 ->
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
          let uu____6106 =
            let uu____6113 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____6113) in
          EApp uu____6106