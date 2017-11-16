open Prims
type decl =
  | DGlobal of
  (flag Prims.list,(Prims.string Prims.list,Prims.string)
                     FStar_Pervasives_Native.tuple2,Prims.int,typ,expr)
  FStar_Pervasives_Native.tuple5
  | DFunction of
  (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,(Prims.string
                                                                    Prims.list,
                                                                    Prims.string)
                                                                    FStar_Pervasives_Native.tuple2,
  binder Prims.list,expr) FStar_Pervasives_Native.tuple7
  | DTypeAlias of
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
  flag Prims.list,Prims.int,typ) FStar_Pervasives_Native.tuple4
  | DTypeFlat of
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
  flag Prims.list,Prims.int,(Prims.string,(typ,Prims.bool)
                                            FStar_Pervasives_Native.tuple2)
                              FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple4
  | DExternal of
  (cc FStar_Pervasives_Native.option,flag Prims.list,(Prims.string Prims.list,
                                                       Prims.string)
                                                       FStar_Pervasives_Native.tuple2,
  typ) FStar_Pervasives_Native.tuple4
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
  | WipeBody
  | CInline
  | Substitute
  | GCType
  | Comment of Prims.string
  | MustDisappear[@@deriving show]
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
  Prims.list
  | PConstant of (width,Prims.string) FStar_Pervasives_Native.tuple2[@@deriving
                                                                    show]
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
    match projectee with | DGlobal _0 -> true | uu____547 -> false
let __proj__DGlobal__item___0:
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,Prims.int,typ,expr)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | DGlobal _0 -> _0
let uu___is_DFunction: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____639 -> false
let __proj__DFunction__item___0:
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr) FStar_Pervasives_Native.tuple7
  = fun projectee  -> match projectee with | DFunction _0 -> _0
let uu___is_DTypeAlias: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____745 -> false
let __proj__DTypeAlias__item___0:
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,typ) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0
let uu___is_DTypeFlat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____831 -> false
let __proj__DTypeFlat__item___0:
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,(Prims.string,(typ,Prims.bool)
                                                FStar_Pervasives_Native.tuple2)
                                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0
let uu___is_DExternal: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____939 -> false
let __proj__DExternal__item___0:
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,(Prims.string
                                                          Prims.list,
                                                         Prims.string)
                                                         FStar_Pervasives_Native.tuple2,
      typ) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DExternal _0 -> _0
let uu___is_DTypeVariant: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____1037 -> false
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
    match projectee with | StdCall  -> true | uu____1144 -> false
let uu___is_CDecl: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1148 -> false
let uu___is_FastCall: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1152 -> false
let uu___is_Private: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1156 -> false
let uu___is_WipeBody: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1160 -> false
let uu___is_CInline: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1164 -> false
let uu___is_Substitute: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1168 -> false
let uu___is_GCType: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1172 -> false
let uu___is_Comment: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1177 -> false
let __proj__Comment__item___0: flag -> Prims.string =
  fun projectee  -> match projectee with | Comment _0 -> _0
let uu___is_MustDisappear: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1188 -> false
let uu___is_Eternal: lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1192 -> false
let uu___is_Stack: lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1196 -> false
let uu___is_EBound: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1201 -> false
let __proj__EBound__item___0: expr -> Prims.int =
  fun projectee  -> match projectee with | EBound _0 -> _0
let uu___is_EQualified: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1219 -> false
let __proj__EQualified__item___0:
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EQualified _0 -> _0
let uu___is_EConstant: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1253 -> false
let __proj__EConstant__item___0:
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EConstant _0 -> _0
let uu___is_EUnit: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1276 -> false
let uu___is_EApp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1287 -> false
let __proj__EApp__item___0:
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EApp _0 -> _0
let uu___is_ETypApp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1323 -> false
let __proj__ETypApp__item___0:
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ETypApp _0 -> _0
let uu___is_ELet: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1359 -> false
let __proj__ELet__item___0:
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ELet _0 -> _0
let uu___is_EIfThenElse: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1395 -> false
let __proj__EIfThenElse__item___0:
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0
let uu___is_ESequence: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1427 -> false
let __proj__ESequence__item___0: expr -> expr Prims.list =
  fun projectee  -> match projectee with | ESequence _0 -> _0
let uu___is_EAssign: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1449 -> false
let __proj__EAssign__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EAssign _0 -> _0
let uu___is_EBufCreate: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____1479 -> false
let __proj__EBufCreate__item___0:
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0
let uu___is_EBufRead: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____1513 -> false
let __proj__EBufRead__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufRead _0 -> _0
let uu___is_EBufWrite: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____1543 -> false
let __proj__EBufWrite__item___0:
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0
let uu___is_EBufSub: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____1577 -> false
let __proj__EBufSub__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufSub _0 -> _0
let uu___is_EBufBlit: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____1611 -> false
let __proj__EBufBlit__item___0:
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5 =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0
let uu___is_EMatch: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____1663 -> false
let __proj__EMatch__item___0:
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EMatch _0 -> _0
let uu___is_EOp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1709 -> false
let __proj__EOp__item___0: expr -> (op,width) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EOp _0 -> _0
let uu___is_ECast: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1737 -> false
let __proj__ECast__item___0:
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ECast _0 -> _0
let uu___is_EPushFrame: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1760 -> false
let uu___is_EPopFrame: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1764 -> false
let uu___is_EBool: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1769 -> false
let __proj__EBool__item___0: expr -> Prims.bool =
  fun projectee  -> match projectee with | EBool _0 -> _0
let uu___is_EAny: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1780 -> false
let uu___is_EAbort: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1784 -> false
let uu___is_EReturn: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1789 -> false
let __proj__EReturn__item___0: expr -> expr =
  fun projectee  -> match projectee with | EReturn _0 -> _0
let uu___is_EFlat: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1811 -> false
let __proj__EFlat__item___0:
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EFlat _0 -> _0
let uu___is_EField: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____1859 -> false
let __proj__EField__item___0:
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EField _0 -> _0
let uu___is_EWhile: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____1893 -> false
let __proj__EWhile__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EWhile _0 -> _0
let uu___is_EBufCreateL: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____1923 -> false
let __proj__EBufCreateL__item___0:
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0
let uu___is_ETuple: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____1955 -> false
let __proj__ETuple__item___0: expr -> expr Prims.list =
  fun projectee  -> match projectee with | ETuple _0 -> _0
let uu___is_ECons: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____1981 -> false
let __proj__ECons__item___0:
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ECons _0 -> _0
let uu___is_EBufFill: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2023 -> false
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
    match projectee with | EFun _0 -> true | uu____2073 -> false
let __proj__EFun__item___0:
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EFun _0 -> _0
let uu___is_EAbortS: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2109 -> false
let __proj__EAbortS__item___0: expr -> Prims.string =
  fun projectee  -> match projectee with | EAbortS _0 -> _0
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____2120 -> false
let uu___is_AddW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2124 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____2128 -> false
let uu___is_SubW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2132 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____2136 -> false
let uu___is_DivW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2140 -> false
let uu___is_Mult: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2144 -> false
let uu___is_MultW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2148 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____2152 -> false
let uu___is_BOr: op -> Prims.bool =
  fun projectee  -> match projectee with | BOr  -> true | uu____2156 -> false
let uu___is_BAnd: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2160 -> false
let uu___is_BXor: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2164 -> false
let uu___is_BShiftL: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2168 -> false
let uu___is_BShiftR: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2172 -> false
let uu___is_BNot: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2176 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2180 -> false
let uu___is_Neq: op -> Prims.bool =
  fun projectee  -> match projectee with | Neq  -> true | uu____2184 -> false
let uu___is_Lt: op -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2188 -> false
let uu___is_Lte: op -> Prims.bool =
  fun projectee  -> match projectee with | Lte  -> true | uu____2192 -> false
let uu___is_Gt: op -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2196 -> false
let uu___is_Gte: op -> Prims.bool =
  fun projectee  -> match projectee with | Gte  -> true | uu____2200 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____2204 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____2208 -> false
let uu___is_Xor: op -> Prims.bool =
  fun projectee  -> match projectee with | Xor  -> true | uu____2212 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____2216 -> false
let uu___is_PUnit: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2220 -> false
let uu___is_PBool: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2225 -> false
let __proj__PBool__item___0: pattern -> Prims.bool =
  fun projectee  -> match projectee with | PBool _0 -> _0
let uu___is_PVar: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2237 -> false
let __proj__PVar__item___0: pattern -> binder =
  fun projectee  -> match projectee with | PVar _0 -> _0
let uu___is_PCons: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2255 -> false
let __proj__PCons__item___0:
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PCons _0 -> _0
let uu___is_PTuple: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2287 -> false
let __proj__PTuple__item___0: pattern -> pattern Prims.list =
  fun projectee  -> match projectee with | PTuple _0 -> _0
let uu___is_PRecord: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2311 -> false
let __proj__PRecord__item___0:
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list
  = fun projectee  -> match projectee with | PRecord _0 -> _0
let uu___is_PConstant: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____2345 -> false
let __proj__PConstant__item___0:
  pattern -> (width,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | PConstant _0 -> _0
let uu___is_UInt8: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____2368 -> false
let uu___is_UInt16: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2372 -> false
let uu___is_UInt32: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2376 -> false
let uu___is_UInt64: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2380 -> false
let uu___is_Int8: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2384 -> false
let uu___is_Int16: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2388 -> false
let uu___is_Int32: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2392 -> false
let uu___is_Int64: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2396 -> false
let uu___is_Bool: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2400 -> false
let uu___is_CInt: width -> Prims.bool =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____2404 -> false
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
    match projectee with | TInt _0 -> true | uu____2427 -> false
let __proj__TInt__item___0: typ -> width =
  fun projectee  -> match projectee with | TInt _0 -> _0
let uu___is_TBuf: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2439 -> false
let __proj__TBuf__item___0: typ -> typ =
  fun projectee  -> match projectee with | TBuf _0 -> _0
let uu___is_TUnit: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2450 -> false
let uu___is_TQualified: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2461 -> false
let __proj__TQualified__item___0:
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TQualified _0 -> _0
let uu___is_TBool: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2490 -> false
let uu___is_TAny: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2494 -> false
let uu___is_TArrow: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2503 -> false
let __proj__TArrow__item___0: typ -> (typ,typ) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TArrow _0 -> _0
let uu___is_TBound: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2527 -> false
let __proj__TBound__item___0: typ -> Prims.int =
  fun projectee  -> match projectee with | TBound _0 -> _0
let uu___is_TApp: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2551 -> false
let __proj__TApp__item___0:
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TApp _0 -> _0
let uu___is_TTuple: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____2601 -> false
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
let current_version: version = Prims.parse_int "27"
type file = (Prims.string,program) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
type binary_format = (version,file Prims.list) FStar_Pervasives_Native.tuple2
[@@deriving show]
let fst3:
  'Auu____2677 'Auu____2678 'Auu____2679 .
    ('Auu____2679,'Auu____2678,'Auu____2677) FStar_Pervasives_Native.tuple3
      -> 'Auu____2679
  = fun uu____2689  -> match uu____2689 with | (x,uu____2697,uu____2698) -> x
let snd3:
  'Auu____2703 'Auu____2704 'Auu____2705 .
    ('Auu____2705,'Auu____2704,'Auu____2703) FStar_Pervasives_Native.tuple3
      -> 'Auu____2704
  = fun uu____2715  -> match uu____2715 with | (uu____2722,x,uu____2724) -> x
let thd3:
  'Auu____2729 'Auu____2730 'Auu____2731 .
    ('Auu____2731,'Auu____2730,'Auu____2729) FStar_Pervasives_Native.tuple3
      -> 'Auu____2729
  = fun uu____2741  -> match uu____2741 with | (uu____2748,uu____2749,x) -> x
let mk_width: Prims.string -> width FStar_Pervasives_Native.option =
  fun uu___188_2755  ->
    match uu___188_2755 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____2758 -> FStar_Pervasives_Native.None
let mk_bool_op: Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___189_2763  ->
    match uu___189_2763 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____2766 -> FStar_Pervasives_Native.None
let is_bool_op: Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None
let mk_op: Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___190_2776  ->
    match uu___190_2776 with
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
    | uu____2779 -> FStar_Pervasives_Native.None
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
        let uu___196_2890 = env in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___196_2890.names_t);
          module_name = (uu___196_2890.module_name)
        }
let extend_t: env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___197_2897 = env in
      {
        names = (uu___197_2897.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___197_2897.module_name)
      }
let find_name: env -> Prims.string -> name =
  fun env  ->
    fun x  ->
      let uu____2904 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names in
      match uu____2904 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
let is_mutable: env -> Prims.string -> Prims.bool =
  fun env  -> fun x  -> let uu____2916 = find_name env x in uu____2916.mut
let find: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____2931 ->
          let uu____2932 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____2932
let find_t: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____2947 ->
          let uu____2948 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____2948
let add_binders:
  'Auu____2952 .
    env ->
      (Prims.string,'Auu____2952) FStar_Pervasives_Native.tuple2 Prims.list
        -> env
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____2982  ->
             match uu____2982 with
             | (name,uu____2988) -> extend env1 name false) env binders
let rec translate: FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____3137  ->
    match uu____3137 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3197 = m in
               match uu____3197 with
               | ((prefix1,final),uu____3218,uu____3219) ->
                   FStar_String.concat "."
                     (FStar_List.append prefix1 [final]) in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____3251 = translate_module m in
                FStar_Pervasives_Native.Some uu____3251)
             with
             | e ->
                 ((let uu____3260 = FStar_Util.print_exn e in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3260);
                  FStar_Pervasives_Native.None)) modules
and translate_module:
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
    (FStar_Extraction_ML_Syntax.mlsig,FStar_Extraction_ML_Syntax.mlmodule)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,FStar_Extraction_ML_Syntax.mllib)
    FStar_Pervasives_Native.tuple3 -> file
  =
  fun uu____3261  ->
    match uu____3261 with
    | (module_name,modul,uu____3282) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name] in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____3325 ->
              failwith "Unexpected standalone interface or nested modules" in
        ((FStar_String.concat "_" module_name1), program)
and translate_flags:
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list =
  fun flags  ->
    FStar_List.choose
      (fun uu___191_3340  ->
         match uu___191_3340 with
         | FStar_Extraction_ML_Syntax.Private  ->
             FStar_Pervasives_Native.Some Private
         | FStar_Extraction_ML_Syntax.NoExtract  ->
             FStar_Pervasives_Native.Some WipeBody
         | FStar_Extraction_ML_Syntax.CInline  ->
             FStar_Pervasives_Native.Some CInline
         | FStar_Extraction_ML_Syntax.Substitute  ->
             FStar_Pervasives_Native.Some Substitute
         | FStar_Extraction_ML_Syntax.GCType  ->
             FStar_Pervasives_Native.Some GCType
         | FStar_Extraction_ML_Syntax.Comment s ->
             FStar_Pervasives_Native.Some (Comment s)
         | uu____3344 -> FStar_Pervasives_Native.None) flags
and translate_decl:
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,flags,lbs) ->
          FStar_List.choose (translate_let env flavor flags) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3356 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3358 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____3362) ->
          (FStar_Util.print1_warning
             "Skipping the translation of exception: %s\n" m;
           [])
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
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3385;
              FStar_Extraction_ML_Syntax.mllb_def =
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                  FStar_Extraction_ML_Syntax.mlty = uu____3388;
                  FStar_Extraction_ML_Syntax.loc = uu____3389;_};
              FStar_Extraction_ML_Syntax.print_typ = uu____3390;_} ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___192_3409  ->
                     match uu___192_3409 with
                     | FStar_Extraction_ML_Syntax.Assumed  -> true
                     | uu____3410 -> false) flags in
              let env1 =
                if flavor = FStar_Extraction_ML_Syntax.Rec
                then extend env name false
                else env in
              let env2 =
                FStar_List.fold_left
                  (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars in
              let rec find_return_type eff i uu___193_3431 =
                match uu___193_3431 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3436,eff1,t)
                    when i > (Prims.parse_int "0") ->
                    find_return_type eff1 (i - (Prims.parse_int "1")) t
                | t -> (eff, t) in
              let uu____3440 =
                find_return_type FStar_Extraction_ML_Syntax.E_PURE
                  (FStar_List.length args) t0 in
              (match uu____3440 with
               | (eff,t) ->
                   let t1 = translate_type env2 t in
                   let binders = translate_binders env2 args in
                   let env3 = add_binders env2 args in
                   let name1 = ((env3.module_name), name) in
                   let flags1 =
                     match eff with
                     | FStar_Extraction_ML_Syntax.E_GHOST  ->
                         let uu____3472 = translate_flags flags in
                         MustDisappear :: uu____3472
                     | uu____3475 -> translate_flags flags in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____3480 =
                          let uu____3481 =
                            let uu____3500 = translate_type env3 t0 in
                            (FStar_Pervasives_Native.None, flags1, name1,
                              uu____3500) in
                          DExternal uu____3481 in
                        FStar_Pervasives_Native.Some uu____3480
                      else (
                          (FStar_Util.print1_warning
                             "No writing anything for %s (polymorphic assume)\n"
                             (FStar_Pervasives_Native.snd name1));
                        FStar_Pervasives_Native.None))
                   else
                     (try
                        let body1 = translate_expr env3 body in
                        FStar_Pervasives_Native.Some
                          (DFunction
                             (FStar_Pervasives_Native.None, flags1,
                               (FStar_List.length tvars), t1, name1, binders,
                               body1))
                      with
                      | e ->
                          let msg = FStar_Util.print_exn e in
                          (FStar_Util.print2_warning
                             "Writing a stub for %s (%s)\n"
                             (FStar_Pervasives_Native.snd name1) msg;
                           (let msg1 =
                              Prims.strcat
                                "This function was not extracted:\n" msg in
                            FStar_Pervasives_Native.Some
                              (DFunction
                                 (FStar_Pervasives_Native.None, flags1,
                                   (FStar_List.length tvars), t1, name1,
                                   binders, (EAbortS msg1)))))))
          | { FStar_Extraction_ML_Syntax.mllb_name = name;
              FStar_Extraction_ML_Syntax.mllb_tysc =
                FStar_Pervasives_Native.Some (tvars,t0);
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3562;
              FStar_Extraction_ML_Syntax.mllb_def =
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Coerce
                    ({
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                       FStar_Extraction_ML_Syntax.mlty = uu____3565;
                       FStar_Extraction_ML_Syntax.loc = uu____3566;_},uu____3567,uu____3568);
                  FStar_Extraction_ML_Syntax.mlty = uu____3569;
                  FStar_Extraction_ML_Syntax.loc = uu____3570;_};
              FStar_Extraction_ML_Syntax.print_typ = uu____3571;_} ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___192_3590  ->
                     match uu___192_3590 with
                     | FStar_Extraction_ML_Syntax.Assumed  -> true
                     | uu____3591 -> false) flags in
              let env1 =
                if flavor = FStar_Extraction_ML_Syntax.Rec
                then extend env name false
                else env in
              let env2 =
                FStar_List.fold_left
                  (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars in
              let rec find_return_type eff i uu___193_3612 =
                match uu___193_3612 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3617,eff1,t)
                    when i > (Prims.parse_int "0") ->
                    find_return_type eff1 (i - (Prims.parse_int "1")) t
                | t -> (eff, t) in
              let uu____3621 =
                find_return_type FStar_Extraction_ML_Syntax.E_PURE
                  (FStar_List.length args) t0 in
              (match uu____3621 with
               | (eff,t) ->
                   let t1 = translate_type env2 t in
                   let binders = translate_binders env2 args in
                   let env3 = add_binders env2 args in
                   let name1 = ((env3.module_name), name) in
                   let flags1 =
                     match eff with
                     | FStar_Extraction_ML_Syntax.E_GHOST  ->
                         let uu____3653 = translate_flags flags in
                         MustDisappear :: uu____3653
                     | uu____3656 -> translate_flags flags in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____3661 =
                          let uu____3662 =
                            let uu____3681 = translate_type env3 t0 in
                            (FStar_Pervasives_Native.None, flags1, name1,
                              uu____3681) in
                          DExternal uu____3662 in
                        FStar_Pervasives_Native.Some uu____3661
                      else FStar_Pervasives_Native.None)
                   else
                     (try
                        let body1 = translate_expr env3 body in
                        FStar_Pervasives_Native.Some
                          (DFunction
                             (FStar_Pervasives_Native.None, flags1,
                               (FStar_List.length tvars), t1, name1, binders,
                               body1))
                      with
                      | e ->
                          let msg = FStar_Util.print_exn e in
                          (FStar_Util.print2_warning
                             "Writing a stub for %s (%s)\n"
                             (FStar_Pervasives_Native.snd name1) msg;
                           (let msg1 =
                              Prims.strcat
                                "This function was not extracted:\n" msg in
                            FStar_Pervasives_Native.Some
                              (DFunction
                                 (FStar_Pervasives_Native.None, flags1,
                                   (FStar_List.length tvars), t1, name1,
                                   binders, (EAbortS msg1)))))))
          | { FStar_Extraction_ML_Syntax.mllb_name = name;
              FStar_Extraction_ML_Syntax.mllb_tysc =
                FStar_Pervasives_Native.Some (tvars,t);
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3743;
              FStar_Extraction_ML_Syntax.mllb_def = expr;
              FStar_Extraction_ML_Syntax.print_typ = uu____3745;_} ->
              let flags1 = translate_flags flags in
              let env1 =
                FStar_List.fold_left
                  (fun env1  -> fun name1  -> extend_t env1 name1) env tvars in
              let t1 = translate_type env1 t in
              let name1 = ((env1.module_name), name) in
              (try
                 let expr1 = translate_expr env1 expr in
                 FStar_Pervasives_Native.Some
                   (DGlobal
                      (flags1, name1, (FStar_List.length tvars), t1, expr1))
               with
               | e ->
                   ((let uu____3792 = FStar_Util.print_exn e in
                     FStar_Util.print2_warning
                       "Not translating definition for %s (%s)\n"
                       (FStar_Pervasives_Native.snd name1) uu____3792);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (flags1, name1, (FStar_List.length tvars), t1, EAny))))
          | { FStar_Extraction_ML_Syntax.mllb_name = name;
              FStar_Extraction_ML_Syntax.mllb_tysc = ts;
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3805;
              FStar_Extraction_ML_Syntax.mllb_def = uu____3806;
              FStar_Extraction_ML_Syntax.print_typ = uu____3807;_} ->
              (FStar_Util.print1_warning
                 "Not translating definition for %s\n" name;
               (match ts with
                | FStar_Pervasives_Native.Some (idents,t) ->
                    let uu____3818 =
                      FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                    FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                      (FStar_String.concat ", " idents) uu____3818
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
      | (assumed,name,_mangled_name,args,flags,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Abbrev t)) ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args in
          if assumed
          then FStar_Pervasives_Native.None
          else
            (let uu____3854 =
               let uu____3855 =
                 let uu____3872 = translate_flags flags in
                 let uu____3875 = translate_type env1 t in
                 (name1, uu____3872, (FStar_List.length args), uu____3875) in
               DTypeAlias uu____3855 in
             FStar_Pervasives_Native.Some uu____3854)
      | (uu____3884,name,_mangled_name,args,flags,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args in
          let uu____3916 =
            let uu____3917 =
              let uu____3944 = translate_flags flags in
              let uu____3947 =
                FStar_List.map
                  (fun uu____3974  ->
                     match uu____3974 with
                     | (f,t) ->
                         let uu____3989 =
                           let uu____3994 = translate_type env1 t in
                           (uu____3994, false) in
                         (f, uu____3989)) fields in
              (name1, uu____3944, (FStar_List.length args), uu____3947) in
            DTypeFlat uu____3917 in
          FStar_Pervasives_Native.Some uu____3916
      | (uu____4017,name,_mangled_name,args,flags,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
          let name1 = ((env.module_name), name) in
          let flags1 = translate_flags flags in
          let env1 = FStar_List.fold_left extend_t env args in
          let uu____4054 =
            let uu____4055 =
              let uu____4088 =
                FStar_List.map
                  (fun uu____4133  ->
                     match uu____4133 with
                     | (cons1,ts) ->
                         let uu____4172 =
                           FStar_List.map
                             (fun uu____4199  ->
                                match uu____4199 with
                                | (name2,t) ->
                                    let uu____4214 =
                                      let uu____4219 = translate_type env1 t in
                                      (uu____4219, false) in
                                    (name2, uu____4214)) ts in
                         (cons1, uu____4172)) branches in
              (name1, flags1, (FStar_List.length args), uu____4088) in
            DTypeVariant uu____4055 in
          FStar_Pervasives_Native.Some uu____4054
      | (uu____4258,name,_mangled_name,uu____4261,uu____4262,uu____4263) ->
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
          let uu____4276 = find_t env name in TBound uu____4276
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4278,t2) ->
          let uu____4280 =
            let uu____4285 = translate_type env t1 in
            let uu____4286 = translate_type env t2 in
            (uu____4285, uu____4286) in
          TArrow uu____4280
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4290 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4290 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4294 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4294 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4306 = FStar_Util.must (mk_width m) in TInt uu____4306
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4318 = FStar_Util.must (mk_width m) in TInt uu____4318
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4323 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4323 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4328 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4328 = "FStar.Buffer.buffer" ->
          let uu____4329 = translate_type env arg in TBuf uu____4329
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4330::[],p) when
          let uu____4334 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4334 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4372 = FStar_List.map (translate_type env) args in
          TTuple uu____4372
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4381 =
              let uu____4394 = FStar_List.map (translate_type env) args in
              (lid, uu____4394) in
            TApp uu____4381
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4403 = FStar_List.map (translate_type env) ts in
          TTuple uu____4403
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
    fun uu____4419  ->
      match uu____4419 with
      | (name,typ) ->
          let uu____4426 = translate_type env typ in
          { name; typ = uu____4426; mut = false }
and translate_expr: env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____4431 = find env name in EBound uu____4431
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4436 =
            let uu____4441 = FStar_Util.must (mk_op op) in
            let uu____4442 = FStar_Util.must (mk_width m) in
            (uu____4441, uu____4442) in
          EOp uu____4436
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4446 =
            let uu____4451 = FStar_Util.must (mk_bool_op op) in
            (uu____4451, Bool) in
          EOp uu____4446
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
              (fun uu___194_4481  ->
                 match uu___194_4481 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____4482 -> false) flags in
          let uu____4483 =
            if is_mut
            then
              let uu____4492 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____4497 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4497 = "FStar.ST.stackref" -> t
                | uu____4498 ->
                    let uu____4499 =
                      let uu____4500 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____4500 in
                    failwith uu____4499 in
              let uu____4503 =
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
                      (uu____4504,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____4506;
                    FStar_Extraction_ML_Syntax.loc = uu____4507;_} -> body1
                | uu____4510 ->
                    failwith "unexpected: bad desugaring of Mutable" in
              (uu____4492, uu____4503)
            else (typ, body) in
          (match uu____4483 with
           | (typ1,body1) ->
               let binder =
                 let uu____4515 = translate_type env typ1 in
                 { name; typ = uu____4515; mut = is_mut } in
               let body2 = translate_expr env body1 in
               let env1 = extend env name is_mut in
               let continuation1 = translate_expr env1 continuation in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4541 =
            let uu____4552 = translate_expr env expr in
            let uu____4553 = translate_branches env branches in
            (uu____4552, uu____4553) in
          EMatch uu____4541
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4567;
             FStar_Extraction_ML_Syntax.loc = uu____4568;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                v1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4570;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4571;_}::[])
          when
          (let uu____4576 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4576 = "FStar.HyperStack.ST.op_Bang") && (is_mutable env v1)
          -> let uu____4577 = find env v1 in EBound uu____4577
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4579;
             FStar_Extraction_ML_Syntax.loc = uu____4580;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                v1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4582;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4583;_}::e1::[])
          when
          (let uu____4589 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4589 = "FStar.HyperStack.ST.op_Colon_Equals") &&
            (is_mutable env v1)
          ->
          let uu____4590 =
            let uu____4595 =
              let uu____4596 = find env v1 in EBound uu____4596 in
            let uu____4597 = translate_expr env e1 in
            (uu____4595, uu____4597) in
          EAssign uu____4590
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4599;
                  FStar_Extraction_ML_Syntax.loc = uu____4600;_},uu____4601);
             FStar_Extraction_ML_Syntax.mlty = uu____4602;
             FStar_Extraction_ML_Syntax.loc = uu____4603;_},e1::e2::[])
          when
          (let uu____4614 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4614 = "FStar.Buffer.index") ||
            (let uu____4616 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4616 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____4617 =
            let uu____4622 = translate_expr env e1 in
            let uu____4623 = translate_expr env e2 in
            (uu____4622, uu____4623) in
          EBufRead uu____4617
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4625;
                  FStar_Extraction_ML_Syntax.loc = uu____4626;_},uu____4627);
             FStar_Extraction_ML_Syntax.mlty = uu____4628;
             FStar_Extraction_ML_Syntax.loc = uu____4629;_},e1::[])
          when
          let uu____4637 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4637 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____4638 =
            let uu____4643 = translate_expr env e1 in
            (uu____4643, (EConstant (UInt32, "0"))) in
          EBufRead uu____4638
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4645;
                  FStar_Extraction_ML_Syntax.loc = uu____4646;_},uu____4647);
             FStar_Extraction_ML_Syntax.mlty = uu____4648;
             FStar_Extraction_ML_Syntax.loc = uu____4649;_},e1::e2::[])
          when
          let uu____4658 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4658 = "FStar.Buffer.create" ->
          let uu____4659 =
            let uu____4666 = translate_expr env e1 in
            let uu____4667 = translate_expr env e2 in
            (Stack, uu____4666, uu____4667) in
          EBufCreate uu____4659
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4669;
                  FStar_Extraction_ML_Syntax.loc = uu____4670;_},uu____4671);
             FStar_Extraction_ML_Syntax.mlty = uu____4672;
             FStar_Extraction_ML_Syntax.loc = uu____4673;_},_rid::init1::[])
          when
          let uu____4682 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4682 = "FStar.HyperStack.ST.ralloc" ->
          let uu____4683 =
            let uu____4690 = translate_expr env init1 in
            (Eternal, uu____4690, (EConstant (UInt32, "0"))) in
          EBufCreate uu____4683
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4692;
                  FStar_Extraction_ML_Syntax.loc = uu____4693;_},uu____4694);
             FStar_Extraction_ML_Syntax.mlty = uu____4695;
             FStar_Extraction_ML_Syntax.loc = uu____4696;_},_e0::e1::e2::[])
          when
          let uu____4706 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4706 = "FStar.Buffer.rcreate" ->
          let uu____4707 =
            let uu____4714 = translate_expr env e1 in
            let uu____4715 = translate_expr env e2 in
            (Eternal, uu____4714, uu____4715) in
          EBufCreate uu____4707
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4717;
                  FStar_Extraction_ML_Syntax.loc = uu____4718;_},uu____4719);
             FStar_Extraction_ML_Syntax.mlty = uu____4720;
             FStar_Extraction_ML_Syntax.loc = uu____4721;_},e2::[])
          when
          let uu____4729 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4729 = "FStar.Buffer.createL" ->
          let rec list_elements acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____4767 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!" in
          let list_elements1 = list_elements [] in
          let uu____4775 =
            let uu____4782 =
              let uu____4785 = list_elements1 e2 in
              FStar_List.map (translate_expr env) uu____4785 in
            (Stack, uu____4782) in
          EBufCreateL uu____4775
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4791;
                  FStar_Extraction_ML_Syntax.loc = uu____4792;_},uu____4793);
             FStar_Extraction_ML_Syntax.mlty = uu____4794;
             FStar_Extraction_ML_Syntax.loc = uu____4795;_},e1::e2::_e3::[])
          when
          let uu____4805 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4805 = "FStar.Buffer.sub" ->
          let uu____4806 =
            let uu____4811 = translate_expr env e1 in
            let uu____4812 = translate_expr env e2 in
            (uu____4811, uu____4812) in
          EBufSub uu____4806
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4814;
                  FStar_Extraction_ML_Syntax.loc = uu____4815;_},uu____4816);
             FStar_Extraction_ML_Syntax.mlty = uu____4817;
             FStar_Extraction_ML_Syntax.loc = uu____4818;_},e1::e2::[])
          when
          let uu____4827 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4827 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4829;
                  FStar_Extraction_ML_Syntax.loc = uu____4830;_},uu____4831);
             FStar_Extraction_ML_Syntax.mlty = uu____4832;
             FStar_Extraction_ML_Syntax.loc = uu____4833;_},e1::e2::[])
          when
          let uu____4842 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4842 = "FStar.Buffer.offset" ->
          let uu____4843 =
            let uu____4848 = translate_expr env e1 in
            let uu____4849 = translate_expr env e2 in
            (uu____4848, uu____4849) in
          EBufSub uu____4843
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4851;
                  FStar_Extraction_ML_Syntax.loc = uu____4852;_},uu____4853);
             FStar_Extraction_ML_Syntax.mlty = uu____4854;
             FStar_Extraction_ML_Syntax.loc = uu____4855;_},e1::e2::e3::[])
          when
          (let uu____4867 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4867 = "FStar.Buffer.upd") ||
            (let uu____4869 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4869 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____4870 =
            let uu____4877 = translate_expr env e1 in
            let uu____4878 = translate_expr env e2 in
            let uu____4879 = translate_expr env e3 in
            (uu____4877, uu____4878, uu____4879) in
          EBufWrite uu____4870
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4881;
                  FStar_Extraction_ML_Syntax.loc = uu____4882;_},uu____4883);
             FStar_Extraction_ML_Syntax.mlty = uu____4884;
             FStar_Extraction_ML_Syntax.loc = uu____4885;_},e1::e2::[])
          when
          let uu____4894 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4894 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____4895 =
            let uu____4902 = translate_expr env e1 in
            let uu____4903 = translate_expr env e2 in
            (uu____4902, (EConstant (UInt32, "0")), uu____4903) in
          EBufWrite uu____4895
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4905;
             FStar_Extraction_ML_Syntax.loc = uu____4906;_},uu____4907::[])
          when
          let uu____4910 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4910 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4912;
             FStar_Extraction_ML_Syntax.loc = uu____4913;_},uu____4914::[])
          when
          let uu____4917 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4917 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4919;
                  FStar_Extraction_ML_Syntax.loc = uu____4920;_},uu____4921);
             FStar_Extraction_ML_Syntax.mlty = uu____4922;
             FStar_Extraction_ML_Syntax.loc = uu____4923;_},e1::e2::e3::e4::e5::[])
          when
          let uu____4935 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4935 = "FStar.Buffer.blit" ->
          let uu____4936 =
            let uu____4947 = translate_expr env e1 in
            let uu____4948 = translate_expr env e2 in
            let uu____4949 = translate_expr env e3 in
            let uu____4950 = translate_expr env e4 in
            let uu____4951 = translate_expr env e5 in
            (uu____4947, uu____4948, uu____4949, uu____4950, uu____4951) in
          EBufBlit uu____4936
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4953;
                  FStar_Extraction_ML_Syntax.loc = uu____4954;_},uu____4955);
             FStar_Extraction_ML_Syntax.mlty = uu____4956;
             FStar_Extraction_ML_Syntax.loc = uu____4957;_},e1::e2::e3::[])
          when
          let uu____4967 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4967 = "FStar.Buffer.fill" ->
          let uu____4968 =
            let uu____4975 = translate_expr env e1 in
            let uu____4976 = translate_expr env e2 in
            let uu____4977 = translate_expr env e3 in
            (uu____4975, uu____4976, uu____4977) in
          EBufFill uu____4968
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4979;
             FStar_Extraction_ML_Syntax.loc = uu____4980;_},uu____4981::[])
          when
          let uu____4984 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4984 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4986;
             FStar_Extraction_ML_Syntax.loc = uu____4987;_},e1::[])
          when
          let uu____4991 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4991 = "Obj.repr" ->
          let uu____4992 =
            let uu____4997 = translate_expr env e1 in (uu____4997, TAny) in
          ECast uu____4992
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5000;
             FStar_Extraction_ML_Syntax.loc = uu____5001;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5009 = FStar_Util.must (mk_width m) in
          let uu____5010 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____5009 uu____5010 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5012;
             FStar_Extraction_ML_Syntax.loc = uu____5013;_},args)
          when is_bool_op op ->
          let uu____5021 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____5021 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5023;
             FStar_Extraction_ML_Syntax.loc = uu____5024;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5026;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5027;_}::[])
          when is_machine_int m ->
          let uu____5042 =
            let uu____5047 = FStar_Util.must (mk_width m) in (uu____5047, c) in
          EConstant uu____5042
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5049;
             FStar_Extraction_ML_Syntax.loc = uu____5050;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5052;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5053;_}::[])
          when is_machine_int m ->
          let uu____5068 =
            let uu____5073 = FStar_Util.must (mk_width m) in (uu____5073, c) in
          EConstant uu____5068
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5074;
             FStar_Extraction_ML_Syntax.loc = uu____5075;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5077;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5078;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5084 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5085;
             FStar_Extraction_ML_Syntax.loc = uu____5086;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5088;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5089;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5095 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5097;
             FStar_Extraction_ML_Syntax.loc = uu____5098;_},arg::[])
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
            let uu____5105 =
              let uu____5110 = translate_expr env arg in
              (uu____5110, (TInt UInt64)) in
            ECast uu____5105
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5112 =
                 let uu____5117 = translate_expr env arg in
                 (uu____5117, (TInt UInt32)) in
               ECast uu____5112)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5119 =
                   let uu____5124 = translate_expr env arg in
                   (uu____5124, (TInt UInt16)) in
                 ECast uu____5119)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5126 =
                     let uu____5131 = translate_expr env arg in
                     (uu____5131, (TInt UInt8)) in
                   ECast uu____5126)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5133 =
                       let uu____5138 = translate_expr env arg in
                       (uu____5138, (TInt Int64)) in
                     ECast uu____5133)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5140 =
                         let uu____5145 = translate_expr env arg in
                         (uu____5145, (TInt Int32)) in
                       ECast uu____5140)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5147 =
                           let uu____5152 = translate_expr env arg in
                           (uu____5152, (TInt Int16)) in
                         ECast uu____5147)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5154 =
                             let uu____5159 = translate_expr env arg in
                             (uu____5159, (TInt Int8)) in
                           ECast uu____5154)
                        else
                          (let uu____5161 =
                             let uu____5168 =
                               let uu____5171 = translate_expr env arg in
                               [uu____5171] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5168) in
                           EApp uu____5161)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5182 =
            let uu____5189 = translate_expr env head1 in
            let uu____5190 = FStar_List.map (translate_expr env) args in
            (uu____5189, uu____5190) in
          EApp uu____5182
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5201 =
            let uu____5208 = translate_expr env head1 in
            let uu____5209 = FStar_List.map (translate_type env) ty_args in
            (uu____5208, uu____5209) in
          ETypApp uu____5201
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5217 =
            let uu____5222 = translate_expr env e1 in
            let uu____5223 = translate_type env t_to in
            (uu____5222, uu____5223) in
          ECast uu____5217
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5224,fields) ->
          let uu____5242 =
            let uu____5253 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5254 =
              FStar_List.map
                (fun uu____5273  ->
                   match uu____5273 with
                   | (field,expr) ->
                       let uu____5284 = translate_expr env expr in
                       (field, uu____5284)) fields in
            (uu____5253, uu____5254) in
          EFlat uu____5242
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5293 =
            let uu____5300 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____5301 = translate_expr env e1 in
            (uu____5300, uu____5301, (FStar_Pervasives_Native.snd path)) in
          EField uu____5293
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5304 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5318) ->
          let uu____5323 =
            let uu____5324 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1 in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5324 in
          failwith uu____5323
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5330 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____5330
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5336 = FStar_List.map (translate_expr env) es in
          ETuple uu____5336
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5339,cons1),es) ->
          let uu____5356 =
            let uu____5365 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5366 = FStar_List.map (translate_expr env) es in
            (uu____5365, cons1, uu____5366) in
          ECons uu____5356
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args in
          let env1 = add_binders env args in
          let uu____5389 =
            let uu____5398 = translate_expr env1 body in
            let uu____5399 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty in
            (binders, uu____5398, uu____5399) in
          EFun uu____5389
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5409 =
            let uu____5416 = translate_expr env e1 in
            let uu____5417 = translate_expr env e2 in
            let uu____5418 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31 in
            (uu____5416, uu____5417, uu____5418) in
          EIfThenElse uu____5409
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5420 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5427 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____5442 ->
          failwith "todo: translate_expr [MLE_Coerce]"
and assert_lid: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____5457 =
              let uu____5470 = FStar_List.map (translate_type env) ts in
              (lid, uu____5470) in
            TApp uu____5457
          else TQualified lid
      | uu____5476 -> failwith "invalid argument: assert_lid"
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
    fun uu____5502  ->
      match uu____5502 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____5528 = translate_pat env pat in
            (match uu____5528 with
             | (env1,pat1) ->
                 let uu____5539 = translate_expr env1 expr in
                 (pat1, uu____5539))
          else failwith "todo: translate_branch"
and translate_width:
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width
  =
  fun uu___195_5545  ->
    match uu___195_5545 with
    | FStar_Pervasives_Native.None  -> CInt
    | FStar_Pervasives_Native.Some (FStar_Const.Signed ,FStar_Const.Int8 ) ->
        Int8
    | FStar_Pervasives_Native.Some (FStar_Const.Signed ,FStar_Const.Int16 )
        -> Int16
    | FStar_Pervasives_Native.Some (FStar_Const.Signed ,FStar_Const.Int32 )
        -> Int32
    | FStar_Pervasives_Native.Some (FStar_Const.Signed ,FStar_Const.Int64 )
        -> Int64
    | FStar_Pervasives_Native.Some (FStar_Const.Unsigned ,FStar_Const.Int8 )
        -> UInt8
    | FStar_Pervasives_Native.Some (FStar_Const.Unsigned ,FStar_Const.Int16 )
        -> UInt16
    | FStar_Pervasives_Native.Some (FStar_Const.Unsigned ,FStar_Const.Int32 )
        -> UInt32
    | FStar_Pervasives_Native.Some (FStar_Const.Unsigned ,FStar_Const.Int64 )
        -> UInt64
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
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Int (s,sw)) ->
          let uu____5609 =
            let uu____5610 =
              let uu____5615 = translate_width sw in (uu____5615, s) in
            PConstant uu____5610 in
          (env, uu____5609)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name false in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_" false in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5619,cons1),ps) ->
          let uu____5636 =
            FStar_List.fold_left
              (fun uu____5656  ->
                 fun p1  ->
                   match uu____5656 with
                   | (env1,acc) ->
                       let uu____5676 = translate_pat env1 p1 in
                       (match uu____5676 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____5636 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____5705,ps) ->
          let uu____5723 =
            FStar_List.fold_left
              (fun uu____5757  ->
                 fun uu____5758  ->
                   match (uu____5757, uu____5758) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____5827 = translate_pat env1 p1 in
                       (match uu____5827 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps in
          (match uu____5723 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____5889 =
            FStar_List.fold_left
              (fun uu____5909  ->
                 fun p1  ->
                   match uu____5909 with
                   | (env1,acc) ->
                       let uu____5929 = translate_pat env1 p1 in
                       (match uu____5929 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____5889 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____5956 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____5961 ->
          failwith "todo: translate_pat [MLP_Branch]"
and translate_constant: FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____5972 =
            let uu____5973 = FStar_String.list_of_string s in
            FStar_All.pipe_right uu____5973
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0")))) in
          if uu____5972
          then
            let uu____5985 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s in
            failwith uu____5985
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____5988) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6003 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____6004 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6005 ->
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
          let uu____6025 =
            let uu____6032 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____6032) in
          EApp uu____6025
