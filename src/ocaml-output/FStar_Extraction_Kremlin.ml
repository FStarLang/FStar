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
  fun uu___189_2755  ->
    match uu___189_2755 with
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
  fun uu___190_2763  ->
    match uu___190_2763 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____2766 -> FStar_Pervasives_Native.None
let is_bool_op: Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None
let mk_op: Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___191_2776  ->
    match uu___191_2776 with
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
        let uu___197_2890 = env in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___197_2890.names_t);
          module_name = (uu___197_2890.module_name)
        }
let extend_t: env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___198_2897 = env in
      {
        names = (uu___198_2897.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___198_2897.module_name)
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
  fun flags1  ->
    FStar_List.choose
      (fun uu___192_3340  ->
         match uu___192_3340 with
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
         | uu____3344 -> FStar_Pervasives_Native.None) flags1
and translate_decl:
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,flags1,lbs) ->
          FStar_List.choose (translate_let env flavor flags1) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3356 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3358 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____3361 ->
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
      fun flags1  ->
        fun lb  ->
          match lb with
          | { FStar_Extraction_ML_Syntax.mllb_name = name;
              FStar_Extraction_ML_Syntax.mllb_tysc =
                FStar_Pervasives_Native.Some (tvars,t0);
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3383;
              FStar_Extraction_ML_Syntax.mllb_def =
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                  FStar_Extraction_ML_Syntax.mlty = uu____3386;
                  FStar_Extraction_ML_Syntax.loc = uu____3387;_};
              FStar_Extraction_ML_Syntax.print_typ = uu____3388;_} ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___193_3407  ->
                     match uu___193_3407 with
                     | FStar_Extraction_ML_Syntax.Assumed  -> true
                     | uu____3408 -> false) flags1 in
              let env1 =
                if flavor = FStar_Extraction_ML_Syntax.Rec
                then extend env name false
                else env in
              let env2 =
                FStar_List.fold_left
                  (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars in
              let rec find_return_type eff i uu___194_3429 =
                match uu___194_3429 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3434,eff1,t)
                    when i > (Prims.parse_int "0") ->
                    find_return_type eff1 (i - (Prims.parse_int "1")) t
                | t -> (eff, t) in
              let uu____3438 =
                find_return_type FStar_Extraction_ML_Syntax.E_PURE
                  (FStar_List.length args) t0 in
              (match uu____3438 with
               | (eff,t) ->
                   let t1 = translate_type env2 t in
                   let binders = translate_binders env2 args in
                   let env3 = add_binders env2 args in
                   let name1 = ((env3.module_name), name) in
                   let flags2 =
                     match eff with
                     | FStar_Extraction_ML_Syntax.E_GHOST  ->
                         let uu____3470 = translate_flags flags1 in
                         MustDisappear :: uu____3470
                     | uu____3473 -> translate_flags flags1 in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____3478 =
                          let uu____3479 =
                            let uu____3498 = translate_type env3 t0 in
                            (FStar_Pervasives_Native.None, flags2, name1,
                              uu____3498) in
                          DExternal uu____3479 in
                        FStar_Pervasives_Native.Some uu____3478
                      else FStar_Pervasives_Native.None)
                   else
                     (try
                        let body1 = translate_expr env3 body in
                        FStar_Pervasives_Native.Some
                          (DFunction
                             (FStar_Pervasives_Native.None, flags2,
                               (FStar_List.length tvars), t1, name1, binders,
                               body1))
                      with
                      | e ->
                          let msg = FStar_Util.print_exn e in
                          ((let uu____3542 =
                              let uu____3547 =
                                FStar_Util.format2
                                  "Writing a stub for %s (%s)\n"
                                  (FStar_Pervasives_Native.snd name1) msg in
                              (FStar_Errors.FunctionNotExtacted, uu____3547) in
                            FStar_Errors.maybe_fatal_err uu____3542);
                           (let msg1 =
                              Prims.strcat
                                "This function was not extracted:\n" msg in
                            FStar_Pervasives_Native.Some
                              (DFunction
                                 (FStar_Pervasives_Native.None, flags2,
                                   (FStar_List.length tvars), t1, name1,
                                   binders, (EAbortS msg1)))))))
          | { FStar_Extraction_ML_Syntax.mllb_name = name;
              FStar_Extraction_ML_Syntax.mllb_tysc =
                FStar_Pervasives_Native.Some (tvars,t0);
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3566;
              FStar_Extraction_ML_Syntax.mllb_def =
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Coerce
                    ({
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                       FStar_Extraction_ML_Syntax.mlty = uu____3569;
                       FStar_Extraction_ML_Syntax.loc = uu____3570;_},uu____3571,uu____3572);
                  FStar_Extraction_ML_Syntax.mlty = uu____3573;
                  FStar_Extraction_ML_Syntax.loc = uu____3574;_};
              FStar_Extraction_ML_Syntax.print_typ = uu____3575;_} ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___193_3594  ->
                     match uu___193_3594 with
                     | FStar_Extraction_ML_Syntax.Assumed  -> true
                     | uu____3595 -> false) flags1 in
              let env1 =
                if flavor = FStar_Extraction_ML_Syntax.Rec
                then extend env name false
                else env in
              let env2 =
                FStar_List.fold_left
                  (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars in
              let rec find_return_type eff i uu___194_3616 =
                match uu___194_3616 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3621,eff1,t)
                    when i > (Prims.parse_int "0") ->
                    find_return_type eff1 (i - (Prims.parse_int "1")) t
                | t -> (eff, t) in
              let uu____3625 =
                find_return_type FStar_Extraction_ML_Syntax.E_PURE
                  (FStar_List.length args) t0 in
              (match uu____3625 with
               | (eff,t) ->
                   let t1 = translate_type env2 t in
                   let binders = translate_binders env2 args in
                   let env3 = add_binders env2 args in
                   let name1 = ((env3.module_name), name) in
                   let flags2 =
                     match eff with
                     | FStar_Extraction_ML_Syntax.E_GHOST  ->
                         let uu____3657 = translate_flags flags1 in
                         MustDisappear :: uu____3657
                     | uu____3660 -> translate_flags flags1 in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____3665 =
                          let uu____3666 =
                            let uu____3685 = translate_type env3 t0 in
                            (FStar_Pervasives_Native.None, flags2, name1,
                              uu____3685) in
                          DExternal uu____3666 in
                        FStar_Pervasives_Native.Some uu____3665
                      else FStar_Pervasives_Native.None)
                   else
                     (try
                        let body1 = translate_expr env3 body in
                        FStar_Pervasives_Native.Some
                          (DFunction
                             (FStar_Pervasives_Native.None, flags2,
                               (FStar_List.length tvars), t1, name1, binders,
                               body1))
                      with
                      | e ->
                          let msg = FStar_Util.print_exn e in
                          ((let uu____3729 =
                              let uu____3734 =
                                FStar_Util.format2
                                  "Writing a stub for %s (%s)\n"
                                  (FStar_Pervasives_Native.snd name1) msg in
                              (FStar_Errors.FunctionNotExtacted, uu____3734) in
                            FStar_Errors.maybe_fatal_err uu____3729);
                           (let msg1 =
                              Prims.strcat
                                "This function was not extracted:\n" msg in
                            FStar_Pervasives_Native.Some
                              (DFunction
                                 (FStar_Pervasives_Native.None, flags2,
                                   (FStar_List.length tvars), t1, name1,
                                   binders, (EAbortS msg1)))))))
          | { FStar_Extraction_ML_Syntax.mllb_name = name;
              FStar_Extraction_ML_Syntax.mllb_tysc =
                FStar_Pervasives_Native.Some (tvars,t);
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3753;
              FStar_Extraction_ML_Syntax.mllb_def = expr;
              FStar_Extraction_ML_Syntax.print_typ = uu____3755;_} ->
              let flags2 = translate_flags flags1 in
              let env1 =
                FStar_List.fold_left
                  (fun env1  -> fun name1  -> extend_t env1 name1) env tvars in
              let t1 = translate_type env1 t in
              let name1 = ((env1.module_name), name) in
              (try
                 let expr1 = translate_expr env1 expr in
                 FStar_Pervasives_Native.Some
                   (DGlobal
                      (flags2, name1, (FStar_List.length tvars), t1, expr1))
               with
               | e ->
                   ((let uu____3802 =
                       let uu____3807 =
                         let uu____3808 = FStar_Util.print_exn e in
                         FStar_Util.format2
                           "Not translating definition for %s (%s)\n"
                           (FStar_Pervasives_Native.snd name1) uu____3808 in
                       (FStar_Errors.DefinitionNotTranslated, uu____3807) in
                     FStar_Errors.maybe_fatal_err uu____3802);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (flags2, name1, (FStar_List.length tvars), t1, EAny))))
          | { FStar_Extraction_ML_Syntax.mllb_name = name;
              FStar_Extraction_ML_Syntax.mllb_tysc = ts;
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3821;
              FStar_Extraction_ML_Syntax.mllb_def = uu____3822;
              FStar_Extraction_ML_Syntax.print_typ = uu____3823;_} ->
              ((let uu____3827 =
                  let uu____3832 =
                    FStar_Util.format1 "Not translating definition for %s\n"
                      name in
                  (FStar_Errors.DefinitionNotTranslated, uu____3832) in
                FStar_Errors.maybe_fatal_err uu____3827);
               (match ts with
                | FStar_Pervasives_Native.Some (idents,t) ->
                    let uu____3840 =
                      FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                    FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                      (FStar_String.concat ", " idents) uu____3840
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
      | (assumed,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Abbrev t)) ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args in
          if assumed
          then FStar_Pervasives_Native.None
          else
            (let uu____3876 =
               let uu____3877 =
                 let uu____3894 = translate_flags flags1 in
                 let uu____3897 = translate_type env1 t in
                 (name1, uu____3894, (FStar_List.length args), uu____3897) in
               DTypeAlias uu____3877 in
             FStar_Pervasives_Native.Some uu____3876)
      | (uu____3906,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args in
          let uu____3938 =
            let uu____3939 =
              let uu____3966 = translate_flags flags1 in
              let uu____3969 =
                FStar_List.map
                  (fun uu____3996  ->
                     match uu____3996 with
                     | (f,t) ->
                         let uu____4011 =
                           let uu____4016 = translate_type env1 t in
                           (uu____4016, false) in
                         (f, uu____4011)) fields in
              (name1, uu____3966, (FStar_List.length args), uu____3969) in
            DTypeFlat uu____3939 in
          FStar_Pervasives_Native.Some uu____3938
      | (uu____4039,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
          let name1 = ((env.module_name), name) in
          let flags2 = translate_flags flags1 in
          let env1 = FStar_List.fold_left extend_t env args in
          let uu____4076 =
            let uu____4077 =
              let uu____4110 =
                FStar_List.map
                  (fun uu____4155  ->
                     match uu____4155 with
                     | (cons1,ts) ->
                         let uu____4194 =
                           FStar_List.map
                             (fun uu____4221  ->
                                match uu____4221 with
                                | (name2,t) ->
                                    let uu____4236 =
                                      let uu____4241 = translate_type env1 t in
                                      (uu____4241, false) in
                                    (name2, uu____4236)) ts in
                         (cons1, uu____4194)) branches in
              (name1, flags2, (FStar_List.length args), uu____4110) in
            DTypeVariant uu____4077 in
          FStar_Pervasives_Native.Some uu____4076
      | (uu____4280,name,_mangled_name,uu____4283,uu____4284,uu____4285) ->
          ((let uu____4295 =
              let uu____4300 =
                FStar_Util.format1 "Not translating type definition for %s\n"
                  name in
              (FStar_Errors.DefinitionNotTranslated, uu____4300) in
            FStar_Errors.maybe_fatal_err uu____4295);
           FStar_Pervasives_Native.None)
and translate_type: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4304 = find_t env name in TBound uu____4304
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4306,t2) ->
          let uu____4308 =
            let uu____4313 = translate_type env t1 in
            let uu____4314 = translate_type env t2 in
            (uu____4313, uu____4314) in
          TArrow uu____4308
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4318 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4318 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4322 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4322 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4334 = FStar_Util.must (mk_width m) in TInt uu____4334
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4346 = FStar_Util.must (mk_width m) in TInt uu____4346
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4351 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4351 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4356 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4356 = "FStar.Buffer.buffer" ->
          let uu____4357 = translate_type env arg in TBuf uu____4357
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4358::[],p) when
          let uu____4362 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4362 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4400 = FStar_List.map (translate_type env) args in
          TTuple uu____4400
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4409 =
              let uu____4422 = FStar_List.map (translate_type env) args in
              (lid, uu____4422) in
            TApp uu____4409
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4431 = FStar_List.map (translate_type env) ts in
          TTuple uu____4431
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
    fun uu____4447  ->
      match uu____4447 with
      | (name,typ) ->
          let uu____4454 = translate_type env typ in
          { name; typ = uu____4454; mut = false }
and translate_expr: env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____4459 = find env name in EBound uu____4459
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4464 =
            let uu____4469 = FStar_Util.must (mk_op op) in
            let uu____4470 = FStar_Util.must (mk_width m) in
            (uu____4469, uu____4470) in
          EOp uu____4464
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4474 =
            let uu____4479 = FStar_Util.must (mk_bool_op op) in
            (uu____4479, Bool) in
          EOp uu____4474
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags1,{ FStar_Extraction_ML_Syntax.mllb_name = name;
                            FStar_Extraction_ML_Syntax.mllb_tysc =
                              FStar_Pervasives_Native.Some ([],typ);
                            FStar_Extraction_ML_Syntax.mllb_add_unit =
                              add_unit;
                            FStar_Extraction_ML_Syntax.mllb_def = body;
                            FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let is_mut =
            FStar_Util.for_some
              (fun uu___195_4509  ->
                 match uu___195_4509 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____4510 -> false) flags1 in
          let uu____4511 =
            if is_mut
            then
              let uu____4520 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____4525 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4525 = "FStar.ST.stackref" -> t
                | uu____4526 ->
                    let uu____4527 =
                      let uu____4528 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____4528 in
                    failwith uu____4527 in
              let uu____4531 =
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
                      (uu____4532,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____4534;
                    FStar_Extraction_ML_Syntax.loc = uu____4535;_} -> body1
                | uu____4538 ->
                    failwith "unexpected: bad desugaring of Mutable" in
              (uu____4520, uu____4531)
            else (typ, body) in
          (match uu____4511 with
           | (typ1,body1) ->
               let binder =
                 let uu____4543 = translate_type env typ1 in
                 { name; typ = uu____4543; mut = is_mut } in
               let body2 = translate_expr env body1 in
               let env1 = extend env name is_mut in
               let continuation1 = translate_expr env1 continuation in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4569 =
            let uu____4580 = translate_expr env expr in
            let uu____4581 = translate_branches env branches in
            (uu____4580, uu____4581) in
          EMatch uu____4569
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4595;
             FStar_Extraction_ML_Syntax.loc = uu____4596;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                v1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4598;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4599;_}::[])
          when
          (let uu____4604 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4604 = "FStar.HyperStack.ST.op_Bang") && (is_mutable env v1)
          -> let uu____4605 = find env v1 in EBound uu____4605
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4607;
             FStar_Extraction_ML_Syntax.loc = uu____4608;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                v1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4610;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4611;_}::e1::[])
          when
          (let uu____4617 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4617 = "FStar.HyperStack.ST.op_Colon_Equals") &&
            (is_mutable env v1)
          ->
          let uu____4618 =
            let uu____4623 =
              let uu____4624 = find env v1 in EBound uu____4624 in
            let uu____4625 = translate_expr env e1 in
            (uu____4623, uu____4625) in
          EAssign uu____4618
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4627;
                  FStar_Extraction_ML_Syntax.loc = uu____4628;_},uu____4629);
             FStar_Extraction_ML_Syntax.mlty = uu____4630;
             FStar_Extraction_ML_Syntax.loc = uu____4631;_},e1::e2::[])
          when
          (let uu____4642 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4642 = "FStar.Buffer.index") ||
            (let uu____4644 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4644 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____4645 =
            let uu____4650 = translate_expr env e1 in
            let uu____4651 = translate_expr env e2 in
            (uu____4650, uu____4651) in
          EBufRead uu____4645
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4653;
                  FStar_Extraction_ML_Syntax.loc = uu____4654;_},uu____4655);
             FStar_Extraction_ML_Syntax.mlty = uu____4656;
             FStar_Extraction_ML_Syntax.loc = uu____4657;_},e1::e2::[])
          when
          let uu____4666 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4666 = "FStar.Buffer.create" ->
          let uu____4667 =
            let uu____4674 = translate_expr env e1 in
            let uu____4675 = translate_expr env e2 in
            (Stack, uu____4674, uu____4675) in
          EBufCreate uu____4667
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4677;
                  FStar_Extraction_ML_Syntax.loc = uu____4678;_},uu____4679);
             FStar_Extraction_ML_Syntax.mlty = uu____4680;
             FStar_Extraction_ML_Syntax.loc = uu____4681;_},_e0::e1::e2::[])
          when
          let uu____4691 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4691 = "FStar.Buffer.rcreate" ->
          let uu____4692 =
            let uu____4699 = translate_expr env e1 in
            let uu____4700 = translate_expr env e2 in
            (Eternal, uu____4699, uu____4700) in
          EBufCreate uu____4692
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4702;
                  FStar_Extraction_ML_Syntax.loc = uu____4703;_},uu____4704);
             FStar_Extraction_ML_Syntax.mlty = uu____4705;
             FStar_Extraction_ML_Syntax.loc = uu____4706;_},e2::[])
          when
          let uu____4714 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4714 = "FStar.Buffer.createL" ->
          let rec list_elements acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____4752 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!" in
          let list_elements1 = list_elements [] in
          let uu____4760 =
            let uu____4767 =
              let uu____4770 = list_elements1 e2 in
              FStar_List.map (translate_expr env) uu____4770 in
            (Stack, uu____4767) in
          EBufCreateL uu____4760
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4776;
                  FStar_Extraction_ML_Syntax.loc = uu____4777;_},uu____4778);
             FStar_Extraction_ML_Syntax.mlty = uu____4779;
             FStar_Extraction_ML_Syntax.loc = uu____4780;_},e1::e2::_e3::[])
          when
          let uu____4790 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4790 = "FStar.Buffer.sub" ->
          let uu____4791 =
            let uu____4796 = translate_expr env e1 in
            let uu____4797 = translate_expr env e2 in
            (uu____4796, uu____4797) in
          EBufSub uu____4791
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4799;
                  FStar_Extraction_ML_Syntax.loc = uu____4800;_},uu____4801);
             FStar_Extraction_ML_Syntax.mlty = uu____4802;
             FStar_Extraction_ML_Syntax.loc = uu____4803;_},e1::e2::[])
          when
          let uu____4812 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4812 = "FStar.Buffer.join" -> translate_expr env e1
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
          uu____4827 = "FStar.Buffer.offset" ->
          let uu____4828 =
            let uu____4833 = translate_expr env e1 in
            let uu____4834 = translate_expr env e2 in
            (uu____4833, uu____4834) in
          EBufSub uu____4828
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4836;
                  FStar_Extraction_ML_Syntax.loc = uu____4837;_},uu____4838);
             FStar_Extraction_ML_Syntax.mlty = uu____4839;
             FStar_Extraction_ML_Syntax.loc = uu____4840;_},e1::e2::e3::[])
          when
          (let uu____4852 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4852 = "FStar.Buffer.upd") ||
            (let uu____4854 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4854 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____4855 =
            let uu____4862 = translate_expr env e1 in
            let uu____4863 = translate_expr env e2 in
            let uu____4864 = translate_expr env e3 in
            (uu____4862, uu____4863, uu____4864) in
          EBufWrite uu____4855
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4866;
             FStar_Extraction_ML_Syntax.loc = uu____4867;_},uu____4868::[])
          when
          let uu____4871 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4871 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4873;
             FStar_Extraction_ML_Syntax.loc = uu____4874;_},uu____4875::[])
          when
          let uu____4878 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4878 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4880;
                  FStar_Extraction_ML_Syntax.loc = uu____4881;_},uu____4882);
             FStar_Extraction_ML_Syntax.mlty = uu____4883;
             FStar_Extraction_ML_Syntax.loc = uu____4884;_},e1::e2::e3::e4::e5::[])
          when
          let uu____4896 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4896 = "FStar.Buffer.blit" ->
          let uu____4897 =
            let uu____4908 = translate_expr env e1 in
            let uu____4909 = translate_expr env e2 in
            let uu____4910 = translate_expr env e3 in
            let uu____4911 = translate_expr env e4 in
            let uu____4912 = translate_expr env e5 in
            (uu____4908, uu____4909, uu____4910, uu____4911, uu____4912) in
          EBufBlit uu____4897
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4914;
                  FStar_Extraction_ML_Syntax.loc = uu____4915;_},uu____4916);
             FStar_Extraction_ML_Syntax.mlty = uu____4917;
             FStar_Extraction_ML_Syntax.loc = uu____4918;_},e1::e2::e3::[])
          when
          let uu____4928 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4928 = "FStar.Buffer.fill" ->
          let uu____4929 =
            let uu____4936 = translate_expr env e1 in
            let uu____4937 = translate_expr env e2 in
            let uu____4938 = translate_expr env e3 in
            (uu____4936, uu____4937, uu____4938) in
          EBufFill uu____4929
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4940;
             FStar_Extraction_ML_Syntax.loc = uu____4941;_},uu____4942::[])
          when
          let uu____4945 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4945 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4947;
             FStar_Extraction_ML_Syntax.loc = uu____4948;_},e1::[])
          when
          let uu____4952 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4952 = "Obj.repr" ->
          let uu____4953 =
            let uu____4958 = translate_expr env e1 in (uu____4958, TAny) in
          ECast uu____4953
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____4961;
             FStar_Extraction_ML_Syntax.loc = uu____4962;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____4970 = FStar_Util.must (mk_width m) in
          let uu____4971 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____4970 uu____4971 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____4973;
             FStar_Extraction_ML_Syntax.loc = uu____4974;_},args)
          when is_bool_op op ->
          let uu____4982 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____4982 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____4984;
             FStar_Extraction_ML_Syntax.loc = uu____4985;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4987;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4988;_}::[])
          when is_machine_int m ->
          let uu____5003 =
            let uu____5008 = FStar_Util.must (mk_width m) in (uu____5008, c) in
          EConstant uu____5003
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5010;
             FStar_Extraction_ML_Syntax.loc = uu____5011;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5013;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5014;_}::[])
          when is_machine_int m ->
          let uu____5029 =
            let uu____5034 = FStar_Util.must (mk_width m) in (uu____5034, c) in
          EConstant uu____5029
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5035;
             FStar_Extraction_ML_Syntax.loc = uu____5036;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5038;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5039;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5045 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5046;
             FStar_Extraction_ML_Syntax.loc = uu____5047;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5049;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5050;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5056 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5058;
             FStar_Extraction_ML_Syntax.loc = uu____5059;_},arg::[])
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
            let uu____5066 =
              let uu____5071 = translate_expr env arg in
              (uu____5071, (TInt UInt64)) in
            ECast uu____5066
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5073 =
                 let uu____5078 = translate_expr env arg in
                 (uu____5078, (TInt UInt32)) in
               ECast uu____5073)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5080 =
                   let uu____5085 = translate_expr env arg in
                   (uu____5085, (TInt UInt16)) in
                 ECast uu____5080)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5087 =
                     let uu____5092 = translate_expr env arg in
                     (uu____5092, (TInt UInt8)) in
                   ECast uu____5087)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5094 =
                       let uu____5099 = translate_expr env arg in
                       (uu____5099, (TInt Int64)) in
                     ECast uu____5094)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5101 =
                         let uu____5106 = translate_expr env arg in
                         (uu____5106, (TInt Int32)) in
                       ECast uu____5101)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5108 =
                           let uu____5113 = translate_expr env arg in
                           (uu____5113, (TInt Int16)) in
                         ECast uu____5108)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5115 =
                             let uu____5120 = translate_expr env arg in
                             (uu____5120, (TInt Int8)) in
                           ECast uu____5115)
                        else
                          (let uu____5122 =
                             let uu____5129 =
                               let uu____5132 = translate_expr env arg in
                               [uu____5132] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5129) in
                           EApp uu____5122)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5143 =
            let uu____5150 = translate_expr env head1 in
            let uu____5151 = FStar_List.map (translate_expr env) args in
            (uu____5150, uu____5151) in
          EApp uu____5143
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5162 =
            let uu____5169 = translate_expr env head1 in
            let uu____5170 = FStar_List.map (translate_type env) ty_args in
            (uu____5169, uu____5170) in
          ETypApp uu____5162
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5178 =
            let uu____5183 = translate_expr env e1 in
            let uu____5184 = translate_type env t_to in
            (uu____5183, uu____5184) in
          ECast uu____5178
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5185,fields) ->
          let uu____5203 =
            let uu____5214 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5215 =
              FStar_List.map
                (fun uu____5234  ->
                   match uu____5234 with
                   | (field,expr) ->
                       let uu____5245 = translate_expr env expr in
                       (field, uu____5245)) fields in
            (uu____5214, uu____5215) in
          EFlat uu____5203
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5254 =
            let uu____5261 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____5262 = translate_expr env e1 in
            (uu____5261, uu____5262, (FStar_Pervasives_Native.snd path)) in
          EField uu____5254
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5265 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5279) ->
          let uu____5284 =
            let uu____5285 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1 in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5285 in
          failwith uu____5284
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5291 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____5291
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5297 = FStar_List.map (translate_expr env) es in
          ETuple uu____5297
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5300,cons1),es) ->
          let uu____5317 =
            let uu____5326 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5327 = FStar_List.map (translate_expr env) es in
            (uu____5326, cons1, uu____5327) in
          ECons uu____5317
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args in
          let env1 = add_binders env args in
          let uu____5350 =
            let uu____5359 = translate_expr env1 body in
            let uu____5360 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty in
            (binders, uu____5359, uu____5360) in
          EFun uu____5350
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5370 =
            let uu____5377 = translate_expr env e1 in
            let uu____5378 = translate_expr env e2 in
            let uu____5379 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31 in
            (uu____5377, uu____5378, uu____5379) in
          EIfThenElse uu____5370
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5381 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5388 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____5403 ->
          failwith "todo: translate_expr [MLE_Coerce]"
and assert_lid: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____5418 =
              let uu____5431 = FStar_List.map (translate_type env) ts in
              (lid, uu____5431) in
            TApp uu____5418
          else TQualified lid
      | uu____5437 -> failwith "invalid argument: assert_lid"
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
    fun uu____5463  ->
      match uu____5463 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____5489 = translate_pat env pat in
            (match uu____5489 with
             | (env1,pat1) ->
                 let uu____5500 = translate_expr env1 expr in
                 (pat1, uu____5500))
          else failwith "todo: translate_branch"
and translate_width:
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width
  =
  fun uu___196_5506  ->
    match uu___196_5506 with
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
          let uu____5570 =
            let uu____5571 =
              let uu____5576 = translate_width sw in (uu____5576, s) in
            PConstant uu____5571 in
          (env, uu____5570)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name false in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_" false in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5580,cons1),ps) ->
          let uu____5597 =
            FStar_List.fold_left
              (fun uu____5617  ->
                 fun p1  ->
                   match uu____5617 with
                   | (env1,acc) ->
                       let uu____5637 = translate_pat env1 p1 in
                       (match uu____5637 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____5597 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____5666,ps) ->
          let uu____5684 =
            FStar_List.fold_left
              (fun uu____5718  ->
                 fun uu____5719  ->
                   match (uu____5718, uu____5719) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____5788 = translate_pat env1 p1 in
                       (match uu____5788 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps in
          (match uu____5684 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____5850 =
            FStar_List.fold_left
              (fun uu____5870  ->
                 fun p1  ->
                   match uu____5870 with
                   | (env1,acc) ->
                       let uu____5890 = translate_pat env1 p1 in
                       (match uu____5890 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____5850 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____5917 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____5922 ->
          failwith "todo: translate_pat [MLP_Branch]"
and translate_constant: FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____5933 =
            let uu____5934 = FStar_String.list_of_string s in
            FStar_All.pipe_right uu____5934
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0")))) in
          if uu____5933
          then
            let uu____5941 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s in
            failwith uu____5941
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____5944) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____5959 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____5960 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____5961 ->
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
          let uu____5981 =
            let uu____5988 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____5988) in
          EApp uu____5981