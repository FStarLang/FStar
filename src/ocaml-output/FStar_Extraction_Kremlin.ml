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
  FStar_Pervasives_Native.tuple4
  | DTypeMutual of decl Prims.list[@@deriving show]
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
    match projectee with | DGlobal _0 -> true | uu____530 -> false
let __proj__DGlobal__item___0:
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,typ,expr)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DGlobal _0 -> _0
let uu___is_DFunction: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____618 -> false
let __proj__DFunction__item___0:
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr) FStar_Pervasives_Native.tuple7
  = fun projectee  -> match projectee with | DFunction _0 -> _0
let uu___is_DTypeAlias: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____722 -> false
let __proj__DTypeAlias__item___0:
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      Prims.int,typ) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0
let uu___is_DTypeFlat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____794 -> false
let __proj__DTypeFlat__item___0:
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      Prims.int,(Prims.string,(typ,Prims.bool) FStar_Pervasives_Native.tuple2)
                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0
let uu___is_DExternal: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____888 -> false
let __proj__DExternal__item___0:
  decl ->
    (cc FStar_Pervasives_Native.option,(Prims.string Prims.list,Prims.string)
                                         FStar_Pervasives_Native.tuple2,
      typ) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DExternal _0 -> _0
let uu___is_DTypeVariant: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____976 -> false
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
let uu___is_DTypeMutual: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeMutual _0 -> true | uu____1088 -> false
let __proj__DTypeMutual__item___0: decl -> decl Prims.list =
  fun projectee  -> match projectee with | DTypeMutual _0 -> _0
let uu___is_StdCall: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1107 -> false
let uu___is_CDecl: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1112 -> false
let uu___is_FastCall: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1117 -> false
let uu___is_Private: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1122 -> false
let uu___is_NoExtract: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____1127 -> false
let uu___is_CInline: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1132 -> false
let uu___is_Substitute: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1137 -> false
let uu___is_GCType: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1142 -> false
let uu___is_Comment: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1148 -> false
let __proj__Comment__item___0: flag -> Prims.string =
  fun projectee  -> match projectee with | Comment _0 -> _0
let uu___is_Eternal: lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1161 -> false
let uu___is_Stack: lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1166 -> false
let uu___is_EBound: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1172 -> false
let __proj__EBound__item___0: expr -> Prims.int =
  fun projectee  -> match projectee with | EBound _0 -> _0
let uu___is_EQualified: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1192 -> false
let __proj__EQualified__item___0:
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EQualified _0 -> _0
let uu___is_EConstant: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1228 -> false
let __proj__EConstant__item___0:
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EConstant _0 -> _0
let uu___is_EUnit: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1253 -> false
let uu___is_EApp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1265 -> false
let __proj__EApp__item___0:
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EApp _0 -> _0
let uu___is_ETypApp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1303 -> false
let __proj__ETypApp__item___0:
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ETypApp _0 -> _0
let uu___is_ELet: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1341 -> false
let __proj__ELet__item___0:
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ELet _0 -> _0
let uu___is_EIfThenElse: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1379 -> false
let __proj__EIfThenElse__item___0:
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0
let uu___is_ESequence: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1413 -> false
let __proj__ESequence__item___0: expr -> expr Prims.list =
  fun projectee  -> match projectee with | ESequence _0 -> _0
let uu___is_EAssign: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1437 -> false
let __proj__EAssign__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EAssign _0 -> _0
let uu___is_EBufCreate: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____1469 -> false
let __proj__EBufCreate__item___0:
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0
let uu___is_EBufRead: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____1505 -> false
let __proj__EBufRead__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufRead _0 -> _0
let uu___is_EBufWrite: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____1537 -> false
let __proj__EBufWrite__item___0:
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0
let uu___is_EBufSub: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____1573 -> false
let __proj__EBufSub__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufSub _0 -> _0
let uu___is_EBufBlit: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____1609 -> false
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
    match projectee with | EOp _0 -> true | uu____1711 -> false
let __proj__EOp__item___0: expr -> (op,width) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EOp _0 -> _0
let uu___is_ECast: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1741 -> false
let __proj__ECast__item___0:
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ECast _0 -> _0
let uu___is_EPushFrame: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1766 -> false
let uu___is_EPopFrame: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1771 -> false
let uu___is_EBool: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1777 -> false
let __proj__EBool__item___0: expr -> Prims.bool =
  fun projectee  -> match projectee with | EBool _0 -> _0
let uu___is_EAny: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1790 -> false
let uu___is_EAbort: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1795 -> false
let uu___is_EReturn: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1801 -> false
let __proj__EReturn__item___0: expr -> expr =
  fun projectee  -> match projectee with | EReturn _0 -> _0
let uu___is_EFlat: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1825 -> false
let __proj__EFlat__item___0:
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EFlat _0 -> _0
let uu___is_EField: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____1875 -> false
let __proj__EField__item___0:
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EField _0 -> _0
let uu___is_EWhile: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____1911 -> false
let __proj__EWhile__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EWhile _0 -> _0
let uu___is_EBufCreateL: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____1943 -> false
let __proj__EBufCreateL__item___0:
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0
let uu___is_ETuple: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____1977 -> false
let __proj__ETuple__item___0: expr -> expr Prims.list =
  fun projectee  -> match projectee with | ETuple _0 -> _0
let uu___is_ECons: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2005 -> false
let __proj__ECons__item___0:
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ECons _0 -> _0
let uu___is_EBufFill: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2049 -> false
let __proj__EBufFill__item___0:
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufFill _0 -> _0
let uu___is_EString: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2081 -> false
let __proj__EString__item___0: expr -> Prims.string =
  fun projectee  -> match projectee with | EString _0 -> _0
let uu___is_EFun: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2103 -> false
let __proj__EFun__item___0:
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EFun _0 -> _0
let uu___is_EAbortS: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2141 -> false
let __proj__EAbortS__item___0: expr -> Prims.string =
  fun projectee  -> match projectee with | EAbortS _0 -> _0
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____2154 -> false
let uu___is_AddW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2159 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____2164 -> false
let uu___is_SubW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2169 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____2174 -> false
let uu___is_DivW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2179 -> false
let uu___is_Mult: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2184 -> false
let uu___is_MultW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2189 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____2194 -> false
let uu___is_BOr: op -> Prims.bool =
  fun projectee  -> match projectee with | BOr  -> true | uu____2199 -> false
let uu___is_BAnd: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2204 -> false
let uu___is_BXor: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2209 -> false
let uu___is_BShiftL: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2214 -> false
let uu___is_BShiftR: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2219 -> false
let uu___is_BNot: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2224 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2229 -> false
let uu___is_Neq: op -> Prims.bool =
  fun projectee  -> match projectee with | Neq  -> true | uu____2234 -> false
let uu___is_Lt: op -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2239 -> false
let uu___is_Lte: op -> Prims.bool =
  fun projectee  -> match projectee with | Lte  -> true | uu____2244 -> false
let uu___is_Gt: op -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2249 -> false
let uu___is_Gte: op -> Prims.bool =
  fun projectee  -> match projectee with | Gte  -> true | uu____2254 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____2259 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____2264 -> false
let uu___is_Xor: op -> Prims.bool =
  fun projectee  -> match projectee with | Xor  -> true | uu____2269 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____2274 -> false
let uu___is_PUnit: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2279 -> false
let uu___is_PBool: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2285 -> false
let __proj__PBool__item___0: pattern -> Prims.bool =
  fun projectee  -> match projectee with | PBool _0 -> _0
let uu___is_PVar: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2299 -> false
let __proj__PVar__item___0: pattern -> binder =
  fun projectee  -> match projectee with | PVar _0 -> _0
let uu___is_PCons: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2319 -> false
let __proj__PCons__item___0:
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PCons _0 -> _0
let uu___is_PTuple: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2353 -> false
let __proj__PTuple__item___0: pattern -> pattern Prims.list =
  fun projectee  -> match projectee with | PTuple _0 -> _0
let uu___is_PRecord: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2379 -> false
let __proj__PRecord__item___0:
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list
  = fun projectee  -> match projectee with | PRecord _0 -> _0
let uu___is_UInt8: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____2410 -> false
let uu___is_UInt16: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2415 -> false
let uu___is_UInt32: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2420 -> false
let uu___is_UInt64: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2425 -> false
let uu___is_Int8: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2430 -> false
let uu___is_Int16: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2435 -> false
let uu___is_Int32: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2440 -> false
let uu___is_Int64: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2445 -> false
let uu___is_Bool: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2450 -> false
let uu___is_CInt: width -> Prims.bool =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____2455 -> false
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
    match projectee with | TInt _0 -> true | uu____2482 -> false
let __proj__TInt__item___0: typ -> width =
  fun projectee  -> match projectee with | TInt _0 -> _0
let uu___is_TBuf: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2496 -> false
let __proj__TBuf__item___0: typ -> typ =
  fun projectee  -> match projectee with | TBuf _0 -> _0
let uu___is_TUnit: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2509 -> false
let uu___is_TQualified: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2521 -> false
let __proj__TQualified__item___0:
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TQualified _0 -> _0
let uu___is_TBool: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2552 -> false
let uu___is_TAny: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2557 -> false
let uu___is_TArrow: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2567 -> false
let __proj__TArrow__item___0: typ -> (typ,typ) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TArrow _0 -> _0
let uu___is_TBound: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2593 -> false
let __proj__TBound__item___0: typ -> Prims.int =
  fun projectee  -> match projectee with | TBound _0 -> _0
let uu___is_TApp: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2619 -> false
let __proj__TApp__item___0:
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TApp _0 -> _0
let uu___is_TTuple: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____2671 -> false
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
let current_version: version = Prims.parse_int "25"
type file = (Prims.string,program) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
type binary_format = (version,file Prims.list) FStar_Pervasives_Native.tuple2
[@@deriving show]
let fst3:
  'Auu____2752 'Auu____2753 'Auu____2754 .
    ('Auu____2754,'Auu____2753,'Auu____2752) FStar_Pervasives_Native.tuple3
      -> 'Auu____2754
  = fun uu____2764  -> match uu____2764 with | (x,uu____2772,uu____2773) -> x
let snd3:
  'Auu____2782 'Auu____2783 'Auu____2784 .
    ('Auu____2784,'Auu____2783,'Auu____2782) FStar_Pervasives_Native.tuple3
      -> 'Auu____2783
  = fun uu____2794  -> match uu____2794 with | (uu____2801,x,uu____2803) -> x
let thd3:
  'Auu____2812 'Auu____2813 'Auu____2814 .
    ('Auu____2814,'Auu____2813,'Auu____2812) FStar_Pervasives_Native.tuple3
      -> 'Auu____2812
  = fun uu____2824  -> match uu____2824 with | (uu____2831,uu____2832,x) -> x
let mk_width: Prims.string -> width FStar_Pervasives_Native.option =
  fun uu___127_2839  ->
    match uu___127_2839 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____2842 -> FStar_Pervasives_Native.None
let mk_bool_op: Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___128_2848  ->
    match uu___128_2848 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____2851 -> FStar_Pervasives_Native.None
let is_bool_op: Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None
let mk_op: Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___129_2863  ->
    match uu___129_2863 with
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
    | uu____2866 -> FStar_Pervasives_Native.None
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
        let uu___134_2988 = env in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___134_2988.names_t);
          module_name = (uu___134_2988.module_name)
        }
let extend_t: env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___135_2997 = env in
      {
        names = (uu___135_2997.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___135_2997.module_name)
      }
let find_name: env -> Prims.string -> name =
  fun env  ->
    fun x  ->
      let uu____3006 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names in
      match uu____3006 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
let is_mutable: env -> Prims.string -> Prims.bool =
  fun env  -> fun x  -> let uu____3020 = find_name env x in uu____3020.mut
let find: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____3037 ->
          let uu____3038 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____3038
let find_t: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____3055 ->
          let uu____3056 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____3056
let add_binders:
  'Auu____3065 'Auu____3066 .
    env ->
      ((Prims.string,'Auu____3066) FStar_Pervasives_Native.tuple2,'Auu____3065)
        FStar_Pervasives_Native.tuple2 Prims.list -> env
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____3109  ->
             match uu____3109 with
             | ((name,uu____3119),uu____3120) -> extend env1 name false) env
        binders
let rec translate: FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____3255  ->
    match uu____3255 with
    | FStar_Extraction_ML_Syntax.MLLib modules1 ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3315 = m in
               match uu____3315 with
               | ((prefix1,final),uu____3336,uu____3337) ->
                   FStar_String.concat "."
                     (FStar_List.append prefix1 [final]) in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____3369 = translate_module m in
                FStar_Pervasives_Native.Some uu____3369)
             with
             | e ->
                 ((let uu____3378 = FStar_Util.print_exn e in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3378);
                  FStar_Pervasives_Native.None)) modules1
and translate_module:
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
    (FStar_Extraction_ML_Syntax.mlsig,FStar_Extraction_ML_Syntax.mlmodule)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,FStar_Extraction_ML_Syntax.mllib)
    FStar_Pervasives_Native.tuple3 -> file
  =
  fun uu____3379  ->
    match uu____3379 with
    | (module_name,modul,uu____3400) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name] in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.filter_map (translate_decl (empty module_name1))
                decls
          | uu____3443 ->
              failwith "Unexpected standalone interface or nested modules" in
        ((FStar_String.concat "_" module_name1), program)
and translate_flags:
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list =
  fun flags  ->
    FStar_List.choose
      (fun uu___130_3458  ->
         match uu___130_3458 with
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
         | uu____3462 -> FStar_Pervasives_Native.None) flags
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
                            (name,uu____3470);
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3473;
                          FStar_Extraction_ML_Syntax.mllb_def =
                            {
                              FStar_Extraction_ML_Syntax.expr =
                                FStar_Extraction_ML_Syntax.MLE_Fun
                                (args,body);
                              FStar_Extraction_ML_Syntax.mlty = uu____3476;
                              FStar_Extraction_ML_Syntax.loc = uu____3477;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____3478;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___131_3499  ->
                 match uu___131_3499 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____3500 -> false) flags in
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun uu____3513  ->
                   match uu____3513 with
                   | (name1,uu____3519) -> extend_t env2 name1) env1 tvars in
          let rec find_return_type i uu___132_3526 =
            match uu___132_3526 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3527,uu____3528,t)
                when i > (Prims.parse_int "0") ->
                find_return_type (i - (Prims.parse_int "1")) t
            | t -> t in
          let t =
            let uu____3532 = find_return_type (FStar_List.length args) t0 in
            translate_type env2 uu____3532 in
          let binders = translate_binders env2 args in
          let env3 = add_binders env2 args in
          let name1 = ((env3.module_name), name) in
          let flags1 =
            match t0 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun
                (uu____3555,FStar_Extraction_ML_Syntax.E_GHOST ,uu____3556)
                ->
                let uu____3557 = translate_flags flags in NoExtract ::
                  uu____3557
            | uu____3560 -> translate_flags flags in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
               let uu____3565 =
                 let uu____3566 =
                   let uu____3581 = translate_type env3 t0 in
                   (FStar_Pervasives_Native.None, name1, uu____3581) in
                 DExternal uu____3566 in
               FStar_Pervasives_Native.Some uu____3565
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
                            (name,uu____3641);
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3644;
                          FStar_Extraction_ML_Syntax.mllb_def =
                            {
                              FStar_Extraction_ML_Syntax.expr =
                                FStar_Extraction_ML_Syntax.MLE_Coerce
                                ({
                                   FStar_Extraction_ML_Syntax.expr =
                                     FStar_Extraction_ML_Syntax.MLE_Fun
                                     (args,body);
                                   FStar_Extraction_ML_Syntax.mlty =
                                     uu____3647;
                                   FStar_Extraction_ML_Syntax.loc =
                                     uu____3648;_},uu____3649,uu____3650);
                              FStar_Extraction_ML_Syntax.mlty = uu____3651;
                              FStar_Extraction_ML_Syntax.loc = uu____3652;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____3653;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___131_3674  ->
                 match uu___131_3674 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____3675 -> false) flags in
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun uu____3688  ->
                   match uu____3688 with
                   | (name1,uu____3694) -> extend_t env2 name1) env1 tvars in
          let rec find_return_type i uu___132_3701 =
            match uu___132_3701 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3702,uu____3703,t)
                when i > (Prims.parse_int "0") ->
                find_return_type (i - (Prims.parse_int "1")) t
            | t -> t in
          let t =
            let uu____3707 = find_return_type (FStar_List.length args) t0 in
            translate_type env2 uu____3707 in
          let binders = translate_binders env2 args in
          let env3 = add_binders env2 args in
          let name1 = ((env3.module_name), name) in
          let flags1 =
            match t0 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun
                (uu____3730,FStar_Extraction_ML_Syntax.E_GHOST ,uu____3731)
                ->
                let uu____3732 = translate_flags flags in NoExtract ::
                  uu____3732
            | uu____3735 -> translate_flags flags in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
               let uu____3740 =
                 let uu____3741 =
                   let uu____3756 = translate_type env3 t0 in
                   (FStar_Pervasives_Native.None, name1, uu____3756) in
                 DExternal uu____3741 in
               FStar_Pervasives_Native.Some uu____3740
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
                            (name,uu____3816);
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some ([],t);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3818;
                          FStar_Extraction_ML_Syntax.mllb_def = expr;
                          FStar_Extraction_ML_Syntax.print_typ = uu____3820;_}::[])
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
               ((let uu____3868 = FStar_Util.print_exn e in
                 FStar_Util.print2
                   "Warning: not translating definition for %s (%s)\n"
                   (FStar_Pervasives_Native.snd name1) uu____3868);
                FStar_Pervasives_Native.Some
                  (DGlobal (flags1, name1, t1, EAny))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (uu____3879,uu____3880,{
                                   FStar_Extraction_ML_Syntax.mllb_name =
                                     (name,uu____3882);
                                   FStar_Extraction_ML_Syntax.mllb_tysc = ts;
                                   FStar_Extraction_ML_Syntax.mllb_add_unit =
                                     uu____3884;
                                   FStar_Extraction_ML_Syntax.mllb_def =
                                     uu____3885;
                                   FStar_Extraction_ML_Syntax.print_typ =
                                     uu____3886;_}::uu____3887)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           (match ts with
            | FStar_Pervasives_Native.Some (idents,t) ->
                let uu____3902 =
                  let uu____3903 =
                    FStar_List.map FStar_Pervasives_Native.fst idents in
                  FStar_String.concat ", " uu____3903 in
                let uu____3910 =
                  FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                  uu____3902 uu____3910
            | FStar_Pervasives_Native.None  -> ());
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Let uu____3913 ->
          failwith "impossible"
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3916 ->
          FStar_Pervasives_Native.None
      | FStar_Extraction_ML_Syntax.MLM_Ty (ty_decl::[]) ->
          translate_single_type_decl env ty_decl
      | FStar_Extraction_ML_Syntax.MLM_Ty ty_decls ->
          let rec traverse f xs =
            match xs with
            | [] -> FStar_Pervasives_Native.Some []
            | o::os ->
                let uu____3957 = traverse f os in
                (match uu____3957 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some os' ->
                     let uu____3975 = f o in
                     (match uu____3975 with
                      | FStar_Pervasives_Native.None  ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some o' ->
                          FStar_Pervasives_Native.Some (o' :: os'))) in
          let uu____3987 = traverse (translate_single_type_decl env) ty_decls in
          (match uu____3987 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some decls ->
               FStar_Pervasives_Native.Some (DTypeMutual decls))
      | FStar_Extraction_ML_Syntax.MLM_Ty [] ->
          (FStar_Util.print_string
             "Impossible!! Empty block of mutually recursive type declarations";
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Top uu____4002 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____4005 ->
          failwith "todo: translate_decl [MLM_Exn]"
and translate_single_type_decl:
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ty_decl  ->
      match ty_decl with
      | (assumed,name,_mangled_name,args,uu____4026,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Abbrev t)) ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____4053  ->
                   match uu____4053 with
                   | (name2,uu____4059) -> extend_t env1 name2) env args in
          if assumed
          then FStar_Pervasives_Native.None
          else
            (let uu____4063 =
               let uu____4064 =
                 let uu____4077 = translate_type env1 t in
                 (name1, (FStar_List.length args), uu____4077) in
               DTypeAlias uu____4064 in
             FStar_Pervasives_Native.Some uu____4063)
      | (uu____4084,name,_mangled_name,args,uu____4088,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____4121  ->
                   match uu____4121 with
                   | (name2,uu____4127) -> extend_t env1 name2) env args in
          let uu____4128 =
            let uu____4129 =
              let uu____4152 =
                FStar_List.map
                  (fun uu____4179  ->
                     match uu____4179 with
                     | (f,t) ->
                         let uu____4194 =
                           let uu____4199 = translate_type env1 t in
                           (uu____4199, false) in
                         (f, uu____4194)) fields in
              (name1, (FStar_List.length args), uu____4152) in
            DTypeFlat uu____4129 in
          FStar_Pervasives_Native.Some uu____4128
      | (uu____4220,name,_mangled_name,args,attrs,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
          let name1 = ((env.module_name), name) in
          let flags = translate_flags attrs in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____4266  ->
                   match uu____4266 with
                   | (name2,uu____4272) -> extend_t env1 name2) env args in
          let uu____4273 =
            let uu____4274 =
              let uu____4307 =
                FStar_List.map
                  (fun uu____4352  ->
                     match uu____4352 with
                     | (cons1,ts) ->
                         let uu____4391 =
                           FStar_List.map
                             (fun uu____4418  ->
                                match uu____4418 with
                                | (name2,t) ->
                                    let uu____4433 =
                                      let uu____4438 = translate_type env1 t in
                                      (uu____4438, false) in
                                    (name2, uu____4433)) ts in
                         (cons1, uu____4391)) branches in
              (name1, flags, (FStar_List.length args), uu____4307) in
            DTypeVariant uu____4274 in
          FStar_Pervasives_Native.Some uu____4273
and translate_type: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var (name,uu____4480) ->
          let uu____4481 = find_t env name in TBound uu____4481
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4483,t2) ->
          let uu____4485 =
            let uu____4490 = translate_type env t1 in
            let uu____4491 = translate_type env t2 in
            (uu____4490, uu____4491) in
          TArrow uu____4485
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4495 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4495 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4499 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4499 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4511 = FStar_Util.must (mk_width m) in TInt uu____4511
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4523 = FStar_Util.must (mk_width m) in TInt uu____4523
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4528 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4528 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4533 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4533 = "FStar.Buffer.buffer" ->
          let uu____4534 = translate_type env arg in TBuf uu____4534
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4535::[],p) when
          let uu____4539 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4539 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4577 = FStar_List.map (translate_type env) args in
          TTuple uu____4577
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4586 =
              let uu____4599 = FStar_List.map (translate_type env) args in
              (lid, uu____4599) in
            TApp uu____4586
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4608 = FStar_List.map (translate_type env) ts in
          TTuple uu____4608
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
    fun uu____4624  ->
      match uu____4624 with
      | ((name,uu____4630),typ) ->
          let uu____4636 = translate_type env typ in
          { name; typ = uu____4636; mut = false }
and translate_expr: env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____4641) ->
          let uu____4642 = find env name in EBound uu____4642
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4647 =
            let uu____4652 = FStar_Util.must (mk_op op) in
            let uu____4653 = FStar_Util.must (mk_width m) in
            (uu____4652, uu____4653) in
          EOp uu____4647
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4657 =
            let uu____4662 = FStar_Util.must (mk_bool_op op) in
            (uu____4662, Bool) in
          EOp uu____4657
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags,{
                           FStar_Extraction_ML_Syntax.mllb_name =
                             (name,uu____4667);
                           FStar_Extraction_ML_Syntax.mllb_tysc =
                             FStar_Pervasives_Native.Some ([],typ);
                           FStar_Extraction_ML_Syntax.mllb_add_unit =
                             add_unit;
                           FStar_Extraction_ML_Syntax.mllb_def = body;
                           FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let is_mut =
            FStar_Util.for_some
              (fun uu___133_4693  ->
                 match uu___133_4693 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____4694 -> false) flags in
          let uu____4695 =
            if is_mut
            then
              let uu____4704 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____4709 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4709 = "FStar.ST.stackref" -> t
                | uu____4710 ->
                    let uu____4711 =
                      let uu____4712 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____4712 in
                    failwith uu____4711 in
              let uu____4715 =
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
                      (uu____4716,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____4718;
                    FStar_Extraction_ML_Syntax.loc = uu____4719;_} -> body1
                | uu____4722 ->
                    failwith "unexpected: bad desugaring of Mutable" in
              (uu____4704, uu____4715)
            else (typ, body) in
          (match uu____4695 with
           | (typ1,body1) ->
               let binder =
                 let uu____4727 = translate_type env typ1 in
                 { name; typ = uu____4727; mut = is_mut } in
               let body2 = translate_expr env body1 in
               let env1 = extend env name is_mut in
               let continuation1 = translate_expr env1 continuation in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4753 =
            let uu____4764 = translate_expr env expr in
            let uu____4765 = translate_branches env branches in
            (uu____4764, uu____4765) in
          EMatch uu____4753
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4779;
             FStar_Extraction_ML_Syntax.loc = uu____4780;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____4782);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4783;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4784;_}::[])
          when
          (let uu____4789 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4789 = "FStar.HyperStack.ST.op_Bang") && (is_mutable env v1)
          -> let uu____4790 = find env v1 in EBound uu____4790
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4792;
             FStar_Extraction_ML_Syntax.loc = uu____4793;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____4795);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4796;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4797;_}::e1::[])
          when
          (let uu____4803 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4803 = "FStar.HyperStack.ST.op_Colon_Equals") &&
            (is_mutable env v1)
          ->
          let uu____4804 =
            let uu____4809 =
              let uu____4810 = find env v1 in EBound uu____4810 in
            let uu____4811 = translate_expr env e1 in
            (uu____4809, uu____4811) in
          EAssign uu____4804
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4813;
                  FStar_Extraction_ML_Syntax.loc = uu____4814;_},uu____4815);
             FStar_Extraction_ML_Syntax.mlty = uu____4816;
             FStar_Extraction_ML_Syntax.loc = uu____4817;_},e1::e2::[])
          when
          (let uu____4828 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4828 = "FStar.Buffer.index") ||
            (let uu____4830 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4830 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____4831 =
            let uu____4836 = translate_expr env e1 in
            let uu____4837 = translate_expr env e2 in
            (uu____4836, uu____4837) in
          EBufRead uu____4831
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4839;
                  FStar_Extraction_ML_Syntax.loc = uu____4840;_},uu____4841);
             FStar_Extraction_ML_Syntax.mlty = uu____4842;
             FStar_Extraction_ML_Syntax.loc = uu____4843;_},e1::e2::[])
          when
          let uu____4852 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4852 = "FStar.Buffer.create" ->
          let uu____4853 =
            let uu____4860 = translate_expr env e1 in
            let uu____4861 = translate_expr env e2 in
            (Stack, uu____4860, uu____4861) in
          EBufCreate uu____4853
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
             FStar_Extraction_ML_Syntax.loc = uu____4867;_},_e0::e1::e2::[])
          when
          let uu____4877 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4877 = "FStar.Buffer.rcreate" ->
          let uu____4878 =
            let uu____4885 = translate_expr env e1 in
            let uu____4886 = translate_expr env e2 in
            (Eternal, uu____4885, uu____4886) in
          EBufCreate uu____4878
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4888;
                  FStar_Extraction_ML_Syntax.loc = uu____4889;_},uu____4890);
             FStar_Extraction_ML_Syntax.mlty = uu____4891;
             FStar_Extraction_ML_Syntax.loc = uu____4892;_},e2::[])
          when
          let uu____4900 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4900 = "FStar.Buffer.createL" ->
          let rec list_elements1 acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements1 (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____4938 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!" in
          let list_elements2 = list_elements1 [] in
          let uu____4946 =
            let uu____4953 =
              let uu____4956 = list_elements2 e2 in
              FStar_List.map (translate_expr env) uu____4956 in
            (Stack, uu____4953) in
          EBufCreateL uu____4946
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4962;
                  FStar_Extraction_ML_Syntax.loc = uu____4963;_},uu____4964);
             FStar_Extraction_ML_Syntax.mlty = uu____4965;
             FStar_Extraction_ML_Syntax.loc = uu____4966;_},e1::e2::_e3::[])
          when
          let uu____4976 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4976 = "FStar.Buffer.sub" ->
          let uu____4977 =
            let uu____4982 = translate_expr env e1 in
            let uu____4983 = translate_expr env e2 in
            (uu____4982, uu____4983) in
          EBufSub uu____4977
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4985;
                  FStar_Extraction_ML_Syntax.loc = uu____4986;_},uu____4987);
             FStar_Extraction_ML_Syntax.mlty = uu____4988;
             FStar_Extraction_ML_Syntax.loc = uu____4989;_},e1::e2::[])
          when
          let uu____4998 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4998 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5000;
                  FStar_Extraction_ML_Syntax.loc = uu____5001;_},uu____5002);
             FStar_Extraction_ML_Syntax.mlty = uu____5003;
             FStar_Extraction_ML_Syntax.loc = uu____5004;_},e1::e2::[])
          when
          let uu____5013 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5013 = "FStar.Buffer.offset" ->
          let uu____5014 =
            let uu____5019 = translate_expr env e1 in
            let uu____5020 = translate_expr env e2 in
            (uu____5019, uu____5020) in
          EBufSub uu____5014
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5022;
                  FStar_Extraction_ML_Syntax.loc = uu____5023;_},uu____5024);
             FStar_Extraction_ML_Syntax.mlty = uu____5025;
             FStar_Extraction_ML_Syntax.loc = uu____5026;_},e1::e2::e3::[])
          when
          (let uu____5038 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5038 = "FStar.Buffer.upd") ||
            (let uu____5040 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5040 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____5041 =
            let uu____5048 = translate_expr env e1 in
            let uu____5049 = translate_expr env e2 in
            let uu____5050 = translate_expr env e3 in
            (uu____5048, uu____5049, uu____5050) in
          EBufWrite uu____5041
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5052;
             FStar_Extraction_ML_Syntax.loc = uu____5053;_},uu____5054::[])
          when
          let uu____5057 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5057 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5059;
             FStar_Extraction_ML_Syntax.loc = uu____5060;_},uu____5061::[])
          when
          let uu____5064 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5064 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5066;
                  FStar_Extraction_ML_Syntax.loc = uu____5067;_},uu____5068);
             FStar_Extraction_ML_Syntax.mlty = uu____5069;
             FStar_Extraction_ML_Syntax.loc = uu____5070;_},e1::e2::e3::e4::e5::[])
          when
          let uu____5082 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5082 = "FStar.Buffer.blit" ->
          let uu____5083 =
            let uu____5094 = translate_expr env e1 in
            let uu____5095 = translate_expr env e2 in
            let uu____5096 = translate_expr env e3 in
            let uu____5097 = translate_expr env e4 in
            let uu____5098 = translate_expr env e5 in
            (uu____5094, uu____5095, uu____5096, uu____5097, uu____5098) in
          EBufBlit uu____5083
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5100;
                  FStar_Extraction_ML_Syntax.loc = uu____5101;_},uu____5102);
             FStar_Extraction_ML_Syntax.mlty = uu____5103;
             FStar_Extraction_ML_Syntax.loc = uu____5104;_},e1::e2::e3::[])
          when
          let uu____5114 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5114 = "FStar.Buffer.fill" ->
          let uu____5115 =
            let uu____5122 = translate_expr env e1 in
            let uu____5123 = translate_expr env e2 in
            let uu____5124 = translate_expr env e3 in
            (uu____5122, uu____5123, uu____5124) in
          EBufFill uu____5115
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5126;
             FStar_Extraction_ML_Syntax.loc = uu____5127;_},uu____5128::[])
          when
          let uu____5131 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5131 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5133;
             FStar_Extraction_ML_Syntax.loc = uu____5134;_},e1::[])
          when
          let uu____5138 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5138 = "Obj.repr" ->
          let uu____5139 =
            let uu____5144 = translate_expr env e1 in (uu____5144, TAny) in
          ECast uu____5139
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5147;
             FStar_Extraction_ML_Syntax.loc = uu____5148;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5156 = FStar_Util.must (mk_width m) in
          let uu____5157 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____5156 uu____5157 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5159;
             FStar_Extraction_ML_Syntax.loc = uu____5160;_},args)
          when is_bool_op op ->
          let uu____5168 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____5168 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5170;
             FStar_Extraction_ML_Syntax.loc = uu____5171;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5173;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5174;_}::[])
          when is_machine_int m ->
          let uu____5189 =
            let uu____5194 = FStar_Util.must (mk_width m) in (uu____5194, c) in
          EConstant uu____5189
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5196;
             FStar_Extraction_ML_Syntax.loc = uu____5197;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5199;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5200;_}::[])
          when is_machine_int m ->
          let uu____5215 =
            let uu____5220 = FStar_Util.must (mk_width m) in (uu____5220, c) in
          EConstant uu____5215
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5221;
             FStar_Extraction_ML_Syntax.loc = uu____5222;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5224;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5225;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5231 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5233;
             FStar_Extraction_ML_Syntax.loc = uu____5234;_},arg::[])
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
            let uu____5241 =
              let uu____5246 = translate_expr env arg in
              (uu____5246, (TInt UInt64)) in
            ECast uu____5241
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5248 =
                 let uu____5253 = translate_expr env arg in
                 (uu____5253, (TInt UInt32)) in
               ECast uu____5248)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5255 =
                   let uu____5260 = translate_expr env arg in
                   (uu____5260, (TInt UInt16)) in
                 ECast uu____5255)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5262 =
                     let uu____5267 = translate_expr env arg in
                     (uu____5267, (TInt UInt8)) in
                   ECast uu____5262)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5269 =
                       let uu____5274 = translate_expr env arg in
                       (uu____5274, (TInt Int64)) in
                     ECast uu____5269)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5276 =
                         let uu____5281 = translate_expr env arg in
                         (uu____5281, (TInt Int32)) in
                       ECast uu____5276)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5283 =
                           let uu____5288 = translate_expr env arg in
                           (uu____5288, (TInt Int16)) in
                         ECast uu____5283)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5290 =
                             let uu____5295 = translate_expr env arg in
                             (uu____5295, (TInt Int8)) in
                           ECast uu____5290)
                        else
                          (let uu____5297 =
                             let uu____5304 =
                               let uu____5307 = translate_expr env arg in
                               [uu____5307] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5304) in
                           EApp uu____5297)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5318 =
            let uu____5325 = translate_expr env head1 in
            let uu____5326 = FStar_List.map (translate_expr env) args in
            (uu____5325, uu____5326) in
          EApp uu____5318
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5337 =
            let uu____5344 = translate_expr env head1 in
            let uu____5345 = FStar_List.map (translate_type env) ty_args in
            (uu____5344, uu____5345) in
          ETypApp uu____5337
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5353 =
            let uu____5358 = translate_expr env e1 in
            let uu____5359 = translate_type env t_to in
            (uu____5358, uu____5359) in
          ECast uu____5353
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5360,fields) ->
          let uu____5378 =
            let uu____5389 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5390 =
              FStar_List.map
                (fun uu____5409  ->
                   match uu____5409 with
                   | (field,expr) ->
                       let uu____5420 = translate_expr env expr in
                       (field, uu____5420)) fields in
            (uu____5389, uu____5390) in
          EFlat uu____5378
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5429 =
            let uu____5436 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____5437 = translate_expr env e1 in
            (uu____5436, uu____5437, (FStar_Pervasives_Native.snd path)) in
          EField uu____5429
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5440 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5454) ->
          let uu____5459 =
            let uu____5460 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1 in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5460 in
          failwith uu____5459
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5466 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____5466
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5472 = FStar_List.map (translate_expr env) es in
          ETuple uu____5472
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5475,cons1),es) ->
          let uu____5492 =
            let uu____5501 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5502 = FStar_List.map (translate_expr env) es in
            (uu____5501, cons1, uu____5502) in
          ECons uu____5492
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args in
          let env1 = add_binders env args in
          let uu____5525 =
            let uu____5534 = translate_expr env1 body in
            let uu____5535 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty in
            (binders, uu____5534, uu____5535) in
          EFun uu____5525
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5545 =
            let uu____5552 = translate_expr env e1 in
            let uu____5553 = translate_expr env e2 in
            let uu____5554 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31 in
            (uu____5552, uu____5553, uu____5554) in
          EIfThenElse uu____5545
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5556 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5563 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____5578 ->
          failwith "todo: translate_expr [MLE_Coerce]"
and assert_lid: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____5593 =
              let uu____5606 = FStar_List.map (translate_type env) ts in
              (lid, uu____5606) in
            TApp uu____5593
          else TQualified lid
      | uu____5612 -> failwith "invalid argument: assert_lid"
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
    fun uu____5638  ->
      match uu____5638 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____5664 = translate_pat env pat in
            (match uu____5664 with
             | (env1,pat1) ->
                 let uu____5675 = translate_expr env1 expr in
                 (pat1, uu____5675))
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
      | FStar_Extraction_ML_Syntax.MLP_Var (name,uu____5689) ->
          let env1 = extend env name false in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_" false in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5692,cons1),ps) ->
          let uu____5709 =
            FStar_List.fold_left
              (fun uu____5729  ->
                 fun p1  ->
                   match uu____5729 with
                   | (env1,acc) ->
                       let uu____5749 = translate_pat env1 p1 in
                       (match uu____5749 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____5709 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____5778,ps) ->
          let uu____5796 =
            FStar_List.fold_left
              (fun uu____5830  ->
                 fun uu____5831  ->
                   match (uu____5830, uu____5831) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____5900 = translate_pat env1 p1 in
                       (match uu____5900 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps in
          (match uu____5796 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____5962 =
            FStar_List.fold_left
              (fun uu____5982  ->
                 fun p1  ->
                   match uu____5982 with
                   | (env1,acc) ->
                       let uu____6002 = translate_pat env1 p1 in
                       (match uu____6002 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____5962 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6029 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6034 ->
          failwith "todo: translate_pat [MLP_Branch]"
and translate_constant: FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6044) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6059 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____6060 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____6061 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6062 ->
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
          let uu____6082 =
            let uu____6089 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____6089) in
          EApp uu____6082