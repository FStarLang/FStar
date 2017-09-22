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
let current_version: version = Prims.parse_int "26"
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
  fun uu____3267  ->
    match uu____3267 with
    | FStar_Extraction_ML_Syntax.MLLib modules1 ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3327 = m in
               match uu____3327 with
               | ((prefix1,final),uu____3348,uu____3349) ->
                   FStar_String.concat "."
                     (FStar_List.append prefix1 [final]) in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____3381 = translate_module m in
                FStar_Pervasives_Native.Some uu____3381)
             with
             | e ->
                 ((let uu____3390 = FStar_Util.print_exn e in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3390);
                  FStar_Pervasives_Native.None)) modules1
and translate_module:
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
    (FStar_Extraction_ML_Syntax.mlsig,FStar_Extraction_ML_Syntax.mlmodule)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,FStar_Extraction_ML_Syntax.mllib)
    FStar_Pervasives_Native.tuple3 -> file
  =
  fun uu____3391  ->
    match uu____3391 with
    | (module_name,modul,uu____3412) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name] in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.filter_map (translate_decl (empty module_name1))
                decls
          | uu____3455 ->
              failwith "Unexpected standalone interface or nested modules" in
        ((FStar_String.concat "_" module_name1), program)
and translate_flags:
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list =
  fun flags  ->
    FStar_List.choose
      (fun uu___130_3470  ->
         match uu___130_3470 with
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
         | uu____3474 -> FStar_Pervasives_Native.None) flags
and translate_single_let:
  env ->
    FStar_Extraction_ML_Syntax.mlletflavor ->
      FStar_Extraction_ML_Syntax.meta Prims.list ->
        FStar_Extraction_ML_Syntax.mllb ->
          decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun flavor  ->
      fun flags  ->
        fun binding  ->
          match (flavor, flags, binding) with
          | (flavor1,flags1,{
                              FStar_Extraction_ML_Syntax.mllb_name =
                                (name,uu____3488);
                              FStar_Extraction_ML_Syntax.mllb_tysc =
                                FStar_Pervasives_Native.Some (tvars,t0);
                              FStar_Extraction_ML_Syntax.mllb_add_unit =
                                uu____3491;
                              FStar_Extraction_ML_Syntax.mllb_def =
                                {
                                  FStar_Extraction_ML_Syntax.expr =
                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                    (args,body);
                                  FStar_Extraction_ML_Syntax.mlty =
                                    uu____3494;
                                  FStar_Extraction_ML_Syntax.loc = uu____3495;_};
                              FStar_Extraction_ML_Syntax.print_typ =
                                uu____3496;_})
              ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___131_3519  ->
                     match uu___131_3519 with
                     | FStar_Extraction_ML_Syntax.Assumed  -> true
                     | uu____3520 -> false) flags1 in
              let env1 =
                if flavor1 = FStar_Extraction_ML_Syntax.Rec
                then extend env name false
                else env in
              let env2 =
                FStar_List.fold_left
                  (fun env2  ->
                     fun uu____3533  ->
                       match uu____3533 with
                       | (name1,uu____3539) -> extend_t env2 name1) env1
                  tvars in
              let rec find_return_type i uu___132_3546 =
                match uu___132_3546 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun
                    (uu____3547,uu____3548,t) when i > (Prims.parse_int "0")
                    -> find_return_type (i - (Prims.parse_int "1")) t
                | t -> t in
              let t =
                let uu____3552 = find_return_type (FStar_List.length args) t0 in
                translate_type env2 uu____3552 in
              let binders = translate_binders env2 args in
              let env3 = add_binders env2 args in
              let name1 = ((env3.module_name), name) in
              let flags2 =
                match t0 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun
                    (uu____3575,FStar_Extraction_ML_Syntax.E_GHOST
                     ,uu____3576)
                    ->
                    let uu____3577 = translate_flags flags1 in NoExtract ::
                      uu____3577
                | uu____3580 -> translate_flags flags1 in
              if assumed
              then
                (if (FStar_List.length tvars) = (Prims.parse_int "0")
                 then
                   let uu____3585 =
                     let uu____3586 =
                       let uu____3601 = translate_type env3 t0 in
                       (FStar_Pervasives_Native.None, name1, uu____3601) in
                     DExternal uu____3586 in
                   FStar_Pervasives_Native.Some uu____3585
                 else FStar_Pervasives_Native.None)
              else
                (try
                   let body1 = translate_expr env3 body in
                   FStar_Pervasives_Native.Some
                     (DFunction
                        (FStar_Pervasives_Native.None, flags2,
                          (FStar_List.length tvars), t, name1, binders,
                          body1))
                 with
                 | e ->
                     let msg = FStar_Util.print_exn e in
                     (FStar_Util.print2
                        "Warning: writing a stub for %s (%s)\n"
                        (FStar_Pervasives_Native.snd name1) msg;
                      (let msg1 =
                         Prims.strcat "This function was not extracted:\n"
                           msg in
                       FStar_Pervasives_Native.Some
                         (DFunction
                            (FStar_Pervasives_Native.None, flags2,
                              (FStar_List.length tvars), t, name1, binders,
                              (EAbortS msg1))))))
          | (flavor1,flags1,{
                              FStar_Extraction_ML_Syntax.mllb_name =
                                (name,uu____3661);
                              FStar_Extraction_ML_Syntax.mllb_tysc =
                                FStar_Pervasives_Native.Some (tvars,t0);
                              FStar_Extraction_ML_Syntax.mllb_add_unit =
                                uu____3664;
                              FStar_Extraction_ML_Syntax.mllb_def =
                                {
                                  FStar_Extraction_ML_Syntax.expr =
                                    FStar_Extraction_ML_Syntax.MLE_Coerce
                                    ({
                                       FStar_Extraction_ML_Syntax.expr =
                                         FStar_Extraction_ML_Syntax.MLE_Fun
                                         (args,body);
                                       FStar_Extraction_ML_Syntax.mlty =
                                         uu____3667;
                                       FStar_Extraction_ML_Syntax.loc =
                                         uu____3668;_},uu____3669,uu____3670);
                                  FStar_Extraction_ML_Syntax.mlty =
                                    uu____3671;
                                  FStar_Extraction_ML_Syntax.loc = uu____3672;_};
                              FStar_Extraction_ML_Syntax.print_typ =
                                uu____3673;_})
              ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___131_3696  ->
                     match uu___131_3696 with
                     | FStar_Extraction_ML_Syntax.Assumed  -> true
                     | uu____3697 -> false) flags1 in
              let env1 =
                if flavor1 = FStar_Extraction_ML_Syntax.Rec
                then extend env name false
                else env in
              let env2 =
                FStar_List.fold_left
                  (fun env2  ->
                     fun uu____3710  ->
                       match uu____3710 with
                       | (name1,uu____3716) -> extend_t env2 name1) env1
                  tvars in
              let rec find_return_type i uu___132_3723 =
                match uu___132_3723 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun
                    (uu____3724,uu____3725,t) when i > (Prims.parse_int "0")
                    -> find_return_type (i - (Prims.parse_int "1")) t
                | t -> t in
              let t =
                let uu____3729 = find_return_type (FStar_List.length args) t0 in
                translate_type env2 uu____3729 in
              let binders = translate_binders env2 args in
              let env3 = add_binders env2 args in
              let name1 = ((env3.module_name), name) in
              let flags2 =
                match t0 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun
                    (uu____3752,FStar_Extraction_ML_Syntax.E_GHOST
                     ,uu____3753)
                    ->
                    let uu____3754 = translate_flags flags1 in NoExtract ::
                      uu____3754
                | uu____3757 -> translate_flags flags1 in
              if assumed
              then
                (if (FStar_List.length tvars) = (Prims.parse_int "0")
                 then
                   let uu____3762 =
                     let uu____3763 =
                       let uu____3778 = translate_type env3 t0 in
                       (FStar_Pervasives_Native.None, name1, uu____3778) in
                     DExternal uu____3763 in
                   FStar_Pervasives_Native.Some uu____3762
                 else FStar_Pervasives_Native.None)
              else
                (try
                   let body1 = translate_expr env3 body in
                   FStar_Pervasives_Native.Some
                     (DFunction
                        (FStar_Pervasives_Native.None, flags2,
                          (FStar_List.length tvars), t, name1, binders,
                          body1))
                 with
                 | e ->
                     let msg = FStar_Util.print_exn e in
                     (FStar_Util.print2
                        "Warning: writing a stub for %s (%s)\n"
                        (FStar_Pervasives_Native.snd name1) msg;
                      (let msg1 =
                         Prims.strcat "This function was not extracted:\n"
                           msg in
                       FStar_Pervasives_Native.Some
                         (DFunction
                            (FStar_Pervasives_Native.None, flags2,
                              (FStar_List.length tvars), t, name1, binders,
                              (EAbortS msg1))))))
          | (flavor1,flags1,{
                              FStar_Extraction_ML_Syntax.mllb_name =
                                (name,uu____3838);
                              FStar_Extraction_ML_Syntax.mllb_tysc =
                                FStar_Pervasives_Native.Some ([],t);
                              FStar_Extraction_ML_Syntax.mllb_add_unit =
                                uu____3840;
                              FStar_Extraction_ML_Syntax.mllb_def = expr;
                              FStar_Extraction_ML_Syntax.print_typ =
                                uu____3842;_})
              ->
              let flags2 = translate_flags flags1 in
              let t1 = translate_type env t in
              let name1 = ((env.module_name), name) in
              (try
                 let expr1 = translate_expr env expr in
                 FStar_Pervasives_Native.Some
                   (DGlobal (flags2, name1, t1, expr1))
               with
               | e ->
                   ((let uu____3892 = FStar_Util.print_exn e in
                     FStar_Util.print2
                       "Warning: not translating definition for %s (%s)\n"
                       (FStar_Pervasives_Native.snd name1) uu____3892);
                    FStar_Pervasives_Native.Some
                      (DGlobal (flags2, name1, t1, EAny))))
          | (uu____3903,uu____3904,{
                                     FStar_Extraction_ML_Syntax.mllb_name =
                                       (name,uu____3906);
                                     FStar_Extraction_ML_Syntax.mllb_tysc =
                                       ts;
                                     FStar_Extraction_ML_Syntax.mllb_add_unit
                                       = uu____3908;
                                     FStar_Extraction_ML_Syntax.mllb_def =
                                       uu____3909;
                                     FStar_Extraction_ML_Syntax.print_typ =
                                       uu____3910;_})
              ->
              (FStar_Util.print1
                 "Warning: not translating definition for %s (and possibly others)\n"
                 name;
               (match ts with
                | FStar_Pervasives_Native.Some (idents,t) ->
                    let uu____3925 =
                      let uu____3926 =
                        FStar_List.map FStar_Pervasives_Native.fst idents in
                      FStar_String.concat ", " uu____3926 in
                    let uu____3933 =
                      FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                    FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                      uu____3925 uu____3933
                | FStar_Pervasives_Native.None  -> ());
               FStar_Pervasives_Native.None)
          | uu____3936 -> failwith "impossible"
and translate_decl:
  env ->
    FStar_Extraction_ML_Syntax.mlmodule1 ->
      decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,flags,letbinding::[]) ->
          translate_single_let env flavor flags letbinding
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3956 ->
          FStar_Pervasives_Native.None
      | FStar_Extraction_ML_Syntax.MLM_Ty (ty_decl::[]) ->
          translate_single_type_decl env ty_decl
      | FStar_Extraction_ML_Syntax.MLM_Ty ty_decls ->
          let rec traverse f xs =
            match xs with
            | [] -> FStar_Pervasives_Native.Some []
            | o::os ->
                let uu____3997 = traverse f os in
                (match uu____3997 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some os' ->
                     let uu____4015 = f o in
                     (match uu____4015 with
                      | FStar_Pervasives_Native.None  ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some o' ->
                          FStar_Pervasives_Native.Some (o' :: os'))) in
          let uu____4027 = traverse (translate_single_type_decl env) ty_decls in
          (match uu____4027 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some decls ->
               FStar_Pervasives_Native.Some (DTypeMutual decls))
      | FStar_Extraction_ML_Syntax.MLM_Ty [] ->
          (FStar_Util.print_string
             "Impossible!! Empty block of mutually recursive type declarations";
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Top uu____4042 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____4045 ->
          failwith "todo: translate_decl [MLM_Exn]"
and translate_single_type_decl:
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ty_decl  ->
      match ty_decl with
      | (assumed,name,_mangled_name,args,uu____4066,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Abbrev t)) ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____4093  ->
                   match uu____4093 with
                   | (name2,uu____4099) -> extend_t env1 name2) env args in
          if assumed
          then FStar_Pervasives_Native.None
          else
            (let uu____4103 =
               let uu____4104 =
                 let uu____4117 = translate_type env1 t in
                 (name1, (FStar_List.length args), uu____4117) in
               DTypeAlias uu____4104 in
             FStar_Pervasives_Native.Some uu____4103)
      | (uu____4124,name,_mangled_name,args,uu____4128,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____4161  ->
                   match uu____4161 with
                   | (name2,uu____4167) -> extend_t env1 name2) env args in
          let uu____4168 =
            let uu____4169 =
              let uu____4192 =
                FStar_List.map
                  (fun uu____4219  ->
                     match uu____4219 with
                     | (f,t) ->
                         let uu____4234 =
                           let uu____4239 = translate_type env1 t in
                           (uu____4239, false) in
                         (f, uu____4234)) fields in
              (name1, (FStar_List.length args), uu____4192) in
            DTypeFlat uu____4169 in
          FStar_Pervasives_Native.Some uu____4168
      | (uu____4260,name,_mangled_name,args,attrs,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
          let name1 = ((env.module_name), name) in
          let flags = translate_flags attrs in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____4306  ->
                   match uu____4306 with
                   | (name2,uu____4312) -> extend_t env1 name2) env args in
          let uu____4313 =
            let uu____4314 =
              let uu____4347 =
                FStar_List.map
                  (fun uu____4392  ->
                     match uu____4392 with
                     | (cons1,ts) ->
                         let uu____4431 =
                           FStar_List.map
                             (fun uu____4458  ->
                                match uu____4458 with
                                | (name2,t) ->
                                    let uu____4473 =
                                      let uu____4478 = translate_type env1 t in
                                      (uu____4478, false) in
                                    (name2, uu____4473)) ts in
                         (cons1, uu____4431)) branches in
              (name1, flags, (FStar_List.length args), uu____4347) in
            DTypeVariant uu____4314 in
          FStar_Pervasives_Native.Some uu____4313
and translate_type: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var (name,uu____4520) ->
          let uu____4521 = find_t env name in TBound uu____4521
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4523,t2) ->
          let uu____4525 =
            let uu____4530 = translate_type env t1 in
            let uu____4531 = translate_type env t2 in
            (uu____4530, uu____4531) in
          TArrow uu____4525
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4535 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4535 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4539 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4539 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4551 = FStar_Util.must (mk_width m) in TInt uu____4551
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4563 = FStar_Util.must (mk_width m) in TInt uu____4563
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4568 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4568 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4573 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4573 = "FStar.Buffer.buffer" ->
          let uu____4574 = translate_type env arg in TBuf uu____4574
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4575::[],p) when
          let uu____4579 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4579 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4617 = FStar_List.map (translate_type env) args in
          TTuple uu____4617
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4626 =
              let uu____4639 = FStar_List.map (translate_type env) args in
              (lid, uu____4639) in
            TApp uu____4626
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4648 = FStar_List.map (translate_type env) ts in
          TTuple uu____4648
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
    fun uu____4664  ->
      match uu____4664 with
      | ((name,uu____4670),typ) ->
          let uu____4676 = translate_type env typ in
          { name; typ = uu____4676; mut = false }
and translate_expr: env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____4681) ->
          let uu____4682 = find env name in EBound uu____4682
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4687 =
            let uu____4692 = FStar_Util.must (mk_op op) in
            let uu____4693 = FStar_Util.must (mk_width m) in
            (uu____4692, uu____4693) in
          EOp uu____4687
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4697 =
            let uu____4702 = FStar_Util.must (mk_bool_op op) in
            (uu____4702, Bool) in
          EOp uu____4697
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags,{
                           FStar_Extraction_ML_Syntax.mllb_name =
                             (name,uu____4707);
                           FStar_Extraction_ML_Syntax.mllb_tysc =
                             FStar_Pervasives_Native.Some ([],typ);
                           FStar_Extraction_ML_Syntax.mllb_add_unit =
                             add_unit;
                           FStar_Extraction_ML_Syntax.mllb_def = body;
                           FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let is_mut =
            FStar_Util.for_some
              (fun uu___133_4733  ->
                 match uu___133_4733 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____4734 -> false) flags in
          let uu____4735 =
            if is_mut
            then
              let uu____4744 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____4749 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4749 = "FStar.ST.stackref" -> t
                | uu____4750 ->
                    let uu____4751 =
                      let uu____4752 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____4752 in
                    failwith uu____4751 in
              let uu____4755 =
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
                      (uu____4756,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____4758;
                    FStar_Extraction_ML_Syntax.loc = uu____4759;_} -> body1
                | uu____4762 ->
                    failwith "unexpected: bad desugaring of Mutable" in
              (uu____4744, uu____4755)
            else (typ, body) in
          (match uu____4735 with
           | (typ1,body1) ->
               let binder =
                 let uu____4767 = translate_type env typ1 in
                 { name; typ = uu____4767; mut = is_mut } in
               let body2 = translate_expr env body1 in
               let env1 = extend env name is_mut in
               let continuation1 = translate_expr env1 continuation in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4793 =
            let uu____4804 = translate_expr env expr in
            let uu____4805 = translate_branches env branches in
            (uu____4804, uu____4805) in
          EMatch uu____4793
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4819;
             FStar_Extraction_ML_Syntax.loc = uu____4820;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____4822);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4823;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4824;_}::[])
          when
          (let uu____4829 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4829 = "FStar.HyperStack.ST.op_Bang") && (is_mutable env v1)
          -> let uu____4830 = find env v1 in EBound uu____4830
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4832;
             FStar_Extraction_ML_Syntax.loc = uu____4833;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____4835);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4836;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4837;_}::e1::[])
          when
          (let uu____4843 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4843 = "FStar.HyperStack.ST.op_Colon_Equals") &&
            (is_mutable env v1)
          ->
          let uu____4844 =
            let uu____4849 =
              let uu____4850 = find env v1 in EBound uu____4850 in
            let uu____4851 = translate_expr env e1 in
            (uu____4849, uu____4851) in
          EAssign uu____4844
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4853;
                  FStar_Extraction_ML_Syntax.loc = uu____4854;_},uu____4855);
             FStar_Extraction_ML_Syntax.mlty = uu____4856;
             FStar_Extraction_ML_Syntax.loc = uu____4857;_},e1::e2::[])
          when
          (let uu____4868 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4868 = "FStar.Buffer.index") ||
            (let uu____4870 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4870 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____4871 =
            let uu____4876 = translate_expr env e1 in
            let uu____4877 = translate_expr env e2 in
            (uu____4876, uu____4877) in
          EBufRead uu____4871
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4879;
                  FStar_Extraction_ML_Syntax.loc = uu____4880;_},uu____4881);
             FStar_Extraction_ML_Syntax.mlty = uu____4882;
             FStar_Extraction_ML_Syntax.loc = uu____4883;_},e1::e2::[])
          when
          let uu____4892 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4892 = "FStar.Buffer.create" ->
          let uu____4893 =
            let uu____4900 = translate_expr env e1 in
            let uu____4901 = translate_expr env e2 in
            (Stack, uu____4900, uu____4901) in
          EBufCreate uu____4893
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4903;
                  FStar_Extraction_ML_Syntax.loc = uu____4904;_},uu____4905);
             FStar_Extraction_ML_Syntax.mlty = uu____4906;
             FStar_Extraction_ML_Syntax.loc = uu____4907;_},_e0::e1::e2::[])
          when
          let uu____4917 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4917 = "FStar.Buffer.rcreate" ->
          let uu____4918 =
            let uu____4925 = translate_expr env e1 in
            let uu____4926 = translate_expr env e2 in
            (Eternal, uu____4925, uu____4926) in
          EBufCreate uu____4918
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4928;
                  FStar_Extraction_ML_Syntax.loc = uu____4929;_},uu____4930);
             FStar_Extraction_ML_Syntax.mlty = uu____4931;
             FStar_Extraction_ML_Syntax.loc = uu____4932;_},e2::[])
          when
          let uu____4940 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4940 = "FStar.Buffer.createL" ->
          let rec list_elements1 acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements1 (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____4978 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!" in
          let list_elements2 = list_elements1 [] in
          let uu____4986 =
            let uu____4993 =
              let uu____4996 = list_elements2 e2 in
              FStar_List.map (translate_expr env) uu____4996 in
            (Stack, uu____4993) in
          EBufCreateL uu____4986
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5002;
                  FStar_Extraction_ML_Syntax.loc = uu____5003;_},uu____5004);
             FStar_Extraction_ML_Syntax.mlty = uu____5005;
             FStar_Extraction_ML_Syntax.loc = uu____5006;_},e1::e2::_e3::[])
          when
          let uu____5016 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5016 = "FStar.Buffer.sub" ->
          let uu____5017 =
            let uu____5022 = translate_expr env e1 in
            let uu____5023 = translate_expr env e2 in
            (uu____5022, uu____5023) in
          EBufSub uu____5017
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5025;
                  FStar_Extraction_ML_Syntax.loc = uu____5026;_},uu____5027);
             FStar_Extraction_ML_Syntax.mlty = uu____5028;
             FStar_Extraction_ML_Syntax.loc = uu____5029;_},e1::e2::[])
          when
          let uu____5038 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5038 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5040;
                  FStar_Extraction_ML_Syntax.loc = uu____5041;_},uu____5042);
             FStar_Extraction_ML_Syntax.mlty = uu____5043;
             FStar_Extraction_ML_Syntax.loc = uu____5044;_},e1::e2::[])
          when
          let uu____5053 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5053 = "FStar.Buffer.offset" ->
          let uu____5054 =
            let uu____5059 = translate_expr env e1 in
            let uu____5060 = translate_expr env e2 in
            (uu____5059, uu____5060) in
          EBufSub uu____5054
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5062;
                  FStar_Extraction_ML_Syntax.loc = uu____5063;_},uu____5064);
             FStar_Extraction_ML_Syntax.mlty = uu____5065;
             FStar_Extraction_ML_Syntax.loc = uu____5066;_},e1::e2::e3::[])
          when
          (let uu____5078 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5078 = "FStar.Buffer.upd") ||
            (let uu____5080 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5080 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____5081 =
            let uu____5088 = translate_expr env e1 in
            let uu____5089 = translate_expr env e2 in
            let uu____5090 = translate_expr env e3 in
            (uu____5088, uu____5089, uu____5090) in
          EBufWrite uu____5081
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5092;
             FStar_Extraction_ML_Syntax.loc = uu____5093;_},uu____5094::[])
          when
          let uu____5097 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5097 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5099;
             FStar_Extraction_ML_Syntax.loc = uu____5100;_},uu____5101::[])
          when
          let uu____5104 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5104 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5106;
                  FStar_Extraction_ML_Syntax.loc = uu____5107;_},uu____5108);
             FStar_Extraction_ML_Syntax.mlty = uu____5109;
             FStar_Extraction_ML_Syntax.loc = uu____5110;_},e1::e2::e3::e4::e5::[])
          when
          let uu____5122 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5122 = "FStar.Buffer.blit" ->
          let uu____5123 =
            let uu____5134 = translate_expr env e1 in
            let uu____5135 = translate_expr env e2 in
            let uu____5136 = translate_expr env e3 in
            let uu____5137 = translate_expr env e4 in
            let uu____5138 = translate_expr env e5 in
            (uu____5134, uu____5135, uu____5136, uu____5137, uu____5138) in
          EBufBlit uu____5123
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5140;
                  FStar_Extraction_ML_Syntax.loc = uu____5141;_},uu____5142);
             FStar_Extraction_ML_Syntax.mlty = uu____5143;
             FStar_Extraction_ML_Syntax.loc = uu____5144;_},e1::e2::e3::[])
          when
          let uu____5154 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5154 = "FStar.Buffer.fill" ->
          let uu____5155 =
            let uu____5162 = translate_expr env e1 in
            let uu____5163 = translate_expr env e2 in
            let uu____5164 = translate_expr env e3 in
            (uu____5162, uu____5163, uu____5164) in
          EBufFill uu____5155
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5166;
             FStar_Extraction_ML_Syntax.loc = uu____5167;_},uu____5168::[])
          when
          let uu____5171 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5171 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5173;
             FStar_Extraction_ML_Syntax.loc = uu____5174;_},e1::[])
          when
          let uu____5178 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5178 = "Obj.repr" ->
          let uu____5179 =
            let uu____5184 = translate_expr env e1 in (uu____5184, TAny) in
          ECast uu____5179
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5187;
             FStar_Extraction_ML_Syntax.loc = uu____5188;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5196 = FStar_Util.must (mk_width m) in
          let uu____5197 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____5196 uu____5197 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5199;
             FStar_Extraction_ML_Syntax.loc = uu____5200;_},args)
          when is_bool_op op ->
          let uu____5208 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____5208 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5210;
             FStar_Extraction_ML_Syntax.loc = uu____5211;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5213;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5214;_}::[])
          when is_machine_int m ->
          let uu____5229 =
            let uu____5234 = FStar_Util.must (mk_width m) in (uu____5234, c) in
          EConstant uu____5229
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5236;
             FStar_Extraction_ML_Syntax.loc = uu____5237;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5239;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5240;_}::[])
          when is_machine_int m ->
          let uu____5255 =
            let uu____5260 = FStar_Util.must (mk_width m) in (uu____5260, c) in
          EConstant uu____5255
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5261;
             FStar_Extraction_ML_Syntax.loc = uu____5262;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5264;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5265;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5271 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5273;
             FStar_Extraction_ML_Syntax.loc = uu____5274;_},arg::[])
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
            let uu____5281 =
              let uu____5286 = translate_expr env arg in
              (uu____5286, (TInt UInt64)) in
            ECast uu____5281
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5288 =
                 let uu____5293 = translate_expr env arg in
                 (uu____5293, (TInt UInt32)) in
               ECast uu____5288)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5295 =
                   let uu____5300 = translate_expr env arg in
                   (uu____5300, (TInt UInt16)) in
                 ECast uu____5295)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5302 =
                     let uu____5307 = translate_expr env arg in
                     (uu____5307, (TInt UInt8)) in
                   ECast uu____5302)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5309 =
                       let uu____5314 = translate_expr env arg in
                       (uu____5314, (TInt Int64)) in
                     ECast uu____5309)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5316 =
                         let uu____5321 = translate_expr env arg in
                         (uu____5321, (TInt Int32)) in
                       ECast uu____5316)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5323 =
                           let uu____5328 = translate_expr env arg in
                           (uu____5328, (TInt Int16)) in
                         ECast uu____5323)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5330 =
                             let uu____5335 = translate_expr env arg in
                             (uu____5335, (TInt Int8)) in
                           ECast uu____5330)
                        else
                          (let uu____5337 =
                             let uu____5344 =
                               let uu____5347 = translate_expr env arg in
                               [uu____5347] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5344) in
                           EApp uu____5337)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5358 =
            let uu____5365 = translate_expr env head1 in
            let uu____5366 = FStar_List.map (translate_expr env) args in
            (uu____5365, uu____5366) in
          EApp uu____5358
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5377 =
            let uu____5384 = translate_expr env head1 in
            let uu____5385 = FStar_List.map (translate_type env) ty_args in
            (uu____5384, uu____5385) in
          ETypApp uu____5377
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5393 =
            let uu____5398 = translate_expr env e1 in
            let uu____5399 = translate_type env t_to in
            (uu____5398, uu____5399) in
          ECast uu____5393
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5400,fields) ->
          let uu____5418 =
            let uu____5429 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5430 =
              FStar_List.map
                (fun uu____5449  ->
                   match uu____5449 with
                   | (field,expr) ->
                       let uu____5460 = translate_expr env expr in
                       (field, uu____5460)) fields in
            (uu____5429, uu____5430) in
          EFlat uu____5418
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5469 =
            let uu____5476 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____5477 = translate_expr env e1 in
            (uu____5476, uu____5477, (FStar_Pervasives_Native.snd path)) in
          EField uu____5469
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5480 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5494) ->
          let uu____5499 =
            let uu____5500 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1 in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5500 in
          failwith uu____5499
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5506 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____5506
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5512 = FStar_List.map (translate_expr env) es in
          ETuple uu____5512
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5515,cons1),es) ->
          let uu____5532 =
            let uu____5541 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5542 = FStar_List.map (translate_expr env) es in
            (uu____5541, cons1, uu____5542) in
          ECons uu____5532
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args in
          let env1 = add_binders env args in
          let uu____5565 =
            let uu____5574 = translate_expr env1 body in
            let uu____5575 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty in
            (binders, uu____5574, uu____5575) in
          EFun uu____5565
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5585 =
            let uu____5592 = translate_expr env e1 in
            let uu____5593 = translate_expr env e2 in
            let uu____5594 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31 in
            (uu____5592, uu____5593, uu____5594) in
          EIfThenElse uu____5585
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5596 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5603 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____5618 ->
          failwith "todo: translate_expr [MLE_Coerce]"
and assert_lid: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____5633 =
              let uu____5646 = FStar_List.map (translate_type env) ts in
              (lid, uu____5646) in
            TApp uu____5633
          else TQualified lid
      | uu____5652 -> failwith "invalid argument: assert_lid"
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
    fun uu____5678  ->
      match uu____5678 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____5704 = translate_pat env pat in
            (match uu____5704 with
             | (env1,pat1) ->
                 let uu____5715 = translate_expr env1 expr in
                 (pat1, uu____5715))
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
      | FStar_Extraction_ML_Syntax.MLP_Var (name,uu____5729) ->
          let env1 = extend env name false in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_" false in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5732,cons1),ps) ->
          let uu____5749 =
            FStar_List.fold_left
              (fun uu____5769  ->
                 fun p1  ->
                   match uu____5769 with
                   | (env1,acc) ->
                       let uu____5789 = translate_pat env1 p1 in
                       (match uu____5789 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____5749 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____5818,ps) ->
          let uu____5836 =
            FStar_List.fold_left
              (fun uu____5870  ->
                 fun uu____5871  ->
                   match (uu____5870, uu____5871) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____5940 = translate_pat env1 p1 in
                       (match uu____5940 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps in
          (match uu____5836 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____6002 =
            FStar_List.fold_left
              (fun uu____6022  ->
                 fun p1  ->
                   match uu____6022 with
                   | (env1,acc) ->
                       let uu____6042 = translate_pat env1 p1 in
                       (match uu____6042 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____6002 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6069 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6074 ->
          failwith "todo: translate_pat [MLP_Branch]"
and translate_constant: FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6084) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6099 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____6100 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____6101 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6102 ->
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
          let uu____6122 =
            let uu____6129 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____6129) in
          EApp uu____6122