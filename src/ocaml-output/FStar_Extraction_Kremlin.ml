open Prims
type source_info =
  {
  file_name: Prims.string;
  mod_name: Prims.string Prims.list;
  position: (Prims.int,Prims.int) FStar_Pervasives_Native.tuple2;}[@@deriving
                                                                    show]
and decl =
  | DGlobal of
  (flag Prims.list,(Prims.string Prims.list,Prims.string)
                     FStar_Pervasives_Native.tuple2,typ,expr)
  FStar_Pervasives_Native.tuple4
  | DFunction of
  (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,(Prims.string
                                                                    Prims.list,
                                                                    Prims.string)
                                                                    FStar_Pervasives_Native.tuple2,
  binder Prims.list,expr,source_info) FStar_Pervasives_Native.tuple8
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
  typ,binder Prims.list) FStar_Pervasives_Native.tuple4
  | DTypeVariant of
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
  flag Prims.list,Prims.int,(Prims.string,(Prims.string,(typ,Prims.bool)
                                                          FStar_Pervasives_Native.tuple2)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list)
                              FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple4
  | DTypeMutual of decl Prims.list
  | DFunctionMutual of decl Prims.list[@@deriving show]
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
let __proj__Mksource_info__item__file_name: source_info -> Prims.string =
  fun projectee  ->
    match projectee with
    | { file_name = __fname__file_name; mod_name = __fname__mod_name;
        position = __fname__position;_} -> __fname__file_name
let __proj__Mksource_info__item__mod_name:
  source_info -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { file_name = __fname__file_name; mod_name = __fname__mod_name;
        position = __fname__position;_} -> __fname__mod_name
let __proj__Mksource_info__item__position:
  source_info -> (Prims.int,Prims.int) FStar_Pervasives_Native.tuple2 =
  fun projectee  ->
    match projectee with
    | { file_name = __fname__file_name; mod_name = __fname__mod_name;
        position = __fname__position;_} -> __fname__position
let uu___is_DGlobal: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DGlobal _0 -> true | uu____615 -> false
let __proj__DGlobal__item___0:
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,typ,expr)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DGlobal _0 -> _0
let uu___is_DFunction: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____703 -> false
let __proj__DFunction__item___0:
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr,source_info) FStar_Pervasives_Native.tuple8
  = fun projectee  -> match projectee with | DFunction _0 -> _0
let uu___is_DTypeAlias: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____811 -> false
let __proj__DTypeAlias__item___0:
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      Prims.int,typ) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0
let uu___is_DTypeFlat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____881 -> false
let __proj__DTypeFlat__item___0:
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      Prims.int,(Prims.string,(typ,Prims.bool) FStar_Pervasives_Native.tuple2)
                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0
let uu___is_DExternal: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____977 -> false
let __proj__DExternal__item___0:
  decl ->
    (cc FStar_Pervasives_Native.option,(Prims.string Prims.list,Prims.string)
                                         FStar_Pervasives_Native.tuple2,
      typ,binder Prims.list) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DExternal _0 -> _0
let uu___is_DTypeVariant: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____1075 -> false
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
    match projectee with | DTypeMutual _0 -> true | uu____1185 -> false
let __proj__DTypeMutual__item___0: decl -> decl Prims.list =
  fun projectee  -> match projectee with | DTypeMutual _0 -> _0
let uu___is_DFunctionMutual: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DFunctionMutual _0 -> true | uu____1205 -> false
let __proj__DFunctionMutual__item___0: decl -> decl Prims.list =
  fun projectee  -> match projectee with | DFunctionMutual _0 -> _0
let uu___is_StdCall: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1222 -> false
let uu___is_CDecl: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1226 -> false
let uu___is_FastCall: cc -> Prims.bool =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1230 -> false
let uu___is_Private: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1234 -> false
let uu___is_NoExtract: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____1238 -> false
let uu___is_CInline: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1242 -> false
let uu___is_Substitute: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1246 -> false
let uu___is_GCType: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1250 -> false
let uu___is_Comment: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1255 -> false
let __proj__Comment__item___0: flag -> Prims.string =
  fun projectee  -> match projectee with | Comment _0 -> _0
let uu___is_Eternal: lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1266 -> false
let uu___is_Stack: lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1270 -> false
let uu___is_EBound: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1275 -> false
let __proj__EBound__item___0: expr -> Prims.int =
  fun projectee  -> match projectee with | EBound _0 -> _0
let uu___is_EQualified: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1293 -> false
let __proj__EQualified__item___0:
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EQualified _0 -> _0
let uu___is_EConstant: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1327 -> false
let __proj__EConstant__item___0:
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EConstant _0 -> _0
let uu___is_EUnit: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1350 -> false
let uu___is_EApp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1361 -> false
let __proj__EApp__item___0:
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EApp _0 -> _0
let uu___is_ETypApp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1397 -> false
let __proj__ETypApp__item___0:
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ETypApp _0 -> _0
let uu___is_ELet: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1433 -> false
let __proj__ELet__item___0:
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ELet _0 -> _0
let uu___is_EIfThenElse: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1469 -> false
let __proj__EIfThenElse__item___0:
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0
let uu___is_ESequence: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1501 -> false
let __proj__ESequence__item___0: expr -> expr Prims.list =
  fun projectee  -> match projectee with | ESequence _0 -> _0
let uu___is_EAssign: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1523 -> false
let __proj__EAssign__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EAssign _0 -> _0
let uu___is_EBufCreate: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____1553 -> false
let __proj__EBufCreate__item___0:
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0
let uu___is_EBufRead: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____1587 -> false
let __proj__EBufRead__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufRead _0 -> _0
let uu___is_EBufWrite: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____1617 -> false
let __proj__EBufWrite__item___0:
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0
let uu___is_EBufSub: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____1651 -> false
let __proj__EBufSub__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufSub _0 -> _0
let uu___is_EBufBlit: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____1685 -> false
let __proj__EBufBlit__item___0:
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5 =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0
let uu___is_EMatch: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____1737 -> false
let __proj__EMatch__item___0:
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EMatch _0 -> _0
let uu___is_EOp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1783 -> false
let __proj__EOp__item___0: expr -> (op,width) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EOp _0 -> _0
let uu___is_ECast: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1811 -> false
let __proj__ECast__item___0:
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ECast _0 -> _0
let uu___is_EPushFrame: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1834 -> false
let uu___is_EPopFrame: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1838 -> false
let uu___is_EBool: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1843 -> false
let __proj__EBool__item___0: expr -> Prims.bool =
  fun projectee  -> match projectee with | EBool _0 -> _0
let uu___is_EAny: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1854 -> false
let uu___is_EAbort: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1858 -> false
let uu___is_EReturn: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1863 -> false
let __proj__EReturn__item___0: expr -> expr =
  fun projectee  -> match projectee with | EReturn _0 -> _0
let uu___is_EFlat: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1885 -> false
let __proj__EFlat__item___0:
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EFlat _0 -> _0
let uu___is_EField: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____1933 -> false
let __proj__EField__item___0:
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EField _0 -> _0
let uu___is_EWhile: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____1967 -> false
let __proj__EWhile__item___0:
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EWhile _0 -> _0
let uu___is_EBufCreateL: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____1997 -> false
let __proj__EBufCreateL__item___0:
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0
let uu___is_ETuple: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2029 -> false
let __proj__ETuple__item___0: expr -> expr Prims.list =
  fun projectee  -> match projectee with | ETuple _0 -> _0
let uu___is_ECons: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2055 -> false
let __proj__ECons__item___0:
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ECons _0 -> _0
let uu___is_EBufFill: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2097 -> false
let __proj__EBufFill__item___0:
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufFill _0 -> _0
let uu___is_EString: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2127 -> false
let __proj__EString__item___0: expr -> Prims.string =
  fun projectee  -> match projectee with | EString _0 -> _0
let uu___is_EFun: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2147 -> false
let __proj__EFun__item___0:
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EFun _0 -> _0
let uu___is_EAbortS: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2183 -> false
let __proj__EAbortS__item___0: expr -> Prims.string =
  fun projectee  -> match projectee with | EAbortS _0 -> _0
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____2194 -> false
let uu___is_AddW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2198 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____2202 -> false
let uu___is_SubW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2206 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____2210 -> false
let uu___is_DivW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2214 -> false
let uu___is_Mult: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2218 -> false
let uu___is_MultW: op -> Prims.bool =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2222 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____2226 -> false
let uu___is_BOr: op -> Prims.bool =
  fun projectee  -> match projectee with | BOr  -> true | uu____2230 -> false
let uu___is_BAnd: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2234 -> false
let uu___is_BXor: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2238 -> false
let uu___is_BShiftL: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2242 -> false
let uu___is_BShiftR: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2246 -> false
let uu___is_BNot: op -> Prims.bool =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2250 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2254 -> false
let uu___is_Neq: op -> Prims.bool =
  fun projectee  -> match projectee with | Neq  -> true | uu____2258 -> false
let uu___is_Lt: op -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2262 -> false
let uu___is_Lte: op -> Prims.bool =
  fun projectee  -> match projectee with | Lte  -> true | uu____2266 -> false
let uu___is_Gt: op -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2270 -> false
let uu___is_Gte: op -> Prims.bool =
  fun projectee  -> match projectee with | Gte  -> true | uu____2274 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____2278 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____2282 -> false
let uu___is_Xor: op -> Prims.bool =
  fun projectee  -> match projectee with | Xor  -> true | uu____2286 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____2290 -> false
let uu___is_PUnit: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2294 -> false
let uu___is_PBool: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2299 -> false
let __proj__PBool__item___0: pattern -> Prims.bool =
  fun projectee  -> match projectee with | PBool _0 -> _0
let uu___is_PVar: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2311 -> false
let __proj__PVar__item___0: pattern -> binder =
  fun projectee  -> match projectee with | PVar _0 -> _0
let uu___is_PCons: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2329 -> false
let __proj__PCons__item___0:
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PCons _0 -> _0
let uu___is_PTuple: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2361 -> false
let __proj__PTuple__item___0: pattern -> pattern Prims.list =
  fun projectee  -> match projectee with | PTuple _0 -> _0
let uu___is_PRecord: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2385 -> false
let __proj__PRecord__item___0:
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list
  = fun projectee  -> match projectee with | PRecord _0 -> _0
let uu___is_PConstant: pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____2419 -> false
let __proj__PConstant__item___0:
  pattern -> (width,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | PConstant _0 -> _0
let uu___is_UInt8: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____2442 -> false
let uu___is_UInt16: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2446 -> false
let uu___is_UInt32: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2450 -> false
let uu___is_UInt64: width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2454 -> false
let uu___is_Int8: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2458 -> false
let uu___is_Int16: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2462 -> false
let uu___is_Int32: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2466 -> false
let uu___is_Int64: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2470 -> false
let uu___is_Bool: width -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2474 -> false
let uu___is_CInt: width -> Prims.bool =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____2478 -> false
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
    match projectee with | TInt _0 -> true | uu____2501 -> false
let __proj__TInt__item___0: typ -> width =
  fun projectee  -> match projectee with | TInt _0 -> _0
let uu___is_TBuf: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2513 -> false
let __proj__TBuf__item___0: typ -> typ =
  fun projectee  -> match projectee with | TBuf _0 -> _0
let uu___is_TUnit: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2524 -> false
let uu___is_TQualified: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2535 -> false
let __proj__TQualified__item___0:
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TQualified _0 -> _0
let uu___is_TBool: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2564 -> false
let uu___is_TAny: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2568 -> false
let uu___is_TArrow: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2577 -> false
let __proj__TArrow__item___0: typ -> (typ,typ) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TArrow _0 -> _0
let uu___is_TBound: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2601 -> false
let __proj__TBound__item___0: typ -> Prims.int =
  fun projectee  -> match projectee with | TBound _0 -> _0
let uu___is_TApp: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2625 -> false
let __proj__TApp__item___0:
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TApp _0 -> _0
let uu___is_TTuple: typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____2675 -> false
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
  'Auu____2751 'Auu____2752 'Auu____2753 .
    ('Auu____2753,'Auu____2752,'Auu____2751) FStar_Pervasives_Native.tuple3
      -> 'Auu____2753
  = fun uu____2763  -> match uu____2763 with | (x,uu____2771,uu____2772) -> x
let snd3:
  'Auu____2777 'Auu____2778 'Auu____2779 .
    ('Auu____2779,'Auu____2778,'Auu____2777) FStar_Pervasives_Native.tuple3
      -> 'Auu____2778
  = fun uu____2789  -> match uu____2789 with | (uu____2796,x,uu____2798) -> x
let thd3:
  'Auu____2803 'Auu____2804 'Auu____2805 .
    ('Auu____2805,'Auu____2804,'Auu____2803) FStar_Pervasives_Native.tuple3
      -> 'Auu____2803
  = fun uu____2815  -> match uu____2815 with | (uu____2822,uu____2823,x) -> x
let mk_width: Prims.string -> width FStar_Pervasives_Native.option =
  fun uu___401_2829  ->
    match uu___401_2829 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____2832 -> FStar_Pervasives_Native.None
let mk_bool_op: Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___402_2837  ->
    match uu___402_2837 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____2840 -> FStar_Pervasives_Native.None
let is_bool_op: Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None
let mk_op: Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___403_2850  ->
    match uu___403_2850 with
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
    | uu____2853 -> FStar_Pervasives_Native.None
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
        let uu___408_2964 = env in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___408_2964.names_t);
          module_name = (uu___408_2964.module_name)
        }
let extend_t: env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___409_2971 = env in
      {
        names = (uu___409_2971.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___409_2971.module_name)
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
  fun env  -> fun x  -> let uu____2990 = find_name env x in uu____2990.mut
let find: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____3005 ->
          let uu____3006 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____3006
let find_t: env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____3021 ->
          let uu____3022 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____3022
let add_binders:
  'Auu____3026 .
    env ->
      (Prims.string,'Auu____3026) FStar_Pervasives_Native.tuple2 Prims.list
        -> env
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____3056  ->
             match uu____3056 with
             | (name,uu____3062) -> extend env1 name false) env binders
let rec translate: FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____3207  ->
    match uu____3207 with
    | FStar_Extraction_ML_Syntax.MLLib modules1 ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3267 = m in
               match uu____3267 with
               | ((prefix1,final),uu____3288,uu____3289) ->
                   FStar_String.concat "."
                     (FStar_List.append prefix1 [final]) in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____3321 = translate_module m in
                FStar_Pervasives_Native.Some uu____3321)
             with
             | e ->
                 ((let uu____3330 = FStar_Util.print_exn e in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3330);
                  FStar_Pervasives_Native.None)) modules1
and translate_module:
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
    (FStar_Extraction_ML_Syntax.mlsig,FStar_Extraction_ML_Syntax.mlmodule)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,FStar_Extraction_ML_Syntax.mllib)
    FStar_Pervasives_Native.tuple3 -> file
  =
  fun uu____3331  ->
    match uu____3331 with
    | (module_name,modul,uu____3352) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name] in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.filter_map (translate_decl (empty module_name1))
                decls
          | uu____3395 ->
              failwith "Unexpected standalone interface or nested modules" in
        ((FStar_String.concat "_" module_name1), program)
and translate_flags:
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list =
  fun flags  ->
    FStar_List.choose
      (fun uu___404_3410  ->
         match uu___404_3410 with
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
         | uu____3414 -> FStar_Pervasives_Native.None) flags
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
          | (flavor1,flags1,{ FStar_Extraction_ML_Syntax.mllb_name = name;
                              FStar_Extraction_ML_Syntax.mllb_tysc =
                                FStar_Pervasives_Native.Some (tvars,t0);
                              FStar_Extraction_ML_Syntax.mllb_add_unit =
                                uu____3430;
                              FStar_Extraction_ML_Syntax.mllb_def =
                                {
                                  FStar_Extraction_ML_Syntax.expr =
                                    FStar_Extraction_ML_Syntax.MLE_Fun
                                    (args,body);
                                  FStar_Extraction_ML_Syntax.mlty =
                                    uu____3433;
                                  FStar_Extraction_ML_Syntax.loc =
                                    (row,file_name);_};
                              FStar_Extraction_ML_Syntax.print_typ =
                                uu____3436;_})
              ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___405_3459  ->
                     match uu___405_3459 with
                     | FStar_Extraction_ML_Syntax.Assumed  -> true
                     | uu____3460 -> false) flags1 in
              let env1 =
                if flavor1 = FStar_Extraction_ML_Syntax.Rec
                then extend env name false
                else env in
              let env2 =
                FStar_List.fold_left
                  (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars in
              let rec find_return_type i uu___406_3474 =
                match uu___406_3474 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun
                    (uu____3475,uu____3476,t) when i > (Prims.parse_int "0")
                    -> find_return_type (i - (Prims.parse_int "1")) t
                | t -> t in
              let t =
                let uu____3480 = find_return_type (FStar_List.length args) t0 in
                translate_type env2 uu____3480 in
              let binders = translate_binders env2 args in
              let env3 = add_binders env2 args in
              let name1 = ((env3.module_name), name) in
              let flags2 =
                match t0 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun
                    (uu____3503,FStar_Extraction_ML_Syntax.E_GHOST
                     ,uu____3504)
                    ->
                    let uu____3505 = translate_flags flags1 in NoExtract ::
                      uu____3505
                | uu____3508 -> translate_flags flags1 in
              if assumed
              then
                (if (FStar_List.length tvars) = (Prims.parse_int "0")
                 then
                   let uu____3513 =
                     let uu____3514 =
                       let uu____3533 = translate_type env3 t0 in
                       (FStar_Pervasives_Native.None, name1, uu____3533,
                         binders) in
                     DExternal uu____3514 in
                   FStar_Pervasives_Native.Some uu____3513
                 else FStar_Pervasives_Native.None)
              else
                (let si =
                   {
                     file_name;
                     mod_name = (env3.module_name);
                     position = (row, (Prims.parse_int "0"))
                   } in
                 try
                   let body1 = translate_expr env3 body in
                   FStar_Pervasives_Native.Some
                     (DFunction
                        (FStar_Pervasives_Native.None, flags2,
                          (FStar_List.length tvars), t, name1, binders,
                          body1, si))
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
                            (FStar_Pervasives_Native.None, flags2,
                              (FStar_List.length tvars), t, name1, binders,
                              (EAbortS msg1), si)))))
          | (flavor1,flags1,{ FStar_Extraction_ML_Syntax.mllb_name = name;
                              FStar_Extraction_ML_Syntax.mllb_tysc =
                                FStar_Pervasives_Native.Some (tvars,t0);
                              FStar_Extraction_ML_Syntax.mllb_add_unit =
                                uu____3598;
                              FStar_Extraction_ML_Syntax.mllb_def =
                                {
                                  FStar_Extraction_ML_Syntax.expr =
                                    FStar_Extraction_ML_Syntax.MLE_Coerce
                                    ({
                                       FStar_Extraction_ML_Syntax.expr =
                                         FStar_Extraction_ML_Syntax.MLE_Fun
                                         (args,body);
                                       FStar_Extraction_ML_Syntax.mlty =
                                         uu____3601;
                                       FStar_Extraction_ML_Syntax.loc =
                                         (row,file_name);_},uu____3604,uu____3605);
                                  FStar_Extraction_ML_Syntax.mlty =
                                    uu____3606;
                                  FStar_Extraction_ML_Syntax.loc = uu____3607;_};
                              FStar_Extraction_ML_Syntax.print_typ =
                                uu____3608;_})
              ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___405_3631  ->
                     match uu___405_3631 with
                     | FStar_Extraction_ML_Syntax.Assumed  -> true
                     | uu____3632 -> false) flags1 in
              let env1 =
                if flavor1 = FStar_Extraction_ML_Syntax.Rec
                then extend env name false
                else env in
              let env2 =
                FStar_List.fold_left
                  (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars in
              let rec find_return_type i uu___406_3646 =
                match uu___406_3646 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun
                    (uu____3647,uu____3648,t) when i > (Prims.parse_int "0")
                    -> find_return_type (i - (Prims.parse_int "1")) t
                | t -> t in
              let t =
                let uu____3652 = find_return_type (FStar_List.length args) t0 in
                translate_type env2 uu____3652 in
              let binders = translate_binders env2 args in
              let env3 = add_binders env2 args in
              let name1 = ((env3.module_name), name) in
              let flags2 =
                match t0 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun
                    (uu____3675,FStar_Extraction_ML_Syntax.E_GHOST
                     ,uu____3676)
                    ->
                    let uu____3677 = translate_flags flags1 in NoExtract ::
                      uu____3677
                | uu____3680 -> translate_flags flags1 in
              if assumed
              then
                (if (FStar_List.length tvars) = (Prims.parse_int "0")
                 then
                   let uu____3685 =
                     let uu____3686 =
                       let uu____3705 = translate_type env3 t0 in
                       (FStar_Pervasives_Native.None, name1, uu____3705,
                         binders) in
                     DExternal uu____3686 in
                   FStar_Pervasives_Native.Some uu____3685
                 else FStar_Pervasives_Native.None)
              else
                (let si =
                   {
                     file_name;
                     mod_name = (env3.module_name);
                     position = (row, (Prims.parse_int "0"))
                   } in
                 try
                   let body1 = translate_expr env3 body in
                   FStar_Pervasives_Native.Some
                     (DFunction
                        (FStar_Pervasives_Native.None, flags2,
                          (FStar_List.length tvars), t, name1, binders,
                          body1, si))
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
                            (FStar_Pervasives_Native.None, flags2,
                              (FStar_List.length tvars), t, name1, binders,
                              (EAbortS msg1), si)))))
          | (flavor1,flags1,{ FStar_Extraction_ML_Syntax.mllb_name = name;
                              FStar_Extraction_ML_Syntax.mllb_tysc =
                                FStar_Pervasives_Native.Some ([],t);
                              FStar_Extraction_ML_Syntax.mllb_add_unit =
                                uu____3769;
                              FStar_Extraction_ML_Syntax.mllb_def = expr;
                              FStar_Extraction_ML_Syntax.print_typ =
                                uu____3771;_})
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
                   ((let uu____3821 = FStar_Util.print_exn e in
                     FStar_Util.print2_warning
                       "Not translating definition for %s (%s)\n"
                       (FStar_Pervasives_Native.snd name1) uu____3821);
                    FStar_Pervasives_Native.Some
                      (DGlobal (flags2, name1, t1, EAny))))
          | (uu____3832,uu____3833,{
                                     FStar_Extraction_ML_Syntax.mllb_name =
                                       name;
                                     FStar_Extraction_ML_Syntax.mllb_tysc =
                                       ts;
                                     FStar_Extraction_ML_Syntax.mllb_add_unit
                                       = uu____3836;
                                     FStar_Extraction_ML_Syntax.mllb_def =
                                       uu____3837;
                                     FStar_Extraction_ML_Syntax.print_typ =
                                       uu____3838;_})
              ->
              (FStar_Util.print1_warning
                 "Not translating definition for %s (and possibly others)\n"
                 name;
               (match ts with
                | FStar_Pervasives_Native.Some (idents,t) ->
                    let uu____3853 =
                      FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                    FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                      (FStar_String.concat ", " idents) uu____3853
                | FStar_Pervasives_Native.None  -> ());
               FStar_Pervasives_Native.None)
          | uu____3856 -> failwith "impossible"
and translate_decl:
  env ->
    FStar_Extraction_ML_Syntax.mlmodule1 ->
      decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,flags,lbs) ->
          let ls =
            FStar_List.filter_map (translate_single_let env flavor flags) lbs in
          FStar_Pervasives_Native.Some (DFunctionMutual ls)
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3881 ->
          FStar_Pervasives_Native.None
      | FStar_Extraction_ML_Syntax.MLM_Ty (ty_decl::[]) ->
          translate_single_type_decl env ty_decl
      | FStar_Extraction_ML_Syntax.MLM_Ty ty_decls ->
          let rec traverse f xs =
            match xs with
            | [] -> FStar_Pervasives_Native.Some []
            | o::os ->
                let uu____3922 = traverse f os in
                (match uu____3922 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some os' ->
                     let uu____3940 = f o in
                     (match uu____3940 with
                      | FStar_Pervasives_Native.None  ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some o' ->
                          FStar_Pervasives_Native.Some (o' :: os'))) in
          let uu____3952 = traverse (translate_single_type_decl env) ty_decls in
          (match uu____3952 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some decls ->
               FStar_Pervasives_Native.Some (DTypeMutual decls))
      | FStar_Extraction_ML_Syntax.MLM_Ty [] ->
          (FStar_Util.print_string
             "Impossible!! Empty block of mutually recursive type declarations";
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3967 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____3970 ->
          failwith "todo: translate_decl [MLM_Exn]"
and translate_single_type_decl:
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ty_decl  ->
      match ty_decl with
      | (assumed,name,_mangled_name,args,uu____3991,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Abbrev t)) ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args in
          if assumed
          then FStar_Pervasives_Native.None
          else
            (let uu____4016 =
               let uu____4017 =
                 let uu____4030 = translate_type env1 t in
                 (name1, (FStar_List.length args), uu____4030) in
               DTypeAlias uu____4017 in
             FStar_Pervasives_Native.Some uu____4016)
      | (uu____4037,name,_mangled_name,args,uu____4041,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
          let name1 = ((env.module_name), name) in
          let env1 = FStar_List.fold_left extend_t env args in
          let uu____4065 =
            let uu____4066 =
              let uu____4089 =
                FStar_List.map
                  (fun uu____4116  ->
                     match uu____4116 with
                     | (f,t) ->
                         let uu____4131 =
                           let uu____4136 = translate_type env1 t in
                           (uu____4136, false) in
                         (f, uu____4131)) fields in
              (name1, (FStar_List.length args), uu____4089) in
            DTypeFlat uu____4066 in
          FStar_Pervasives_Native.Some uu____4065
      | (uu____4157,name,_mangled_name,args,attrs,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
          let name1 = ((env.module_name), name) in
          let flags = translate_flags attrs in
          let env1 = FStar_List.fold_left extend_t env args in
          let uu____4194 =
            let uu____4195 =
              let uu____4228 =
                FStar_List.map
                  (fun uu____4273  ->
                     match uu____4273 with
                     | (cons1,ts) ->
                         let uu____4312 =
                           FStar_List.map
                             (fun uu____4339  ->
                                match uu____4339 with
                                | (name2,t) ->
                                    let uu____4354 =
                                      let uu____4359 = translate_type env1 t in
                                      (uu____4359, false) in
                                    (name2, uu____4354)) ts in
                         (cons1, uu____4312)) branches in
              (name1, flags, (FStar_List.length args), uu____4228) in
            DTypeVariant uu____4195 in
          FStar_Pervasives_Native.Some uu____4194
      | uu____4398 -> failwith "unable to translate type..."
and translate_type: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4404 = find_t env name in TBound uu____4404
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4406,t2) ->
          let uu____4408 =
            let uu____4413 = translate_type env t1 in
            let uu____4414 = translate_type env t2 in
            (uu____4413, uu____4414) in
          TArrow uu____4408
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4418 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4418 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4422 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4422 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4434 = FStar_Util.must (mk_width m) in TInt uu____4434
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4446 = FStar_Util.must (mk_width m) in TInt uu____4446
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4451 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4451 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4456 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4456 = "FStar.Buffer.buffer" ->
          let uu____4457 = translate_type env arg in TBuf uu____4457
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4458::[],p) when
          let uu____4462 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4462 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4500 = FStar_List.map (translate_type env) args in
          TTuple uu____4500
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4509 =
              let uu____4522 = FStar_List.map (translate_type env) args in
              (lid, uu____4522) in
            TApp uu____4509
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4531 = FStar_List.map (translate_type env) ts in
          TTuple uu____4531
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
    fun uu____4547  ->
      match uu____4547 with
      | (name,typ) ->
          let uu____4554 = translate_type env typ in
          { name; typ = uu____4554; mut = false }
and translate_expr: env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____4559 = find env name in EBound uu____4559
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4564 =
            let uu____4569 = FStar_Util.must (mk_op op) in
            let uu____4570 = FStar_Util.must (mk_width m) in
            (uu____4569, uu____4570) in
          EOp uu____4564
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4574 =
            let uu____4579 = FStar_Util.must (mk_bool_op op) in
            (uu____4579, Bool) in
          EOp uu____4574
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
              (fun uu___407_4609  ->
                 match uu___407_4609 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____4610 -> false) flags in
          let uu____4611 =
            if is_mut
            then
              let uu____4620 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____4625 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4625 = "FStar.ST.stackref" -> t
                | uu____4626 ->
                    let uu____4627 =
                      let uu____4628 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____4628 in
                    failwith uu____4627 in
              let uu____4631 =
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
                      (uu____4632,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____4634;
                    FStar_Extraction_ML_Syntax.loc = uu____4635;_} -> body1
                | uu____4638 ->
                    failwith "unexpected: bad desugaring of Mutable" in
              (uu____4620, uu____4631)
            else (typ, body) in
          (match uu____4611 with
           | (typ1,body1) ->
               let binder =
                 let uu____4643 = translate_type env typ1 in
                 { name; typ = uu____4643; mut = is_mut } in
               let body2 = translate_expr env body1 in
               let env1 = extend env name is_mut in
               let continuation1 = translate_expr env1 continuation in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4669 =
            let uu____4680 = translate_expr env expr in
            let uu____4681 = translate_branches env branches in
            (uu____4680, uu____4681) in
          EMatch uu____4669
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4695;
             FStar_Extraction_ML_Syntax.loc = uu____4696;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                v1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4698;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4699;_}::[])
          when
          (let uu____4704 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4704 = "FStar.HyperStack.ST.op_Bang") && (is_mutable env v1)
          -> let uu____4705 = find env v1 in EBound uu____4705
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4707;
             FStar_Extraction_ML_Syntax.loc = uu____4708;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                v1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4710;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4711;_}::e1::[])
          when
          (let uu____4717 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4717 = "FStar.HyperStack.ST.op_Colon_Equals") &&
            (is_mutable env v1)
          ->
          let uu____4718 =
            let uu____4723 =
              let uu____4724 = find env v1 in EBound uu____4724 in
            let uu____4725 = translate_expr env e1 in
            (uu____4723, uu____4725) in
          EAssign uu____4718
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4727;
                  FStar_Extraction_ML_Syntax.loc = uu____4728;_},uu____4729);
             FStar_Extraction_ML_Syntax.mlty = uu____4730;
             FStar_Extraction_ML_Syntax.loc = uu____4731;_},e1::e2::[])
          when
          (let uu____4742 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4742 = "FStar.Buffer.index") ||
            (let uu____4744 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4744 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____4745 =
            let uu____4750 = translate_expr env e1 in
            let uu____4751 = translate_expr env e2 in
            (uu____4750, uu____4751) in
          EBufRead uu____4745
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4753;
                  FStar_Extraction_ML_Syntax.loc = uu____4754;_},uu____4755);
             FStar_Extraction_ML_Syntax.mlty = uu____4756;
             FStar_Extraction_ML_Syntax.loc = uu____4757;_},e1::[])
          when
          let uu____4765 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4765 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____4766 =
            let uu____4771 = translate_expr env e1 in
            (uu____4771, (EConstant (UInt32, "0"))) in
          EBufRead uu____4766
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4773;
                  FStar_Extraction_ML_Syntax.loc = uu____4774;_},uu____4775);
             FStar_Extraction_ML_Syntax.mlty = uu____4776;
             FStar_Extraction_ML_Syntax.loc = uu____4777;_},e1::e2::[])
          when
          let uu____4786 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4786 = "FStar.Buffer.create" ->
          let uu____4787 =
            let uu____4794 = translate_expr env e1 in
            let uu____4795 = translate_expr env e2 in
            (Stack, uu____4794, uu____4795) in
          EBufCreate uu____4787
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4797;
                  FStar_Extraction_ML_Syntax.loc = uu____4798;_},uu____4799);
             FStar_Extraction_ML_Syntax.mlty = uu____4800;
             FStar_Extraction_ML_Syntax.loc = uu____4801;_},_rid::init1::[])
          when
          let uu____4810 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4810 = "FStar.HyperStack.ST.ralloc" ->
          let uu____4811 =
            let uu____4818 = translate_expr env init1 in
            (Eternal, uu____4818, (EConstant (UInt32, "0"))) in
          EBufCreate uu____4811
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4820;
                  FStar_Extraction_ML_Syntax.loc = uu____4821;_},uu____4822);
             FStar_Extraction_ML_Syntax.mlty = uu____4823;
             FStar_Extraction_ML_Syntax.loc = uu____4824;_},_e0::e1::e2::[])
          when
          let uu____4834 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4834 = "FStar.Buffer.rcreate" ->
          let uu____4835 =
            let uu____4842 = translate_expr env e1 in
            let uu____4843 = translate_expr env e2 in
            (Eternal, uu____4842, uu____4843) in
          EBufCreate uu____4835
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4845;
                  FStar_Extraction_ML_Syntax.loc = uu____4846;_},uu____4847);
             FStar_Extraction_ML_Syntax.mlty = uu____4848;
             FStar_Extraction_ML_Syntax.loc = uu____4849;_},e2::[])
          when
          let uu____4857 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4857 = "FStar.Buffer.createL" ->
          let rec list_elements1 acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements1 (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____4895 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!" in
          let list_elements2 = list_elements1 [] in
          let uu____4903 =
            let uu____4910 =
              let uu____4913 = list_elements2 e2 in
              FStar_List.map (translate_expr env) uu____4913 in
            (Stack, uu____4910) in
          EBufCreateL uu____4903
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
             FStar_Extraction_ML_Syntax.loc = uu____4923;_},e1::e2::_e3::[])
          when
          let uu____4933 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4933 = "FStar.Buffer.sub" ->
          let uu____4934 =
            let uu____4939 = translate_expr env e1 in
            let uu____4940 = translate_expr env e2 in
            (uu____4939, uu____4940) in
          EBufSub uu____4934
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4942;
                  FStar_Extraction_ML_Syntax.loc = uu____4943;_},uu____4944);
             FStar_Extraction_ML_Syntax.mlty = uu____4945;
             FStar_Extraction_ML_Syntax.loc = uu____4946;_},e1::e2::[])
          when
          let uu____4955 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4955 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4957;
                  FStar_Extraction_ML_Syntax.loc = uu____4958;_},uu____4959);
             FStar_Extraction_ML_Syntax.mlty = uu____4960;
             FStar_Extraction_ML_Syntax.loc = uu____4961;_},e1::e2::[])
          when
          let uu____4970 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4970 = "FStar.Buffer.offset" ->
          let uu____4971 =
            let uu____4976 = translate_expr env e1 in
            let uu____4977 = translate_expr env e2 in
            (uu____4976, uu____4977) in
          EBufSub uu____4971
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4979;
                  FStar_Extraction_ML_Syntax.loc = uu____4980;_},uu____4981);
             FStar_Extraction_ML_Syntax.mlty = uu____4982;
             FStar_Extraction_ML_Syntax.loc = uu____4983;_},e1::e2::e3::[])
          when
          (let uu____4995 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4995 = "FStar.Buffer.upd") ||
            (let uu____4997 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4997 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____4998 =
            let uu____5005 = translate_expr env e1 in
            let uu____5006 = translate_expr env e2 in
            let uu____5007 = translate_expr env e3 in
            (uu____5005, uu____5006, uu____5007) in
          EBufWrite uu____4998
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
          uu____5022 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5023 =
            let uu____5030 = translate_expr env e1 in
            let uu____5031 = translate_expr env e2 in
            (uu____5030, (EConstant (UInt32, "0")), uu____5031) in
          EBufWrite uu____5023
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5033;
             FStar_Extraction_ML_Syntax.loc = uu____5034;_},uu____5035::[])
          when
          let uu____5038 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5038 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5040;
             FStar_Extraction_ML_Syntax.loc = uu____5041;_},uu____5042::[])
          when
          let uu____5045 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5045 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5047;
                  FStar_Extraction_ML_Syntax.loc = uu____5048;_},uu____5049);
             FStar_Extraction_ML_Syntax.mlty = uu____5050;
             FStar_Extraction_ML_Syntax.loc = uu____5051;_},e1::e2::e3::e4::e5::[])
          when
          let uu____5063 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5063 = "FStar.Buffer.blit" ->
          let uu____5064 =
            let uu____5075 = translate_expr env e1 in
            let uu____5076 = translate_expr env e2 in
            let uu____5077 = translate_expr env e3 in
            let uu____5078 = translate_expr env e4 in
            let uu____5079 = translate_expr env e5 in
            (uu____5075, uu____5076, uu____5077, uu____5078, uu____5079) in
          EBufBlit uu____5064
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5081;
                  FStar_Extraction_ML_Syntax.loc = uu____5082;_},uu____5083);
             FStar_Extraction_ML_Syntax.mlty = uu____5084;
             FStar_Extraction_ML_Syntax.loc = uu____5085;_},e1::e2::e3::[])
          when
          let uu____5095 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5095 = "FStar.Buffer.fill" ->
          let uu____5096 =
            let uu____5103 = translate_expr env e1 in
            let uu____5104 = translate_expr env e2 in
            let uu____5105 = translate_expr env e3 in
            (uu____5103, uu____5104, uu____5105) in
          EBufFill uu____5096
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5107;
             FStar_Extraction_ML_Syntax.loc = uu____5108;_},uu____5109::[])
          when
          let uu____5112 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5112 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5114;
             FStar_Extraction_ML_Syntax.loc = uu____5115;_},e1::[])
          when
          let uu____5119 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5119 = "Obj.repr" ->
          let uu____5120 =
            let uu____5125 = translate_expr env e1 in (uu____5125, TAny) in
          ECast uu____5120
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5128;
             FStar_Extraction_ML_Syntax.loc = uu____5129;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5137 = FStar_Util.must (mk_width m) in
          let uu____5138 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____5137 uu____5138 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5140;
             FStar_Extraction_ML_Syntax.loc = uu____5141;_},args)
          when is_bool_op op ->
          let uu____5149 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____5149 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5151;
             FStar_Extraction_ML_Syntax.loc = uu____5152;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5154;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5155;_}::[])
          when is_machine_int m ->
          let uu____5170 =
            let uu____5175 = FStar_Util.must (mk_width m) in (uu____5175, c) in
          EConstant uu____5170
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5177;
             FStar_Extraction_ML_Syntax.loc = uu____5178;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5180;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5181;_}::[])
          when is_machine_int m ->
          let uu____5196 =
            let uu____5201 = FStar_Util.must (mk_width m) in (uu____5201, c) in
          EConstant uu____5196
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5202;
             FStar_Extraction_ML_Syntax.loc = uu____5203;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5205;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5206;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5212 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5213;
             FStar_Extraction_ML_Syntax.loc = uu____5214;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5216;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5217;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5223 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5225;
             FStar_Extraction_ML_Syntax.loc = uu____5226;_},arg::[])
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
            let uu____5233 =
              let uu____5238 = translate_expr env arg in
              (uu____5238, (TInt UInt64)) in
            ECast uu____5233
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5240 =
                 let uu____5245 = translate_expr env arg in
                 (uu____5245, (TInt UInt32)) in
               ECast uu____5240)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5247 =
                   let uu____5252 = translate_expr env arg in
                   (uu____5252, (TInt UInt16)) in
                 ECast uu____5247)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5254 =
                     let uu____5259 = translate_expr env arg in
                     (uu____5259, (TInt UInt8)) in
                   ECast uu____5254)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5261 =
                       let uu____5266 = translate_expr env arg in
                       (uu____5266, (TInt Int64)) in
                     ECast uu____5261)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5268 =
                         let uu____5273 = translate_expr env arg in
                         (uu____5273, (TInt Int32)) in
                       ECast uu____5268)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5275 =
                           let uu____5280 = translate_expr env arg in
                           (uu____5280, (TInt Int16)) in
                         ECast uu____5275)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5282 =
                             let uu____5287 = translate_expr env arg in
                             (uu____5287, (TInt Int8)) in
                           ECast uu____5282)
                        else
                          (let uu____5289 =
                             let uu____5296 =
                               let uu____5299 = translate_expr env arg in
                               [uu____5299] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5296) in
                           EApp uu____5289)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5310 =
            let uu____5317 = translate_expr env head1 in
            let uu____5318 = FStar_List.map (translate_expr env) args in
            (uu____5317, uu____5318) in
          EApp uu____5310
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5329 =
            let uu____5336 = translate_expr env head1 in
            let uu____5337 = FStar_List.map (translate_type env) ty_args in
            (uu____5336, uu____5337) in
          ETypApp uu____5329
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5345 =
            let uu____5350 = translate_expr env e1 in
            let uu____5351 = translate_type env t_to in
            (uu____5350, uu____5351) in
          ECast uu____5345
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5352,fields) ->
          let uu____5370 =
            let uu____5381 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5382 =
              FStar_List.map
                (fun uu____5401  ->
                   match uu____5401 with
                   | (field,expr) ->
                       let uu____5412 = translate_expr env expr in
                       (field, uu____5412)) fields in
            (uu____5381, uu____5382) in
          EFlat uu____5370
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5421 =
            let uu____5428 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____5429 = translate_expr env e1 in
            (uu____5428, uu____5429, (FStar_Pervasives_Native.snd path)) in
          EField uu____5421
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5432 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5446) ->
          let uu____5451 =
            let uu____5452 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1 in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5452 in
          failwith uu____5451
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5458 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____5458
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5464 = FStar_List.map (translate_expr env) es in
          ETuple uu____5464
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5467,cons1),es) ->
          let uu____5484 =
            let uu____5493 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5494 = FStar_List.map (translate_expr env) es in
            (uu____5493, cons1, uu____5494) in
          ECons uu____5484
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args in
          let env1 = add_binders env args in
          let uu____5517 =
            let uu____5526 = translate_expr env1 body in
            let uu____5527 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty in
            (binders, uu____5526, uu____5527) in
          EFun uu____5517
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5537 =
            let uu____5544 = translate_expr env e1 in
            let uu____5545 = translate_expr env e2 in
            let uu____5546 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31 in
            (uu____5544, uu____5545, uu____5546) in
          EIfThenElse uu____5537
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5548 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5555 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____5570 ->
          failwith "todo: translate_expr [MLE_Coerce]"
and assert_lid: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____5585 =
              let uu____5598 = FStar_List.map (translate_type env) ts in
              (lid, uu____5598) in
            TApp uu____5585
          else TQualified lid
      | uu____5604 -> failwith "invalid argument: assert_lid"
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
    fun uu____5630  ->
      match uu____5630 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____5656 = translate_pat env pat in
            (match uu____5656 with
             | (env1,pat1) ->
                 let uu____5667 = translate_expr env1 expr in
                 (pat1, uu____5667))
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
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5683,cons1),ps) ->
          let uu____5700 =
            FStar_List.fold_left
              (fun uu____5720  ->
                 fun p1  ->
                   match uu____5720 with
                   | (env1,acc) ->
                       let uu____5740 = translate_pat env1 p1 in
                       (match uu____5740 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____5700 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____5769,ps) ->
          let uu____5787 =
            FStar_List.fold_left
              (fun uu____5821  ->
                 fun uu____5822  ->
                   match (uu____5821, uu____5822) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____5891 = translate_pat env1 p1 in
                       (match uu____5891 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps in
          (match uu____5787 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____5953 =
            FStar_List.fold_left
              (fun uu____5973  ->
                 fun p1  ->
                   match uu____5973 with
                   | (env1,acc) ->
                       let uu____5993 = translate_pat env1 p1 in
                       (match uu____5993 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____5953 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          let uu____6021 =
            let uu____6022 = translate_pat_constant c in PConstant uu____6022 in
          (env, uu____6021)
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6027 ->
          failwith "todo: translate_pat [MLP_Branch]"
and translate_pat_constant: FStar_Extraction_ML_Syntax.mlconstant -> constant
  =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        (CInt, s)
and translate_constant: FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6049) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6064 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____6065 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____6066 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6067 ->
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
          let uu____6087 =
            let uu____6094 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____6094) in
          EApp uu____6087