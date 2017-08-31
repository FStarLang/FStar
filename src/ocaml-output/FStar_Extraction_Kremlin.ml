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
<<<<<<< HEAD
  FStar_Pervasives_Native.tuple4[@@deriving show]
=======
  FStar_Pervasives_Native.tuple4 
  | DTypeMutual of decl Prims.list 
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
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
<<<<<<< HEAD
    match projectee with | DGlobal _0 -> true | uu____523 -> false
let __proj__DGlobal__item___0:
=======
    match projectee with | DGlobal _0 -> true | uu____526 -> false
  
let __proj__DGlobal__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,typ,expr)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DGlobal _0 -> _0
let uu___is_DFunction: decl -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | DFunction _0 -> true | uu____609 -> false
let __proj__DFunction__item___0:
=======
    match projectee with | DFunction _0 -> true | uu____614 -> false
  
let __proj__DFunction__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr) FStar_Pervasives_Native.tuple7
  = fun projectee  -> match projectee with | DFunction _0 -> _0
let uu___is_DTypeAlias: decl -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | DTypeAlias _0 -> true | uu____711 -> false
let __proj__DTypeAlias__item___0:
=======
    match projectee with | DTypeAlias _0 -> true | uu____718 -> false
  
let __proj__DTypeAlias__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      Prims.int,typ) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0
let uu___is_DTypeFlat: decl -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | DTypeFlat _0 -> true | uu____781 -> false
let __proj__DTypeFlat__item___0:
=======
    match projectee with | DTypeFlat _0 -> true | uu____790 -> false
  
let __proj__DTypeFlat__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      Prims.int,(Prims.string,(typ,Prims.bool) FStar_Pervasives_Native.tuple2)
                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0
let uu___is_DExternal: decl -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | DExternal _0 -> true | uu____873 -> false
let __proj__DExternal__item___0:
=======
    match projectee with | DExternal _0 -> true | uu____884 -> false
  
let __proj__DExternal__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  decl ->
    (cc FStar_Pervasives_Native.option,(Prims.string Prims.list,Prims.string)
                                         FStar_Pervasives_Native.tuple2,
      typ) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DExternal _0 -> _0
let uu___is_DTypeVariant: decl -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | DTypeVariant _0 -> true | uu____959 -> false
let __proj__DTypeVariant__item___0:
=======
    match projectee with | DTypeVariant _0 -> true | uu____972 -> false
  
let __proj__DTypeVariant__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,(Prims.string,(Prims.string,(typ,Prims.bool)
                                                              FStar_Pervasives_Native.tuple2)
                                                FStar_Pervasives_Native.tuple2
                                                Prims.list)
                                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple4
<<<<<<< HEAD
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
=======
  = fun projectee  -> match projectee with | DTypeVariant _0 -> _0 
let uu___is_DTypeMutual : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeMutual _0 -> true | uu____1084 -> false
  
let __proj__DTypeMutual__item___0 : decl -> decl Prims.list =
  fun projectee  -> match projectee with | DTypeMutual _0 -> _0 
let uu___is_StdCall : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1103 -> false
  
let uu___is_CDecl : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1108 -> false
  
let uu___is_FastCall : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1113 -> false
  
let uu___is_Private : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1118 -> false
  
let uu___is_NoExtract : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____1123 -> false
  
let uu___is_CInline : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1128 -> false
  
let uu___is_Substitute : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1133 -> false
  
let uu___is_GCType : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1138 -> false
  
let uu___is_Eternal : lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1143 -> false
  
let uu___is_Stack : lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1148 -> false
  
let uu___is_EBound : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1154 -> false
  
let __proj__EBound__item___0 : expr -> Prims.int =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let uu___is_EQualified : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1174 -> false
  
let __proj__EQualified__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EQualified _0 -> _0
let uu___is_EConstant: expr -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | EConstant _0 -> true | uu____1171 -> false
let __proj__EConstant__item___0:
=======
    match projectee with | EConstant _0 -> true | uu____1210 -> false
  
let __proj__EConstant__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EConstant _0 -> _0
let uu___is_EUnit: expr -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | EUnit  -> true | uu____1194 -> false
let uu___is_EApp: expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1205 -> false
let __proj__EApp__item___0:
=======
    match projectee with | EUnit  -> true | uu____1235 -> false
  
let uu___is_EApp : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1247 -> false
  
let __proj__EApp__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EApp _0 -> _0
let uu___is_ETypApp: expr -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | ETypApp _0 -> true | uu____1241 -> false
let __proj__ETypApp__item___0:
=======
    match projectee with | ETypApp _0 -> true | uu____1285 -> false
  
let __proj__ETypApp__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ETypApp _0 -> _0
let uu___is_ELet: expr -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | ELet _0 -> true | uu____1277 -> false
let __proj__ELet__item___0:
=======
    match projectee with | ELet _0 -> true | uu____1323 -> false
  
let __proj__ELet__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ELet _0 -> _0
let uu___is_EIfThenElse: expr -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
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
=======
    match projectee with | EIfThenElse _0 -> true | uu____1361 -> false
  
let __proj__EIfThenElse__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let uu___is_ESequence : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1395 -> false
  
let __proj__ESequence__item___0 : expr -> expr Prims.list =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let uu___is_EAssign : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1419 -> false
  
let __proj__EAssign__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EAssign _0 -> _0
let uu___is_EBufCreate: expr -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | EBufCreate _0 -> true | uu____1397 -> false
let __proj__EBufCreate__item___0:
=======
    match projectee with | EBufCreate _0 -> true | uu____1451 -> false
  
let __proj__EBufCreate__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0
let uu___is_EBufRead: expr -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | EBufRead _0 -> true | uu____1431 -> false
let __proj__EBufRead__item___0:
=======
    match projectee with | EBufRead _0 -> true | uu____1487 -> false
  
let __proj__EBufRead__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufRead _0 -> _0
let uu___is_EBufWrite: expr -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | EBufWrite _0 -> true | uu____1461 -> false
let __proj__EBufWrite__item___0:
=======
    match projectee with | EBufWrite _0 -> true | uu____1519 -> false
  
let __proj__EBufWrite__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0
let uu___is_EBufSub: expr -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | EBufSub _0 -> true | uu____1495 -> false
let __proj__EBufSub__item___0:
=======
    match projectee with | EBufSub _0 -> true | uu____1555 -> false
  
let __proj__EBufSub__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufSub _0 -> _0
let uu___is_EBufBlit: expr -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | EBufBlit _0 -> true | uu____1529 -> false
let __proj__EBufBlit__item___0:
=======
    match projectee with | EBufBlit _0 -> true | uu____1591 -> false
  
let __proj__EBufBlit__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5 =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0
let uu___is_EMatch: expr -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
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
=======
    match projectee with | EMatch _0 -> true | uu____1645 -> false
  
let __proj__EMatch__item___0 :
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let uu___is_EOp : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1693 -> false
  
let __proj__EOp__item___0 : expr -> (op,width) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EOp _0 -> _0 
let uu___is_ECast : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1723 -> false
  
let __proj__ECast__item___0 :
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let uu___is_EPushFrame : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1748 -> false
  
let uu___is_EPopFrame : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1753 -> false
  
let uu___is_EBool : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1759 -> false
  
let __proj__EBool__item___0 : expr -> Prims.bool =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let uu___is_EAny : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1772 -> false
  
let uu___is_EAbort : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1777 -> false
  
let uu___is_EReturn : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1783 -> false
  
let __proj__EReturn__item___0 : expr -> expr =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let uu___is_EFlat : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1807 -> false
  
let __proj__EFlat__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EFlat _0 -> _0
let uu___is_EField: expr -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | EField _0 -> true | uu____1777 -> false
let __proj__EField__item___0:
=======
    match projectee with | EField _0 -> true | uu____1857 -> false
  
let __proj__EField__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EField _0 -> _0
let uu___is_EWhile: expr -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | EWhile _0 -> true | uu____1811 -> false
let __proj__EWhile__item___0:
=======
    match projectee with | EWhile _0 -> true | uu____1893 -> false
  
let __proj__EWhile__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EWhile _0 -> _0
let uu___is_EBufCreateL: expr -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
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
=======
    match projectee with | EBufCreateL _0 -> true | uu____1925 -> false
  
let __proj__EBufCreateL__item___0 :
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let uu___is_ETuple : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____1959 -> false
  
let __proj__ETuple__item___0 : expr -> expr Prims.list =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let uu___is_ECons : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____1987 -> false
  
let __proj__ECons__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ECons _0 -> _0
let uu___is_EBufFill: expr -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
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
=======
    match projectee with | EBufFill _0 -> true | uu____2031 -> false
  
let __proj__EBufFill__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let uu___is_EString : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2063 -> false
  
let __proj__EString__item___0 : expr -> Prims.string =
  fun projectee  -> match projectee with | EString _0 -> _0 
let uu___is_EFun : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2085 -> false
  
let __proj__EFun__item___0 :
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let uu___is_EAbortS : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2123 -> false
  
let __proj__EAbortS__item___0 : expr -> Prims.string =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let uu___is_Add : op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____2136 -> false 
let uu___is_AddW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2141 -> false
  
let uu___is_Sub : op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____2146 -> false 
let uu___is_SubW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2151 -> false
  
let uu___is_Div : op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____2156 -> false 
let uu___is_DivW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2161 -> false
  
let uu___is_Mult : op -> Prims.bool =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2166 -> false
  
let uu___is_MultW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2171 -> false
  
let uu___is_Mod : op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____2176 -> false 
let uu___is_BOr : op -> Prims.bool =
  fun projectee  -> match projectee with | BOr  -> true | uu____2181 -> false 
let uu___is_BAnd : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2186 -> false
  
let uu___is_BXor : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2191 -> false
  
let uu___is_BShiftL : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2196 -> false
  
let uu___is_BShiftR : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2201 -> false
  
let uu___is_BNot : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2206 -> false
  
let uu___is_Eq : op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2211 -> false 
let uu___is_Neq : op -> Prims.bool =
  fun projectee  -> match projectee with | Neq  -> true | uu____2216 -> false 
let uu___is_Lt : op -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2221 -> false 
let uu___is_Lte : op -> Prims.bool =
  fun projectee  -> match projectee with | Lte  -> true | uu____2226 -> false 
let uu___is_Gt : op -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2231 -> false 
let uu___is_Gte : op -> Prims.bool =
  fun projectee  -> match projectee with | Gte  -> true | uu____2236 -> false 
let uu___is_And : op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____2241 -> false 
let uu___is_Or : op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____2246 -> false 
let uu___is_Xor : op -> Prims.bool =
  fun projectee  -> match projectee with | Xor  -> true | uu____2251 -> false 
let uu___is_Not : op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____2256 -> false 
let uu___is_PUnit : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2261 -> false
  
let uu___is_PBool : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2267 -> false
  
let __proj__PBool__item___0 : pattern -> Prims.bool =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let uu___is_PVar : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2281 -> false
  
let __proj__PVar__item___0 : pattern -> binder =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let uu___is_PCons : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2301 -> false
  
let __proj__PCons__item___0 :
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PCons _0 -> _0 
let uu___is_PTuple : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2335 -> false
  
let __proj__PTuple__item___0 : pattern -> pattern Prims.list =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let uu___is_PRecord : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2361 -> false
  
let __proj__PRecord__item___0 :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list
  = fun projectee  -> match projectee with | PRecord _0 -> _0
let uu___is_UInt8: width -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
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
=======
    match projectee with | UInt8  -> true | uu____2392 -> false
  
let uu___is_UInt16 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2397 -> false
  
let uu___is_UInt32 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2402 -> false
  
let uu___is_UInt64 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2407 -> false
  
let uu___is_Int8 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2412 -> false
  
let uu___is_Int16 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2417 -> false
  
let uu___is_Int32 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2422 -> false
  
let uu___is_Int64 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2427 -> false
  
let uu___is_Bool : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2432 -> false
  
let uu___is_CInt : width -> Prims.bool =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____2437 -> false
  
let __proj__Mkbinder__item__name : binder -> Prims.string =
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
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
<<<<<<< HEAD
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
=======
  
let uu___is_TInt : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____2464 -> false
  
let __proj__TInt__item___0 : typ -> width =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let uu___is_TBuf : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2478 -> false
  
let __proj__TBuf__item___0 : typ -> typ =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let uu___is_TUnit : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2491 -> false
  
let uu___is_TQualified : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2503 -> false
  
let __proj__TQualified__item___0 :
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TQualified _0 -> _0 
let uu___is_TBool : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2534 -> false
  
let uu___is_TAny : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2539 -> false
  
let uu___is_TArrow : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2549 -> false
  
let __proj__TArrow__item___0 :
  typ -> (typ,typ) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let uu___is_TBound : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2575 -> false
  
let __proj__TBound__item___0 : typ -> Prims.int =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let uu___is_TApp : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2601 -> false
  
let __proj__TApp__item___0 :
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TApp _0 -> _0 
let uu___is_TTuple : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____2653 -> false
  
let __proj__TTuple__item___0 : typ -> typ Prims.list =
  fun projectee  -> match projectee with | TTuple _0 -> _0 
type program = decl Prims.list
type ident = Prims.string
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
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
<<<<<<< HEAD
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
=======
type version = Prims.int
let current_version : version = (Prims.parse_int "25") 
type file = (Prims.string,program) FStar_Pervasives_Native.tuple2
type binary_format = (version,file Prims.list) FStar_Pervasives_Native.tuple2
let fst3 :
  'Auu____2734 'Auu____2735 'Auu____2736 .
    ('Auu____2736,'Auu____2735,'Auu____2734) FStar_Pervasives_Native.tuple3
      -> 'Auu____2736
  = fun uu____2746  -> match uu____2746 with | (x,uu____2754,uu____2755) -> x 
let snd3 :
  'Auu____2764 'Auu____2765 'Auu____2766 .
    ('Auu____2766,'Auu____2765,'Auu____2764) FStar_Pervasives_Native.tuple3
      -> 'Auu____2765
  = fun uu____2776  -> match uu____2776 with | (uu____2783,x,uu____2785) -> x 
let thd3 :
  'Auu____2794 'Auu____2795 'Auu____2796 .
    ('Auu____2796,'Auu____2795,'Auu____2794) FStar_Pervasives_Native.tuple3
      -> 'Auu____2794
  = fun uu____2806  -> match uu____2806 with | (uu____2813,uu____2814,x) -> x 
let mk_width : Prims.string -> width FStar_Pervasives_Native.option =
  fun uu___123_2821  ->
    match uu___123_2821 with
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
<<<<<<< HEAD
    | uu____2648 -> FStar_Pervasives_Native.None
let mk_bool_op: Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___402_2653  ->
    match uu___402_2653 with
=======
    | uu____2824 -> FStar_Pervasives_Native.None
  
let mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___124_2830  ->
    match uu___124_2830 with
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
<<<<<<< HEAD
    | uu____2656 -> FStar_Pervasives_Native.None
let is_bool_op: Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None
let mk_op: Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___403_2666  ->
    match uu___403_2666 with
=======
    | uu____2833 -> FStar_Pervasives_Native.None
  
let is_bool_op : Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let mk_op : Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___125_2845  ->
    match uu___125_2845 with
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
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
<<<<<<< HEAD
    | uu____2669 -> FStar_Pervasives_Native.None
let is_op: Prims.string -> Prims.bool =
  fun op  -> (mk_op op) <> FStar_Pervasives_Native.None
let is_machine_int: Prims.string -> Prims.bool =
  fun m  -> (mk_width m) <> FStar_Pervasives_Native.None
=======
    | uu____2848 -> FStar_Pervasives_Native.None
  
let is_op : Prims.string -> Prims.bool =
  fun op  -> (mk_op op) <> FStar_Pervasives_Native.None 
let is_machine_int : Prims.string -> Prims.bool =
  fun m  -> (mk_width m) <> FStar_Pervasives_Native.None 
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
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
<<<<<<< HEAD
        let uu___408_2780 = env in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___408_2780.names_t);
          module_name = (uu___408_2780.module_name)
=======
        let uu___130_2970 = env  in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___130_2970.names_t);
          module_name = (uu___130_2970.module_name)
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
        }
let extend_t: env -> Prims.string -> env =
  fun env  ->
    fun x  ->
<<<<<<< HEAD
      let uu___409_2787 = env in
      {
        names = (uu___409_2787.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___409_2787.module_name)
=======
      let uu___131_2979 = env  in
      {
        names = (uu___131_2979.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___131_2979.module_name)
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      }
let find_name: env -> Prims.string -> name =
  fun env  ->
    fun x  ->
<<<<<<< HEAD
      let uu____2794 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names in
      match uu____2794 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
let is_mutable: env -> Prims.string -> Prims.bool =
  fun env  -> fun x  -> let uu____2806 = find_name env x in uu____2806.mut
let find: env -> Prims.string -> Prims.int =
=======
      let uu____2988 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____2988 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let is_mutable : env -> Prims.string -> Prims.bool =
  fun env  -> fun x  -> let uu____3002 = find_name env x  in uu____3002.mut 
let find : env -> Prims.string -> Prims.int =
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
<<<<<<< HEAD
      | uu____2821 ->
          let uu____2822 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____2822
let find_t: env -> Prims.string -> Prims.int =
=======
      | uu____3019 ->
          let uu____3020 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____3020
  
let find_t : env -> Prims.string -> Prims.int =
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
<<<<<<< HEAD
      | uu____2837 ->
          let uu____2838 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____2838
let add_binders:
  'Auu____2842 .
    env ->
      (Prims.string,'Auu____2842) FStar_Pervasives_Native.tuple2 Prims.list
        -> env
=======
      | uu____3037 ->
          let uu____3038 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____3038
  
let add_binders :
  'Auu____3047 'Auu____3048 .
    env ->
      ((Prims.string,'Auu____3048) FStar_Pervasives_Native.tuple2,'Auu____3047)
        FStar_Pervasives_Native.tuple2 Prims.list -> env
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
<<<<<<< HEAD
           fun uu____2872  ->
             match uu____2872 with
             | (name,uu____2878) -> extend env1 name false) env binders
let rec translate: FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____3003  ->
    match uu____3003 with
=======
           fun uu____3091  ->
             match uu____3091 with
             | ((name,uu____3101),uu____3102) -> extend env1 name false) env
        binders
  
let rec translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____3237  ->
    match uu____3237 with
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
    | FStar_Extraction_ML_Syntax.MLLib modules1 ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
<<<<<<< HEAD
               let uu____3063 = m in
               match uu____3063 with
               | ((prefix1,final),uu____3084,uu____3085) ->
=======
               let uu____3297 = m  in
               match uu____3297 with
               | ((prefix1,final),uu____3318,uu____3319) ->
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
                   FStar_String.concat "."
                     (FStar_List.append prefix1 [final]) in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
<<<<<<< HEAD
               (let uu____3117 = translate_module m in
                FStar_Pervasives_Native.Some uu____3117)
             with
             | e ->
                 ((let uu____3126 = FStar_Util.print_exn e in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3126);
=======
               (let uu____3351 = translate_module m  in
                FStar_Pervasives_Native.Some uu____3351)
             with
             | e ->
                 ((let uu____3360 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3360);
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
                  FStar_Pervasives_Native.None)) modules1
and translate_module:
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
    (FStar_Extraction_ML_Syntax.mlsig,FStar_Extraction_ML_Syntax.mlmodule)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,FStar_Extraction_ML_Syntax.mllib)
    FStar_Pervasives_Native.tuple3 -> file
  =
<<<<<<< HEAD
  fun uu____3127  ->
    match uu____3127 with
    | (module_name,modul,uu____3148) ->
=======
  fun uu____3361  ->
    match uu____3361 with
    | (module_name,modul,uu____3382) ->
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name] in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.filter_map (translate_decl (empty module_name1))
                decls
<<<<<<< HEAD
          | uu____3191 ->
              failwith "Unexpected standalone interface or nested modules" in
=======
          | uu____3425 ->
              failwith "Unexpected standalone interface or nested modules"
           in
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
        ((FStar_String.concat "_" module_name1), program)
and translate_flags:
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list =
  fun flags  ->
    FStar_List.choose
<<<<<<< HEAD
      (fun uu___404_3206  ->
         match uu___404_3206 with
=======
      (fun uu___126_3440  ->
         match uu___126_3440 with
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
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
<<<<<<< HEAD
         | FStar_Extraction_ML_Syntax.Comment s ->
             FStar_Pervasives_Native.Some (Comment s)
         | uu____3210 -> FStar_Pervasives_Native.None) flags
and translate_decl:
=======
         | uu____3443 -> FStar_Pervasives_Native.None) flags

and translate_decl :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  env ->
    FStar_Extraction_ML_Syntax.mlmodule1 ->
      decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let
<<<<<<< HEAD
          (flavor,flags,{ FStar_Extraction_ML_Syntax.mllb_name = name;
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3220;
=======
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____3451);
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3454;
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
                          FStar_Extraction_ML_Syntax.mllb_def =
                            {
                              FStar_Extraction_ML_Syntax.expr =
                                FStar_Extraction_ML_Syntax.MLE_Fun
                                (args,body);
<<<<<<< HEAD
                              FStar_Extraction_ML_Syntax.mlty = uu____3223;
                              FStar_Extraction_ML_Syntax.loc = uu____3224;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____3225;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___405_3246  ->
                 match uu___405_3246 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____3247 -> false) flags in
=======
                              FStar_Extraction_ML_Syntax.mlty = uu____3457;
                              FStar_Extraction_ML_Syntax.loc = uu____3458;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____3459;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___127_3480  ->
                 match uu___127_3480 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____3481 -> false) flags
             in
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env in
          let env2 =
            FStar_List.fold_left
<<<<<<< HEAD
              (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars in
          let rec find_return_type i uu___406_3261 =
            match uu___406_3261 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3262,uu____3263,t)
=======
              (fun env2  ->
                 fun uu____3494  ->
                   match uu____3494 with
                   | (name1,uu____3500) -> extend_t env2 name1) env1 tvars
             in
          let rec find_return_type i uu___128_3507 =
            match uu___128_3507 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3508,uu____3509,t)
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
                when i > (Prims.parse_int "0") ->
                find_return_type (i - (Prims.parse_int "1")) t
            | t -> t in
          let t =
<<<<<<< HEAD
            let uu____3267 = find_return_type (FStar_List.length args) t0 in
            translate_type env2 uu____3267 in
          let binders = translate_binders env2 args in
          let env3 = add_binders env2 args in
          let name1 = ((env3.module_name), name) in
          let flags1 =
            match t0 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun
                (uu____3290,FStar_Extraction_ML_Syntax.E_GHOST ,uu____3291)
                ->
                let uu____3292 = translate_flags flags in NoExtract ::
                  uu____3292
            | uu____3295 -> translate_flags flags in
=======
            let uu____3513 = find_return_type (FStar_List.length args) t0  in
            translate_type env2 uu____3513  in
          let binders = translate_binders env2 args  in
          let env3 = add_binders env2 args  in
          let name1 = ((env3.module_name), name)  in
          let flags1 =
            match t0 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun
                (uu____3536,FStar_Extraction_ML_Syntax.E_GHOST ,uu____3537)
                ->
                let uu____3538 = translate_flags flags  in NoExtract ::
                  uu____3538
            | uu____3541 -> translate_flags flags  in
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
<<<<<<< HEAD
               let uu____3300 =
                 let uu____3301 =
                   let uu____3316 = translate_type env3 t0 in
                   (FStar_Pervasives_Native.None, name1, uu____3316) in
                 DExternal uu____3301 in
               FStar_Pervasives_Native.Some uu____3300
=======
               let uu____3546 =
                 let uu____3547 =
                   let uu____3562 = translate_type env3 t0  in
                   (FStar_Pervasives_Native.None, name1, uu____3562)  in
                 DExternal uu____3547  in
               FStar_Pervasives_Native.Some uu____3546
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
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
                 (FStar_Util.print2_warning "Writing a stub for %s (%s)\n"
                    (FStar_Pervasives_Native.snd name1) msg;
                  (let msg1 =
                     Prims.strcat "This function was not extracted:\n" msg in
                   FStar_Pervasives_Native.Some
                     (DFunction
                        (FStar_Pervasives_Native.None, flags1,
                          (FStar_List.length tvars), t, name1, binders,
                          (EAbortS msg1))))))
      | FStar_Extraction_ML_Syntax.MLM_Let
<<<<<<< HEAD
          (flavor,flags,{ FStar_Extraction_ML_Syntax.mllb_name = name;
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3378;
=======
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____3622);
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3625;
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
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
                                     uu____3381;
                                   FStar_Extraction_ML_Syntax.loc =
                                     uu____3382;_},uu____3383,uu____3384);
                              FStar_Extraction_ML_Syntax.mlty = uu____3385;
                              FStar_Extraction_ML_Syntax.loc = uu____3386;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____3387;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___405_3408  ->
                 match uu___405_3408 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____3409 -> false) flags in
=======
                                     uu____3628;
                                   FStar_Extraction_ML_Syntax.loc =
                                     uu____3629;_},uu____3630,uu____3631);
                              FStar_Extraction_ML_Syntax.mlty = uu____3632;
                              FStar_Extraction_ML_Syntax.loc = uu____3633;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____3634;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___127_3655  ->
                 match uu___127_3655 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____3656 -> false) flags
             in
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env in
          let env2 =
            FStar_List.fold_left
<<<<<<< HEAD
              (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars in
          let rec find_return_type i uu___406_3423 =
            match uu___406_3423 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3424,uu____3425,t)
=======
              (fun env2  ->
                 fun uu____3669  ->
                   match uu____3669 with
                   | (name1,uu____3675) -> extend_t env2 name1) env1 tvars
             in
          let rec find_return_type i uu___128_3682 =
            match uu___128_3682 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3683,uu____3684,t)
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
                when i > (Prims.parse_int "0") ->
                find_return_type (i - (Prims.parse_int "1")) t
            | t -> t in
          let t =
<<<<<<< HEAD
            let uu____3429 = find_return_type (FStar_List.length args) t0 in
            translate_type env2 uu____3429 in
          let binders = translate_binders env2 args in
          let env3 = add_binders env2 args in
          let name1 = ((env3.module_name), name) in
          let flags1 =
            match t0 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun
                (uu____3452,FStar_Extraction_ML_Syntax.E_GHOST ,uu____3453)
                ->
                let uu____3454 = translate_flags flags in NoExtract ::
                  uu____3454
            | uu____3457 -> translate_flags flags in
=======
            let uu____3688 = find_return_type (FStar_List.length args) t0  in
            translate_type env2 uu____3688  in
          let binders = translate_binders env2 args  in
          let env3 = add_binders env2 args  in
          let name1 = ((env3.module_name), name)  in
          let flags1 =
            match t0 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun
                (uu____3711,FStar_Extraction_ML_Syntax.E_GHOST ,uu____3712)
                ->
                let uu____3713 = translate_flags flags  in NoExtract ::
                  uu____3713
            | uu____3716 -> translate_flags flags  in
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
<<<<<<< HEAD
               let uu____3462 =
                 let uu____3463 =
                   let uu____3478 = translate_type env3 t0 in
                   (FStar_Pervasives_Native.None, name1, uu____3478) in
                 DExternal uu____3463 in
               FStar_Pervasives_Native.Some uu____3462
=======
               let uu____3721 =
                 let uu____3722 =
                   let uu____3737 = translate_type env3 t0  in
                   (FStar_Pervasives_Native.None, name1, uu____3737)  in
                 DExternal uu____3722  in
               FStar_Pervasives_Native.Some uu____3721
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
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
                 (FStar_Util.print2_warning "Writing a stub for %s (%s)\n"
                    (FStar_Pervasives_Native.snd name1) msg;
                  (let msg1 =
                     Prims.strcat "This function was not extracted:\n" msg in
                   FStar_Pervasives_Native.Some
                     (DFunction
                        (FStar_Pervasives_Native.None, flags1,
                          (FStar_List.length tvars), t, name1, binders,
                          (EAbortS msg1))))))
      | FStar_Extraction_ML_Syntax.MLM_Let
<<<<<<< HEAD
          (flavor,flags,{ FStar_Extraction_ML_Syntax.mllb_name = name;
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some ([],t);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3539;
                          FStar_Extraction_ML_Syntax.mllb_def = expr;
                          FStar_Extraction_ML_Syntax.print_typ = uu____3541;_}::[])
=======
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____3797);
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some ([],t);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3799;
                          FStar_Extraction_ML_Syntax.mllb_def = expr;
                          FStar_Extraction_ML_Syntax.print_typ = uu____3801;_}::[])
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
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
<<<<<<< HEAD
               ((let uu____3589 = FStar_Util.print_exn e in
                 FStar_Util.print2_warning
                   "Not translating definition for %s (%s)\n"
                   (FStar_Pervasives_Native.snd name1) uu____3589);
                FStar_Pervasives_Native.Some
                  (DGlobal (flags1, name1, t1, EAny))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (uu____3600,uu____3601,{
                                   FStar_Extraction_ML_Syntax.mllb_name =
                                     name;
                                   FStar_Extraction_ML_Syntax.mllb_tysc = ts;
                                   FStar_Extraction_ML_Syntax.mllb_add_unit =
                                     uu____3604;
                                   FStar_Extraction_ML_Syntax.mllb_def =
                                     uu____3605;
                                   FStar_Extraction_ML_Syntax.print_typ =
                                     uu____3606;_}::uu____3607)
=======
               ((let uu____3849 = FStar_Util.print_exn e  in
                 FStar_Util.print2
                   "Warning: not translating definition for %s (%s)\n"
                   (FStar_Pervasives_Native.snd name1) uu____3849);
                FStar_Pervasives_Native.Some
                  (DGlobal (flags1, name1, t1, EAny))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (uu____3860,uu____3861,{
                                   FStar_Extraction_ML_Syntax.mllb_name =
                                     (name,uu____3863);
                                   FStar_Extraction_ML_Syntax.mllb_tysc = ts;
                                   FStar_Extraction_ML_Syntax.mllb_add_unit =
                                     uu____3865;
                                   FStar_Extraction_ML_Syntax.mllb_def =
                                     uu____3866;
                                   FStar_Extraction_ML_Syntax.print_typ =
                                     uu____3867;_}::uu____3868)
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
          ->
          (FStar_Util.print1_warning
             "Not translating definition for %s (and possibly others)\n" name;
           (match ts with
            | FStar_Pervasives_Native.Some (idents,t) ->
<<<<<<< HEAD
                let uu____3622 =
                  FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                  (FStar_String.concat ", " idents) uu____3622
            | FStar_Pervasives_Native.None  -> ());
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Let uu____3625 ->
          failwith "impossible"
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3628 ->
          FStar_Pervasives_Native.None
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((assumed,name,_mangled_name,args,uu____3633,FStar_Pervasives_Native.Some
            (FStar_Extraction_ML_Syntax.MLTD_Abbrev t))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args in
          if assumed
          then FStar_Pervasives_Native.None
          else
            (let uu____3690 =
               let uu____3691 =
                 let uu____3704 = translate_type env1 t in
                 (name1, (FStar_List.length args), uu____3704) in
               DTypeAlias uu____3691 in
             FStar_Pervasives_Native.Some uu____3690)
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____3711,name,_mangled_name,args,uu____3715,FStar_Pervasives_Native.Some
            (FStar_Extraction_ML_Syntax.MLTD_Record fields))::[])
          ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args in
          let uu____3775 =
            let uu____3776 =
              let uu____3799 =
                FStar_List.map
                  (fun uu____3826  ->
                     match uu____3826 with
                     | (f,t) ->
                         let uu____3841 =
                           let uu____3846 = translate_type env1 t in
                           (uu____3846, false) in
                         (f, uu____3841)) fields in
              (name1, (FStar_List.length args), uu____3799) in
            DTypeFlat uu____3776 in
          FStar_Pervasives_Native.Some uu____3775
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____3867,name,_mangled_name,args,attrs,FStar_Pervasives_Native.Some
            (FStar_Extraction_ML_Syntax.MLTD_DType branches))::[])
          ->
          let name1 = ((env.module_name), name) in
          let flags = translate_flags attrs in
          let env1 = FStar_List.fold_left extend_t env args in
          let uu____3936 =
            let uu____3937 =
              let uu____3970 =
                FStar_List.map
                  (fun uu____4015  ->
                     match uu____4015 with
                     | (cons1,ts) ->
                         let uu____4054 =
                           FStar_List.map
                             (fun uu____4081  ->
                                match uu____4081 with
                                | (name2,t) ->
                                    let uu____4096 =
                                      let uu____4101 = translate_type env1 t in
                                      (uu____4101, false) in
                                    (name2, uu____4096)) ts in
                         (cons1, uu____4054)) branches in
              (name1, flags, (FStar_List.length args), uu____3970) in
            DTypeVariant uu____3937 in
          FStar_Pervasives_Native.Some uu____3936
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____4140,name,_mangled_name,uu____4143,uu____4144,uu____4145)::uu____4146)
          ->
          (FStar_Util.print1_warning
             "Not translating definition for %s (and possibly others)\n" name;
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Ty [] ->
          (FStar_Util.print_string
             "Impossible!! Empty block of mutually recursive type declarations\n";
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Top uu____4191 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____4194 ->
          failwith "todo: translate_decl [MLM_Exn]"
and translate_type: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
=======
                let uu____3883 =
                  let uu____3884 =
                    FStar_List.map FStar_Pervasives_Native.fst idents  in
                  FStar_String.concat ", " uu____3884  in
                let uu____3891 =
                  FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                  uu____3883 uu____3891
            | FStar_Pervasives_Native.None  -> ());
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Let uu____3894 ->
          failwith "impossible"
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3897 ->
          FStar_Pervasives_Native.None
      | FStar_Extraction_ML_Syntax.MLM_Ty (ty_decl::[]) ->
          translate_single_type_decl env ty_decl
      | FStar_Extraction_ML_Syntax.MLM_Ty ty_decls ->
          let rec traverse f xs =
            match xs with
            | [] -> FStar_Pervasives_Native.Some []
            | o::os ->
                let uu____3938 = traverse f os  in
                (match uu____3938 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some os' ->
                     let uu____3956 = f o  in
                     (match uu____3956 with
                      | FStar_Pervasives_Native.None  ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some o' ->
                          FStar_Pervasives_Native.Some (o' :: os')))
             in
          let uu____3968 = traverse (translate_single_type_decl env) ty_decls
             in
          (match uu____3968 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some decls ->
               FStar_Pervasives_Native.Some (DTypeMutual decls))
      | FStar_Extraction_ML_Syntax.MLM_Ty [] ->
          (FStar_Util.print_string
             "Impossible!! Empty block of mutually recursive type declarations";
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3983 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____3986 ->
          failwith "todo: translate_decl [MLM_Exn]"

and translate_single_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ty_decl  ->
      match ty_decl with
      | (assumed,name,_mangled_name,args,uu____4007,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Abbrev t)) ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____4034  ->
                   match uu____4034 with
                   | (name2,uu____4040) -> extend_t env1 name2) env args
             in
          if assumed
          then FStar_Pervasives_Native.None
          else
            (let uu____4044 =
               let uu____4045 =
                 let uu____4058 = translate_type env1 t  in
                 (name1, (FStar_List.length args), uu____4058)  in
               DTypeAlias uu____4045  in
             FStar_Pervasives_Native.Some uu____4044)
      | (uu____4065,name,_mangled_name,args,uu____4069,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____4102  ->
                   match uu____4102 with
                   | (name2,uu____4108) -> extend_t env1 name2) env args
             in
          let uu____4109 =
            let uu____4110 =
              let uu____4133 =
                FStar_List.map
                  (fun uu____4160  ->
                     match uu____4160 with
                     | (f,t) ->
                         let uu____4175 =
                           let uu____4180 = translate_type env1 t  in
                           (uu____4180, false)  in
                         (f, uu____4175)) fields
                 in
              (name1, (FStar_List.length args), uu____4133)  in
            DTypeFlat uu____4110  in
          FStar_Pervasives_Native.Some uu____4109
      | (uu____4201,name,_mangled_name,args,attrs,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
          let name1 = ((env.module_name), name)  in
          let flags = translate_flags attrs  in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____4247  ->
                   match uu____4247 with
                   | (name2,uu____4253) -> extend_t env1 name2) env args
             in
          let uu____4254 =
            let uu____4255 =
              let uu____4288 =
                FStar_List.map
                  (fun uu____4333  ->
                     match uu____4333 with
                     | (cons1,ts) ->
                         let uu____4372 =
                           FStar_List.map
                             (fun uu____4399  ->
                                match uu____4399 with
                                | (name2,t) ->
                                    let uu____4414 =
                                      let uu____4419 = translate_type env1 t
                                         in
                                      (uu____4419, false)  in
                                    (name2, uu____4414)) ts
                            in
                         (cons1, uu____4372)) branches
                 in
              (name1, flags, (FStar_List.length args), uu____4288)  in
            DTypeVariant uu____4255  in
          FStar_Pervasives_Native.Some uu____4254

and translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ =
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
<<<<<<< HEAD
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4210 = find_t env name in TBound uu____4210
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4212,t2) ->
          let uu____4214 =
            let uu____4219 = translate_type env t1 in
            let uu____4220 = translate_type env t2 in
            (uu____4219, uu____4220) in
          TArrow uu____4214
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4224 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4224 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4228 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4228 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4240 = FStar_Util.must (mk_width m) in TInt uu____4240
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4252 = FStar_Util.must (mk_width m) in TInt uu____4252
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4257 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4257 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4262 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4262 = "FStar.Buffer.buffer" ->
          let uu____4263 = translate_type env arg in TBuf uu____4263
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4264::[],p) when
          let uu____4268 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4268 = "FStar.Ghost.erased" -> TAny
=======
      | FStar_Extraction_ML_Syntax.MLTY_Var (name,uu____4461) ->
          let uu____4462 = find_t env name  in TBound uu____4462
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4464,t2) ->
          let uu____4466 =
            let uu____4471 = translate_type env t1  in
            let uu____4472 = translate_type env t2  in
            (uu____4471, uu____4472)  in
          TArrow uu____4466
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4476 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4476 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4480 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4480 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4492 = FStar_Util.must (mk_width m)  in TInt uu____4492
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4504 = FStar_Util.must (mk_width m)  in TInt uu____4504
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4509 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4509 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4514 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4514 = "FStar.Buffer.buffer" ->
          let uu____4515 = translate_type env arg  in TBuf uu____4515
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4516::[],p) when
          let uu____4520 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4520 = "FStar.Ghost.erased" -> TAny
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
<<<<<<< HEAD
          let uu____4306 = FStar_List.map (translate_type env) args in
          TTuple uu____4306
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4315 =
              let uu____4328 = FStar_List.map (translate_type env) args in
              (lid, uu____4328) in
            TApp uu____4315
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4337 = FStar_List.map (translate_type env) ts in
          TTuple uu____4337
and translate_binders:
=======
          let uu____4558 = FStar_List.map (translate_type env) args  in
          TTuple uu____4558
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4567 =
              let uu____4580 = FStar_List.map (translate_type env) args  in
              (lid, uu____4580)  in
            TApp uu____4567
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4589 = FStar_List.map (translate_type env) ts  in
          TTuple uu____4589

and translate_binders :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
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
<<<<<<< HEAD
    fun uu____4353  ->
      match uu____4353 with
      | (name,typ) ->
          let uu____4360 = translate_type env typ in
          { name; typ = uu____4360; mut = false }
and translate_expr: env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
=======
    fun uu____4605  ->
      match uu____4605 with
      | ((name,uu____4611),typ) ->
          let uu____4617 = translate_type env typ  in
          { name; typ = uu____4617; mut = false }

and translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
<<<<<<< HEAD
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____4365 = find env name in EBound uu____4365
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4370 =
            let uu____4375 = FStar_Util.must (mk_op op) in
            let uu____4376 = FStar_Util.must (mk_width m) in
            (uu____4375, uu____4376) in
          EOp uu____4370
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4380 =
            let uu____4385 = FStar_Util.must (mk_bool_op op) in
            (uu____4385, Bool) in
          EOp uu____4380
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags,{ FStar_Extraction_ML_Syntax.mllb_name = name;
=======
      | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____4622) ->
          let uu____4623 = find env name  in EBound uu____4623
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4628 =
            let uu____4633 = FStar_Util.must (mk_op op)  in
            let uu____4634 = FStar_Util.must (mk_width m)  in
            (uu____4633, uu____4634)  in
          EOp uu____4628
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4638 =
            let uu____4643 = FStar_Util.must (mk_bool_op op)  in
            (uu____4643, Bool)  in
          EOp uu____4638
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags,{
                           FStar_Extraction_ML_Syntax.mllb_name =
                             (name,uu____4648);
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
                           FStar_Extraction_ML_Syntax.mllb_tysc =
                             FStar_Pervasives_Native.Some ([],typ);
                           FStar_Extraction_ML_Syntax.mllb_add_unit =
                             add_unit;
                           FStar_Extraction_ML_Syntax.mllb_def = body;
                           FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let is_mut =
            FStar_Util.for_some
<<<<<<< HEAD
              (fun uu___407_4415  ->
                 match uu___407_4415 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____4416 -> false) flags in
          let uu____4417 =
            if is_mut
            then
              let uu____4426 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____4431 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4431 = "FStar.ST.stackref" -> t
                | uu____4432 ->
                    let uu____4433 =
                      let uu____4434 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____4434 in
                    failwith uu____4433 in
              let uu____4437 =
=======
              (fun uu___129_4674  ->
                 match uu___129_4674 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____4675 -> false) flags
             in
          let uu____4676 =
            if is_mut
            then
              let uu____4685 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____4690 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4690 = "FStar.ST.stackref" -> t
                | uu____4691 ->
                    let uu____4692 =
                      let uu____4693 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ
                         in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____4693
                       in
                    failwith uu____4692
                 in
              let uu____4696 =
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
<<<<<<< HEAD
                      (uu____4438,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____4440;
                    FStar_Extraction_ML_Syntax.loc = uu____4441;_} -> body1
                | uu____4444 ->
                    failwith "unexpected: bad desugaring of Mutable" in
              (uu____4426, uu____4437)
            else (typ, body) in
          (match uu____4417 with
           | (typ1,body1) ->
               let binder =
                 let uu____4449 = translate_type env typ1 in
                 { name; typ = uu____4449; mut = is_mut } in
               let body2 = translate_expr env body1 in
               let env1 = extend env name is_mut in
               let continuation1 = translate_expr env1 continuation in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4475 =
            let uu____4486 = translate_expr env expr in
            let uu____4487 = translate_branches env branches in
            (uu____4486, uu____4487) in
          EMatch uu____4475
=======
                      (uu____4697,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____4699;
                    FStar_Extraction_ML_Syntax.loc = uu____4700;_} -> body1
                | uu____4703 ->
                    failwith "unexpected: bad desugaring of Mutable"
                 in
              (uu____4685, uu____4696)
            else (typ, body)  in
          (match uu____4676 with
           | (typ1,body1) ->
               let binder =
                 let uu____4708 = translate_type env typ1  in
                 { name; typ = uu____4708; mut = is_mut }  in
               let body2 = translate_expr env body1  in
               let env1 = extend env name is_mut  in
               let continuation1 = translate_expr env1 continuation  in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4734 =
            let uu____4745 = translate_expr env expr  in
            let uu____4746 = translate_branches env branches  in
            (uu____4745, uu____4746)  in
          EMatch uu____4734
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____4501;
             FStar_Extraction_ML_Syntax.loc = uu____4502;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                v1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4504;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4505;_}::[])
          when
          (let uu____4510 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4510 = "FStar.HyperStack.ST.op_Bang") && (is_mutable env v1)
          -> let uu____4511 = find env v1 in EBound uu____4511
=======
             FStar_Extraction_ML_Syntax.mlty = uu____4760;
             FStar_Extraction_ML_Syntax.loc = uu____4761;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____4763);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4764;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4765;_}::[])
          when
          (let uu____4770 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4770 = "FStar.HyperStack.ST.op_Bang") && (is_mutable env v1)
          -> let uu____4771 = find env v1  in EBound uu____4771
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____4513;
             FStar_Extraction_ML_Syntax.loc = uu____4514;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                v1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4516;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4517;_}::e1::[])
          when
          (let uu____4523 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4523 = "FStar.HyperStack.ST.op_Colon_Equals") &&
            (is_mutable env v1)
          ->
          let uu____4524 =
            let uu____4529 =
              let uu____4530 = find env v1 in EBound uu____4530 in
            let uu____4531 = translate_expr env e1 in
            (uu____4529, uu____4531) in
          EAssign uu____4524
=======
             FStar_Extraction_ML_Syntax.mlty = uu____4773;
             FStar_Extraction_ML_Syntax.loc = uu____4774;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____4776);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4777;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4778;_}::e1::[])
          when
          (let uu____4784 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4784 = "FStar.HyperStack.ST.op_Colon_Equals") &&
            (is_mutable env v1)
          ->
          let uu____4785 =
            let uu____4790 =
              let uu____4791 = find env v1  in EBound uu____4791  in
            let uu____4792 = translate_expr env e1  in
            (uu____4790, uu____4792)  in
          EAssign uu____4785
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
                  FStar_Extraction_ML_Syntax.mlty = uu____4533;
                  FStar_Extraction_ML_Syntax.loc = uu____4534;_},uu____4535);
             FStar_Extraction_ML_Syntax.mlty = uu____4536;
             FStar_Extraction_ML_Syntax.loc = uu____4537;_},e1::e2::[])
          when
          (let uu____4548 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4548 = "FStar.Buffer.index") ||
            (let uu____4550 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4550 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____4551 =
            let uu____4556 = translate_expr env e1 in
            let uu____4557 = translate_expr env e2 in
            (uu____4556, uu____4557) in
          EBufRead uu____4551
=======
                  FStar_Extraction_ML_Syntax.mlty = uu____4794;
                  FStar_Extraction_ML_Syntax.loc = uu____4795;_},uu____4796);
             FStar_Extraction_ML_Syntax.mlty = uu____4797;
             FStar_Extraction_ML_Syntax.loc = uu____4798;_},e1::e2::[])
          when
          (let uu____4809 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4809 = "FStar.Buffer.index") ||
            (let uu____4811 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4811 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____4812 =
            let uu____4817 = translate_expr env e1  in
            let uu____4818 = translate_expr env e2  in
            (uu____4817, uu____4818)  in
          EBufRead uu____4812
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
                  FStar_Extraction_ML_Syntax.mlty = uu____4559;
                  FStar_Extraction_ML_Syntax.loc = uu____4560;_},uu____4561);
             FStar_Extraction_ML_Syntax.mlty = uu____4562;
             FStar_Extraction_ML_Syntax.loc = uu____4563;_},e1::e2::[])
          when
          let uu____4572 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4572 = "FStar.Buffer.create" ->
          let uu____4573 =
            let uu____4580 = translate_expr env e1 in
            let uu____4581 = translate_expr env e2 in
            (Stack, uu____4580, uu____4581) in
          EBufCreate uu____4573
=======
                  FStar_Extraction_ML_Syntax.mlty = uu____4820;
                  FStar_Extraction_ML_Syntax.loc = uu____4821;_},uu____4822);
             FStar_Extraction_ML_Syntax.mlty = uu____4823;
             FStar_Extraction_ML_Syntax.loc = uu____4824;_},e1::e2::[])
          when
          let uu____4833 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4833 = "FStar.Buffer.create" ->
          let uu____4834 =
            let uu____4841 = translate_expr env e1  in
            let uu____4842 = translate_expr env e2  in
            (Stack, uu____4841, uu____4842)  in
          EBufCreate uu____4834
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
                  FStar_Extraction_ML_Syntax.mlty = uu____4583;
                  FStar_Extraction_ML_Syntax.loc = uu____4584;_},uu____4585);
             FStar_Extraction_ML_Syntax.mlty = uu____4586;
             FStar_Extraction_ML_Syntax.loc = uu____4587;_},_e0::e1::e2::[])
          when
          let uu____4597 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4597 = "FStar.Buffer.rcreate" ->
          let uu____4598 =
            let uu____4605 = translate_expr env e1 in
            let uu____4606 = translate_expr env e2 in
            (Eternal, uu____4605, uu____4606) in
          EBufCreate uu____4598
=======
                  FStar_Extraction_ML_Syntax.mlty = uu____4844;
                  FStar_Extraction_ML_Syntax.loc = uu____4845;_},uu____4846);
             FStar_Extraction_ML_Syntax.mlty = uu____4847;
             FStar_Extraction_ML_Syntax.loc = uu____4848;_},_e0::e1::e2::[])
          when
          let uu____4858 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4858 = "FStar.Buffer.rcreate" ->
          let uu____4859 =
            let uu____4866 = translate_expr env e1  in
            let uu____4867 = translate_expr env e2  in
            (Eternal, uu____4866, uu____4867)  in
          EBufCreate uu____4859
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
                  FStar_Extraction_ML_Syntax.mlty = uu____4608;
                  FStar_Extraction_ML_Syntax.loc = uu____4609;_},uu____4610);
             FStar_Extraction_ML_Syntax.mlty = uu____4611;
             FStar_Extraction_ML_Syntax.loc = uu____4612;_},e2::[])
          when
          let uu____4620 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4620 = "FStar.Buffer.createL" ->
=======
                  FStar_Extraction_ML_Syntax.mlty = uu____4869;
                  FStar_Extraction_ML_Syntax.loc = uu____4870;_},uu____4871);
             FStar_Extraction_ML_Syntax.mlty = uu____4872;
             FStar_Extraction_ML_Syntax.loc = uu____4873;_},e2::[])
          when
          let uu____4881 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4881 = "FStar.Buffer.createL" ->
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
          let rec list_elements1 acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements1 (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
<<<<<<< HEAD
            | uu____4658 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!" in
          let list_elements2 = list_elements1 [] in
          let uu____4666 =
            let uu____4673 =
              let uu____4676 = list_elements2 e2 in
              FStar_List.map (translate_expr env) uu____4676 in
            (Stack, uu____4673) in
          EBufCreateL uu____4666
=======
            | uu____4919 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!"
             in
          let list_elements2 = list_elements1 []  in
          let uu____4927 =
            let uu____4934 =
              let uu____4937 = list_elements2 e2  in
              FStar_List.map (translate_expr env) uu____4937  in
            (Stack, uu____4934)  in
          EBufCreateL uu____4927
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
                  FStar_Extraction_ML_Syntax.mlty = uu____4682;
                  FStar_Extraction_ML_Syntax.loc = uu____4683;_},uu____4684);
             FStar_Extraction_ML_Syntax.mlty = uu____4685;
             FStar_Extraction_ML_Syntax.loc = uu____4686;_},e1::e2::_e3::[])
          when
          let uu____4696 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4696 = "FStar.Buffer.sub" ->
          let uu____4697 =
            let uu____4702 = translate_expr env e1 in
            let uu____4703 = translate_expr env e2 in
            (uu____4702, uu____4703) in
          EBufSub uu____4697
=======
                  FStar_Extraction_ML_Syntax.mlty = uu____4943;
                  FStar_Extraction_ML_Syntax.loc = uu____4944;_},uu____4945);
             FStar_Extraction_ML_Syntax.mlty = uu____4946;
             FStar_Extraction_ML_Syntax.loc = uu____4947;_},e1::e2::_e3::[])
          when
          let uu____4957 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4957 = "FStar.Buffer.sub" ->
          let uu____4958 =
            let uu____4963 = translate_expr env e1  in
            let uu____4964 = translate_expr env e2  in
            (uu____4963, uu____4964)  in
          EBufSub uu____4958
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
                  FStar_Extraction_ML_Syntax.mlty = uu____4705;
                  FStar_Extraction_ML_Syntax.loc = uu____4706;_},uu____4707);
             FStar_Extraction_ML_Syntax.mlty = uu____4708;
             FStar_Extraction_ML_Syntax.loc = uu____4709;_},e1::e2::[])
          when
          let uu____4718 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4718 = "FStar.Buffer.join" -> translate_expr env e1
=======
                  FStar_Extraction_ML_Syntax.mlty = uu____4966;
                  FStar_Extraction_ML_Syntax.loc = uu____4967;_},uu____4968);
             FStar_Extraction_ML_Syntax.mlty = uu____4969;
             FStar_Extraction_ML_Syntax.loc = uu____4970;_},e1::e2::[])
          when
          let uu____4979 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4979 = "FStar.Buffer.join" -> translate_expr env e1
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
                  FStar_Extraction_ML_Syntax.mlty = uu____4720;
                  FStar_Extraction_ML_Syntax.loc = uu____4721;_},uu____4722);
             FStar_Extraction_ML_Syntax.mlty = uu____4723;
             FStar_Extraction_ML_Syntax.loc = uu____4724;_},e1::e2::[])
          when
          let uu____4733 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4733 = "FStar.Buffer.offset" ->
          let uu____4734 =
            let uu____4739 = translate_expr env e1 in
            let uu____4740 = translate_expr env e2 in
            (uu____4739, uu____4740) in
          EBufSub uu____4734
=======
                  FStar_Extraction_ML_Syntax.mlty = uu____4981;
                  FStar_Extraction_ML_Syntax.loc = uu____4982;_},uu____4983);
             FStar_Extraction_ML_Syntax.mlty = uu____4984;
             FStar_Extraction_ML_Syntax.loc = uu____4985;_},e1::e2::[])
          when
          let uu____4994 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4994 = "FStar.Buffer.offset" ->
          let uu____4995 =
            let uu____5000 = translate_expr env e1  in
            let uu____5001 = translate_expr env e2  in
            (uu____5000, uu____5001)  in
          EBufSub uu____4995
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
                  FStar_Extraction_ML_Syntax.mlty = uu____4742;
                  FStar_Extraction_ML_Syntax.loc = uu____4743;_},uu____4744);
             FStar_Extraction_ML_Syntax.mlty = uu____4745;
             FStar_Extraction_ML_Syntax.loc = uu____4746;_},e1::e2::e3::[])
          when
          (let uu____4758 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4758 = "FStar.Buffer.upd") ||
            (let uu____4760 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4760 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____4761 =
            let uu____4768 = translate_expr env e1 in
            let uu____4769 = translate_expr env e2 in
            let uu____4770 = translate_expr env e3 in
            (uu____4768, uu____4769, uu____4770) in
          EBufWrite uu____4761
=======
                  FStar_Extraction_ML_Syntax.mlty = uu____5003;
                  FStar_Extraction_ML_Syntax.loc = uu____5004;_},uu____5005);
             FStar_Extraction_ML_Syntax.mlty = uu____5006;
             FStar_Extraction_ML_Syntax.loc = uu____5007;_},e1::e2::e3::[])
          when
          (let uu____5019 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5019 = "FStar.Buffer.upd") ||
            (let uu____5021 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5021 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____5022 =
            let uu____5029 = translate_expr env e1  in
            let uu____5030 = translate_expr env e2  in
            let uu____5031 = translate_expr env e3  in
            (uu____5029, uu____5030, uu____5031)  in
          EBufWrite uu____5022
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____4772;
             FStar_Extraction_ML_Syntax.loc = uu____4773;_},uu____4774::[])
          when
          let uu____4777 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4777 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
=======
             FStar_Extraction_ML_Syntax.mlty = uu____5033;
             FStar_Extraction_ML_Syntax.loc = uu____5034;_},uu____5035::[])
          when
          let uu____5038 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5038 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____4779;
             FStar_Extraction_ML_Syntax.loc = uu____4780;_},uu____4781::[])
          when
          let uu____4784 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4784 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
=======
             FStar_Extraction_ML_Syntax.mlty = uu____5040;
             FStar_Extraction_ML_Syntax.loc = uu____5041;_},uu____5042::[])
          when
          let uu____5045 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5045 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
                  FStar_Extraction_ML_Syntax.mlty = uu____4786;
                  FStar_Extraction_ML_Syntax.loc = uu____4787;_},uu____4788);
             FStar_Extraction_ML_Syntax.mlty = uu____4789;
             FStar_Extraction_ML_Syntax.loc = uu____4790;_},e1::e2::e3::e4::e5::[])
          when
          let uu____4802 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4802 = "FStar.Buffer.blit" ->
          let uu____4803 =
            let uu____4814 = translate_expr env e1 in
            let uu____4815 = translate_expr env e2 in
            let uu____4816 = translate_expr env e3 in
            let uu____4817 = translate_expr env e4 in
            let uu____4818 = translate_expr env e5 in
            (uu____4814, uu____4815, uu____4816, uu____4817, uu____4818) in
          EBufBlit uu____4803
=======
                  FStar_Extraction_ML_Syntax.mlty = uu____5047;
                  FStar_Extraction_ML_Syntax.loc = uu____5048;_},uu____5049);
             FStar_Extraction_ML_Syntax.mlty = uu____5050;
             FStar_Extraction_ML_Syntax.loc = uu____5051;_},e1::e2::e3::e4::e5::[])
          when
          let uu____5063 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5063 = "FStar.Buffer.blit" ->
          let uu____5064 =
            let uu____5075 = translate_expr env e1  in
            let uu____5076 = translate_expr env e2  in
            let uu____5077 = translate_expr env e3  in
            let uu____5078 = translate_expr env e4  in
            let uu____5079 = translate_expr env e5  in
            (uu____5075, uu____5076, uu____5077, uu____5078, uu____5079)  in
          EBufBlit uu____5064
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
                  FStar_Extraction_ML_Syntax.mlty = uu____4820;
                  FStar_Extraction_ML_Syntax.loc = uu____4821;_},uu____4822);
             FStar_Extraction_ML_Syntax.mlty = uu____4823;
             FStar_Extraction_ML_Syntax.loc = uu____4824;_},e1::e2::e3::[])
          when
          let uu____4834 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4834 = "FStar.Buffer.fill" ->
          let uu____4835 =
            let uu____4842 = translate_expr env e1 in
            let uu____4843 = translate_expr env e2 in
            let uu____4844 = translate_expr env e3 in
            (uu____4842, uu____4843, uu____4844) in
          EBufFill uu____4835
=======
                  FStar_Extraction_ML_Syntax.mlty = uu____5081;
                  FStar_Extraction_ML_Syntax.loc = uu____5082;_},uu____5083);
             FStar_Extraction_ML_Syntax.mlty = uu____5084;
             FStar_Extraction_ML_Syntax.loc = uu____5085;_},e1::e2::e3::[])
          when
          let uu____5095 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5095 = "FStar.Buffer.fill" ->
          let uu____5096 =
            let uu____5103 = translate_expr env e1  in
            let uu____5104 = translate_expr env e2  in
            let uu____5105 = translate_expr env e3  in
            (uu____5103, uu____5104, uu____5105)  in
          EBufFill uu____5096
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____4846;
             FStar_Extraction_ML_Syntax.loc = uu____4847;_},uu____4848::[])
          when
          let uu____4851 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4851 = "FStar.HyperStack.ST.get" -> EUnit
=======
             FStar_Extraction_ML_Syntax.mlty = uu____5107;
             FStar_Extraction_ML_Syntax.loc = uu____5108;_},uu____5109::[])
          when
          let uu____5112 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5112 = "FStar.HyperStack.ST.get" -> EUnit
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____4853;
             FStar_Extraction_ML_Syntax.loc = uu____4854;_},e1::[])
          when
          let uu____4858 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4858 = "Obj.repr" ->
          let uu____4859 =
            let uu____4864 = translate_expr env e1 in (uu____4864, TAny) in
          ECast uu____4859
=======
             FStar_Extraction_ML_Syntax.mlty = uu____5114;
             FStar_Extraction_ML_Syntax.loc = uu____5115;_},e1::[])
          when
          let uu____5119 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5119 = "Obj.repr" ->
          let uu____5120 =
            let uu____5125 = translate_expr env e1  in (uu____5125, TAny)  in
          ECast uu____5120
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____4867;
             FStar_Extraction_ML_Syntax.loc = uu____4868;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____4876 = FStar_Util.must (mk_width m) in
          let uu____4877 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____4876 uu____4877 args
=======
             FStar_Extraction_ML_Syntax.mlty = uu____5128;
             FStar_Extraction_ML_Syntax.loc = uu____5129;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5137 = FStar_Util.must (mk_width m)  in
          let uu____5138 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____5137 uu____5138 args
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____4879;
             FStar_Extraction_ML_Syntax.loc = uu____4880;_},args)
          when is_bool_op op ->
          let uu____4888 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____4888 args
=======
             FStar_Extraction_ML_Syntax.mlty = uu____5140;
             FStar_Extraction_ML_Syntax.loc = uu____5141;_},args)
          when is_bool_op op ->
          let uu____5149 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____5149 args
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____4890;
             FStar_Extraction_ML_Syntax.loc = uu____4891;_},{
=======
             FStar_Extraction_ML_Syntax.mlty = uu____5151;
             FStar_Extraction_ML_Syntax.loc = uu____5152;_},{
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
<<<<<<< HEAD
                                                                = uu____4893;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4894;_}::[])
          when is_machine_int m ->
          let uu____4909 =
            let uu____4914 = FStar_Util.must (mk_width m) in (uu____4914, c) in
          EConstant uu____4909
=======
                                                                = uu____5154;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5155;_}::[])
          when is_machine_int m ->
          let uu____5170 =
            let uu____5175 = FStar_Util.must (mk_width m)  in (uu____5175, c)
             in
          EConstant uu____5170
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____4916;
             FStar_Extraction_ML_Syntax.loc = uu____4917;_},{
=======
             FStar_Extraction_ML_Syntax.mlty = uu____5177;
             FStar_Extraction_ML_Syntax.loc = uu____5178;_},{
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
<<<<<<< HEAD
                                                                = uu____4919;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4920;_}::[])
          when is_machine_int m ->
          let uu____4935 =
            let uu____4940 = FStar_Util.must (mk_width m) in (uu____4940, c) in
          EConstant uu____4935
=======
                                                                = uu____5180;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5181;_}::[])
          when is_machine_int m ->
          let uu____5196 =
            let uu____5201 = FStar_Util.must (mk_width m)  in (uu____5201, c)
             in
          EConstant uu____5196
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____4941;
             FStar_Extraction_ML_Syntax.loc = uu____4942;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4944;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4945;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____4951 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____4952;
             FStar_Extraction_ML_Syntax.loc = uu____4953;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4955;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4956;_}::[])
=======
             FStar_Extraction_ML_Syntax.mlty = uu____5202;
             FStar_Extraction_ML_Syntax.loc = uu____5203;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5205;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5206;_}::[])
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
<<<<<<< HEAD
           | uu____4962 ->
=======
           | uu____5212 ->
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
<<<<<<< HEAD
             FStar_Extraction_ML_Syntax.mlty = uu____4964;
             FStar_Extraction_ML_Syntax.loc = uu____4965;_},arg::[])
=======
             FStar_Extraction_ML_Syntax.mlty = uu____5214;
             FStar_Extraction_ML_Syntax.loc = uu____5215;_},arg::[])
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
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
            let uu____4972 =
              let uu____4977 = translate_expr env arg in
              (uu____4977, (TInt UInt64)) in
            ECast uu____4972
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____4979 =
                 let uu____4984 = translate_expr env arg in
                 (uu____4984, (TInt UInt32)) in
               ECast uu____4979)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____4986 =
                   let uu____4991 = translate_expr env arg in
                   (uu____4991, (TInt UInt16)) in
                 ECast uu____4986)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____4993 =
                     let uu____4998 = translate_expr env arg in
                     (uu____4998, (TInt UInt8)) in
                   ECast uu____4993)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5000 =
                       let uu____5005 = translate_expr env arg in
                       (uu____5005, (TInt Int64)) in
                     ECast uu____5000)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5007 =
                         let uu____5012 = translate_expr env arg in
                         (uu____5012, (TInt Int32)) in
                       ECast uu____5007)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5014 =
                           let uu____5019 = translate_expr env arg in
                           (uu____5019, (TInt Int16)) in
                         ECast uu____5014)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5021 =
                             let uu____5026 = translate_expr env arg in
                             (uu____5026, (TInt Int8)) in
                           ECast uu____5021)
                        else
                          (let uu____5028 =
                             let uu____5035 =
                               let uu____5038 = translate_expr env arg in
                               [uu____5038] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5035) in
                           EApp uu____5028)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5049 =
            let uu____5056 = translate_expr env head1 in
            let uu____5057 = FStar_List.map (translate_expr env) args in
            (uu____5056, uu____5057) in
          EApp uu____5049
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5068 =
            let uu____5075 = translate_expr env head1 in
            let uu____5076 = FStar_List.map (translate_type env) ty_args in
            (uu____5075, uu____5076) in
          ETypApp uu____5068
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5084 =
            let uu____5089 = translate_expr env e1 in
            let uu____5090 = translate_type env t_to in
            (uu____5089, uu____5090) in
          ECast uu____5084
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5091,fields) ->
          let uu____5109 =
            let uu____5120 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5121 =
              FStar_List.map
                (fun uu____5140  ->
                   match uu____5140 with
                   | (field,expr) ->
                       let uu____5151 = translate_expr env expr in
                       (field, uu____5151)) fields in
            (uu____5120, uu____5121) in
          EFlat uu____5109
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5160 =
            let uu____5167 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____5168 = translate_expr env e1 in
            (uu____5167, uu____5168, (FStar_Pervasives_Native.snd path)) in
          EField uu____5160
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5171 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5185) ->
          let uu____5190 =
            let uu____5191 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1 in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5191 in
          failwith uu____5190
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5197 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____5197
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5203 = FStar_List.map (translate_expr env) es in
          ETuple uu____5203
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5206,cons1),es) ->
          let uu____5223 =
            let uu____5232 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5233 = FStar_List.map (translate_expr env) es in
            (uu____5232, cons1, uu____5233) in
          ECons uu____5223
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args in
          let env1 = add_binders env args in
          let uu____5256 =
            let uu____5265 = translate_expr env1 body in
            let uu____5266 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty in
            (binders, uu____5265, uu____5266) in
          EFun uu____5256
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5276 =
            let uu____5283 = translate_expr env e1 in
            let uu____5284 = translate_expr env e2 in
            let uu____5285 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31 in
            (uu____5283, uu____5284, uu____5285) in
          EIfThenElse uu____5276
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5287 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5294 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____5309 ->
=======
            let uu____5222 =
              let uu____5227 = translate_expr env arg  in
              (uu____5227, (TInt UInt64))  in
            ECast uu____5222
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5229 =
                 let uu____5234 = translate_expr env arg  in
                 (uu____5234, (TInt UInt32))  in
               ECast uu____5229)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5236 =
                   let uu____5241 = translate_expr env arg  in
                   (uu____5241, (TInt UInt16))  in
                 ECast uu____5236)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5243 =
                     let uu____5248 = translate_expr env arg  in
                     (uu____5248, (TInt UInt8))  in
                   ECast uu____5243)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5250 =
                       let uu____5255 = translate_expr env arg  in
                       (uu____5255, (TInt Int64))  in
                     ECast uu____5250)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5257 =
                         let uu____5262 = translate_expr env arg  in
                         (uu____5262, (TInt Int32))  in
                       ECast uu____5257)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5264 =
                           let uu____5269 = translate_expr env arg  in
                           (uu____5269, (TInt Int16))  in
                         ECast uu____5264)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5271 =
                             let uu____5276 = translate_expr env arg  in
                             (uu____5276, (TInt Int8))  in
                           ECast uu____5271)
                        else
                          (let uu____5278 =
                             let uu____5285 =
                               let uu____5288 = translate_expr env arg  in
                               [uu____5288]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5285)
                              in
                           EApp uu____5278)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5299 =
            let uu____5306 = translate_expr env head1  in
            let uu____5307 = FStar_List.map (translate_expr env) args  in
            (uu____5306, uu____5307)  in
          EApp uu____5299
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5318 =
            let uu____5325 = translate_expr env head1  in
            let uu____5326 = FStar_List.map (translate_type env) ty_args  in
            (uu____5325, uu____5326)  in
          ETypApp uu____5318
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5334 =
            let uu____5339 = translate_expr env e1  in
            let uu____5340 = translate_type env t_to  in
            (uu____5339, uu____5340)  in
          ECast uu____5334
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5341,fields) ->
          let uu____5359 =
            let uu____5370 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5371 =
              FStar_List.map
                (fun uu____5390  ->
                   match uu____5390 with
                   | (field,expr) ->
                       let uu____5401 = translate_expr env expr  in
                       (field, uu____5401)) fields
               in
            (uu____5370, uu____5371)  in
          EFlat uu____5359
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5410 =
            let uu____5417 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____5418 = translate_expr env e1  in
            (uu____5417, uu____5418, (FStar_Pervasives_Native.snd path))  in
          EField uu____5410
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5421 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5435) ->
          let uu____5440 =
            let uu____5441 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5441
             in
          failwith uu____5440
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5447 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____5447
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5453 = FStar_List.map (translate_expr env) es  in
          ETuple uu____5453
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5456,cons1),es) ->
          let uu____5473 =
            let uu____5482 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5483 = FStar_List.map (translate_expr env) es  in
            (uu____5482, cons1, uu____5483)  in
          ECons uu____5473
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____5506 =
            let uu____5515 = translate_expr env1 body  in
            let uu____5516 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____5515, uu____5516)  in
          EFun uu____5506
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5526 =
            let uu____5533 = translate_expr env e1  in
            let uu____5534 = translate_expr env e2  in
            let uu____5535 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____5533, uu____5534, uu____5535)  in
          EIfThenElse uu____5526
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5537 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5544 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____5559 ->
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
          failwith "todo: translate_expr [MLE_Coerce]"
and assert_lid: env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
<<<<<<< HEAD
            let uu____5324 =
              let uu____5337 = FStar_List.map (translate_type env) ts in
              (lid, uu____5337) in
            TApp uu____5324
          else TQualified lid
      | uu____5343 -> failwith "invalid argument: assert_lid"
and translate_branches:
=======
            let uu____5574 =
              let uu____5587 = FStar_List.map (translate_type env) ts  in
              (lid, uu____5587)  in
            TApp uu____5574
          else TQualified lid
      | uu____5593 -> failwith "invalid argument: assert_lid"

and translate_branches :
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
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
<<<<<<< HEAD
    fun uu____5369  ->
      match uu____5369 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____5395 = translate_pat env pat in
            (match uu____5395 with
             | (env1,pat1) ->
                 let uu____5406 = translate_expr env1 expr in
                 (pat1, uu____5406))
=======
    fun uu____5619  ->
      match uu____5619 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____5645 = translate_pat env pat  in
            (match uu____5645 with
             | (env1,pat1) ->
                 let uu____5656 = translate_expr env1 expr  in
                 (pat1, uu____5656))
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
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
<<<<<<< HEAD
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name false in
=======
      | FStar_Extraction_ML_Syntax.MLP_Var (name,uu____5670) ->
          let env1 = extend env name false  in
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_" false in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
<<<<<<< HEAD
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5422,cons1),ps) ->
          let uu____5439 =
            FStar_List.fold_left
              (fun uu____5459  ->
                 fun p1  ->
                   match uu____5459 with
                   | (env1,acc) ->
                       let uu____5479 = translate_pat env1 p1 in
                       (match uu____5479 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____5439 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____5508,ps) ->
          let uu____5526 =
            FStar_List.fold_left
              (fun uu____5560  ->
                 fun uu____5561  ->
                   match (uu____5560, uu____5561) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____5630 = translate_pat env1 p1 in
                       (match uu____5630 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps in
          (match uu____5526 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____5692 =
            FStar_List.fold_left
              (fun uu____5712  ->
                 fun p1  ->
                   match uu____5712 with
                   | (env1,acc) ->
                       let uu____5732 = translate_pat env1 p1 in
                       (match uu____5732 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____5692 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____5759 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____5764 ->
=======
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5673,cons1),ps) ->
          let uu____5690 =
            FStar_List.fold_left
              (fun uu____5710  ->
                 fun p1  ->
                   match uu____5710 with
                   | (env1,acc) ->
                       let uu____5730 = translate_pat env1 p1  in
                       (match uu____5730 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____5690 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____5759,ps) ->
          let uu____5777 =
            FStar_List.fold_left
              (fun uu____5811  ->
                 fun uu____5812  ->
                   match (uu____5811, uu____5812) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____5881 = translate_pat env1 p1  in
                       (match uu____5881 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____5777 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____5943 =
            FStar_List.fold_left
              (fun uu____5963  ->
                 fun p1  ->
                   match uu____5963 with
                   | (env1,acc) ->
                       let uu____5983 = translate_pat env1 p1  in
                       (match uu____5983 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____5943 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6010 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6015 ->
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
          failwith "todo: translate_pat [MLP_Branch]"
and translate_constant: FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_Int
<<<<<<< HEAD
        (s,FStar_Pervasives_Native.Some uu____5774) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____5789 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____5790 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____5791 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____5792 ->
=======
        (s,FStar_Pervasives_Native.Some uu____6025) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6040 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____6041 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____6042 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6043 ->
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
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
<<<<<<< HEAD
          let uu____5812 =
            let uu____5819 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____5819) in
          EApp uu____5812
=======
          let uu____6063 =
            let uu____6070 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____6070)  in
          EApp uu____6063
>>>>>>> e808de684... Add support for extracting mutually recursive data types via Kremlin
