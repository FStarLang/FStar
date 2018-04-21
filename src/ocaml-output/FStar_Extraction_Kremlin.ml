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
  FStar_Pervasives_Native.tuple4 [@@deriving show]
and cc =
  | StdCall 
  | CDecl 
  | FastCall [@@deriving show]
and flag =
  | Private 
  | WipeBody 
  | CInline 
  | Substitute 
  | GCType 
  | Comment of Prims.string 
  | MustDisappear 
  | Const of Prims.string 
  | Prologue of Prims.string 
  | Epilogue of Prims.string [@@deriving show]
and lifetime =
  | Eternal 
  | Stack 
  | ManuallyManaged [@@deriving show]
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
  | EAbortS of Prims.string 
  | EBufFree of expr [@@deriving show]
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
  | Not [@@deriving show]
and pattern =
  | PUnit 
  | PBool of Prims.bool 
  | PVar of binder 
  | PCons of (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2
  
  | PTuple of pattern Prims.list 
  | PRecord of (Prims.string,pattern) FStar_Pervasives_Native.tuple2
  Prims.list 
  | PConstant of (width,Prims.string) FStar_Pervasives_Native.tuple2 
[@@deriving show]
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
  | CInt [@@deriving show]
and binder = {
  name: Prims.string ;
  typ: typ }[@@deriving show]
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
  | TTuple of typ Prims.list [@@deriving show]
let uu___is_DGlobal : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DGlobal _0 -> true | uu____616 -> false
  
let __proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,Prims.int,typ,expr)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let uu___is_DFunction : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____710 -> false
  
let __proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr) FStar_Pervasives_Native.tuple7
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let uu___is_DTypeAlias : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____818 -> false
  
let __proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,typ) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let uu___is_DTypeFlat : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____906 -> false
  
let __proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,(Prims.string,(typ,Prims.bool)
                                                FStar_Pervasives_Native.tuple2)
                                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let uu___is_DExternal : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____1016 -> false
  
let __proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,(Prims.string
                                                          Prims.list,
                                                         Prims.string)
                                                         FStar_Pervasives_Native.tuple2,
      typ) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let uu___is_DTypeVariant : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____1116 -> false
  
let __proj__DTypeVariant__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,(Prims.string,(Prims.string,(typ,Prims.bool)
                                                              FStar_Pervasives_Native.tuple2)
                                                FStar_Pervasives_Native.tuple2
                                                Prims.list)
                                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DTypeVariant _0 -> _0 
let uu___is_StdCall : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1225 -> false
  
let uu___is_CDecl : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1231 -> false
  
let uu___is_FastCall : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1237 -> false
  
let uu___is_Private : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1243 -> false
  
let uu___is_WipeBody : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1249 -> false
  
let uu___is_CInline : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1255 -> false
  
let uu___is_Substitute : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1261 -> false
  
let uu___is_GCType : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1267 -> false
  
let uu___is_Comment : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1274 -> false
  
let __proj__Comment__item___0 : flag -> Prims.string =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let uu___is_MustDisappear : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1287 -> false
  
let uu___is_Const : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1294 -> false
  
let __proj__Const__item___0 : flag -> Prims.string =
  fun projectee  -> match projectee with | Const _0 -> _0 
let uu___is_Prologue : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1308 -> false
  
let __proj__Prologue__item___0 : flag -> Prims.string =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let uu___is_Epilogue : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1322 -> false
  
let __proj__Epilogue__item___0 : flag -> Prims.string =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let uu___is_Eternal : lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1335 -> false
  
let uu___is_Stack : lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1341 -> false
  
let uu___is_ManuallyManaged : lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1347 -> false
  
let uu___is_EBound : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1354 -> false
  
let __proj__EBound__item___0 : expr -> Prims.int =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let uu___is_EQualified : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1374 -> false
  
let __proj__EQualified__item___0 :
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EQualified _0 -> _0 
let uu___is_EConstant : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1410 -> false
  
let __proj__EConstant__item___0 :
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let uu___is_EUnit : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1435 -> false
  
let uu___is_EApp : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1448 -> false
  
let __proj__EApp__item___0 :
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let uu___is_ETypApp : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1486 -> false
  
let __proj__ETypApp__item___0 :
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let uu___is_ELet : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1524 -> false
  
let __proj__ELet__item___0 :
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let uu___is_EIfThenElse : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1562 -> false
  
let __proj__EIfThenElse__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let uu___is_ESequence : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1596 -> false
  
let __proj__ESequence__item___0 : expr -> expr Prims.list =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let uu___is_EAssign : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1620 -> false
  
let __proj__EAssign__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let uu___is_EBufCreate : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____1652 -> false
  
let __proj__EBufCreate__item___0 :
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let uu___is_EBufRead : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____1688 -> false
  
let __proj__EBufRead__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let uu___is_EBufWrite : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____1720 -> false
  
let __proj__EBufWrite__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let uu___is_EBufSub : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____1756 -> false
  
let __proj__EBufSub__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let uu___is_EBufBlit : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____1792 -> false
  
let __proj__EBufBlit__item___0 :
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5 =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let uu___is_EMatch : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____1846 -> false
  
let __proj__EMatch__item___0 :
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let uu___is_EOp : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1894 -> false
  
let __proj__EOp__item___0 : expr -> (op,width) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EOp _0 -> _0 
let uu___is_ECast : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1924 -> false
  
let __proj__ECast__item___0 :
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let uu___is_EPushFrame : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1949 -> false
  
let uu___is_EPopFrame : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1955 -> false
  
let uu___is_EBool : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1962 -> false
  
let __proj__EBool__item___0 : expr -> Prims.bool =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let uu___is_EAny : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1975 -> false
  
let uu___is_EAbort : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1981 -> false
  
let uu___is_EReturn : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1988 -> false
  
let __proj__EReturn__item___0 : expr -> expr =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let uu___is_EFlat : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____2012 -> false
  
let __proj__EFlat__item___0 :
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EFlat _0 -> _0 
let uu___is_EField : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____2062 -> false
  
let __proj__EField__item___0 :
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EField _0 -> _0 
let uu___is_EWhile : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____2098 -> false
  
let __proj__EWhile__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let uu___is_EBufCreateL : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____2130 -> false
  
let __proj__EBufCreateL__item___0 :
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let uu___is_ETuple : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2164 -> false
  
let __proj__ETuple__item___0 : expr -> expr Prims.list =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let uu___is_ECons : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2192 -> false
  
let __proj__ECons__item___0 :
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let uu___is_EBufFill : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2236 -> false
  
let __proj__EBufFill__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let uu___is_EString : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2268 -> false
  
let __proj__EString__item___0 : expr -> Prims.string =
  fun projectee  -> match projectee with | EString _0 -> _0 
let uu___is_EFun : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2290 -> false
  
let __proj__EFun__item___0 :
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let uu___is_EAbortS : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2328 -> false
  
let __proj__EAbortS__item___0 : expr -> Prims.string =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let uu___is_EBufFree : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____2342 -> false
  
let __proj__EBufFree__item___0 : expr -> expr =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let uu___is_Add : op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____2355 -> false 
let uu___is_AddW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2361 -> false
  
let uu___is_Sub : op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____2367 -> false 
let uu___is_SubW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2373 -> false
  
let uu___is_Div : op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____2379 -> false 
let uu___is_DivW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2385 -> false
  
let uu___is_Mult : op -> Prims.bool =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2391 -> false
  
let uu___is_MultW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2397 -> false
  
let uu___is_Mod : op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____2403 -> false 
let uu___is_BOr : op -> Prims.bool =
  fun projectee  -> match projectee with | BOr  -> true | uu____2409 -> false 
let uu___is_BAnd : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2415 -> false
  
let uu___is_BXor : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2421 -> false
  
let uu___is_BShiftL : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2427 -> false
  
let uu___is_BShiftR : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2433 -> false
  
let uu___is_BNot : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2439 -> false
  
let uu___is_Eq : op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2445 -> false 
let uu___is_Neq : op -> Prims.bool =
  fun projectee  -> match projectee with | Neq  -> true | uu____2451 -> false 
let uu___is_Lt : op -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2457 -> false 
let uu___is_Lte : op -> Prims.bool =
  fun projectee  -> match projectee with | Lte  -> true | uu____2463 -> false 
let uu___is_Gt : op -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2469 -> false 
let uu___is_Gte : op -> Prims.bool =
  fun projectee  -> match projectee with | Gte  -> true | uu____2475 -> false 
let uu___is_And : op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____2481 -> false 
let uu___is_Or : op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____2487 -> false 
let uu___is_Xor : op -> Prims.bool =
  fun projectee  -> match projectee with | Xor  -> true | uu____2493 -> false 
let uu___is_Not : op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____2499 -> false 
let uu___is_PUnit : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2505 -> false
  
let uu___is_PBool : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2512 -> false
  
let __proj__PBool__item___0 : pattern -> Prims.bool =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let uu___is_PVar : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2526 -> false
  
let __proj__PVar__item___0 : pattern -> binder =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let uu___is_PCons : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2546 -> false
  
let __proj__PCons__item___0 :
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PCons _0 -> _0 
let uu___is_PTuple : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2580 -> false
  
let __proj__PTuple__item___0 : pattern -> pattern Prims.list =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let uu___is_PRecord : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2606 -> false
  
let __proj__PRecord__item___0 :
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list
  = fun projectee  -> match projectee with | PRecord _0 -> _0 
let uu___is_PConstant : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____2642 -> false
  
let __proj__PConstant__item___0 :
  pattern -> (width,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let uu___is_UInt8 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____2667 -> false
  
let uu___is_UInt16 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2673 -> false
  
let uu___is_UInt32 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2679 -> false
  
let uu___is_UInt64 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2685 -> false
  
let uu___is_Int8 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2691 -> false
  
let uu___is_Int16 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2697 -> false
  
let uu___is_Int32 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2703 -> false
  
let uu___is_Int64 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2709 -> false
  
let uu___is_Bool : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2715 -> false
  
let uu___is_CInt : width -> Prims.bool =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____2721 -> false
  
let __proj__Mkbinder__item__name : binder -> Prims.string =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ;_} -> __fname__name
  
let __proj__Mkbinder__item__typ : binder -> typ =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ;_} -> __fname__typ
  
let uu___is_TInt : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____2742 -> false
  
let __proj__TInt__item___0 : typ -> width =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let uu___is_TBuf : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2756 -> false
  
let __proj__TBuf__item___0 : typ -> typ =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let uu___is_TUnit : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2769 -> false
  
let uu___is_TQualified : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2782 -> false
  
let __proj__TQualified__item___0 :
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TQualified _0 -> _0 
let uu___is_TBool : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2813 -> false
  
let uu___is_TAny : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2819 -> false
  
let uu___is_TArrow : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2830 -> false
  
let __proj__TArrow__item___0 :
  typ -> (typ,typ) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let uu___is_TBound : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2856 -> false
  
let __proj__TBound__item___0 : typ -> Prims.int =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let uu___is_TApp : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2882 -> false
  
let __proj__TApp__item___0 :
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TApp _0 -> _0 
let uu___is_TTuple : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____2934 -> false
  
let __proj__TTuple__item___0 : typ -> typ Prims.list =
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
let current_version : version = (Prims.lift_native_int (27)) 
type file = (Prims.string,program) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
type binary_format = (version,file Prims.list) FStar_Pervasives_Native.tuple2
[@@deriving show]
let fst3 :
  'Auu____3014 'Auu____3015 'Auu____3016 .
    ('Auu____3014,'Auu____3015,'Auu____3016) FStar_Pervasives_Native.tuple3
      -> 'Auu____3014
  = fun uu____3027  -> match uu____3027 with | (x,uu____3035,uu____3036) -> x 
let snd3 :
  'Auu____3045 'Auu____3046 'Auu____3047 .
    ('Auu____3045,'Auu____3046,'Auu____3047) FStar_Pervasives_Native.tuple3
      -> 'Auu____3046
  = fun uu____3058  -> match uu____3058 with | (uu____3065,x,uu____3067) -> x 
let thd3 :
  'Auu____3076 'Auu____3077 'Auu____3078 .
    ('Auu____3076,'Auu____3077,'Auu____3078) FStar_Pervasives_Native.tuple3
      -> 'Auu____3078
  = fun uu____3089  -> match uu____3089 with | (uu____3096,uu____3097,x) -> x 
let mk_width : Prims.string -> width FStar_Pervasives_Native.option =
  fun uu___35_3105  ->
    match uu___35_3105 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____3108 -> FStar_Pervasives_Native.None
  
let mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___36_3115  ->
    match uu___36_3115 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____3118 -> FStar_Pervasives_Native.None
  
let is_bool_op : Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let mk_op : Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___37_3132  ->
    match uu___37_3132 with
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
    | uu____3135 -> FStar_Pervasives_Native.None
  
let is_op : Prims.string -> Prims.bool =
  fun op  -> (mk_op op) <> FStar_Pervasives_Native.None 
let is_machine_int : Prims.string -> Prims.bool =
  fun m  -> (mk_width m) <> FStar_Pervasives_Native.None 
type env =
  {
  names: name Prims.list ;
  names_t: Prims.string Prims.list ;
  module_name: Prims.string Prims.list }[@@deriving show]
and name = {
  pretty: Prims.string }[@@deriving show]
let __proj__Mkenv__item__names : env -> name Prims.list =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__names
  
let __proj__Mkenv__item__names_t : env -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__names_t
  
let __proj__Mkenv__item__module_name : env -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__module_name
  
let __proj__Mkname__item__pretty : name -> Prims.string =
  fun projectee  ->
    match projectee with | { pretty = __fname__pretty;_} -> __fname__pretty
  
let empty : Prims.string Prims.list -> env =
  fun module_name  -> { names = []; names_t = []; module_name } 
let extend : env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___42_3255 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___42_3255.names_t);
        module_name = (uu___42_3255.module_name)
      }
  
let extend_t : env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___43_3266 = env  in
      {
        names = (uu___43_3266.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___43_3266.module_name)
      }
  
let find_name : env -> Prims.string -> name =
  fun env  ->
    fun x  ->
      let uu____3277 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____3277 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let find : env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____3301 ->
          let uu____3302 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____3302
  
let find_t : env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____3321 ->
          let uu____3322 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____3322
  
let add_binders :
  'Auu____3329 .
    env ->
      (Prims.string,'Auu____3329) FStar_Pervasives_Native.tuple2 Prims.list
        -> env
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____3361  ->
             match uu____3361 with | (name,uu____3367) -> extend env1 name)
        env binders
  
let rec translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____3572  ->
    match uu____3572 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3620 = m  in
               match uu____3620 with
               | (path,uu____3634,uu____3635) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____3657 = translate_module m  in
                FStar_Pervasives_Native.Some uu____3657)
             with
             | e ->
                 ((let uu____3666 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3666);
                  FStar_Pervasives_Native.None)) modules

and translate_module :
  (FStar_Extraction_ML_Syntax.mlpath,(FStar_Extraction_ML_Syntax.mlsig,
                                       FStar_Extraction_ML_Syntax.mlmodule)
                                       FStar_Pervasives_Native.tuple2
                                       FStar_Pervasives_Native.option,
    FStar_Extraction_ML_Syntax.mllib) FStar_Pervasives_Native.tuple3 -> 
    file
  =
  fun uu____3667  ->
    match uu____3667 with
    | (module_name,modul,uu____3682) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____3713 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list =
  fun flags1  ->
    FStar_List.choose
      (fun uu___38_3728  ->
         match uu___38_3728 with
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
         | FStar_Extraction_ML_Syntax.StackInline  ->
             FStar_Pervasives_Native.Some MustDisappear
         | FStar_Extraction_ML_Syntax.CConst s ->
             FStar_Pervasives_Native.Some (Const s)
         | FStar_Extraction_ML_Syntax.CPrologue s ->
             FStar_Pervasives_Native.Some (Prologue s)
         | FStar_Extraction_ML_Syntax.CEpilogue s ->
             FStar_Pervasives_Native.Some (Epilogue s)
         | uu____3735 -> FStar_Pervasives_Native.None) flags1

and translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3746 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3748 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____3752) ->
          (FStar_Util.print1_warning
             "Skipping the translation of exception: %s\n" m;
           [])

and translate_let :
  env ->
    FStar_Extraction_ML_Syntax.mlletflavor ->
      FStar_Extraction_ML_Syntax.mllb -> decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun flavor  ->
      fun lb  ->
        match lb with
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3774;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____3777;
                FStar_Extraction_ML_Syntax.loc = uu____3778;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3780;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___39_3802  ->
                      match uu___39_3802 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____3803 -> false) meta
                  in
               let env1 =
                 if flavor = FStar_Extraction_ML_Syntax.Rec
                 then extend env name
                 else env  in
               let env2 =
                 FStar_List.fold_left
                   (fun env2  -> fun name1  -> extend_t env2 name1) env1
                   tvars
                  in
               let rec find_return_type eff i uu___40_3830 =
                 match uu___40_3830 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3835,eff1,t)
                     when i > (Prims.lift_native_int (0)) ->
                     find_return_type eff1 (i - (Prims.lift_native_int (1)))
                       t
                 | t -> (eff, t)  in
               let uu____3839 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____3839 with
               | (eff,t) ->
                   let t1 = translate_type env2 t  in
                   let binders = translate_binders env2 args  in
                   let env3 = add_binders env2 args  in
                   let name1 = ((env3.module_name), name)  in
                   let meta1 =
                     match (eff, t1) with
                     | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____3871) ->
                         let uu____3872 = translate_flags meta  in
                         MustDisappear :: uu____3872
                     | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                         let uu____3875 = translate_flags meta  in
                         MustDisappear :: uu____3875
                     | uu____3878 -> translate_flags meta  in
                   if assumed
                   then
                     (if
                        (FStar_List.length tvars) =
                          (Prims.lift_native_int (0))
                      then
                        let uu____3887 =
                          let uu____3888 =
                            let uu____3907 = translate_type env3 t0  in
                            (FStar_Pervasives_Native.None, meta1, name1,
                              uu____3907)
                             in
                          DExternal uu____3888  in
                        FStar_Pervasives_Native.Some uu____3887
                      else
                        ((let uu____3920 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1
                             in
                          FStar_Util.print1_warning
                            "No writing anything for %s (polymorphic assume)\n"
                            uu____3920);
                         FStar_Pervasives_Native.None))
                   else
                     (try
                        let body1 = translate_expr env3 body  in
                        FStar_Pervasives_Native.Some
                          (DFunction
                             (FStar_Pervasives_Native.None, meta1,
                               (FStar_List.length tvars), t1, name1, binders,
                               body1))
                      with
                      | e ->
                          let msg = FStar_Util.print_exn e  in
                          ((let uu____3953 =
                              let uu____3958 =
                                let uu____3959 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1
                                   in
                                FStar_Util.format2
                                  "Writing a stub for %s (%s)\n" uu____3959
                                  msg
                                 in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____3958)
                               in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____3953);
                           (let msg1 =
                              Prims.strcat
                                "This function was not extracted:\n" msg
                               in
                            FStar_Pervasives_Native.Some
                              (DFunction
                                 (FStar_Pervasives_Native.None, meta1,
                                   (FStar_List.length tvars), t1, name1,
                                   binders, (EAbortS msg1)))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3976;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Coerce
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____3979;
                     FStar_Extraction_ML_Syntax.loc = uu____3980;_},uu____3981,uu____3982);
                FStar_Extraction_ML_Syntax.mlty = uu____3983;
                FStar_Extraction_ML_Syntax.loc = uu____3984;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3986;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___39_4008  ->
                      match uu___39_4008 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____4009 -> false) meta
                  in
               let env1 =
                 if flavor = FStar_Extraction_ML_Syntax.Rec
                 then extend env name
                 else env  in
               let env2 =
                 FStar_List.fold_left
                   (fun env2  -> fun name1  -> extend_t env2 name1) env1
                   tvars
                  in
               let rec find_return_type eff i uu___40_4036 =
                 match uu___40_4036 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____4041,eff1,t)
                     when i > (Prims.lift_native_int (0)) ->
                     find_return_type eff1 (i - (Prims.lift_native_int (1)))
                       t
                 | t -> (eff, t)  in
               let uu____4045 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____4045 with
               | (eff,t) ->
                   let t1 = translate_type env2 t  in
                   let binders = translate_binders env2 args  in
                   let env3 = add_binders env2 args  in
                   let name1 = ((env3.module_name), name)  in
                   let meta1 =
                     match (eff, t1) with
                     | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____4077) ->
                         let uu____4078 = translate_flags meta  in
                         MustDisappear :: uu____4078
                     | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                         let uu____4081 = translate_flags meta  in
                         MustDisappear :: uu____4081
                     | uu____4084 -> translate_flags meta  in
                   if assumed
                   then
                     (if
                        (FStar_List.length tvars) =
                          (Prims.lift_native_int (0))
                      then
                        let uu____4093 =
                          let uu____4094 =
                            let uu____4113 = translate_type env3 t0  in
                            (FStar_Pervasives_Native.None, meta1, name1,
                              uu____4113)
                             in
                          DExternal uu____4094  in
                        FStar_Pervasives_Native.Some uu____4093
                      else
                        ((let uu____4126 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1
                             in
                          FStar_Util.print1_warning
                            "No writing anything for %s (polymorphic assume)\n"
                            uu____4126);
                         FStar_Pervasives_Native.None))
                   else
                     (try
                        let body1 = translate_expr env3 body  in
                        FStar_Pervasives_Native.Some
                          (DFunction
                             (FStar_Pervasives_Native.None, meta1,
                               (FStar_List.length tvars), t1, name1, binders,
                               body1))
                      with
                      | e ->
                          let msg = FStar_Util.print_exn e  in
                          ((let uu____4159 =
                              let uu____4164 =
                                let uu____4165 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1
                                   in
                                FStar_Util.format2
                                  "Writing a stub for %s (%s)\n" uu____4165
                                  msg
                                 in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____4164)
                               in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____4159);
                           (let msg1 =
                              Prims.strcat
                                "This function was not extracted:\n" msg
                               in
                            FStar_Pervasives_Native.Some
                              (DFunction
                                 (FStar_Pervasives_Native.None, meta1,
                                   (FStar_List.length tvars), t1, name1,
                                   binders, (EAbortS msg1)))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4182;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4185;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let meta1 = translate_flags meta  in
               let env1 =
                 FStar_List.fold_left
                   (fun env1  -> fun name1  -> extend_t env1 name1) env tvars
                  in
               let t1 = translate_type env1 t  in
               let name1 = ((env1.module_name), name)  in
               try
                 let expr1 = translate_expr env1 expr  in
                 FStar_Pervasives_Native.Some
                   (DGlobal
                      (meta1, name1, (FStar_List.length tvars), t1, expr1))
               with
               | e ->
                   ((let uu____4235 =
                       let uu____4240 =
                         let uu____4241 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____4242 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Not translating definition for %s (%s)\n"
                           uu____4241 uu____4242
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____4240)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____4235);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4253;
            FStar_Extraction_ML_Syntax.mllb_def = uu____4254;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____4255;
            FStar_Extraction_ML_Syntax.print_typ = uu____4256;_} ->
            ((let uu____4260 =
                let uu____4265 =
                  FStar_Util.format1 "Not translating definition for %s\n"
                    name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____4265)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____4260);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____4273 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____4273
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ty  ->
      match ty with
      | (assumed,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Abbrev t)) ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args
             in
          if assumed
          then
            let name2 = FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
            (FStar_Util.print1_warning
               "Not translating type definition (assumed) for %s\n" name2;
             FStar_Pervasives_Native.None)
          else
            (let uu____4311 =
               let uu____4312 =
                 let uu____4329 = translate_flags flags1  in
                 let uu____4332 = translate_type env1 t  in
                 (name1, uu____4329, (FStar_List.length args), uu____4332)
                  in
               DTypeAlias uu____4312  in
             FStar_Pervasives_Native.Some uu____4311)
      | (uu____4341,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args
             in
          let uu____4373 =
            let uu____4374 =
              let uu____4401 = translate_flags flags1  in
              let uu____4404 =
                FStar_List.map
                  (fun uu____4431  ->
                     match uu____4431 with
                     | (f,t) ->
                         let uu____4446 =
                           let uu____4451 = translate_type env1 t  in
                           (uu____4451, false)  in
                         (f, uu____4446)) fields
                 in
              (name1, uu____4401, (FStar_List.length args), uu____4404)  in
            DTypeFlat uu____4374  in
          FStar_Pervasives_Native.Some uu____4373
      | (uu____4474,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
          let name1 = ((env.module_name), name)  in
          let flags2 = translate_flags flags1  in
          let env1 = FStar_List.fold_left extend_t env args  in
          let uu____4511 =
            let uu____4512 =
              let uu____4545 =
                FStar_List.map
                  (fun uu____4590  ->
                     match uu____4590 with
                     | (cons1,ts) ->
                         let uu____4629 =
                           FStar_List.map
                             (fun uu____4656  ->
                                match uu____4656 with
                                | (name2,t) ->
                                    let uu____4671 =
                                      let uu____4676 = translate_type env1 t
                                         in
                                      (uu____4676, false)  in
                                    (name2, uu____4671)) ts
                            in
                         (cons1, uu____4629)) branches
                 in
              (name1, flags2, (FStar_List.length args), uu____4545)  in
            DTypeVariant uu____4512  in
          FStar_Pervasives_Native.Some uu____4511
      | (uu____4715,name,_mangled_name,uu____4718,uu____4719,uu____4720) ->
          ((let uu____4730 =
              let uu____4735 =
                FStar_Util.format1 "Not translating type definition for %s\n"
                  name
                 in
              (FStar_Errors.Warning_DefinitionNotTranslated, uu____4735)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____4730);
           FStar_Pervasives_Native.None)

and translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4739 = find_t env name  in TBound uu____4739
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4741,t2) ->
          let uu____4743 =
            let uu____4748 = translate_type env t1  in
            let uu____4749 = translate_type env t2  in
            (uu____4748, uu____4749)  in
          TArrow uu____4743
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4753 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4753 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4757 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4757 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4769 = FStar_Util.must (mk_width m)  in TInt uu____4769
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4781 = FStar_Util.must (mk_width m)  in TInt uu____4781
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4786 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4786 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____4787::arg::uu____4789::[],p) when
          (((let uu____4795 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4795 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____4797 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4797 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____4799 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4799 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____4801 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4801 = "FStar.HyperStack.ST.s_mref")
          -> let uu____4802 = translate_type env arg  in TBuf uu____4802
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____4804::[],p) when
          ((((((((((let uu____4810 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4810 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____4812 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4812 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____4814 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4814 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____4816 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4816 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____4818 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4818 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____4820 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4820 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____4822 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4822 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____4824 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4824 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____4826 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4826 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____4828 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4828 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____4830 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4830 = "FStar.HyperStack.ST.mmmref")
          -> let uu____4831 = translate_type env arg  in TBuf uu____4831
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          ((((((((((let uu____4838 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4838 = "FStar.Buffer.buffer") ||
                     (let uu____4840 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4840 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____4842 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4842 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____4844 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4844 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____4846 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4846 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____4848 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4848 = "FStar.HyperStack.mmref"))
                ||
                (let uu____4850 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4850 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____4852 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4852 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____4854 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4854 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____4856 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4856 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____4858 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4858 = "FStar.HyperStack.ST.mmref")
          -> let uu____4859 = translate_type env arg  in TBuf uu____4859
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4860::arg::[],p) when
          (let uu____4867 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4867 = "FStar.HyperStack.s_ref") ||
            (let uu____4869 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4869 = "FStar.HyperStack.ST.s_ref")
          -> let uu____4870 = translate_type env arg  in TBuf uu____4870
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4871::[],p) when
          let uu____4875 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4875 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4913 = FStar_List.map (translate_type env) args  in
          TTuple uu____4913
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.lift_native_int (0))
          then
            let uu____4922 =
              let uu____4935 = FStar_List.map (translate_type env) args  in
              (lid, uu____4935)  in
            TApp uu____4922
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4944 = FStar_List.map (translate_type env) ts  in
          TTuple uu____4944

and translate_binders :
  env ->
    (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2 Prims.list -> binder Prims.list
  = fun env  -> fun args  -> FStar_List.map (translate_binder env) args

and translate_binder :
  env ->
    (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2 -> binder
  =
  fun env  ->
    fun uu____4960  ->
      match uu____4960 with
      | (name,typ) ->
          let uu____4967 = translate_type env typ  in
          { name; typ = uu____4967 }

and translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____4972 = find env name  in EBound uu____4972
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4977 =
            let uu____4982 = FStar_Util.must (mk_op op)  in
            let uu____4983 = FStar_Util.must (mk_width m)  in
            (uu____4982, uu____4983)  in
          EOp uu____4977
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4987 =
            let uu____4992 = FStar_Util.must (mk_bool_op op)  in
            (uu____4992, Bool)  in
          EOp uu____4987
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,{ FStar_Extraction_ML_Syntax.mllb_name = name;
                     FStar_Extraction_ML_Syntax.mllb_tysc =
                       FStar_Pervasives_Native.Some ([],typ);
                     FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit;
                     FStar_Extraction_ML_Syntax.mllb_def = body;
                     FStar_Extraction_ML_Syntax.mllb_meta = flags1;
                     FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let binder =
            let uu____5019 = translate_type env typ  in
            { name; typ = uu____5019 }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____5045 =
            let uu____5056 = translate_expr env expr  in
            let uu____5057 = translate_branches env branches  in
            (uu____5056, uu____5057)  in
          EMatch uu____5045
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5071;
                  FStar_Extraction_ML_Syntax.loc = uu____5072;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____5074;
             FStar_Extraction_ML_Syntax.loc = uu____5075;_},arg::[])
          when
          let uu____5081 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5081 = "FStar.Dyn.undyn" ->
          let uu____5082 =
            let uu____5087 = translate_expr env arg  in
            let uu____5088 = translate_type env t  in
            (uu____5087, uu____5088)  in
          ECast uu____5082
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
             FStar_Extraction_ML_Syntax.loc = uu____5094;_},uu____5095)
          when
          let uu____5104 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5104 = "Prims.admit" -> EAbort
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
             FStar_Extraction_ML_Syntax.loc = uu____5110;_},arg::[])
          when
          ((let uu____5120 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5120 = "FStar.HyperStack.All.failwith") ||
             (let uu____5122 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5122 = "FStar.Error.unexpected"))
            ||
            (let uu____5124 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5124 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____5126;
               FStar_Extraction_ML_Syntax.loc = uu____5127;_} -> EAbortS msg
           | uu____5128 ->
               let print7 =
                 let uu____5130 =
                   let uu____5131 =
                     let uu____5132 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____5132
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____5131  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____5130
                  in
               let print8 =
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top
                   (FStar_Extraction_ML_Syntax.MLE_App (print7, [arg]))
                  in
               let t = translate_expr env print8  in ESequence [t; EAbort])
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5138;
                  FStar_Extraction_ML_Syntax.loc = uu____5139;_},uu____5140);
             FStar_Extraction_ML_Syntax.mlty = uu____5141;
             FStar_Extraction_ML_Syntax.loc = uu____5142;_},e1::e2::[])
          when
          (let uu____5153 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5153 = "FStar.Buffer.index") ||
            (let uu____5155 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5155 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____5156 =
            let uu____5161 = translate_expr env e1  in
            let uu____5162 = translate_expr env e2  in
            (uu____5161, uu____5162)  in
          EBufRead uu____5156
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5164;
                  FStar_Extraction_ML_Syntax.loc = uu____5165;_},uu____5166);
             FStar_Extraction_ML_Syntax.mlty = uu____5167;
             FStar_Extraction_ML_Syntax.loc = uu____5168;_},e1::[])
          when
          let uu____5176 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5176 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____5177 =
            let uu____5182 = translate_expr env e1  in
            (uu____5182, (EConstant (UInt32, "0")))  in
          EBufRead uu____5177
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5184;
                  FStar_Extraction_ML_Syntax.loc = uu____5185;_},uu____5186);
             FStar_Extraction_ML_Syntax.mlty = uu____5187;
             FStar_Extraction_ML_Syntax.loc = uu____5188;_},e1::e2::[])
          when
          let uu____5197 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5197 = "FStar.Buffer.create" ->
          let uu____5198 =
            let uu____5205 = translate_expr env e1  in
            let uu____5206 = translate_expr env e2  in
            (Stack, uu____5205, uu____5206)  in
          EBufCreate uu____5198
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5208;
                  FStar_Extraction_ML_Syntax.loc = uu____5209;_},uu____5210);
             FStar_Extraction_ML_Syntax.mlty = uu____5211;
             FStar_Extraction_ML_Syntax.loc = uu____5212;_},init1::[])
          when
          let uu____5220 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5220 = "FStar.HyperStack.ST.salloc" ->
          let uu____5221 =
            let uu____5228 = translate_expr env init1  in
            (Stack, uu____5228, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5221
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5230;
                  FStar_Extraction_ML_Syntax.loc = uu____5231;_},uu____5232);
             FStar_Extraction_ML_Syntax.mlty = uu____5233;
             FStar_Extraction_ML_Syntax.loc = uu____5234;_},e2::[])
          when
          let uu____5242 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5242 = "FStar.Buffer.createL" ->
          let rec list_elements acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____5284 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a list literal!"
             in
          let list_elements1 = list_elements []  in
          let uu____5294 =
            let uu____5301 =
              let uu____5304 = list_elements1 e2  in
              FStar_List.map (translate_expr env) uu____5304  in
            (Stack, uu____5301)  in
          EBufCreateL uu____5294
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5310;
                  FStar_Extraction_ML_Syntax.loc = uu____5311;_},uu____5312);
             FStar_Extraction_ML_Syntax.mlty = uu____5313;
             FStar_Extraction_ML_Syntax.loc = uu____5314;_},_rid::init1::[])
          when
          let uu____5323 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5323 = "FStar.HyperStack.ST.ralloc" ->
          let uu____5324 =
            let uu____5331 = translate_expr env init1  in
            (Eternal, uu____5331, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5324
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5333;
                  FStar_Extraction_ML_Syntax.loc = uu____5334;_},uu____5335);
             FStar_Extraction_ML_Syntax.mlty = uu____5336;
             FStar_Extraction_ML_Syntax.loc = uu____5337;_},_e0::e1::e2::[])
          when
          let uu____5347 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5347 = "FStar.Buffer.rcreate" ->
          let uu____5348 =
            let uu____5355 = translate_expr env e1  in
            let uu____5356 = translate_expr env e2  in
            (Eternal, uu____5355, uu____5356)  in
          EBufCreate uu____5348
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5358;
                  FStar_Extraction_ML_Syntax.loc = uu____5359;_},uu____5360);
             FStar_Extraction_ML_Syntax.mlty = uu____5361;
             FStar_Extraction_ML_Syntax.loc = uu____5362;_},_rid::init1::[])
          when
          let uu____5371 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5371 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____5372 =
            let uu____5379 = translate_expr env init1  in
            (ManuallyManaged, uu____5379, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5372
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5381;
                  FStar_Extraction_ML_Syntax.loc = uu____5382;_},uu____5383);
             FStar_Extraction_ML_Syntax.mlty = uu____5384;
             FStar_Extraction_ML_Syntax.loc = uu____5385;_},_e0::e1::e2::[])
          when
          let uu____5395 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5395 = "FStar.Buffer.rcreate_mm" ->
          let uu____5396 =
            let uu____5403 = translate_expr env e1  in
            let uu____5404 = translate_expr env e2  in
            (ManuallyManaged, uu____5403, uu____5404)  in
          EBufCreate uu____5396
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5406;
                  FStar_Extraction_ML_Syntax.loc = uu____5407;_},uu____5408);
             FStar_Extraction_ML_Syntax.mlty = uu____5409;
             FStar_Extraction_ML_Syntax.loc = uu____5410;_},e2::[])
          when
          let uu____5418 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5418 = "FStar.HyperStack.ST.rfree" ->
          let uu____5419 = translate_expr env e2  in EBufFree uu____5419
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5421;
                  FStar_Extraction_ML_Syntax.loc = uu____5422;_},uu____5423);
             FStar_Extraction_ML_Syntax.mlty = uu____5424;
             FStar_Extraction_ML_Syntax.loc = uu____5425;_},e2::[])
          when
          let uu____5433 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5433 = "FStar.Buffer.rfree" ->
          let uu____5434 = translate_expr env e2  in EBufFree uu____5434
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5436;
                  FStar_Extraction_ML_Syntax.loc = uu____5437;_},uu____5438);
             FStar_Extraction_ML_Syntax.mlty = uu____5439;
             FStar_Extraction_ML_Syntax.loc = uu____5440;_},e1::e2::_e3::[])
          when
          let uu____5450 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5450 = "FStar.Buffer.sub" ->
          let uu____5451 =
            let uu____5456 = translate_expr env e1  in
            let uu____5457 = translate_expr env e2  in
            (uu____5456, uu____5457)  in
          EBufSub uu____5451
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5459;
                  FStar_Extraction_ML_Syntax.loc = uu____5460;_},uu____5461);
             FStar_Extraction_ML_Syntax.mlty = uu____5462;
             FStar_Extraction_ML_Syntax.loc = uu____5463;_},e1::e2::[])
          when
          let uu____5472 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5472 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5474;
                  FStar_Extraction_ML_Syntax.loc = uu____5475;_},uu____5476);
             FStar_Extraction_ML_Syntax.mlty = uu____5477;
             FStar_Extraction_ML_Syntax.loc = uu____5478;_},e1::e2::[])
          when
          let uu____5487 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5487 = "FStar.Buffer.offset" ->
          let uu____5488 =
            let uu____5493 = translate_expr env e1  in
            let uu____5494 = translate_expr env e2  in
            (uu____5493, uu____5494)  in
          EBufSub uu____5488
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5496;
                  FStar_Extraction_ML_Syntax.loc = uu____5497;_},uu____5498);
             FStar_Extraction_ML_Syntax.mlty = uu____5499;
             FStar_Extraction_ML_Syntax.loc = uu____5500;_},e1::e2::e3::[])
          when
          (let uu____5512 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5512 = "FStar.Buffer.upd") ||
            (let uu____5514 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5514 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____5515 =
            let uu____5522 = translate_expr env e1  in
            let uu____5523 = translate_expr env e2  in
            let uu____5524 = translate_expr env e3  in
            (uu____5522, uu____5523, uu____5524)  in
          EBufWrite uu____5515
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5526;
                  FStar_Extraction_ML_Syntax.loc = uu____5527;_},uu____5528);
             FStar_Extraction_ML_Syntax.mlty = uu____5529;
             FStar_Extraction_ML_Syntax.loc = uu____5530;_},e1::e2::[])
          when
          let uu____5539 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5539 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5540 =
            let uu____5547 = translate_expr env e1  in
            let uu____5548 = translate_expr env e2  in
            (uu____5547, (EConstant (UInt32, "0")), uu____5548)  in
          EBufWrite uu____5540
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5550;
             FStar_Extraction_ML_Syntax.loc = uu____5551;_},uu____5552::[])
          when
          let uu____5555 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5555 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5557;
             FStar_Extraction_ML_Syntax.loc = uu____5558;_},uu____5559::[])
          when
          let uu____5562 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5562 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5564;
                  FStar_Extraction_ML_Syntax.loc = uu____5565;_},uu____5566);
             FStar_Extraction_ML_Syntax.mlty = uu____5567;
             FStar_Extraction_ML_Syntax.loc = uu____5568;_},e1::e2::e3::e4::e5::[])
          when
          let uu____5580 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5580 = "FStar.Buffer.blit" ->
          let uu____5581 =
            let uu____5592 = translate_expr env e1  in
            let uu____5593 = translate_expr env e2  in
            let uu____5594 = translate_expr env e3  in
            let uu____5595 = translate_expr env e4  in
            let uu____5596 = translate_expr env e5  in
            (uu____5592, uu____5593, uu____5594, uu____5595, uu____5596)  in
          EBufBlit uu____5581
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5598;
                  FStar_Extraction_ML_Syntax.loc = uu____5599;_},uu____5600);
             FStar_Extraction_ML_Syntax.mlty = uu____5601;
             FStar_Extraction_ML_Syntax.loc = uu____5602;_},e1::e2::e3::[])
          when
          let uu____5612 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5612 = "FStar.Buffer.fill" ->
          let uu____5613 =
            let uu____5620 = translate_expr env e1  in
            let uu____5621 = translate_expr env e2  in
            let uu____5622 = translate_expr env e3  in
            (uu____5620, uu____5621, uu____5622)  in
          EBufFill uu____5613
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5624;
             FStar_Extraction_ML_Syntax.loc = uu____5625;_},uu____5626::[])
          when
          let uu____5629 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5629 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5631;
             FStar_Extraction_ML_Syntax.loc = uu____5632;_},e1::[])
          when
          let uu____5636 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5636 = "Obj.repr" ->
          let uu____5637 =
            let uu____5642 = translate_expr env e1  in (uu____5642, TAny)  in
          ECast uu____5637
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5645;
             FStar_Extraction_ML_Syntax.loc = uu____5646;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5654 = FStar_Util.must (mk_width m)  in
          let uu____5655 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____5654 uu____5655 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5657;
             FStar_Extraction_ML_Syntax.loc = uu____5658;_},args)
          when is_bool_op op ->
          let uu____5666 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____5666 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5668;
             FStar_Extraction_ML_Syntax.loc = uu____5669;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5671;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5672;_}::[])
          when is_machine_int m ->
          let uu____5687 =
            let uu____5692 = FStar_Util.must (mk_width m)  in (uu____5692, c)
             in
          EConstant uu____5687
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5694;
             FStar_Extraction_ML_Syntax.loc = uu____5695;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5697;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5698;_}::[])
          when is_machine_int m ->
          let uu____5713 =
            let uu____5718 = FStar_Util.must (mk_width m)  in (uu____5718, c)
             in
          EConstant uu____5713
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5719;
             FStar_Extraction_ML_Syntax.loc = uu____5720;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5722;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5723;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5729 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5730;
             FStar_Extraction_ML_Syntax.loc = uu____5731;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5733;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5734;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5740 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5742;
             FStar_Extraction_ML_Syntax.loc = uu____5743;_},arg::[])
          ->
          let is_known_type =
            (((((((FStar_Util.starts_with c "uint8") ||
                    (FStar_Util.starts_with c "uint16"))
                   || (FStar_Util.starts_with c "uint32"))
                  || (FStar_Util.starts_with c "uint64"))
                 || (FStar_Util.starts_with c "int8"))
                || (FStar_Util.starts_with c "int16"))
               || (FStar_Util.starts_with c "int32"))
              || (FStar_Util.starts_with c "int64")
             in
          if (FStar_Util.ends_with c "uint64") && is_known_type
          then
            let uu____5750 =
              let uu____5755 = translate_expr env arg  in
              (uu____5755, (TInt UInt64))  in
            ECast uu____5750
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5757 =
                 let uu____5762 = translate_expr env arg  in
                 (uu____5762, (TInt UInt32))  in
               ECast uu____5757)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5764 =
                   let uu____5769 = translate_expr env arg  in
                   (uu____5769, (TInt UInt16))  in
                 ECast uu____5764)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5771 =
                     let uu____5776 = translate_expr env arg  in
                     (uu____5776, (TInt UInt8))  in
                   ECast uu____5771)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5778 =
                       let uu____5783 = translate_expr env arg  in
                       (uu____5783, (TInt Int64))  in
                     ECast uu____5778)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5785 =
                         let uu____5790 = translate_expr env arg  in
                         (uu____5790, (TInt Int32))  in
                       ECast uu____5785)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5792 =
                           let uu____5797 = translate_expr env arg  in
                           (uu____5797, (TInt Int16))  in
                         ECast uu____5792)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5799 =
                             let uu____5804 = translate_expr env arg  in
                             (uu____5804, (TInt Int8))  in
                           ECast uu____5799)
                        else
                          (let uu____5806 =
                             let uu____5813 =
                               let uu____5816 = translate_expr env arg  in
                               [uu____5816]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5813)
                              in
                           EApp uu____5806)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5827 =
            let uu____5834 = translate_expr env head1  in
            let uu____5835 = FStar_List.map (translate_expr env) args  in
            (uu____5834, uu____5835)  in
          EApp uu____5827
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5846 =
            let uu____5853 = translate_expr env head1  in
            let uu____5854 = FStar_List.map (translate_type env) ty_args  in
            (uu____5853, uu____5854)  in
          ETypApp uu____5846
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5862 =
            let uu____5867 = translate_expr env e1  in
            let uu____5868 = translate_type env t_to  in
            (uu____5867, uu____5868)  in
          ECast uu____5862
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5869,fields) ->
          let uu____5887 =
            let uu____5898 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5899 =
              FStar_List.map
                (fun uu____5918  ->
                   match uu____5918 with
                   | (field,expr) ->
                       let uu____5929 = translate_expr env expr  in
                       (field, uu____5929)) fields
               in
            (uu____5898, uu____5899)  in
          EFlat uu____5887
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5938 =
            let uu____5945 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____5946 = translate_expr env e1  in
            (uu____5945, uu____5946, (FStar_Pervasives_Native.snd path))  in
          EField uu____5938
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5949 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5961) ->
          let uu____5966 =
            let uu____5967 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5967
             in
          failwith uu____5966
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5973 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____5973
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5979 = FStar_List.map (translate_expr env) es  in
          ETuple uu____5979
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5982,cons1),es) ->
          let uu____5999 =
            let uu____6008 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____6009 = FStar_List.map (translate_expr env) es  in
            (uu____6008, cons1, uu____6009)  in
          ECons uu____5999
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____6032 =
            let uu____6041 = translate_expr env1 body  in
            let uu____6042 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____6041, uu____6042)  in
          EFun uu____6032
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____6052 =
            let uu____6059 = translate_expr env e1  in
            let uu____6060 = translate_expr env e2  in
            let uu____6061 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____6059, uu____6060, uu____6061)  in
          EIfThenElse uu____6052
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____6063 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____6070 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____6085 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.lift_native_int (0))
          then
            let uu____6100 =
              let uu____6113 = FStar_List.map (translate_type env) ts  in
              (lid, uu____6113)  in
            TApp uu____6100
          else TQualified lid
      | uu____6119 -> failwith "invalid argument: assert_lid"

and translate_branches :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern,FStar_Extraction_ML_Syntax.mlexpr
                                            FStar_Pervasives_Native.option,
      FStar_Extraction_ML_Syntax.mlexpr) FStar_Pervasives_Native.tuple3
      Prims.list -> (pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  -> fun branches  -> FStar_List.map (translate_branch env) branches

and translate_branch :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern,FStar_Extraction_ML_Syntax.mlexpr
                                            FStar_Pervasives_Native.option,
      FStar_Extraction_ML_Syntax.mlexpr) FStar_Pervasives_Native.tuple3 ->
      (pattern,expr) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____6145  ->
      match uu____6145 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____6171 = translate_pat env pat  in
            (match uu____6171 with
             | (env1,pat1) ->
                 let uu____6182 = translate_expr env1 expr  in
                 (pat1, uu____6182))
          else failwith "todo: translate_branch"

and translate_width :
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width
  =
  fun uu___41_6188  ->
    match uu___41_6188 with
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

and translate_pat :
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
          let uu____6252 =
            let uu____6253 =
              let uu____6258 = translate_width sw  in (uu____6258, s)  in
            PConstant uu____6253  in
          (env, uu____6252)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in (env1, (PVar { name; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____6262,cons1),ps) ->
          let uu____6279 =
            FStar_List.fold_left
              (fun uu____6299  ->
                 fun p1  ->
                   match uu____6299 with
                   | (env1,acc) ->
                       let uu____6319 = translate_pat env1 p1  in
                       (match uu____6319 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6279 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____6348,ps) ->
          let uu____6366 =
            FStar_List.fold_left
              (fun uu____6400  ->
                 fun uu____6401  ->
                   match (uu____6400, uu____6401) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____6470 = translate_pat env1 p1  in
                       (match uu____6470 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____6366 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____6532 =
            FStar_List.fold_left
              (fun uu____6552  ->
                 fun p1  ->
                   match uu____6552 with
                   | (env1,acc) ->
                       let uu____6572 = translate_pat env1 p1  in
                       (match uu____6572 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6532 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6599 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6604 ->
          failwith "todo: translate_pat [MLP_Branch]"

and translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____6615 =
            let uu____6616 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____6616
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.lift_native_int (0)))))
             in
          if uu____6615
          then
            let uu____6628 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____6628
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6640) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6655 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6656 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        EConstant (CInt, s)

and mk_op_app :
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr
  =
  fun env  ->
    fun w  ->
      fun op  ->
        fun args  ->
          let uu____6676 =
            let uu____6683 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____6683)  in
          EApp uu____6676
