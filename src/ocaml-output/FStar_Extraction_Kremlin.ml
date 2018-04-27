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
let (uu___is_DGlobal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DGlobal _0 -> true | uu____616 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,Prims.int,typ,expr)
      FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____710 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr) FStar_Pervasives_Native.tuple7)
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____818 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,typ) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____906 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,(Prims.string,(typ,Prims.bool)
                                                FStar_Pervasives_Native.tuple2)
                                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____1016 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,(Prims.string
                                                          Prims.list,
                                                         Prims.string)
                                                         FStar_Pervasives_Native.tuple2,
      typ) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____1116 -> false
  
let (__proj__DTypeVariant__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,(Prims.string,(Prims.string,(typ,Prims.bool)
                                                              FStar_Pervasives_Native.tuple2)
                                                FStar_Pervasives_Native.tuple2
                                                Prims.list)
                                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DTypeVariant _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1225 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1231 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1237 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1243 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1249 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1255 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1261 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1267 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1274 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1287 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1294 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1308 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1322 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1335 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1341 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1347 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1354 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1374 -> false
  
let (__proj__EQualified__item___0 :
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1410 -> false
  
let (__proj__EConstant__item___0 :
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1435 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1448 -> false
  
let (__proj__EApp__item___0 :
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1486 -> false
  
let (__proj__ETypApp__item___0 :
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1524 -> false
  
let (__proj__ELet__item___0 :
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1562 -> false
  
let (__proj__EIfThenElse__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1596 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1620 -> false
  
let (__proj__EAssign__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____1652 -> false
  
let (__proj__EBufCreate__item___0 :
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____1688 -> false
  
let (__proj__EBufRead__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____1720 -> false
  
let (__proj__EBufWrite__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____1756 -> false
  
let (__proj__EBufSub__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____1792 -> false
  
let (__proj__EBufBlit__item___0 :
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5) =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____1846 -> false
  
let (__proj__EMatch__item___0 :
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1894 -> false
  
let (__proj__EOp__item___0 :
  expr -> (op,width) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1924 -> false
  
let (__proj__ECast__item___0 :
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1949 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1955 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1962 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1975 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1981 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1988 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____2012 -> false
  
let (__proj__EFlat__item___0 :
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____2062 -> false
  
let (__proj__EField__item___0 :
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____2098 -> false
  
let (__proj__EWhile__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____2130 -> false
  
let (__proj__EBufCreateL__item___0 :
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2164 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2192 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2236 -> false
  
let (__proj__EBufFill__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2268 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2290 -> false
  
let (__proj__EFun__item___0 :
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2328 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____2342 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____2355 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2361 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____2367 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2373 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____2379 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2385 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2391 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2397 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____2403 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____2409 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2415 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2421 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2427 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2433 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2439 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____2445 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____2451 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____2457 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____2463 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____2469 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____2475 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____2481 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____2487 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____2493 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____2499 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2505 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2512 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2526 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2546 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2580 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2606 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list)
  = fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____2642 -> false
  
let (__proj__PConstant__item___0 :
  pattern -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____2667 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2673 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2679 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2685 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2691 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2697 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2703 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2709 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2715 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____2721 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ;_} -> __fname__name
  
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ;_} -> __fname__typ
  
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____2742 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2756 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2769 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2782 -> false
  
let (__proj__TQualified__item___0 :
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2813 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2819 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2830 -> false
  
let (__proj__TArrow__item___0 :
  typ -> (typ,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2856 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2882 -> false
  
let (__proj__TApp__item___0 :
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____2934 -> false
  
let (__proj__TTuple__item___0 : typ -> typ Prims.list) =
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
let (current_version : version) = (Prims.parse_int "27") 
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
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
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
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___36_3115  ->
    match uu___36_3115 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____3118 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
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
  
let (is_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_op op) <> FStar_Pervasives_Native.None 
let (is_machine_int : Prims.string -> Prims.bool) =
  fun m  -> (mk_width m) <> FStar_Pervasives_Native.None 
type env =
  {
  names: name Prims.list ;
  names_t: Prims.string Prims.list ;
  module_name: Prims.string Prims.list }[@@deriving show]
and name = {
  pretty: Prims.string }[@@deriving show]
let (__proj__Mkenv__item__names : env -> name Prims.list) =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__names
  
let (__proj__Mkenv__item__names_t : env -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__names_t
  
let (__proj__Mkenv__item__module_name : env -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__module_name
  
let (__proj__Mkname__item__pretty : name -> Prims.string) =
  fun projectee  ->
    match projectee with | { pretty = __fname__pretty;_} -> __fname__pretty
  
let (empty : Prims.string Prims.list -> env) =
  fun module_name  -> { names = []; names_t = []; module_name } 
let (extend : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___42_3255 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___42_3255.names_t);
        module_name = (uu___42_3255.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___43_3266 = env  in
      {
        names = (uu___43_3266.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___43_3266.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____3277 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____3277 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____3301 ->
          let uu____3302 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____3302
  
let (find_t : env -> Prims.string -> Prims.int) =
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
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
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

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath,(FStar_Extraction_ML_Syntax.mlsig,
                                       FStar_Extraction_ML_Syntax.mlmodule)
                                       FStar_Pervasives_Native.tuple2
                                       FStar_Pervasives_Native.option,
    FStar_Extraction_ML_Syntax.mllib) FStar_Pervasives_Native.tuple3 -> 
    file)
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
          | uu____3709 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags1  ->
    FStar_List.choose
      (fun uu___38_3720  ->
         match uu___38_3720 with
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
         | uu____3727 -> FStar_Pervasives_Native.None) flags1

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3738 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3740 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____3744) ->
          (FStar_Util.print1_warning
             "Skipping the translation of exception: %s\n" m;
           [])

and (translate_let :
  env ->
    FStar_Extraction_ML_Syntax.mlletflavor ->
      FStar_Extraction_ML_Syntax.mllb -> decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun flavor  ->
      fun lb  ->
        match lb with
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3766;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____3769;
                FStar_Extraction_ML_Syntax.loc = uu____3770;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3772;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___39_3790  ->
                      match uu___39_3790 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____3791 -> false) meta
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
               let rec find_return_type eff i uu___40_3818 =
                 match uu___40_3818 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3823,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (eff, t)  in
               let uu____3827 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____3827 with
               | (eff,t) ->
                   let t1 = translate_type env2 t  in
                   let binders = translate_binders env2 args  in
                   let env3 = add_binders env2 args  in
                   let name1 = ((env3.module_name), name)  in
                   let meta1 =
                     match (eff, t1) with
                     | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____3859) ->
                         let uu____3860 = translate_flags meta  in
                         MustDisappear :: uu____3860
                     | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                         let uu____3863 = translate_flags meta  in
                         MustDisappear :: uu____3863
                     | uu____3866 -> translate_flags meta  in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____3876 =
                          let uu____3877 =
                            let uu____3896 = translate_type env3 t0  in
                            (FStar_Pervasives_Native.None, meta1, name1,
                              uu____3896)
                             in
                          DExternal uu____3877  in
                        FStar_Pervasives_Native.Some uu____3876
                      else
                        ((let uu____3909 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1
                             in
                          FStar_Util.print1_warning
                            "No writing anything for %s (polymorphic assume)\n"
                            uu____3909);
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
                          ((let uu____3942 =
                              let uu____3947 =
                                let uu____3948 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1
                                   in
                                FStar_Util.format2
                                  "Writing a stub for %s (%s)\n" uu____3948
                                  msg
                                 in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____3947)
                               in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____3942);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3965;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Coerce
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____3968;
                     FStar_Extraction_ML_Syntax.loc = uu____3969;_},uu____3970,uu____3971);
                FStar_Extraction_ML_Syntax.mlty = uu____3972;
                FStar_Extraction_ML_Syntax.loc = uu____3973;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3975;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___39_3993  ->
                      match uu___39_3993 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____3994 -> false) meta
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
               let rec find_return_type eff i uu___40_4021 =
                 match uu___40_4021 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____4026,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (eff, t)  in
               let uu____4030 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____4030 with
               | (eff,t) ->
                   let t1 = translate_type env2 t  in
                   let binders = translate_binders env2 args  in
                   let env3 = add_binders env2 args  in
                   let name1 = ((env3.module_name), name)  in
                   let meta1 =
                     match (eff, t1) with
                     | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____4062) ->
                         let uu____4063 = translate_flags meta  in
                         MustDisappear :: uu____4063
                     | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                         let uu____4066 = translate_flags meta  in
                         MustDisappear :: uu____4066
                     | uu____4069 -> translate_flags meta  in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____4079 =
                          let uu____4080 =
                            let uu____4099 = translate_type env3 t0  in
                            (FStar_Pervasives_Native.None, meta1, name1,
                              uu____4099)
                             in
                          DExternal uu____4080  in
                        FStar_Pervasives_Native.Some uu____4079
                      else
                        ((let uu____4112 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1
                             in
                          FStar_Util.print1_warning
                            "No writing anything for %s (polymorphic assume)\n"
                            uu____4112);
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
                          ((let uu____4145 =
                              let uu____4150 =
                                let uu____4151 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1
                                   in
                                FStar_Util.format2
                                  "Writing a stub for %s (%s)\n" uu____4151
                                  msg
                                 in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____4150)
                               in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____4145);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4168;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4171;_} ->
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
                   ((let uu____4217 =
                       let uu____4222 =
                         let uu____4223 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____4224 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Not translating definition for %s (%s)\n"
                           uu____4223 uu____4224
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____4222)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____4217);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4235;
            FStar_Extraction_ML_Syntax.mllb_def = uu____4236;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____4237;
            FStar_Extraction_ML_Syntax.print_typ = uu____4238;_} ->
            ((let uu____4242 =
                let uu____4247 =
                  FStar_Util.format1 "Not translating definition for %s\n"
                    name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____4247)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____4242);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____4251 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____4251
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
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
            (let uu____4289 =
               let uu____4290 =
                 let uu____4307 = translate_flags flags1  in
                 let uu____4310 = translate_type env1 t  in
                 (name1, uu____4307, (FStar_List.length args), uu____4310)
                  in
               DTypeAlias uu____4290  in
             FStar_Pervasives_Native.Some uu____4289)
      | (uu____4319,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args
             in
          let uu____4351 =
            let uu____4352 =
              let uu____4379 = translate_flags flags1  in
              let uu____4382 =
                FStar_List.map
                  (fun uu____4409  ->
                     match uu____4409 with
                     | (f,t) ->
                         let uu____4424 =
                           let uu____4429 = translate_type env1 t  in
                           (uu____4429, false)  in
                         (f, uu____4424)) fields
                 in
              (name1, uu____4379, (FStar_List.length args), uu____4382)  in
            DTypeFlat uu____4352  in
          FStar_Pervasives_Native.Some uu____4351
      | (uu____4452,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
          let name1 = ((env.module_name), name)  in
          let flags2 = translate_flags flags1  in
          let env1 = FStar_List.fold_left extend_t env args  in
          let uu____4489 =
            let uu____4490 =
              let uu____4523 =
                FStar_List.map
                  (fun uu____4568  ->
                     match uu____4568 with
                     | (cons1,ts) ->
                         let uu____4607 =
                           FStar_List.map
                             (fun uu____4634  ->
                                match uu____4634 with
                                | (name2,t) ->
                                    let uu____4649 =
                                      let uu____4654 = translate_type env1 t
                                         in
                                      (uu____4654, false)  in
                                    (name2, uu____4649)) ts
                            in
                         (cons1, uu____4607)) branches
                 in
              (name1, flags2, (FStar_List.length args), uu____4523)  in
            DTypeVariant uu____4490  in
          FStar_Pervasives_Native.Some uu____4489
      | (uu____4693,name,_mangled_name,uu____4696,uu____4697,uu____4698) ->
          ((let uu____4708 =
              let uu____4713 =
                FStar_Util.format1 "Not translating type definition for %s\n"
                  name
                 in
              (FStar_Errors.Warning_DefinitionNotTranslated, uu____4713)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____4708);
           FStar_Pervasives_Native.None)

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4717 = find_t env name  in TBound uu____4717
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4719,t2) ->
          let uu____4721 =
            let uu____4726 = translate_type env t1  in
            let uu____4727 = translate_type env t2  in
            (uu____4726, uu____4727)  in
          TArrow uu____4721
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4731 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4731 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4735 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4735 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4741 = FStar_Util.must (mk_width m)  in TInt uu____4741
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4747 = FStar_Util.must (mk_width m)  in TInt uu____4747
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4752 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4752 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____4753::arg::uu____4755::[],p) when
          (((let uu____4761 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4761 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____4763 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4763 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____4765 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4765 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____4767 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4767 = "FStar.HyperStack.ST.s_mref")
          -> let uu____4768 = translate_type env arg  in TBuf uu____4768
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____4770::[],p) when
          ((((((((((let uu____4776 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4776 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____4778 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4778 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____4780 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4780 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____4782 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4782 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____4784 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4784 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____4786 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4786 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____4788 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4788 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____4790 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4790 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____4792 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4792 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____4794 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4794 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____4796 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4796 = "FStar.HyperStack.ST.mmmref")
          -> let uu____4797 = translate_type env arg  in TBuf uu____4797
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          ((((((((((let uu____4804 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4804 = "FStar.Buffer.buffer") ||
                     (let uu____4806 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4806 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____4808 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4808 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____4810 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4810 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____4812 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4812 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____4814 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4814 = "FStar.HyperStack.mmref"))
                ||
                (let uu____4816 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4816 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____4818 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4818 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____4820 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4820 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____4822 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4822 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____4824 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4824 = "FStar.HyperStack.ST.mmref")
          -> let uu____4825 = translate_type env arg  in TBuf uu____4825
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4826::arg::[],p) when
          (let uu____4833 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4833 = "FStar.HyperStack.s_ref") ||
            (let uu____4835 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4835 = "FStar.HyperStack.ST.s_ref")
          -> let uu____4836 = translate_type env arg  in TBuf uu____4836
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4837::[],p) when
          let uu____4841 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4841 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4867 = FStar_List.map (translate_type env) args  in
          TTuple uu____4867
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4876 =
              let uu____4889 = FStar_List.map (translate_type env) args  in
              (lid, uu____4889)  in
            TApp uu____4876
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4904 = FStar_List.map (translate_type env) ts  in
          TTuple uu____4904

and (translate_binders :
  env ->
    (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2 Prims.list -> binder Prims.list)
  = fun env  -> fun args  -> FStar_List.map (translate_binder env) args

and (translate_binder :
  env ->
    (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2 -> binder)
  =
  fun env  ->
    fun uu____4920  ->
      match uu____4920 with
      | (name,typ) ->
          let uu____4927 = translate_type env typ  in
          { name; typ = uu____4927 }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____4932 = find env name  in EBound uu____4932
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4937 =
            let uu____4942 = FStar_Util.must (mk_op op)  in
            let uu____4943 = FStar_Util.must (mk_width m)  in
            (uu____4942, uu____4943)  in
          EOp uu____4937
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4947 =
            let uu____4952 = FStar_Util.must (mk_bool_op op)  in
            (uu____4952, Bool)  in
          EOp uu____4947
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
            let uu____4971 = translate_type env typ  in
            { name; typ = uu____4971 }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4997 =
            let uu____5008 = translate_expr env expr  in
            let uu____5009 = translate_branches env branches  in
            (uu____5008, uu____5009)  in
          EMatch uu____4997
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5023;
                  FStar_Extraction_ML_Syntax.loc = uu____5024;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____5026;
             FStar_Extraction_ML_Syntax.loc = uu____5027;_},arg::[])
          when
          let uu____5033 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5033 = "FStar.Dyn.undyn" ->
          let uu____5034 =
            let uu____5039 = translate_expr env arg  in
            let uu____5040 = translate_type env t  in
            (uu____5039, uu____5040)  in
          ECast uu____5034
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5042;
                  FStar_Extraction_ML_Syntax.loc = uu____5043;_},uu____5044);
             FStar_Extraction_ML_Syntax.mlty = uu____5045;
             FStar_Extraction_ML_Syntax.loc = uu____5046;_},uu____5047)
          when
          let uu____5056 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5056 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5058;
                  FStar_Extraction_ML_Syntax.loc = uu____5059;_},uu____5060);
             FStar_Extraction_ML_Syntax.mlty = uu____5061;
             FStar_Extraction_ML_Syntax.loc = uu____5062;_},arg::[])
          when
          ((let uu____5072 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5072 = "FStar.HyperStack.All.failwith") ||
             (let uu____5074 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5074 = "FStar.Error.unexpected"))
            ||
            (let uu____5076 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5076 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____5078;
               FStar_Extraction_ML_Syntax.loc = uu____5079;_} -> EAbortS msg
           | uu____5080 ->
               let print7 =
                 let uu____5082 =
                   let uu____5083 =
                     let uu____5084 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____5084
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____5083  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____5082
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
                  FStar_Extraction_ML_Syntax.mlty = uu____5090;
                  FStar_Extraction_ML_Syntax.loc = uu____5091;_},uu____5092);
             FStar_Extraction_ML_Syntax.mlty = uu____5093;
             FStar_Extraction_ML_Syntax.loc = uu____5094;_},e1::e2::[])
          when
          (let uu____5105 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5105 = "FStar.Buffer.index") ||
            (let uu____5107 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5107 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____5108 =
            let uu____5113 = translate_expr env e1  in
            let uu____5114 = translate_expr env e2  in
            (uu____5113, uu____5114)  in
          EBufRead uu____5108
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5116;
                  FStar_Extraction_ML_Syntax.loc = uu____5117;_},uu____5118);
             FStar_Extraction_ML_Syntax.mlty = uu____5119;
             FStar_Extraction_ML_Syntax.loc = uu____5120;_},e1::[])
          when
          let uu____5128 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5128 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____5129 =
            let uu____5134 = translate_expr env e1  in
            (uu____5134, (EConstant (UInt32, "0")))  in
          EBufRead uu____5129
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5136;
                  FStar_Extraction_ML_Syntax.loc = uu____5137;_},uu____5138);
             FStar_Extraction_ML_Syntax.mlty = uu____5139;
             FStar_Extraction_ML_Syntax.loc = uu____5140;_},e1::e2::[])
          when
          let uu____5149 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5149 = "FStar.Buffer.create" ->
          let uu____5150 =
            let uu____5157 = translate_expr env e1  in
            let uu____5158 = translate_expr env e2  in
            (Stack, uu____5157, uu____5158)  in
          EBufCreate uu____5150
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5160;
                  FStar_Extraction_ML_Syntax.loc = uu____5161;_},uu____5162);
             FStar_Extraction_ML_Syntax.mlty = uu____5163;
             FStar_Extraction_ML_Syntax.loc = uu____5164;_},init1::[])
          when
          let uu____5172 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5172 = "FStar.HyperStack.ST.salloc" ->
          let uu____5173 =
            let uu____5180 = translate_expr env init1  in
            (Stack, uu____5180, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5173
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5182;
                  FStar_Extraction_ML_Syntax.loc = uu____5183;_},uu____5184);
             FStar_Extraction_ML_Syntax.mlty = uu____5185;
             FStar_Extraction_ML_Syntax.loc = uu____5186;_},e2::[])
          when
          let uu____5194 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5194 = "FStar.Buffer.createL" ->
          let rec list_elements acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____5224 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a list literal!"
             in
          let list_elements1 = list_elements []  in
          let uu____5234 =
            let uu____5241 =
              let uu____5244 = list_elements1 e2  in
              FStar_List.map (translate_expr env) uu____5244  in
            (Stack, uu____5241)  in
          EBufCreateL uu____5234
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5250;
                  FStar_Extraction_ML_Syntax.loc = uu____5251;_},uu____5252);
             FStar_Extraction_ML_Syntax.mlty = uu____5253;
             FStar_Extraction_ML_Syntax.loc = uu____5254;_},_rid::init1::[])
          when
          let uu____5263 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5263 = "FStar.HyperStack.ST.ralloc" ->
          let uu____5264 =
            let uu____5271 = translate_expr env init1  in
            (Eternal, uu____5271, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5264
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5273;
                  FStar_Extraction_ML_Syntax.loc = uu____5274;_},uu____5275);
             FStar_Extraction_ML_Syntax.mlty = uu____5276;
             FStar_Extraction_ML_Syntax.loc = uu____5277;_},_e0::e1::e2::[])
          when
          let uu____5287 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5287 = "FStar.Buffer.rcreate" ->
          let uu____5288 =
            let uu____5295 = translate_expr env e1  in
            let uu____5296 = translate_expr env e2  in
            (Eternal, uu____5295, uu____5296)  in
          EBufCreate uu____5288
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5298;
                  FStar_Extraction_ML_Syntax.loc = uu____5299;_},uu____5300);
             FStar_Extraction_ML_Syntax.mlty = uu____5301;
             FStar_Extraction_ML_Syntax.loc = uu____5302;_},_rid::init1::[])
          when
          let uu____5311 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5311 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____5312 =
            let uu____5319 = translate_expr env init1  in
            (ManuallyManaged, uu____5319, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5312
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5321;
                  FStar_Extraction_ML_Syntax.loc = uu____5322;_},uu____5323);
             FStar_Extraction_ML_Syntax.mlty = uu____5324;
             FStar_Extraction_ML_Syntax.loc = uu____5325;_},_e0::e1::e2::[])
          when
          let uu____5335 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5335 = "FStar.Buffer.rcreate_mm" ->
          let uu____5336 =
            let uu____5343 = translate_expr env e1  in
            let uu____5344 = translate_expr env e2  in
            (ManuallyManaged, uu____5343, uu____5344)  in
          EBufCreate uu____5336
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5346;
                  FStar_Extraction_ML_Syntax.loc = uu____5347;_},uu____5348);
             FStar_Extraction_ML_Syntax.mlty = uu____5349;
             FStar_Extraction_ML_Syntax.loc = uu____5350;_},e2::[])
          when
          let uu____5358 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5358 = "FStar.HyperStack.ST.rfree" ->
          let uu____5359 = translate_expr env e2  in EBufFree uu____5359
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5361;
                  FStar_Extraction_ML_Syntax.loc = uu____5362;_},uu____5363);
             FStar_Extraction_ML_Syntax.mlty = uu____5364;
             FStar_Extraction_ML_Syntax.loc = uu____5365;_},e2::[])
          when
          let uu____5373 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5373 = "FStar.Buffer.rfree" ->
          let uu____5374 = translate_expr env e2  in EBufFree uu____5374
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5376;
                  FStar_Extraction_ML_Syntax.loc = uu____5377;_},uu____5378);
             FStar_Extraction_ML_Syntax.mlty = uu____5379;
             FStar_Extraction_ML_Syntax.loc = uu____5380;_},e1::e2::_e3::[])
          when
          let uu____5390 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5390 = "FStar.Buffer.sub" ->
          let uu____5391 =
            let uu____5396 = translate_expr env e1  in
            let uu____5397 = translate_expr env e2  in
            (uu____5396, uu____5397)  in
          EBufSub uu____5391
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5399;
                  FStar_Extraction_ML_Syntax.loc = uu____5400;_},uu____5401);
             FStar_Extraction_ML_Syntax.mlty = uu____5402;
             FStar_Extraction_ML_Syntax.loc = uu____5403;_},e1::e2::[])
          when
          let uu____5412 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5412 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5414;
                  FStar_Extraction_ML_Syntax.loc = uu____5415;_},uu____5416);
             FStar_Extraction_ML_Syntax.mlty = uu____5417;
             FStar_Extraction_ML_Syntax.loc = uu____5418;_},e1::e2::[])
          when
          let uu____5427 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5427 = "FStar.Buffer.offset" ->
          let uu____5428 =
            let uu____5433 = translate_expr env e1  in
            let uu____5434 = translate_expr env e2  in
            (uu____5433, uu____5434)  in
          EBufSub uu____5428
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
             FStar_Extraction_ML_Syntax.loc = uu____5440;_},e1::e2::e3::[])
          when
          (let uu____5452 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5452 = "FStar.Buffer.upd") ||
            (let uu____5454 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5454 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____5455 =
            let uu____5462 = translate_expr env e1  in
            let uu____5463 = translate_expr env e2  in
            let uu____5464 = translate_expr env e3  in
            (uu____5462, uu____5463, uu____5464)  in
          EBufWrite uu____5455
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5466;
                  FStar_Extraction_ML_Syntax.loc = uu____5467;_},uu____5468);
             FStar_Extraction_ML_Syntax.mlty = uu____5469;
             FStar_Extraction_ML_Syntax.loc = uu____5470;_},e1::e2::[])
          when
          let uu____5479 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5479 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5480 =
            let uu____5487 = translate_expr env e1  in
            let uu____5488 = translate_expr env e2  in
            (uu____5487, (EConstant (UInt32, "0")), uu____5488)  in
          EBufWrite uu____5480
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5490;
             FStar_Extraction_ML_Syntax.loc = uu____5491;_},uu____5492::[])
          when
          let uu____5495 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5495 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5497;
             FStar_Extraction_ML_Syntax.loc = uu____5498;_},uu____5499::[])
          when
          let uu____5502 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5502 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5504;
                  FStar_Extraction_ML_Syntax.loc = uu____5505;_},uu____5506);
             FStar_Extraction_ML_Syntax.mlty = uu____5507;
             FStar_Extraction_ML_Syntax.loc = uu____5508;_},e1::e2::e3::e4::e5::[])
          when
          let uu____5520 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5520 = "FStar.Buffer.blit" ->
          let uu____5521 =
            let uu____5532 = translate_expr env e1  in
            let uu____5533 = translate_expr env e2  in
            let uu____5534 = translate_expr env e3  in
            let uu____5535 = translate_expr env e4  in
            let uu____5536 = translate_expr env e5  in
            (uu____5532, uu____5533, uu____5534, uu____5535, uu____5536)  in
          EBufBlit uu____5521
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5538;
                  FStar_Extraction_ML_Syntax.loc = uu____5539;_},uu____5540);
             FStar_Extraction_ML_Syntax.mlty = uu____5541;
             FStar_Extraction_ML_Syntax.loc = uu____5542;_},e1::e2::e3::[])
          when
          let uu____5552 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5552 = "FStar.Buffer.fill" ->
          let uu____5553 =
            let uu____5560 = translate_expr env e1  in
            let uu____5561 = translate_expr env e2  in
            let uu____5562 = translate_expr env e3  in
            (uu____5560, uu____5561, uu____5562)  in
          EBufFill uu____5553
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5564;
             FStar_Extraction_ML_Syntax.loc = uu____5565;_},uu____5566::[])
          when
          let uu____5569 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5569 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5571;
             FStar_Extraction_ML_Syntax.loc = uu____5572;_},e1::[])
          when
          let uu____5576 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5576 = "Obj.repr" ->
          let uu____5577 =
            let uu____5582 = translate_expr env e1  in (uu____5582, TAny)  in
          ECast uu____5577
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5585;
             FStar_Extraction_ML_Syntax.loc = uu____5586;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5594 = FStar_Util.must (mk_width m)  in
          let uu____5595 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____5594 uu____5595 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5597;
             FStar_Extraction_ML_Syntax.loc = uu____5598;_},args)
          when is_bool_op op ->
          let uu____5606 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____5606 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5608;
             FStar_Extraction_ML_Syntax.loc = uu____5609;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5611;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5612;_}::[])
          when is_machine_int m ->
          let uu____5627 =
            let uu____5632 = FStar_Util.must (mk_width m)  in (uu____5632, c)
             in
          EConstant uu____5627
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5634;
             FStar_Extraction_ML_Syntax.loc = uu____5635;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5637;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5638;_}::[])
          when is_machine_int m ->
          let uu____5653 =
            let uu____5658 = FStar_Util.must (mk_width m)  in (uu____5658, c)
             in
          EConstant uu____5653
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5659;
             FStar_Extraction_ML_Syntax.loc = uu____5660;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5662;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5663;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5669 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5670;
             FStar_Extraction_ML_Syntax.loc = uu____5671;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5673;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5674;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5680 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5682;
             FStar_Extraction_ML_Syntax.loc = uu____5683;_},arg::[])
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
            let uu____5690 =
              let uu____5695 = translate_expr env arg  in
              (uu____5695, (TInt UInt64))  in
            ECast uu____5690
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5697 =
                 let uu____5702 = translate_expr env arg  in
                 (uu____5702, (TInt UInt32))  in
               ECast uu____5697)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5704 =
                   let uu____5709 = translate_expr env arg  in
                   (uu____5709, (TInt UInt16))  in
                 ECast uu____5704)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5711 =
                     let uu____5716 = translate_expr env arg  in
                     (uu____5716, (TInt UInt8))  in
                   ECast uu____5711)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5718 =
                       let uu____5723 = translate_expr env arg  in
                       (uu____5723, (TInt Int64))  in
                     ECast uu____5718)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5725 =
                         let uu____5730 = translate_expr env arg  in
                         (uu____5730, (TInt Int32))  in
                       ECast uu____5725)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5732 =
                           let uu____5737 = translate_expr env arg  in
                           (uu____5737, (TInt Int16))  in
                         ECast uu____5732)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5739 =
                             let uu____5744 = translate_expr env arg  in
                             (uu____5744, (TInt Int8))  in
                           ECast uu____5739)
                        else
                          (let uu____5746 =
                             let uu____5753 =
                               let uu____5756 = translate_expr env arg  in
                               [uu____5756]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5753)
                              in
                           EApp uu____5746)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5767 =
            let uu____5774 = translate_expr env head1  in
            let uu____5775 = FStar_List.map (translate_expr env) args  in
            (uu____5774, uu____5775)  in
          EApp uu____5767
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5786 =
            let uu____5793 = translate_expr env head1  in
            let uu____5794 = FStar_List.map (translate_type env) ty_args  in
            (uu____5793, uu____5794)  in
          ETypApp uu____5786
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5802 =
            let uu____5807 = translate_expr env e1  in
            let uu____5808 = translate_type env t_to  in
            (uu____5807, uu____5808)  in
          ECast uu____5802
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5809,fields) ->
          let uu____5827 =
            let uu____5838 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5839 =
              FStar_List.map
                (fun uu____5858  ->
                   match uu____5858 with
                   | (field,expr) ->
                       let uu____5869 = translate_expr env expr  in
                       (field, uu____5869)) fields
               in
            (uu____5838, uu____5839)  in
          EFlat uu____5827
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5878 =
            let uu____5885 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____5886 = translate_expr env e1  in
            (uu____5885, uu____5886, (FStar_Pervasives_Native.snd path))  in
          EField uu____5878
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5889 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5901) ->
          let uu____5906 =
            let uu____5907 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5907
             in
          failwith uu____5906
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5913 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____5913
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5919 = FStar_List.map (translate_expr env) es  in
          ETuple uu____5919
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5922,cons1),es) ->
          let uu____5933 =
            let uu____5942 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5943 = FStar_List.map (translate_expr env) es  in
            (uu____5942, cons1, uu____5943)  in
          ECons uu____5933
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____5966 =
            let uu____5975 = translate_expr env1 body  in
            let uu____5976 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____5975, uu____5976)  in
          EFun uu____5966
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5986 =
            let uu____5993 = translate_expr env e1  in
            let uu____5994 = translate_expr env e2  in
            let uu____5995 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____5993, uu____5994, uu____5995)  in
          EIfThenElse uu____5986
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5997 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____6004 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____6019 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____6034 =
              let uu____6047 = FStar_List.map (translate_type env) ts  in
              (lid, uu____6047)  in
            TApp uu____6034
          else TQualified lid
      | uu____6059 -> failwith "invalid argument: assert_lid"

and (translate_branches :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern,FStar_Extraction_ML_Syntax.mlexpr
                                            FStar_Pervasives_Native.option,
      FStar_Extraction_ML_Syntax.mlexpr) FStar_Pervasives_Native.tuple3
      Prims.list -> (pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun env  -> fun branches  -> FStar_List.map (translate_branch env) branches

and (translate_branch :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern,FStar_Extraction_ML_Syntax.mlexpr
                                            FStar_Pervasives_Native.option,
      FStar_Extraction_ML_Syntax.mlexpr) FStar_Pervasives_Native.tuple3 ->
      (pattern,expr) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____6085  ->
      match uu____6085 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____6111 = translate_pat env pat  in
            (match uu____6111 with
             | (env1,pat1) ->
                 let uu____6122 = translate_expr env1 expr  in
                 (pat1, uu____6122))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___41_6128  ->
    match uu___41_6128 with
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

and (translate_pat :
  env ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      (env,pattern) FStar_Pervasives_Native.tuple2)
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
          let uu____6192 =
            let uu____6193 =
              let uu____6198 = translate_width sw  in (uu____6198, s)  in
            PConstant uu____6193  in
          (env, uu____6192)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in (env1, (PVar { name; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____6202,cons1),ps) ->
          let uu____6213 =
            FStar_List.fold_left
              (fun uu____6233  ->
                 fun p1  ->
                   match uu____6233 with
                   | (env1,acc) ->
                       let uu____6253 = translate_pat env1 p1  in
                       (match uu____6253 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6213 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____6282,ps) ->
          let uu____6300 =
            FStar_List.fold_left
              (fun uu____6334  ->
                 fun uu____6335  ->
                   match (uu____6334, uu____6335) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____6404 = translate_pat env1 p1  in
                       (match uu____6404 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____6300 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____6466 =
            FStar_List.fold_left
              (fun uu____6486  ->
                 fun p1  ->
                   match uu____6486 with
                   | (env1,acc) ->
                       let uu____6506 = translate_pat env1 p1  in
                       (match uu____6506 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6466 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6533 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6538 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____6549 =
            let uu____6550 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____6550
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____6549
          then
            let uu____6562 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____6562
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6574) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6589 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6590 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        EConstant (CInt, s)

and (mk_op_app :
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr)
  =
  fun env  ->
    fun w  ->
      fun op  ->
        fun args  ->
          let uu____6610 =
            let uu____6617 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____6617)  in
          EApp uu____6610
