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
  FStar_Pervasives_Native.tuple4 
and cc =
  | StdCall 
  | CDecl 
  | FastCall 
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
  | Epilogue of Prims.string 
and lifetime =
  | Eternal 
  | Stack 
  | ManuallyManaged 
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
  | EBufFree of expr 
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
  | Not 
and pattern =
  | PUnit 
  | PBool of Prims.bool 
  | PVar of binder 
  | PCons of (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2
  
  | PTuple of pattern Prims.list 
  | PRecord of (Prims.string,pattern) FStar_Pervasives_Native.tuple2
  Prims.list 
  | PConstant of (width,Prims.string) FStar_Pervasives_Native.tuple2 
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
  | CInt 
and binder = {
  name: Prims.string ;
  typ: typ }
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
  | TTuple of typ Prims.list 
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
type program = decl Prims.list
type ident = Prims.string
type fields_t =
  (Prims.string,(typ,Prims.bool) FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2 Prims.list
type branches_t =
  (Prims.string,(Prims.string,(typ,Prims.bool) FStar_Pervasives_Native.tuple2)
                  FStar_Pervasives_Native.tuple2 Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list
type fsdoc = Prims.string
type branch = (pattern,expr) FStar_Pervasives_Native.tuple2
type branches = (pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list
type constant = (width,Prims.string) FStar_Pervasives_Native.tuple2
type var = Prims.int
type lident =
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
type version = Prims.int
let (current_version : version) = (Prims.parse_int "27") 
type file = (Prims.string,program) FStar_Pervasives_Native.tuple2
type binary_format = (version,file Prims.list) FStar_Pervasives_Native.tuple2
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
  fun uu___258_3105  ->
    match uu___258_3105 with
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
  fun uu___259_3115  ->
    match uu___259_3115 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____3118 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___260_3132  ->
    match uu___260_3132 with
    | "add" -> FStar_Pervasives_Native.Some Add
    | "op_Plus_Hat" -> FStar_Pervasives_Native.Some Add
    | "add_underspec" -> FStar_Pervasives_Native.Some Add
    | "add_mod" -> FStar_Pervasives_Native.Some AddW
    | "op_Plus_Percent_Hat" -> FStar_Pervasives_Native.Some AddW
    | "sub" -> FStar_Pervasives_Native.Some Sub
    | "op_Subtraction_Hat" -> FStar_Pervasives_Native.Some Sub
    | "sub_underspec" -> FStar_Pervasives_Native.Some Sub
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
  module_name: Prims.string Prims.list }
and name = {
  pretty: Prims.string }
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
      let uu___265_3255 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___265_3255.names_t);
        module_name = (uu___265_3255.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___266_3266 = env  in
      {
        names = (uu___266_3266.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___266_3266.module_name)
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
      (fun uu___261_3720  ->
         match uu___261_3720 with
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
             "Not extracting exception %s to KreMLin (exceptions unsupported)\n"
             m;
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
                   (fun uu___262_3790  ->
                      match uu___262_3790 with
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
               let rec find_return_type eff i uu___263_3818 =
                 match uu___263_3818 with
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
                        let uu____3875 =
                          let uu____3876 =
                            let uu____3895 = translate_type env3 t0  in
                            (FStar_Pervasives_Native.None, meta1, name1,
                              uu____3895)
                             in
                          DExternal uu____3876  in
                        FStar_Pervasives_Native.Some uu____3875
                      else
                        ((let uu____3908 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1
                             in
                          FStar_Util.print1_warning
                            "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                            uu____3908);
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
                          ((let uu____3941 =
                              let uu____3946 =
                                let uu____3947 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1
                                   in
                                FStar_Util.format2
                                  "Error while extracting %s to KreMLin (%s)\n"
                                  uu____3947 msg
                                 in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____3946)
                               in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____3941);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3964;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Coerce
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____3967;
                     FStar_Extraction_ML_Syntax.loc = uu____3968;_},uu____3969,uu____3970);
                FStar_Extraction_ML_Syntax.mlty = uu____3971;
                FStar_Extraction_ML_Syntax.loc = uu____3972;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3974;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___262_3992  ->
                      match uu___262_3992 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____3993 -> false) meta
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
               let rec find_return_type eff i uu___263_4020 =
                 match uu___263_4020 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____4025,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (eff, t)  in
               let uu____4029 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____4029 with
               | (eff,t) ->
                   let t1 = translate_type env2 t  in
                   let binders = translate_binders env2 args  in
                   let env3 = add_binders env2 args  in
                   let name1 = ((env3.module_name), name)  in
                   let meta1 =
                     match (eff, t1) with
                     | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____4061) ->
                         let uu____4062 = translate_flags meta  in
                         MustDisappear :: uu____4062
                     | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                         let uu____4065 = translate_flags meta  in
                         MustDisappear :: uu____4065
                     | uu____4068 -> translate_flags meta  in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____4077 =
                          let uu____4078 =
                            let uu____4097 = translate_type env3 t0  in
                            (FStar_Pervasives_Native.None, meta1, name1,
                              uu____4097)
                             in
                          DExternal uu____4078  in
                        FStar_Pervasives_Native.Some uu____4077
                      else
                        ((let uu____4110 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1
                             in
                          FStar_Util.print1_warning
                            "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                            uu____4110);
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
                          ((let uu____4143 =
                              let uu____4148 =
                                let uu____4149 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1
                                   in
                                FStar_Util.format2
                                  "Error while extracting %s to KreMLin (%s)\n"
                                  uu____4149 msg
                                 in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____4148)
                               in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____4143);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4166;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4169;_} ->
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
                   ((let uu____4215 =
                       let uu____4220 =
                         let uu____4221 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____4222 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____4221
                           uu____4222
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____4220)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____4215);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4233;
            FStar_Extraction_ML_Syntax.mllb_def = uu____4234;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____4235;
            FStar_Extraction_ML_Syntax.print_typ = uu____4236;_} ->
            ((let uu____4240 =
                let uu____4245 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____4245)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____4240);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____4249 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____4249
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____4256 = ty  in
      match uu____4256 with
      | (uu____4259,uu____4260,uu____4261,uu____4262,flags1,uu____4264) ->
          if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract flags1
          then FStar_Pervasives_Native.None
          else
            (match ty with
             | (assumed,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Abbrev t)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 if assumed
                 then
                   let name2 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                   (FStar_Util.print1_warning
                      "Not extracting type definition %s to KreMLin (assumed type)\n"
                      name2;
                    FStar_Pervasives_Native.None)
                 else
                   (let uu____4309 =
                      let uu____4310 =
                        let uu____4327 = translate_flags flags2  in
                        let uu____4330 = translate_type env1 t  in
                        (name1, uu____4327, (FStar_List.length args),
                          uu____4330)
                         in
                      DTypeAlias uu____4310  in
                    FStar_Pervasives_Native.Some uu____4309)
             | (uu____4339,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____4371 =
                   let uu____4372 =
                     let uu____4399 = translate_flags flags2  in
                     let uu____4402 =
                       FStar_List.map
                         (fun uu____4429  ->
                            match uu____4429 with
                            | (f,t) ->
                                let uu____4444 =
                                  let uu____4449 = translate_type env1 t  in
                                  (uu____4449, false)  in
                                (f, uu____4444)) fields
                        in
                     (name1, uu____4399, (FStar_List.length args),
                       uu____4402)
                      in
                   DTypeFlat uu____4372  in
                 FStar_Pervasives_Native.Some uu____4371
             | (uu____4472,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags3 = translate_flags flags2  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____4509 =
                   let uu____4510 =
                     let uu____4543 =
                       FStar_List.map
                         (fun uu____4588  ->
                            match uu____4588 with
                            | (cons1,ts) ->
                                let uu____4627 =
                                  FStar_List.map
                                    (fun uu____4654  ->
                                       match uu____4654 with
                                       | (name2,t) ->
                                           let uu____4669 =
                                             let uu____4674 =
                                               translate_type env1 t  in
                                             (uu____4674, false)  in
                                           (name2, uu____4669)) ts
                                   in
                                (cons1, uu____4627)) branches
                        in
                     (name1, flags3, (FStar_List.length args), uu____4543)
                      in
                   DTypeVariant uu____4510  in
                 FStar_Pervasives_Native.Some uu____4509
             | (uu____4713,name,_mangled_name,uu____4716,uu____4717,uu____4718)
                 ->
                 ((let uu____4728 =
                     let uu____4733 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____4733)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____4728);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4737 = find_t env name  in TBound uu____4737
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4739,t2) ->
          let uu____4741 =
            let uu____4746 = translate_type env t1  in
            let uu____4747 = translate_type env t2  in
            (uu____4746, uu____4747)  in
          TArrow uu____4741
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4751 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4751 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4755 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4755 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4761 = FStar_Util.must (mk_width m)  in TInt uu____4761
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4767 = FStar_Util.must (mk_width m)  in TInt uu____4767
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4772 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4772 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____4773::arg::uu____4775::[],p) when
          (((let uu____4781 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4781 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____4783 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4783 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____4785 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4785 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____4787 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4787 = "FStar.HyperStack.ST.s_mref")
          -> let uu____4788 = translate_type env arg  in TBuf uu____4788
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____4790::[],p) when
          ((((((((((let uu____4796 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4796 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____4798 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4798 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____4800 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4800 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____4802 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4802 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____4804 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4804 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____4806 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4806 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____4808 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4808 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____4810 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4810 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____4812 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4812 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____4814 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4814 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____4816 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4816 = "FStar.HyperStack.ST.mmmref")
          -> let uu____4817 = translate_type env arg  in TBuf uu____4817
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((let uu____4824 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4824 = "LowStar.Buffer.buffer") ||
                      (let uu____4826 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____4826 = "FStar.Buffer.buffer"))
                     ||
                     (let uu____4828 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4828 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____4830 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4830 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____4832 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4832 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____4834 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4834 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____4836 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4836 = "FStar.HyperStack.mmref"))
                ||
                (let uu____4838 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4838 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____4840 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4840 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____4842 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4842 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____4844 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4844 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____4846 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4846 = "FStar.HyperStack.ST.mmref")
          -> let uu____4847 = translate_type env arg  in TBuf uu____4847
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4848::arg::[],p) when
          (let uu____4855 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4855 = "FStar.HyperStack.s_ref") ||
            (let uu____4857 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4857 = "FStar.HyperStack.ST.s_ref")
          -> let uu____4858 = translate_type env arg  in TBuf uu____4858
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4859::[],p) when
          let uu____4863 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4863 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4889 = FStar_List.map (translate_type env) args  in
          TTuple uu____4889
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4898 =
              let uu____4911 = FStar_List.map (translate_type env) args  in
              (lid, uu____4911)  in
            TApp uu____4898
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4926 = FStar_List.map (translate_type env) ts  in
          TTuple uu____4926

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
    fun uu____4942  ->
      match uu____4942 with
      | (name,typ) ->
          let uu____4949 = translate_type env typ  in
          { name; typ = uu____4949 }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____4954 = find env name  in EBound uu____4954
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4959 =
            let uu____4964 = FStar_Util.must (mk_op op)  in
            let uu____4965 = FStar_Util.must (mk_width m)  in
            (uu____4964, uu____4965)  in
          EOp uu____4959
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4969 =
            let uu____4974 = FStar_Util.must (mk_bool_op op)  in
            (uu____4974, Bool)  in
          EOp uu____4969
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
            let uu____4993 = translate_type env typ  in
            { name; typ = uu____4993 }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____5019 =
            let uu____5030 = translate_expr env expr  in
            let uu____5031 = translate_branches env branches  in
            (uu____5030, uu____5031)  in
          EMatch uu____5019
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5045;
                  FStar_Extraction_ML_Syntax.loc = uu____5046;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____5048;
             FStar_Extraction_ML_Syntax.loc = uu____5049;_},arg::[])
          when
          let uu____5055 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5055 = "FStar.Dyn.undyn" ->
          let uu____5056 =
            let uu____5061 = translate_expr env arg  in
            let uu____5062 = translate_type env t  in
            (uu____5061, uu____5062)  in
          ECast uu____5056
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5064;
                  FStar_Extraction_ML_Syntax.loc = uu____5065;_},uu____5066);
             FStar_Extraction_ML_Syntax.mlty = uu____5067;
             FStar_Extraction_ML_Syntax.loc = uu____5068;_},uu____5069)
          when
          let uu____5078 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5078 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5080;
                  FStar_Extraction_ML_Syntax.loc = uu____5081;_},uu____5082);
             FStar_Extraction_ML_Syntax.mlty = uu____5083;
             FStar_Extraction_ML_Syntax.loc = uu____5084;_},arg::[])
          when
          ((let uu____5094 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5094 = "FStar.HyperStack.All.failwith") ||
             (let uu____5096 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5096 = "FStar.Error.unexpected"))
            ||
            (let uu____5098 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5098 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____5100;
               FStar_Extraction_ML_Syntax.loc = uu____5101;_} -> EAbortS msg
           | uu____5102 ->
               let print7 =
                 let uu____5104 =
                   let uu____5105 =
                     let uu____5106 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____5106
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____5105  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____5104
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
                  FStar_Extraction_ML_Syntax.mlty = uu____5112;
                  FStar_Extraction_ML_Syntax.loc = uu____5113;_},uu____5114);
             FStar_Extraction_ML_Syntax.mlty = uu____5115;
             FStar_Extraction_ML_Syntax.loc = uu____5116;_},e1::e2::[])
          when
          ((let uu____5127 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5127 = "FStar.Buffer.index") ||
             (let uu____5129 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5129 = "FStar.Buffer.op_Array_Access"))
            ||
            (let uu____5131 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5131 = "LowStar.Buffer.index")
          ->
          let uu____5132 =
            let uu____5137 = translate_expr env e1  in
            let uu____5138 = translate_expr env e2  in
            (uu____5137, uu____5138)  in
          EBufRead uu____5132
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
             FStar_Extraction_ML_Syntax.loc = uu____5144;_},e1::[])
          when
          let uu____5152 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5152 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____5153 =
            let uu____5158 = translate_expr env e1  in
            (uu____5158, (EConstant (UInt32, "0")))  in
          EBufRead uu____5153
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
             FStar_Extraction_ML_Syntax.loc = uu____5164;_},e1::e2::[])
          when
          (let uu____5175 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5175 = "FStar.Buffer.create") ||
            (let uu____5177 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5177 = "LowStar.Buffer.alloca")
          ->
          let uu____5178 =
            let uu____5185 = translate_expr env e1  in
            let uu____5186 = translate_expr env e2  in
            (Stack, uu____5185, uu____5186)  in
          EBufCreate uu____5178
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5188;
                  FStar_Extraction_ML_Syntax.loc = uu____5189;_},uu____5190);
             FStar_Extraction_ML_Syntax.mlty = uu____5191;
             FStar_Extraction_ML_Syntax.loc = uu____5192;_},init1::[])
          when
          let uu____5200 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5200 = "FStar.HyperStack.ST.salloc" ->
          let uu____5201 =
            let uu____5208 = translate_expr env init1  in
            (Stack, uu____5208, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5201
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5210;
                  FStar_Extraction_ML_Syntax.loc = uu____5211;_},uu____5212);
             FStar_Extraction_ML_Syntax.mlty = uu____5213;
             FStar_Extraction_ML_Syntax.loc = uu____5214;_},e2::[])
          when
          (let uu____5224 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5224 = "FStar.Buffer.createL") ||
            (let uu____5226 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5226 = "LowStar.Buffer.alloca_of_list")
          ->
          let rec list_elements acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____5256 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a list literal!"
             in
          let list_elements1 = list_elements []  in
          let uu____5266 =
            let uu____5273 =
              let uu____5276 = list_elements1 e2  in
              FStar_List.map (translate_expr env) uu____5276  in
            (Stack, uu____5273)  in
          EBufCreateL uu____5266
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5282;
                  FStar_Extraction_ML_Syntax.loc = uu____5283;_},uu____5284);
             FStar_Extraction_ML_Syntax.mlty = uu____5285;
             FStar_Extraction_ML_Syntax.loc = uu____5286;_},_rid::init1::[])
          when
          let uu____5295 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5295 = "FStar.HyperStack.ST.ralloc" ->
          let uu____5296 =
            let uu____5303 = translate_expr env init1  in
            (Eternal, uu____5303, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5296
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5305;
                  FStar_Extraction_ML_Syntax.loc = uu____5306;_},uu____5307);
             FStar_Extraction_ML_Syntax.mlty = uu____5308;
             FStar_Extraction_ML_Syntax.loc = uu____5309;_},_e0::e1::e2::[])
          when
          (let uu____5321 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5321 = "FStar.Buffer.rcreate") ||
            (let uu____5323 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5323 = "LowStar.Buffer.gcmalloc")
          ->
          let uu____5324 =
            let uu____5331 = translate_expr env e1  in
            let uu____5332 = translate_expr env e2  in
            (Eternal, uu____5331, uu____5332)  in
          EBufCreate uu____5324
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5334;
                  FStar_Extraction_ML_Syntax.loc = uu____5335;_},uu____5336);
             FStar_Extraction_ML_Syntax.mlty = uu____5337;
             FStar_Extraction_ML_Syntax.loc = uu____5338;_},_rid::init1::[])
          when
          let uu____5347 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5347 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____5348 =
            let uu____5355 = translate_expr env init1  in
            (ManuallyManaged, uu____5355, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5348
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5357;
                  FStar_Extraction_ML_Syntax.loc = uu____5358;_},uu____5359);
             FStar_Extraction_ML_Syntax.mlty = uu____5360;
             FStar_Extraction_ML_Syntax.loc = uu____5361;_},_e0::e1::e2::[])
          when
          (let uu____5373 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5373 = "FStar.Buffer.rcreate_mm") ||
            (let uu____5375 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5375 = "LowStar.Buffer.malloc")
          ->
          let uu____5376 =
            let uu____5383 = translate_expr env e1  in
            let uu____5384 = translate_expr env e2  in
            (ManuallyManaged, uu____5383, uu____5384)  in
          EBufCreate uu____5376
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5386;
                  FStar_Extraction_ML_Syntax.loc = uu____5387;_},uu____5388);
             FStar_Extraction_ML_Syntax.mlty = uu____5389;
             FStar_Extraction_ML_Syntax.loc = uu____5390;_},e2::[])
          when
          let uu____5398 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5398 = "FStar.HyperStack.ST.rfree" ->
          let uu____5399 = translate_expr env e2  in EBufFree uu____5399
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5401;
                  FStar_Extraction_ML_Syntax.loc = uu____5402;_},uu____5403);
             FStar_Extraction_ML_Syntax.mlty = uu____5404;
             FStar_Extraction_ML_Syntax.loc = uu____5405;_},e2::[])
          when
          (let uu____5415 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5415 = "FStar.Buffer.rfree") ||
            (let uu____5417 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5417 = "LowStar.Buffer.free")
          -> let uu____5418 = translate_expr env e2  in EBufFree uu____5418
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5420;
                  FStar_Extraction_ML_Syntax.loc = uu____5421;_},uu____5422);
             FStar_Extraction_ML_Syntax.mlty = uu____5423;
             FStar_Extraction_ML_Syntax.loc = uu____5424;_},e1::e2::_e3::[])
          when
          (let uu____5436 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5436 = "FStar.Buffer.sub") ||
            (let uu____5438 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5438 = "LowStar.Buffer.sub")
          ->
          let uu____5439 =
            let uu____5444 = translate_expr env e1  in
            let uu____5445 = translate_expr env e2  in
            (uu____5444, uu____5445)  in
          EBufSub uu____5439
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5447;
                  FStar_Extraction_ML_Syntax.loc = uu____5448;_},uu____5449);
             FStar_Extraction_ML_Syntax.mlty = uu____5450;
             FStar_Extraction_ML_Syntax.loc = uu____5451;_},e1::e2::[])
          when
          let uu____5460 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5460 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5462;
                  FStar_Extraction_ML_Syntax.loc = uu____5463;_},uu____5464);
             FStar_Extraction_ML_Syntax.mlty = uu____5465;
             FStar_Extraction_ML_Syntax.loc = uu____5466;_},e1::e2::[])
          when
          (let uu____5477 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5477 = "FStar.Buffer.offset") ||
            (let uu____5479 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5479 = "LowStar.Buffer.offset")
          ->
          let uu____5480 =
            let uu____5485 = translate_expr env e1  in
            let uu____5486 = translate_expr env e2  in
            (uu____5485, uu____5486)  in
          EBufSub uu____5480
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5488;
                  FStar_Extraction_ML_Syntax.loc = uu____5489;_},uu____5490);
             FStar_Extraction_ML_Syntax.mlty = uu____5491;
             FStar_Extraction_ML_Syntax.loc = uu____5492;_},e1::e2::e3::[])
          when
          ((let uu____5504 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5504 = "FStar.Buffer.upd") ||
             (let uu____5506 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5506 = "FStar.Buffer.op_Array_Assignment"))
            ||
            (let uu____5508 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5508 = "LowStar.Buffer.upd")
          ->
          let uu____5509 =
            let uu____5516 = translate_expr env e1  in
            let uu____5517 = translate_expr env e2  in
            let uu____5518 = translate_expr env e3  in
            (uu____5516, uu____5517, uu____5518)  in
          EBufWrite uu____5509
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5520;
                  FStar_Extraction_ML_Syntax.loc = uu____5521;_},uu____5522);
             FStar_Extraction_ML_Syntax.mlty = uu____5523;
             FStar_Extraction_ML_Syntax.loc = uu____5524;_},e1::e2::[])
          when
          let uu____5533 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5533 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5534 =
            let uu____5541 = translate_expr env e1  in
            let uu____5542 = translate_expr env e2  in
            (uu____5541, (EConstant (UInt32, "0")), uu____5542)  in
          EBufWrite uu____5534
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5544;
             FStar_Extraction_ML_Syntax.loc = uu____5545;_},uu____5546::[])
          when
          let uu____5549 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5549 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5551;
             FStar_Extraction_ML_Syntax.loc = uu____5552;_},uu____5553::[])
          when
          let uu____5556 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5556 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5558;
                  FStar_Extraction_ML_Syntax.loc = uu____5559;_},uu____5560);
             FStar_Extraction_ML_Syntax.mlty = uu____5561;
             FStar_Extraction_ML_Syntax.loc = uu____5562;_},e1::e2::e3::e4::e5::[])
          when
          let uu____5574 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5574 = "FStar.Buffer.blit" ->
          let uu____5575 =
            let uu____5586 = translate_expr env e1  in
            let uu____5587 = translate_expr env e2  in
            let uu____5588 = translate_expr env e3  in
            let uu____5589 = translate_expr env e4  in
            let uu____5590 = translate_expr env e5  in
            (uu____5586, uu____5587, uu____5588, uu____5589, uu____5590)  in
          EBufBlit uu____5575
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5592;
                  FStar_Extraction_ML_Syntax.loc = uu____5593;_},uu____5594);
             FStar_Extraction_ML_Syntax.mlty = uu____5595;
             FStar_Extraction_ML_Syntax.loc = uu____5596;_},e1::e2::e3::[])
          when
          let uu____5606 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5606 = "FStar.Buffer.fill" ->
          let uu____5607 =
            let uu____5614 = translate_expr env e1  in
            let uu____5615 = translate_expr env e2  in
            let uu____5616 = translate_expr env e3  in
            (uu____5614, uu____5615, uu____5616)  in
          EBufFill uu____5607
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5618;
             FStar_Extraction_ML_Syntax.loc = uu____5619;_},uu____5620::[])
          when
          let uu____5623 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5623 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5625;
             FStar_Extraction_ML_Syntax.loc = uu____5626;_},e1::[])
          when
          let uu____5630 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5630 = "Obj.repr" ->
          let uu____5631 =
            let uu____5636 = translate_expr env e1  in (uu____5636, TAny)  in
          ECast uu____5631
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5639;
             FStar_Extraction_ML_Syntax.loc = uu____5640;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5648 = FStar_Util.must (mk_width m)  in
          let uu____5649 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____5648 uu____5649 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5651;
             FStar_Extraction_ML_Syntax.loc = uu____5652;_},args)
          when is_bool_op op ->
          let uu____5660 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____5660 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5662;
             FStar_Extraction_ML_Syntax.loc = uu____5663;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5665;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5666;_}::[])
          when is_machine_int m ->
          let uu____5681 =
            let uu____5686 = FStar_Util.must (mk_width m)  in (uu____5686, c)
             in
          EConstant uu____5681
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5688;
             FStar_Extraction_ML_Syntax.loc = uu____5689;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5691;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5692;_}::[])
          when is_machine_int m ->
          let uu____5707 =
            let uu____5712 = FStar_Util.must (mk_width m)  in (uu____5712, c)
             in
          EConstant uu____5707
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5713;
             FStar_Extraction_ML_Syntax.loc = uu____5714;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5716;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5717;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5723 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5724;
             FStar_Extraction_ML_Syntax.loc = uu____5725;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5727;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5728;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5734 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5736;
             FStar_Extraction_ML_Syntax.loc = uu____5737;_},arg::[])
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
            let uu____5744 =
              let uu____5749 = translate_expr env arg  in
              (uu____5749, (TInt UInt64))  in
            ECast uu____5744
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5751 =
                 let uu____5756 = translate_expr env arg  in
                 (uu____5756, (TInt UInt32))  in
               ECast uu____5751)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5758 =
                   let uu____5763 = translate_expr env arg  in
                   (uu____5763, (TInt UInt16))  in
                 ECast uu____5758)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5765 =
                     let uu____5770 = translate_expr env arg  in
                     (uu____5770, (TInt UInt8))  in
                   ECast uu____5765)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5772 =
                       let uu____5777 = translate_expr env arg  in
                       (uu____5777, (TInt Int64))  in
                     ECast uu____5772)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5779 =
                         let uu____5784 = translate_expr env arg  in
                         (uu____5784, (TInt Int32))  in
                       ECast uu____5779)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5786 =
                           let uu____5791 = translate_expr env arg  in
                           (uu____5791, (TInt Int16))  in
                         ECast uu____5786)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5793 =
                             let uu____5798 = translate_expr env arg  in
                             (uu____5798, (TInt Int8))  in
                           ECast uu____5793)
                        else
                          (let uu____5800 =
                             let uu____5807 =
                               let uu____5810 = translate_expr env arg  in
                               [uu____5810]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5807)
                              in
                           EApp uu____5800)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5821 =
            let uu____5828 = translate_expr env head1  in
            let uu____5829 = FStar_List.map (translate_expr env) args  in
            (uu____5828, uu____5829)  in
          EApp uu____5821
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5840 =
            let uu____5847 = translate_expr env head1  in
            let uu____5848 = FStar_List.map (translate_type env) ty_args  in
            (uu____5847, uu____5848)  in
          ETypApp uu____5840
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5856 =
            let uu____5861 = translate_expr env e1  in
            let uu____5862 = translate_type env t_to  in
            (uu____5861, uu____5862)  in
          ECast uu____5856
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5863,fields) ->
          let uu____5881 =
            let uu____5892 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5893 =
              FStar_List.map
                (fun uu____5912  ->
                   match uu____5912 with
                   | (field,expr) ->
                       let uu____5923 = translate_expr env expr  in
                       (field, uu____5923)) fields
               in
            (uu____5892, uu____5893)  in
          EFlat uu____5881
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5932 =
            let uu____5939 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____5940 = translate_expr env e1  in
            (uu____5939, uu____5940, (FStar_Pervasives_Native.snd path))  in
          EField uu____5932
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5943 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5955) ->
          let uu____5960 =
            let uu____5961 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5961
             in
          failwith uu____5960
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5967 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____5967
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5973 = FStar_List.map (translate_expr env) es  in
          ETuple uu____5973
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5976,cons1),es) ->
          let uu____5987 =
            let uu____5996 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5997 = FStar_List.map (translate_expr env) es  in
            (uu____5996, cons1, uu____5997)  in
          ECons uu____5987
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____6020 =
            let uu____6029 = translate_expr env1 body  in
            let uu____6030 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____6029, uu____6030)  in
          EFun uu____6020
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____6040 =
            let uu____6047 = translate_expr env e1  in
            let uu____6048 = translate_expr env e2  in
            let uu____6049 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____6047, uu____6048, uu____6049)  in
          EIfThenElse uu____6040
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____6051 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____6058 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____6073 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____6088 =
              let uu____6101 = FStar_List.map (translate_type env) ts  in
              (lid, uu____6101)  in
            TApp uu____6088
          else TQualified lid
      | uu____6113 -> failwith "invalid argument: assert_lid"

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
    fun uu____6139  ->
      match uu____6139 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____6165 = translate_pat env pat  in
            (match uu____6165 with
             | (env1,pat1) ->
                 let uu____6176 = translate_expr env1 expr  in
                 (pat1, uu____6176))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___264_6182  ->
    match uu___264_6182 with
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
          let uu____6246 =
            let uu____6247 =
              let uu____6252 = translate_width sw  in (uu____6252, s)  in
            PConstant uu____6247  in
          (env, uu____6246)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in (env1, (PVar { name; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____6256,cons1),ps) ->
          let uu____6267 =
            FStar_List.fold_left
              (fun uu____6287  ->
                 fun p1  ->
                   match uu____6287 with
                   | (env1,acc) ->
                       let uu____6307 = translate_pat env1 p1  in
                       (match uu____6307 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6267 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____6336,ps) ->
          let uu____6354 =
            FStar_List.fold_left
              (fun uu____6388  ->
                 fun uu____6389  ->
                   match (uu____6388, uu____6389) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____6458 = translate_pat env1 p1  in
                       (match uu____6458 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____6354 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____6520 =
            FStar_List.fold_left
              (fun uu____6540  ->
                 fun p1  ->
                   match uu____6540 with
                   | (env1,acc) ->
                       let uu____6560 = translate_pat env1 p1  in
                       (match uu____6560 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6520 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6587 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6592 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____6603 =
            let uu____6604 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____6604
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____6603
          then
            let uu____6616 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____6616
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6629) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6644 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6645 ->
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
          let uu____6665 =
            let uu____6672 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____6672)  in
          EApp uu____6665
