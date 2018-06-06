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
      let uu___266_3255 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___266_3255.names_t);
        module_name = (uu___266_3255.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___267_3266 = env  in
      {
        names = (uu___267_3266.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___267_3266.module_name)
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
  fun uu____3580  ->
    match uu____3580 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3628 = m  in
               match uu____3628 with
               | (path,uu____3642,uu____3643) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____3665 = translate_module m  in
                FStar_Pervasives_Native.Some uu____3665)
             with
             | e ->
                 ((let uu____3674 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3674);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath,(FStar_Extraction_ML_Syntax.mlsig,
                                       FStar_Extraction_ML_Syntax.mlmodule)
                                       FStar_Pervasives_Native.tuple2
                                       FStar_Pervasives_Native.option,
    FStar_Extraction_ML_Syntax.mllib) FStar_Pervasives_Native.tuple3 -> 
    file)
  =
  fun uu____3675  ->
    match uu____3675 with
    | (module_name,modul,uu____3690) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____3717 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags1  ->
    FStar_List.choose
      (fun uu___261_3728  ->
         match uu___261_3728 with
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

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags1  ->
    let uu____3739 =
      FStar_List.choose
        (fun uu___262_3744  ->
           match uu___262_3744 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____3748 -> FStar_Pervasives_Native.None) flags1
       in
    match uu____3739 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____3751 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3764 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3766 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____3770) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3792;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____3795;
                FStar_Extraction_ML_Syntax.loc = uu____3796;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3798;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___263_3816  ->
                      match uu___263_3816 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____3817 -> false) meta
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
               let rec find_return_type eff i uu___264_3844 =
                 match uu___264_3844 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3849,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (eff, t)  in
               let uu____3853 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____3853 with
               | (eff,t) ->
                   let t1 = translate_type env2 t  in
                   let binders = translate_binders env2 args  in
                   let env3 = add_binders env2 args  in
                   let name1 = ((env3.module_name), name)  in
                   let cc = translate_cc meta  in
                   let meta1 =
                     match (eff, t1) with
                     | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____3888) ->
                         let uu____3889 = translate_flags meta  in
                         MustDisappear :: uu____3889
                     | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                         let uu____3892 = translate_flags meta  in
                         MustDisappear :: uu____3892
                     | uu____3895 -> translate_flags meta  in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____3904 =
                          let uu____3905 =
                            let uu____3924 = translate_type env3 t0  in
                            (cc, meta1, name1, uu____3924)  in
                          DExternal uu____3905  in
                        FStar_Pervasives_Native.Some uu____3904
                      else
                        ((let uu____3937 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1
                             in
                          FStar_Util.print1_warning
                            "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                            uu____3937);
                         FStar_Pervasives_Native.None))
                   else
                     (try
                        let body1 = translate_expr env3 body  in
                        FStar_Pervasives_Native.Some
                          (DFunction
                             (cc, meta1, (FStar_List.length tvars), t1,
                               name1, binders, body1))
                      with
                      | e ->
                          let msg = FStar_Util.print_exn e  in
                          ((let uu____3970 =
                              let uu____3975 =
                                let uu____3976 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1
                                   in
                                FStar_Util.format2
                                  "Error while extracting %s to KreMLin (%s)\n"
                                  uu____3976 msg
                                 in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____3975)
                               in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____3970);
                           (let msg1 =
                              Prims.strcat
                                "This function was not extracted:\n" msg
                               in
                            FStar_Pervasives_Native.Some
                              (DFunction
                                 (cc, meta1, (FStar_List.length tvars), t1,
                                   name1, binders, (EAbortS msg1)))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3993;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Coerce
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____3996;
                     FStar_Extraction_ML_Syntax.loc = uu____3997;_},uu____3998,uu____3999);
                FStar_Extraction_ML_Syntax.mlty = uu____4000;
                FStar_Extraction_ML_Syntax.loc = uu____4001;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4003;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___263_4021  ->
                      match uu___263_4021 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____4022 -> false) meta
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
               let rec find_return_type eff i uu___264_4049 =
                 match uu___264_4049 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____4054,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (eff, t)  in
               let uu____4058 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____4058 with
               | (eff,t) ->
                   let t1 = translate_type env2 t  in
                   let binders = translate_binders env2 args  in
                   let env3 = add_binders env2 args  in
                   let name1 = ((env3.module_name), name)  in
                   let cc = translate_cc meta  in
                   let meta1 =
                     match (eff, t1) with
                     | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____4093) ->
                         let uu____4094 = translate_flags meta  in
                         MustDisappear :: uu____4094
                     | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                         let uu____4097 = translate_flags meta  in
                         MustDisappear :: uu____4097
                     | uu____4100 -> translate_flags meta  in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____4109 =
                          let uu____4110 =
                            let uu____4129 = translate_type env3 t0  in
                            (cc, meta1, name1, uu____4129)  in
                          DExternal uu____4110  in
                        FStar_Pervasives_Native.Some uu____4109
                      else
                        ((let uu____4142 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1
                             in
                          FStar_Util.print1_warning
                            "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                            uu____4142);
                         FStar_Pervasives_Native.None))
                   else
                     (try
                        let body1 = translate_expr env3 body  in
                        FStar_Pervasives_Native.Some
                          (DFunction
                             (cc, meta1, (FStar_List.length tvars), t1,
                               name1, binders, body1))
                      with
                      | e ->
                          let msg = FStar_Util.print_exn e  in
                          ((let uu____4175 =
                              let uu____4180 =
                                let uu____4181 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1
                                   in
                                FStar_Util.format2
                                  "Error while extracting %s to KreMLin (%s)\n"
                                  uu____4181 msg
                                 in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____4180)
                               in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____4175);
                           (let msg1 =
                              Prims.strcat
                                "This function was not extracted:\n" msg
                               in
                            FStar_Pervasives_Native.Some
                              (DFunction
                                 (cc, meta1, (FStar_List.length tvars), t1,
                                   name1, binders, (EAbortS msg1)))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4198;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4201;_} ->
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
                   ((let uu____4247 =
                       let uu____4252 =
                         let uu____4253 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____4254 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____4253
                           uu____4254
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____4252)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____4247);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4265;
            FStar_Extraction_ML_Syntax.mllb_def = uu____4266;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____4267;
            FStar_Extraction_ML_Syntax.print_typ = uu____4268;_} ->
            ((let uu____4272 =
                let uu____4277 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____4277)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____4272);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____4281 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____4281
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____4288 = ty  in
      match uu____4288 with
      | (uu____4291,uu____4292,uu____4293,uu____4294,flags1,uu____4296) ->
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
                   (let uu____4341 =
                      let uu____4342 =
                        let uu____4359 = translate_flags flags2  in
                        let uu____4362 = translate_type env1 t  in
                        (name1, uu____4359, (FStar_List.length args),
                          uu____4362)
                         in
                      DTypeAlias uu____4342  in
                    FStar_Pervasives_Native.Some uu____4341)
             | (uu____4371,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____4403 =
                   let uu____4404 =
                     let uu____4431 = translate_flags flags2  in
                     let uu____4434 =
                       FStar_List.map
                         (fun uu____4461  ->
                            match uu____4461 with
                            | (f,t) ->
                                let uu____4476 =
                                  let uu____4481 = translate_type env1 t  in
                                  (uu____4481, false)  in
                                (f, uu____4476)) fields
                        in
                     (name1, uu____4431, (FStar_List.length args),
                       uu____4434)
                      in
                   DTypeFlat uu____4404  in
                 FStar_Pervasives_Native.Some uu____4403
             | (uu____4504,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags3 = translate_flags flags2  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____4541 =
                   let uu____4542 =
                     let uu____4575 =
                       FStar_List.map
                         (fun uu____4620  ->
                            match uu____4620 with
                            | (cons1,ts) ->
                                let uu____4659 =
                                  FStar_List.map
                                    (fun uu____4686  ->
                                       match uu____4686 with
                                       | (name2,t) ->
                                           let uu____4701 =
                                             let uu____4706 =
                                               translate_type env1 t  in
                                             (uu____4706, false)  in
                                           (name2, uu____4701)) ts
                                   in
                                (cons1, uu____4659)) branches
                        in
                     (name1, flags3, (FStar_List.length args), uu____4575)
                      in
                   DTypeVariant uu____4542  in
                 FStar_Pervasives_Native.Some uu____4541
             | (uu____4745,name,_mangled_name,uu____4748,uu____4749,uu____4750)
                 ->
                 ((let uu____4760 =
                     let uu____4765 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____4765)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____4760);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4769 = find_t env name  in TBound uu____4769
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4771,t2) ->
          let uu____4773 =
            let uu____4778 = translate_type env t1  in
            let uu____4779 = translate_type env t2  in
            (uu____4778, uu____4779)  in
          TArrow uu____4773
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4783 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4783 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4787 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4787 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4793 = FStar_Util.must (mk_width m)  in TInt uu____4793
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4799 = FStar_Util.must (mk_width m)  in TInt uu____4799
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4804 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4804 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____4805::arg::uu____4807::[],p) when
          (((let uu____4813 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4813 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____4815 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4815 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____4817 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4817 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____4819 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4819 = "FStar.HyperStack.ST.s_mref")
          -> let uu____4820 = translate_type env arg  in TBuf uu____4820
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____4822::[],p) when
          ((((((((((let uu____4828 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4828 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____4830 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4830 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____4832 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4832 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____4834 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4834 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____4836 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4836 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____4838 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4838 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____4840 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4840 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____4842 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4842 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____4844 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4844 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____4846 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4846 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____4848 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4848 = "FStar.HyperStack.ST.mmmref")
          -> let uu____4849 = translate_type env arg  in TBuf uu____4849
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((let uu____4856 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4856 = "LowStar.Buffer.buffer") ||
                      (let uu____4858 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____4858 = "FStar.Buffer.buffer"))
                     ||
                     (let uu____4860 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4860 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____4862 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4862 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____4864 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4864 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____4866 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4866 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____4868 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4868 = "FStar.HyperStack.mmref"))
                ||
                (let uu____4870 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4870 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____4872 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4872 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____4874 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4874 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____4876 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4876 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____4878 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4878 = "FStar.HyperStack.ST.mmref")
          -> let uu____4879 = translate_type env arg  in TBuf uu____4879
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4880::arg::[],p) when
          (let uu____4887 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4887 = "FStar.HyperStack.s_ref") ||
            (let uu____4889 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4889 = "FStar.HyperStack.ST.s_ref")
          -> let uu____4890 = translate_type env arg  in TBuf uu____4890
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4891::[],p) when
          let uu____4895 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4895 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4921 = FStar_List.map (translate_type env) args  in
          TTuple uu____4921
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4930 =
              let uu____4943 = FStar_List.map (translate_type env) args  in
              (lid, uu____4943)  in
            TApp uu____4930
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4958 = FStar_List.map (translate_type env) ts  in
          TTuple uu____4958

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
    fun uu____4974  ->
      match uu____4974 with
      | (name,typ) ->
          let uu____4981 = translate_type env typ  in
          { name; typ = uu____4981 }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____4986 = find env name  in EBound uu____4986
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4991 =
            let uu____4996 = FStar_Util.must (mk_op op)  in
            let uu____4997 = FStar_Util.must (mk_width m)  in
            (uu____4996, uu____4997)  in
          EOp uu____4991
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____5001 =
            let uu____5006 = FStar_Util.must (mk_bool_op op)  in
            (uu____5006, Bool)  in
          EOp uu____5001
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
            let uu____5025 = translate_type env typ  in
            { name; typ = uu____5025 }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____5051 =
            let uu____5062 = translate_expr env expr  in
            let uu____5063 = translate_branches env branches  in
            (uu____5062, uu____5063)  in
          EMatch uu____5051
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5077;
                  FStar_Extraction_ML_Syntax.loc = uu____5078;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____5080;
             FStar_Extraction_ML_Syntax.loc = uu____5081;_},arg::[])
          when
          let uu____5087 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5087 = "FStar.Dyn.undyn" ->
          let uu____5088 =
            let uu____5093 = translate_expr env arg  in
            let uu____5094 = translate_type env t  in
            (uu____5093, uu____5094)  in
          ECast uu____5088
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5096;
                  FStar_Extraction_ML_Syntax.loc = uu____5097;_},uu____5098);
             FStar_Extraction_ML_Syntax.mlty = uu____5099;
             FStar_Extraction_ML_Syntax.loc = uu____5100;_},uu____5101)
          when
          let uu____5110 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5110 = "Prims.admit" -> EAbort
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
             FStar_Extraction_ML_Syntax.loc = uu____5116;_},arg::[])
          when
          ((let uu____5126 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5126 = "FStar.HyperStack.All.failwith") ||
             (let uu____5128 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5128 = "FStar.Error.unexpected"))
            ||
            (let uu____5130 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5130 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____5132;
               FStar_Extraction_ML_Syntax.loc = uu____5133;_} -> EAbortS msg
           | uu____5134 ->
               let print7 =
                 let uu____5136 =
                   let uu____5137 =
                     let uu____5138 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____5138
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____5137  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____5136
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
                  FStar_Extraction_ML_Syntax.mlty = uu____5144;
                  FStar_Extraction_ML_Syntax.loc = uu____5145;_},uu____5146);
             FStar_Extraction_ML_Syntax.mlty = uu____5147;
             FStar_Extraction_ML_Syntax.loc = uu____5148;_},e1::e2::[])
          when
          ((let uu____5159 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5159 = "FStar.Buffer.index") ||
             (let uu____5161 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5161 = "FStar.Buffer.op_Array_Access"))
            ||
            (let uu____5163 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5163 = "LowStar.Buffer.index")
          ->
          let uu____5164 =
            let uu____5169 = translate_expr env e1  in
            let uu____5170 = translate_expr env e2  in
            (uu____5169, uu____5170)  in
          EBufRead uu____5164
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5172;
                  FStar_Extraction_ML_Syntax.loc = uu____5173;_},uu____5174);
             FStar_Extraction_ML_Syntax.mlty = uu____5175;
             FStar_Extraction_ML_Syntax.loc = uu____5176;_},e1::[])
          when
          let uu____5184 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5184 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____5185 =
            let uu____5190 = translate_expr env e1  in
            (uu____5190, (EConstant (UInt32, "0")))  in
          EBufRead uu____5185
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5192;
                  FStar_Extraction_ML_Syntax.loc = uu____5193;_},uu____5194);
             FStar_Extraction_ML_Syntax.mlty = uu____5195;
             FStar_Extraction_ML_Syntax.loc = uu____5196;_},e1::e2::[])
          when
          (let uu____5207 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5207 = "FStar.Buffer.create") ||
            (let uu____5209 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5209 = "LowStar.Buffer.alloca")
          ->
          let uu____5210 =
            let uu____5217 = translate_expr env e1  in
            let uu____5218 = translate_expr env e2  in
            (Stack, uu____5217, uu____5218)  in
          EBufCreate uu____5210
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5220;
                  FStar_Extraction_ML_Syntax.loc = uu____5221;_},uu____5222);
             FStar_Extraction_ML_Syntax.mlty = uu____5223;
             FStar_Extraction_ML_Syntax.loc = uu____5224;_},init1::[])
          when
          let uu____5232 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5232 = "FStar.HyperStack.ST.salloc" ->
          let uu____5233 =
            let uu____5240 = translate_expr env init1  in
            (Stack, uu____5240, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5233
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5242;
                  FStar_Extraction_ML_Syntax.loc = uu____5243;_},uu____5244);
             FStar_Extraction_ML_Syntax.mlty = uu____5245;
             FStar_Extraction_ML_Syntax.loc = uu____5246;_},e2::[])
          when
          (let uu____5256 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5256 = "FStar.Buffer.createL") ||
            (let uu____5258 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5258 = "LowStar.Buffer.alloca_of_list")
          ->
          let rec list_elements acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____5288 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a list literal!"
             in
          let list_elements1 = list_elements []  in
          let uu____5298 =
            let uu____5305 =
              let uu____5308 = list_elements1 e2  in
              FStar_List.map (translate_expr env) uu____5308  in
            (Stack, uu____5305)  in
          EBufCreateL uu____5298
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5314;
                  FStar_Extraction_ML_Syntax.loc = uu____5315;_},uu____5316);
             FStar_Extraction_ML_Syntax.mlty = uu____5317;
             FStar_Extraction_ML_Syntax.loc = uu____5318;_},_rid::init1::[])
          when
          let uu____5327 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5327 = "FStar.HyperStack.ST.ralloc" ->
          let uu____5328 =
            let uu____5335 = translate_expr env init1  in
            (Eternal, uu____5335, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5328
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5337;
                  FStar_Extraction_ML_Syntax.loc = uu____5338;_},uu____5339);
             FStar_Extraction_ML_Syntax.mlty = uu____5340;
             FStar_Extraction_ML_Syntax.loc = uu____5341;_},_e0::e1::e2::[])
          when
          (let uu____5353 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5353 = "FStar.Buffer.rcreate") ||
            (let uu____5355 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5355 = "LowStar.Buffer.gcmalloc")
          ->
          let uu____5356 =
            let uu____5363 = translate_expr env e1  in
            let uu____5364 = translate_expr env e2  in
            (Eternal, uu____5363, uu____5364)  in
          EBufCreate uu____5356
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5366;
                  FStar_Extraction_ML_Syntax.loc = uu____5367;_},uu____5368);
             FStar_Extraction_ML_Syntax.mlty = uu____5369;
             FStar_Extraction_ML_Syntax.loc = uu____5370;_},_rid::init1::[])
          when
          let uu____5379 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5379 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____5380 =
            let uu____5387 = translate_expr env init1  in
            (ManuallyManaged, uu____5387, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5380
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5389;
                  FStar_Extraction_ML_Syntax.loc = uu____5390;_},uu____5391);
             FStar_Extraction_ML_Syntax.mlty = uu____5392;
             FStar_Extraction_ML_Syntax.loc = uu____5393;_},_e0::e1::e2::[])
          when
          (let uu____5405 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5405 = "FStar.Buffer.rcreate_mm") ||
            (let uu____5407 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5407 = "LowStar.Buffer.malloc")
          ->
          let uu____5408 =
            let uu____5415 = translate_expr env e1  in
            let uu____5416 = translate_expr env e2  in
            (ManuallyManaged, uu____5415, uu____5416)  in
          EBufCreate uu____5408
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5418;
                  FStar_Extraction_ML_Syntax.loc = uu____5419;_},uu____5420);
             FStar_Extraction_ML_Syntax.mlty = uu____5421;
             FStar_Extraction_ML_Syntax.loc = uu____5422;_},e2::[])
          when
          let uu____5430 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5430 = "FStar.HyperStack.ST.rfree" ->
          let uu____5431 = translate_expr env e2  in EBufFree uu____5431
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5433;
                  FStar_Extraction_ML_Syntax.loc = uu____5434;_},uu____5435);
             FStar_Extraction_ML_Syntax.mlty = uu____5436;
             FStar_Extraction_ML_Syntax.loc = uu____5437;_},e2::[])
          when
          (let uu____5447 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5447 = "FStar.Buffer.rfree") ||
            (let uu____5449 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5449 = "LowStar.Buffer.free")
          -> let uu____5450 = translate_expr env e2  in EBufFree uu____5450
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5452;
                  FStar_Extraction_ML_Syntax.loc = uu____5453;_},uu____5454);
             FStar_Extraction_ML_Syntax.mlty = uu____5455;
             FStar_Extraction_ML_Syntax.loc = uu____5456;_},e1::e2::_e3::[])
          when
          (let uu____5468 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5468 = "FStar.Buffer.sub") ||
            (let uu____5470 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5470 = "LowStar.Buffer.sub")
          ->
          let uu____5471 =
            let uu____5476 = translate_expr env e1  in
            let uu____5477 = translate_expr env e2  in
            (uu____5476, uu____5477)  in
          EBufSub uu____5471
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5479;
                  FStar_Extraction_ML_Syntax.loc = uu____5480;_},uu____5481);
             FStar_Extraction_ML_Syntax.mlty = uu____5482;
             FStar_Extraction_ML_Syntax.loc = uu____5483;_},e1::e2::[])
          when
          let uu____5492 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5492 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5494;
                  FStar_Extraction_ML_Syntax.loc = uu____5495;_},uu____5496);
             FStar_Extraction_ML_Syntax.mlty = uu____5497;
             FStar_Extraction_ML_Syntax.loc = uu____5498;_},e1::e2::[])
          when
          (let uu____5509 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5509 = "FStar.Buffer.offset") ||
            (let uu____5511 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5511 = "LowStar.Buffer.offset")
          ->
          let uu____5512 =
            let uu____5517 = translate_expr env e1  in
            let uu____5518 = translate_expr env e2  in
            (uu____5517, uu____5518)  in
          EBufSub uu____5512
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
             FStar_Extraction_ML_Syntax.loc = uu____5524;_},e1::e2::e3::[])
          when
          ((let uu____5536 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5536 = "FStar.Buffer.upd") ||
             (let uu____5538 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5538 = "FStar.Buffer.op_Array_Assignment"))
            ||
            (let uu____5540 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5540 = "LowStar.Buffer.upd")
          ->
          let uu____5541 =
            let uu____5548 = translate_expr env e1  in
            let uu____5549 = translate_expr env e2  in
            let uu____5550 = translate_expr env e3  in
            (uu____5548, uu____5549, uu____5550)  in
          EBufWrite uu____5541
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5552;
                  FStar_Extraction_ML_Syntax.loc = uu____5553;_},uu____5554);
             FStar_Extraction_ML_Syntax.mlty = uu____5555;
             FStar_Extraction_ML_Syntax.loc = uu____5556;_},e1::e2::[])
          when
          let uu____5565 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5565 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5566 =
            let uu____5573 = translate_expr env e1  in
            let uu____5574 = translate_expr env e2  in
            (uu____5573, (EConstant (UInt32, "0")), uu____5574)  in
          EBufWrite uu____5566
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5576;
             FStar_Extraction_ML_Syntax.loc = uu____5577;_},uu____5578::[])
          when
          let uu____5581 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5581 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5583;
             FStar_Extraction_ML_Syntax.loc = uu____5584;_},uu____5585::[])
          when
          let uu____5588 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5588 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5590;
                  FStar_Extraction_ML_Syntax.loc = uu____5591;_},uu____5592);
             FStar_Extraction_ML_Syntax.mlty = uu____5593;
             FStar_Extraction_ML_Syntax.loc = uu____5594;_},e1::e2::e3::e4::e5::[])
          when
          let uu____5606 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5606 = "FStar.Buffer.blit" ->
          let uu____5607 =
            let uu____5618 = translate_expr env e1  in
            let uu____5619 = translate_expr env e2  in
            let uu____5620 = translate_expr env e3  in
            let uu____5621 = translate_expr env e4  in
            let uu____5622 = translate_expr env e5  in
            (uu____5618, uu____5619, uu____5620, uu____5621, uu____5622)  in
          EBufBlit uu____5607
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5624;
                  FStar_Extraction_ML_Syntax.loc = uu____5625;_},uu____5626);
             FStar_Extraction_ML_Syntax.mlty = uu____5627;
             FStar_Extraction_ML_Syntax.loc = uu____5628;_},e1::e2::e3::[])
          when
          let uu____5638 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5638 = "FStar.Buffer.fill" ->
          let uu____5639 =
            let uu____5646 = translate_expr env e1  in
            let uu____5647 = translate_expr env e2  in
            let uu____5648 = translate_expr env e3  in
            (uu____5646, uu____5647, uu____5648)  in
          EBufFill uu____5639
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5650;
             FStar_Extraction_ML_Syntax.loc = uu____5651;_},uu____5652::[])
          when
          let uu____5655 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5655 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5657;
             FStar_Extraction_ML_Syntax.loc = uu____5658;_},e1::[])
          when
          let uu____5662 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5662 = "Obj.repr" ->
          let uu____5663 =
            let uu____5668 = translate_expr env e1  in (uu____5668, TAny)  in
          ECast uu____5663
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5671;
             FStar_Extraction_ML_Syntax.loc = uu____5672;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5680 = FStar_Util.must (mk_width m)  in
          let uu____5681 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____5680 uu____5681 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5683;
             FStar_Extraction_ML_Syntax.loc = uu____5684;_},args)
          when is_bool_op op ->
          let uu____5692 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____5692 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
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
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5720;
             FStar_Extraction_ML_Syntax.loc = uu____5721;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5723;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5724;_}::[])
          when is_machine_int m ->
          let uu____5739 =
            let uu____5744 = FStar_Util.must (mk_width m)  in (uu____5744, c)
             in
          EConstant uu____5739
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5745;
             FStar_Extraction_ML_Syntax.loc = uu____5746;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5748;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5749;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5755 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5756;
             FStar_Extraction_ML_Syntax.loc = uu____5757;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5759;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5760;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5766 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5768;
             FStar_Extraction_ML_Syntax.loc = uu____5769;_},arg::[])
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
            let uu____5776 =
              let uu____5781 = translate_expr env arg  in
              (uu____5781, (TInt UInt64))  in
            ECast uu____5776
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5783 =
                 let uu____5788 = translate_expr env arg  in
                 (uu____5788, (TInt UInt32))  in
               ECast uu____5783)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5790 =
                   let uu____5795 = translate_expr env arg  in
                   (uu____5795, (TInt UInt16))  in
                 ECast uu____5790)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5797 =
                     let uu____5802 = translate_expr env arg  in
                     (uu____5802, (TInt UInt8))  in
                   ECast uu____5797)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5804 =
                       let uu____5809 = translate_expr env arg  in
                       (uu____5809, (TInt Int64))  in
                     ECast uu____5804)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5811 =
                         let uu____5816 = translate_expr env arg  in
                         (uu____5816, (TInt Int32))  in
                       ECast uu____5811)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5818 =
                           let uu____5823 = translate_expr env arg  in
                           (uu____5823, (TInt Int16))  in
                         ECast uu____5818)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5825 =
                             let uu____5830 = translate_expr env arg  in
                             (uu____5830, (TInt Int8))  in
                           ECast uu____5825)
                        else
                          (let uu____5832 =
                             let uu____5839 =
                               let uu____5842 = translate_expr env arg  in
                               [uu____5842]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5839)
                              in
                           EApp uu____5832)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5853 =
            let uu____5860 = translate_expr env head1  in
            let uu____5861 = FStar_List.map (translate_expr env) args  in
            (uu____5860, uu____5861)  in
          EApp uu____5853
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5872 =
            let uu____5879 = translate_expr env head1  in
            let uu____5880 = FStar_List.map (translate_type env) ty_args  in
            (uu____5879, uu____5880)  in
          ETypApp uu____5872
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5888 =
            let uu____5893 = translate_expr env e1  in
            let uu____5894 = translate_type env t_to  in
            (uu____5893, uu____5894)  in
          ECast uu____5888
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5895,fields) ->
          let uu____5913 =
            let uu____5924 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5925 =
              FStar_List.map
                (fun uu____5944  ->
                   match uu____5944 with
                   | (field,expr) ->
                       let uu____5955 = translate_expr env expr  in
                       (field, uu____5955)) fields
               in
            (uu____5924, uu____5925)  in
          EFlat uu____5913
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5964 =
            let uu____5971 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____5972 = translate_expr env e1  in
            (uu____5971, uu____5972, (FStar_Pervasives_Native.snd path))  in
          EField uu____5964
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5975 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5987) ->
          let uu____5992 =
            let uu____5993 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5993
             in
          failwith uu____5992
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5999 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____5999
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____6005 = FStar_List.map (translate_expr env) es  in
          ETuple uu____6005
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____6008,cons1),es) ->
          let uu____6019 =
            let uu____6028 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____6029 = FStar_List.map (translate_expr env) es  in
            (uu____6028, cons1, uu____6029)  in
          ECons uu____6019
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____6052 =
            let uu____6061 = translate_expr env1 body  in
            let uu____6062 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____6061, uu____6062)  in
          EFun uu____6052
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____6072 =
            let uu____6079 = translate_expr env e1  in
            let uu____6080 = translate_expr env e2  in
            let uu____6081 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____6079, uu____6080, uu____6081)  in
          EIfThenElse uu____6072
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____6083 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____6090 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____6105 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____6120 =
              let uu____6133 = FStar_List.map (translate_type env) ts  in
              (lid, uu____6133)  in
            TApp uu____6120
          else TQualified lid
      | uu____6145 -> failwith "invalid argument: assert_lid"

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
    fun uu____6171  ->
      match uu____6171 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____6197 = translate_pat env pat  in
            (match uu____6197 with
             | (env1,pat1) ->
                 let uu____6208 = translate_expr env1 expr  in
                 (pat1, uu____6208))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___265_6214  ->
    match uu___265_6214 with
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
          let uu____6278 =
            let uu____6279 =
              let uu____6284 = translate_width sw  in (uu____6284, s)  in
            PConstant uu____6279  in
          (env, uu____6278)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in (env1, (PVar { name; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____6288,cons1),ps) ->
          let uu____6299 =
            FStar_List.fold_left
              (fun uu____6319  ->
                 fun p1  ->
                   match uu____6319 with
                   | (env1,acc) ->
                       let uu____6339 = translate_pat env1 p1  in
                       (match uu____6339 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6299 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____6368,ps) ->
          let uu____6386 =
            FStar_List.fold_left
              (fun uu____6420  ->
                 fun uu____6421  ->
                   match (uu____6420, uu____6421) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____6490 = translate_pat env1 p1  in
                       (match uu____6490 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____6386 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____6552 =
            FStar_List.fold_left
              (fun uu____6572  ->
                 fun p1  ->
                   match uu____6572 with
                   | (env1,acc) ->
                       let uu____6592 = translate_pat env1 p1  in
                       (match uu____6592 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6552 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6619 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6624 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____6635 =
            let uu____6636 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____6636
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____6635
          then
            let uu____6648 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____6648
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6661) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6676 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6677 ->
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
          let uu____6697 =
            let uu____6704 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____6704)  in
          EApp uu____6697
