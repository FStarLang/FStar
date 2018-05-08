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
  fun uu___62_3105  ->
    match uu___62_3105 with
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
  fun uu___63_3115  ->
    match uu___63_3115 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____3118 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___64_3132  ->
    match uu___64_3132 with
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
      let uu___69_3255 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___69_3255.names_t);
        module_name = (uu___69_3255.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___70_3266 = env  in
      {
        names = (uu___70_3266.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___70_3266.module_name)
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
      (fun uu___65_3720  ->
         match uu___65_3720 with
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
                   (fun uu___66_3790  ->
                      match uu___66_3790 with
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
               let rec find_return_type eff i uu___67_3818 =
                 match uu___67_3818 with
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
                            "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
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
                                  "Error while extracting %s to KreMLin (%s)\n"
                                  uu____3948 msg
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
                   (fun uu___66_3993  ->
                      match uu___66_3993 with
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
               let rec find_return_type eff i uu___67_4021 =
                 match uu___67_4021 with
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
                            "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
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
                                  "Error while extracting %s to KreMLin (%s)\n"
                                  uu____4151 msg
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
                           "Error extracting %s to KreMLin (%s)\n" uu____4223
                           uu____4224
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
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
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
      let uu____4258 = ty  in
      match uu____4258 with
      | (uu____4261,uu____4262,uu____4263,uu____4264,flags1,uu____4266) ->
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
                   (let uu____4311 =
                      let uu____4312 =
                        let uu____4329 = translate_flags flags2  in
                        let uu____4332 = translate_type env1 t  in
                        (name1, uu____4329, (FStar_List.length args),
                          uu____4332)
                         in
                      DTypeAlias uu____4312  in
                    FStar_Pervasives_Native.Some uu____4311)
             | (uu____4341,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____4373 =
                   let uu____4374 =
                     let uu____4401 = translate_flags flags2  in
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
                     (name1, uu____4401, (FStar_List.length args),
                       uu____4404)
                      in
                   DTypeFlat uu____4374  in
                 FStar_Pervasives_Native.Some uu____4373
             | (uu____4474,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags3 = translate_flags flags2  in
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
                                             let uu____4676 =
                                               translate_type env1 t  in
                                             (uu____4676, false)  in
                                           (name2, uu____4671)) ts
                                   in
                                (cons1, uu____4629)) branches
                        in
                     (name1, flags3, (FStar_List.length args), uu____4545)
                      in
                   DTypeVariant uu____4512  in
                 FStar_Pervasives_Native.Some uu____4511
             | (uu____4715,name,_mangled_name,uu____4718,uu____4719,uu____4720)
                 ->
                 ((let uu____4730 =
                     let uu____4735 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____4735)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____4730);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
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
          let uu____4763 = FStar_Util.must (mk_width m)  in TInt uu____4763
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4769 = FStar_Util.must (mk_width m)  in TInt uu____4769
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4774 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4774 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____4775::arg::uu____4777::[],p) when
          (((let uu____4783 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4783 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____4785 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4785 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____4787 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4787 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____4789 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4789 = "FStar.HyperStack.ST.s_mref")
          -> let uu____4790 = translate_type env arg  in TBuf uu____4790
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____4792::[],p) when
          ((((((((((let uu____4798 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4798 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____4800 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4800 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____4802 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4802 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____4804 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4804 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____4806 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4806 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____4808 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4808 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____4810 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4810 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____4812 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4812 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____4814 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4814 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____4816 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4816 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____4818 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4818 = "FStar.HyperStack.ST.mmmref")
          -> let uu____4819 = translate_type env arg  in TBuf uu____4819
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          ((((((((((let uu____4826 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4826 = "FStar.Buffer.buffer") ||
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
          (let uu____5127 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5127 = "FStar.Buffer.index") ||
            (let uu____5129 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5129 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____5130 =
            let uu____5135 = translate_expr env e1  in
            let uu____5136 = translate_expr env e2  in
            (uu____5135, uu____5136)  in
          EBufRead uu____5130
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
             FStar_Extraction_ML_Syntax.loc = uu____5142;_},e1::[])
          when
          let uu____5150 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5150 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____5151 =
            let uu____5156 = translate_expr env e1  in
            (uu____5156, (EConstant (UInt32, "0")))  in
          EBufRead uu____5151
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5158;
                  FStar_Extraction_ML_Syntax.loc = uu____5159;_},uu____5160);
             FStar_Extraction_ML_Syntax.mlty = uu____5161;
             FStar_Extraction_ML_Syntax.loc = uu____5162;_},e1::e2::[])
          when
          let uu____5171 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5171 = "FStar.Buffer.create" ->
          let uu____5172 =
            let uu____5179 = translate_expr env e1  in
            let uu____5180 = translate_expr env e2  in
            (Stack, uu____5179, uu____5180)  in
          EBufCreate uu____5172
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
             FStar_Extraction_ML_Syntax.loc = uu____5186;_},init1::[])
          when
          let uu____5194 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5194 = "FStar.HyperStack.ST.salloc" ->
          let uu____5195 =
            let uu____5202 = translate_expr env init1  in
            (Stack, uu____5202, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5195
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5204;
                  FStar_Extraction_ML_Syntax.loc = uu____5205;_},uu____5206);
             FStar_Extraction_ML_Syntax.mlty = uu____5207;
             FStar_Extraction_ML_Syntax.loc = uu____5208;_},e2::[])
          when
          let uu____5216 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5216 = "FStar.Buffer.createL" ->
          let rec list_elements acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____5246 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a list literal!"
             in
          let list_elements1 = list_elements []  in
          let uu____5256 =
            let uu____5263 =
              let uu____5266 = list_elements1 e2  in
              FStar_List.map (translate_expr env) uu____5266  in
            (Stack, uu____5263)  in
          EBufCreateL uu____5256
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5272;
                  FStar_Extraction_ML_Syntax.loc = uu____5273;_},uu____5274);
             FStar_Extraction_ML_Syntax.mlty = uu____5275;
             FStar_Extraction_ML_Syntax.loc = uu____5276;_},_rid::init1::[])
          when
          let uu____5285 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5285 = "FStar.HyperStack.ST.ralloc" ->
          let uu____5286 =
            let uu____5293 = translate_expr env init1  in
            (Eternal, uu____5293, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5286
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5295;
                  FStar_Extraction_ML_Syntax.loc = uu____5296;_},uu____5297);
             FStar_Extraction_ML_Syntax.mlty = uu____5298;
             FStar_Extraction_ML_Syntax.loc = uu____5299;_},_e0::e1::e2::[])
          when
          let uu____5309 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5309 = "FStar.Buffer.rcreate" ->
          let uu____5310 =
            let uu____5317 = translate_expr env e1  in
            let uu____5318 = translate_expr env e2  in
            (Eternal, uu____5317, uu____5318)  in
          EBufCreate uu____5310
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5320;
                  FStar_Extraction_ML_Syntax.loc = uu____5321;_},uu____5322);
             FStar_Extraction_ML_Syntax.mlty = uu____5323;
             FStar_Extraction_ML_Syntax.loc = uu____5324;_},_rid::init1::[])
          when
          let uu____5333 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5333 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____5334 =
            let uu____5341 = translate_expr env init1  in
            (ManuallyManaged, uu____5341, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5334
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5343;
                  FStar_Extraction_ML_Syntax.loc = uu____5344;_},uu____5345);
             FStar_Extraction_ML_Syntax.mlty = uu____5346;
             FStar_Extraction_ML_Syntax.loc = uu____5347;_},_e0::e1::e2::[])
          when
          let uu____5357 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5357 = "FStar.Buffer.rcreate_mm" ->
          let uu____5358 =
            let uu____5365 = translate_expr env e1  in
            let uu____5366 = translate_expr env e2  in
            (ManuallyManaged, uu____5365, uu____5366)  in
          EBufCreate uu____5358
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5368;
                  FStar_Extraction_ML_Syntax.loc = uu____5369;_},uu____5370);
             FStar_Extraction_ML_Syntax.mlty = uu____5371;
             FStar_Extraction_ML_Syntax.loc = uu____5372;_},e2::[])
          when
          let uu____5380 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5380 = "FStar.HyperStack.ST.rfree" ->
          let uu____5381 = translate_expr env e2  in EBufFree uu____5381
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5383;
                  FStar_Extraction_ML_Syntax.loc = uu____5384;_},uu____5385);
             FStar_Extraction_ML_Syntax.mlty = uu____5386;
             FStar_Extraction_ML_Syntax.loc = uu____5387;_},e2::[])
          when
          let uu____5395 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5395 = "FStar.Buffer.rfree" ->
          let uu____5396 = translate_expr env e2  in EBufFree uu____5396
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5398;
                  FStar_Extraction_ML_Syntax.loc = uu____5399;_},uu____5400);
             FStar_Extraction_ML_Syntax.mlty = uu____5401;
             FStar_Extraction_ML_Syntax.loc = uu____5402;_},e1::e2::_e3::[])
          when
          let uu____5412 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5412 = "FStar.Buffer.sub" ->
          let uu____5413 =
            let uu____5418 = translate_expr env e1  in
            let uu____5419 = translate_expr env e2  in
            (uu____5418, uu____5419)  in
          EBufSub uu____5413
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
             FStar_Extraction_ML_Syntax.loc = uu____5425;_},e1::e2::[])
          when
          let uu____5434 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5434 = "FStar.Buffer.join" -> translate_expr env e1
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
             FStar_Extraction_ML_Syntax.loc = uu____5440;_},e1::e2::[])
          when
          let uu____5449 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5449 = "FStar.Buffer.offset" ->
          let uu____5450 =
            let uu____5455 = translate_expr env e1  in
            let uu____5456 = translate_expr env e2  in
            (uu____5455, uu____5456)  in
          EBufSub uu____5450
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5458;
                  FStar_Extraction_ML_Syntax.loc = uu____5459;_},uu____5460);
             FStar_Extraction_ML_Syntax.mlty = uu____5461;
             FStar_Extraction_ML_Syntax.loc = uu____5462;_},e1::e2::e3::[])
          when
          (let uu____5474 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5474 = "FStar.Buffer.upd") ||
            (let uu____5476 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5476 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____5477 =
            let uu____5484 = translate_expr env e1  in
            let uu____5485 = translate_expr env e2  in
            let uu____5486 = translate_expr env e3  in
            (uu____5484, uu____5485, uu____5486)  in
          EBufWrite uu____5477
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
             FStar_Extraction_ML_Syntax.loc = uu____5492;_},e1::e2::[])
          when
          let uu____5501 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5501 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5502 =
            let uu____5509 = translate_expr env e1  in
            let uu____5510 = translate_expr env e2  in
            (uu____5509, (EConstant (UInt32, "0")), uu____5510)  in
          EBufWrite uu____5502
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5512;
             FStar_Extraction_ML_Syntax.loc = uu____5513;_},uu____5514::[])
          when
          let uu____5517 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5517 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5519;
             FStar_Extraction_ML_Syntax.loc = uu____5520;_},uu____5521::[])
          when
          let uu____5524 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5524 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
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
             FStar_Extraction_ML_Syntax.loc = uu____5530;_},e1::e2::e3::e4::e5::[])
          when
          let uu____5542 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5542 = "FStar.Buffer.blit" ->
          let uu____5543 =
            let uu____5554 = translate_expr env e1  in
            let uu____5555 = translate_expr env e2  in
            let uu____5556 = translate_expr env e3  in
            let uu____5557 = translate_expr env e4  in
            let uu____5558 = translate_expr env e5  in
            (uu____5554, uu____5555, uu____5556, uu____5557, uu____5558)  in
          EBufBlit uu____5543
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5560;
                  FStar_Extraction_ML_Syntax.loc = uu____5561;_},uu____5562);
             FStar_Extraction_ML_Syntax.mlty = uu____5563;
             FStar_Extraction_ML_Syntax.loc = uu____5564;_},e1::e2::e3::[])
          when
          let uu____5574 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5574 = "FStar.Buffer.fill" ->
          let uu____5575 =
            let uu____5582 = translate_expr env e1  in
            let uu____5583 = translate_expr env e2  in
            let uu____5584 = translate_expr env e3  in
            (uu____5582, uu____5583, uu____5584)  in
          EBufFill uu____5575
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5586;
             FStar_Extraction_ML_Syntax.loc = uu____5587;_},uu____5588::[])
          when
          let uu____5591 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5591 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5593;
             FStar_Extraction_ML_Syntax.loc = uu____5594;_},e1::[])
          when
          let uu____5598 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5598 = "Obj.repr" ->
          let uu____5599 =
            let uu____5604 = translate_expr env e1  in (uu____5604, TAny)  in
          ECast uu____5599
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5607;
             FStar_Extraction_ML_Syntax.loc = uu____5608;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5616 = FStar_Util.must (mk_width m)  in
          let uu____5617 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____5616 uu____5617 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5619;
             FStar_Extraction_ML_Syntax.loc = uu____5620;_},args)
          when is_bool_op op ->
          let uu____5628 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____5628 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5630;
             FStar_Extraction_ML_Syntax.loc = uu____5631;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5633;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5634;_}::[])
          when is_machine_int m ->
          let uu____5649 =
            let uu____5654 = FStar_Util.must (mk_width m)  in (uu____5654, c)
             in
          EConstant uu____5649
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5656;
             FStar_Extraction_ML_Syntax.loc = uu____5657;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5659;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5660;_}::[])
          when is_machine_int m ->
          let uu____5675 =
            let uu____5680 = FStar_Util.must (mk_width m)  in (uu____5680, c)
             in
          EConstant uu____5675
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5681;
             FStar_Extraction_ML_Syntax.loc = uu____5682;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5684;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5685;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5691 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5692;
             FStar_Extraction_ML_Syntax.loc = uu____5693;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5695;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5696;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5702 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5704;
             FStar_Extraction_ML_Syntax.loc = uu____5705;_},arg::[])
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
            let uu____5712 =
              let uu____5717 = translate_expr env arg  in
              (uu____5717, (TInt UInt64))  in
            ECast uu____5712
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5719 =
                 let uu____5724 = translate_expr env arg  in
                 (uu____5724, (TInt UInt32))  in
               ECast uu____5719)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5726 =
                   let uu____5731 = translate_expr env arg  in
                   (uu____5731, (TInt UInt16))  in
                 ECast uu____5726)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5733 =
                     let uu____5738 = translate_expr env arg  in
                     (uu____5738, (TInt UInt8))  in
                   ECast uu____5733)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5740 =
                       let uu____5745 = translate_expr env arg  in
                       (uu____5745, (TInt Int64))  in
                     ECast uu____5740)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5747 =
                         let uu____5752 = translate_expr env arg  in
                         (uu____5752, (TInt Int32))  in
                       ECast uu____5747)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5754 =
                           let uu____5759 = translate_expr env arg  in
                           (uu____5759, (TInt Int16))  in
                         ECast uu____5754)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5761 =
                             let uu____5766 = translate_expr env arg  in
                             (uu____5766, (TInt Int8))  in
                           ECast uu____5761)
                        else
                          (let uu____5768 =
                             let uu____5775 =
                               let uu____5778 = translate_expr env arg  in
                               [uu____5778]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5775)
                              in
                           EApp uu____5768)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5789 =
            let uu____5796 = translate_expr env head1  in
            let uu____5797 = FStar_List.map (translate_expr env) args  in
            (uu____5796, uu____5797)  in
          EApp uu____5789
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5808 =
            let uu____5815 = translate_expr env head1  in
            let uu____5816 = FStar_List.map (translate_type env) ty_args  in
            (uu____5815, uu____5816)  in
          ETypApp uu____5808
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5824 =
            let uu____5829 = translate_expr env e1  in
            let uu____5830 = translate_type env t_to  in
            (uu____5829, uu____5830)  in
          ECast uu____5824
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5831,fields) ->
          let uu____5849 =
            let uu____5860 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5861 =
              FStar_List.map
                (fun uu____5880  ->
                   match uu____5880 with
                   | (field,expr) ->
                       let uu____5891 = translate_expr env expr  in
                       (field, uu____5891)) fields
               in
            (uu____5860, uu____5861)  in
          EFlat uu____5849
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5900 =
            let uu____5907 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____5908 = translate_expr env e1  in
            (uu____5907, uu____5908, (FStar_Pervasives_Native.snd path))  in
          EField uu____5900
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5911 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5923) ->
          let uu____5928 =
            let uu____5929 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5929
             in
          failwith uu____5928
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5935 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____5935
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5941 = FStar_List.map (translate_expr env) es  in
          ETuple uu____5941
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5944,cons1),es) ->
          let uu____5955 =
            let uu____5964 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5965 = FStar_List.map (translate_expr env) es  in
            (uu____5964, cons1, uu____5965)  in
          ECons uu____5955
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____5988 =
            let uu____5997 = translate_expr env1 body  in
            let uu____5998 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____5997, uu____5998)  in
          EFun uu____5988
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____6008 =
            let uu____6015 = translate_expr env e1  in
            let uu____6016 = translate_expr env e2  in
            let uu____6017 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____6015, uu____6016, uu____6017)  in
          EIfThenElse uu____6008
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____6019 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____6026 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____6041 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____6056 =
              let uu____6069 = FStar_List.map (translate_type env) ts  in
              (lid, uu____6069)  in
            TApp uu____6056
          else TQualified lid
      | uu____6081 -> failwith "invalid argument: assert_lid"

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
    fun uu____6107  ->
      match uu____6107 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____6133 = translate_pat env pat  in
            (match uu____6133 with
             | (env1,pat1) ->
                 let uu____6144 = translate_expr env1 expr  in
                 (pat1, uu____6144))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___68_6150  ->
    match uu___68_6150 with
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
          let uu____6214 =
            let uu____6215 =
              let uu____6220 = translate_width sw  in (uu____6220, s)  in
            PConstant uu____6215  in
          (env, uu____6214)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in (env1, (PVar { name; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____6224,cons1),ps) ->
          let uu____6235 =
            FStar_List.fold_left
              (fun uu____6255  ->
                 fun p1  ->
                   match uu____6255 with
                   | (env1,acc) ->
                       let uu____6275 = translate_pat env1 p1  in
                       (match uu____6275 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6235 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____6304,ps) ->
          let uu____6322 =
            FStar_List.fold_left
              (fun uu____6356  ->
                 fun uu____6357  ->
                   match (uu____6356, uu____6357) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____6426 = translate_pat env1 p1  in
                       (match uu____6426 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____6322 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____6488 =
            FStar_List.fold_left
              (fun uu____6508  ->
                 fun p1  ->
                   match uu____6508 with
                   | (env1,acc) ->
                       let uu____6528 = translate_pat env1 p1  in
                       (match uu____6528 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6488 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6555 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6560 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____6571 =
            let uu____6572 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____6572
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____6571
          then
            let uu____6584 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____6584
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6596) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6611 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6612 ->
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
          let uu____6632 =
            let uu____6639 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____6639)  in
          EApp uu____6632
