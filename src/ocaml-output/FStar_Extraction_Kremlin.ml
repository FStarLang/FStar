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
  | Abstract 
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
  typ: typ ;
  mut: Prims.bool }
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
    match projectee with | DGlobal _0 -> true | uu____621 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,Prims.int,typ,expr)
      FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____715 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr) FStar_Pervasives_Native.tuple7)
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____823 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,typ) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____911 -> false
  
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
    match projectee with | DExternal _0 -> true | uu____1021 -> false
  
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
    match projectee with | DTypeVariant _0 -> true | uu____1121 -> false
  
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
    match projectee with | StdCall  -> true | uu____1230 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1236 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1242 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1248 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1254 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1260 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1266 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1272 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1279 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1292 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1299 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1313 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1327 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____1340 -> false
  
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1346 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1352 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1358 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1365 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1385 -> false
  
let (__proj__EQualified__item___0 :
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1421 -> false
  
let (__proj__EConstant__item___0 :
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1446 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1459 -> false
  
let (__proj__EApp__item___0 :
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1497 -> false
  
let (__proj__ETypApp__item___0 :
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1535 -> false
  
let (__proj__ELet__item___0 :
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1573 -> false
  
let (__proj__EIfThenElse__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1607 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1631 -> false
  
let (__proj__EAssign__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____1663 -> false
  
let (__proj__EBufCreate__item___0 :
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____1699 -> false
  
let (__proj__EBufRead__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____1731 -> false
  
let (__proj__EBufWrite__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____1767 -> false
  
let (__proj__EBufSub__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____1803 -> false
  
let (__proj__EBufBlit__item___0 :
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5) =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____1857 -> false
  
let (__proj__EMatch__item___0 :
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1905 -> false
  
let (__proj__EOp__item___0 :
  expr -> (op,width) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1935 -> false
  
let (__proj__ECast__item___0 :
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1960 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1966 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1973 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1986 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1992 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1999 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____2023 -> false
  
let (__proj__EFlat__item___0 :
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____2073 -> false
  
let (__proj__EField__item___0 :
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____2109 -> false
  
let (__proj__EWhile__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____2141 -> false
  
let (__proj__EBufCreateL__item___0 :
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2175 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2203 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2247 -> false
  
let (__proj__EBufFill__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2279 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2301 -> false
  
let (__proj__EFun__item___0 :
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2339 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____2353 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____2366 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2372 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____2378 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2384 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____2390 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2396 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2402 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2408 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____2414 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____2420 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2426 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2432 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2438 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2444 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2450 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____2456 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____2462 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____2468 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____2474 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____2480 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____2486 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____2492 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____2498 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____2504 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____2510 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2516 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2523 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2537 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2557 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2591 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2617 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list)
  = fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____2653 -> false
  
let (__proj__PConstant__item___0 :
  pattern -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____2678 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2684 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2690 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2696 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2702 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2708 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2714 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2720 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2726 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____2732 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ; mut = __fname__mut;_} ->
        __fname__name
  
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ; mut = __fname__mut;_} ->
        __fname__typ
  
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ; mut = __fname__mut;_} ->
        __fname__mut
  
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____2763 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2777 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2790 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2803 -> false
  
let (__proj__TQualified__item___0 :
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2834 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2840 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2851 -> false
  
let (__proj__TArrow__item___0 :
  typ -> (typ,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2877 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2903 -> false
  
let (__proj__TApp__item___0 :
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____2955 -> false
  
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
  'Auu____3035 'Auu____3036 'Auu____3037 .
    ('Auu____3035,'Auu____3036,'Auu____3037) FStar_Pervasives_Native.tuple3
      -> 'Auu____3035
  = fun uu____3048  -> match uu____3048 with | (x,uu____3056,uu____3057) -> x 
let snd3 :
  'Auu____3066 'Auu____3067 'Auu____3068 .
    ('Auu____3066,'Auu____3067,'Auu____3068) FStar_Pervasives_Native.tuple3
      -> 'Auu____3067
  = fun uu____3079  -> match uu____3079 with | (uu____3086,x,uu____3088) -> x 
let thd3 :
  'Auu____3097 'Auu____3098 'Auu____3099 .
    ('Auu____3097,'Auu____3098,'Auu____3099) FStar_Pervasives_Native.tuple3
      -> 'Auu____3099
  = fun uu____3110  -> match uu____3110 with | (uu____3117,uu____3118,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___272_3126  ->
    match uu___272_3126 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____3129 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___273_3136  ->
    match uu___273_3136 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____3139 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___274_3153  ->
    match uu___274_3153 with
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
    | uu____3156 -> FStar_Pervasives_Native.None
  
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
      let uu___280_3276 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___280_3276.names_t);
        module_name = (uu___280_3276.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___281_3287 = env  in
      {
        names = (uu___281_3287.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___281_3287.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____3298 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____3298 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___283_3315  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___282_3320 ->
          let uu____3321 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____3321
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___285_3333  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___284_3338 ->
          let uu____3339 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____3339
  
let add_binders :
  'Auu____3346 .
    env ->
      (Prims.string,'Auu____3346) FStar_Pervasives_Native.tuple2 Prims.list
        -> env
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____3378  ->
             match uu____3378 with | (name,uu____3384) -> extend env1 name)
        env binders
  
let (list_elements :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr Prims.list)
  =
  fun e2  ->
    let rec list_elements acc e21 =
      match e21.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_CTor
          (("Prims"::[],"Cons"),hd1::tl1::[]) ->
          list_elements (hd1 :: acc) tl1
      | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
          FStar_List.rev acc
      | uu____3421 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____3636  ->
    match uu____3636 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3684 = m  in
               match uu____3684 with
               | (path,uu____3698,uu____3699) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___287_3717  ->
                  match () with
                  | () ->
                      (FStar_Util.print1
                         "Attempting to translate module %s\n" m_name;
                       (let uu____3721 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____3721))) ()
             with
             | e ->
                 ((let uu____3730 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3730);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath,(FStar_Extraction_ML_Syntax.mlsig,
                                       FStar_Extraction_ML_Syntax.mlmodule)
                                       FStar_Pervasives_Native.tuple2
                                       FStar_Pervasives_Native.option,
    FStar_Extraction_ML_Syntax.mllib) FStar_Pervasives_Native.tuple3 -> 
    file)
  =
  fun uu____3731  ->
    match uu____3731 with
    | (module_name,modul,uu____3746) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____3773 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags1  ->
    FStar_List.choose
      (fun uu___275_3784  ->
         match uu___275_3784 with
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
         | FStar_Extraction_ML_Syntax.CAbstract  ->
             FStar_Pervasives_Native.Some Abstract
         | uu____3791 -> FStar_Pervasives_Native.None) flags1

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags1  ->
    let uu____3795 =
      FStar_List.choose
        (fun uu___276_3800  ->
           match uu___276_3800 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____3804 -> FStar_Pervasives_Native.None) flags1
       in
    match uu____3795 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____3807 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3820 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3822 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____3826) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3848;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____3851;
                FStar_Extraction_ML_Syntax.loc = uu____3852;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3854;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___277_3872  ->
                      match uu___277_3872 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____3873 -> false) meta
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
               let rec find_return_type eff i uu___278_3900 =
                 match uu___278_3900 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3905,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (eff, t)  in
               let uu____3909 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____3909 with
               | (eff,t) ->
                   let t1 = translate_type env2 t  in
                   let binders = translate_binders env2 args  in
                   let env3 = add_binders env2 args  in
                   let name1 = ((env3.module_name), name)  in
                   let cc = translate_cc meta  in
                   let meta1 =
                     match (eff, t1) with
                     | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____3944) ->
                         let uu____3945 = translate_flags meta  in
                         MustDisappear :: uu____3945
                     | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                         let uu____3948 = translate_flags meta  in
                         MustDisappear :: uu____3948
                     | uu____3951 -> translate_flags meta  in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____3960 =
                          let uu____3961 =
                            let uu____3980 = translate_type env3 t0  in
                            (cc, meta1, name1, uu____3980)  in
                          DExternal uu____3961  in
                        FStar_Pervasives_Native.Some uu____3960
                      else
                        ((let uu____3993 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1
                             in
                          FStar_Util.print1_warning
                            "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                            uu____3993);
                         FStar_Pervasives_Native.None))
                   else
                     (try
                        (fun uu___289_3999  ->
                           match () with
                           | () ->
                               let body1 = translate_expr env3 body  in
                               FStar_Pervasives_Native.Some
                                 (DFunction
                                    (cc, meta1, (FStar_List.length tvars),
                                      t1, name1, binders, body1))) ()
                      with
                      | e ->
                          let msg = FStar_Util.print_exn e  in
                          ((let uu____4026 =
                              let uu____4031 =
                                let uu____4032 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1
                                   in
                                FStar_Util.format2
                                  "Error while extracting %s to KreMLin (%s)\n"
                                  uu____4032 msg
                                 in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____4031)
                               in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____4026);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4049;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Coerce
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____4052;
                     FStar_Extraction_ML_Syntax.loc = uu____4053;_},uu____4054,uu____4055);
                FStar_Extraction_ML_Syntax.mlty = uu____4056;
                FStar_Extraction_ML_Syntax.loc = uu____4057;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4059;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___277_4077  ->
                      match uu___277_4077 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____4078 -> false) meta
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
               let rec find_return_type eff i uu___278_4105 =
                 match uu___278_4105 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____4110,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (eff, t)  in
               let uu____4114 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____4114 with
               | (eff,t) ->
                   let t1 = translate_type env2 t  in
                   let binders = translate_binders env2 args  in
                   let env3 = add_binders env2 args  in
                   let name1 = ((env3.module_name), name)  in
                   let cc = translate_cc meta  in
                   let meta1 =
                     match (eff, t1) with
                     | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____4149) ->
                         let uu____4150 = translate_flags meta  in
                         MustDisappear :: uu____4150
                     | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                         let uu____4153 = translate_flags meta  in
                         MustDisappear :: uu____4153
                     | uu____4156 -> translate_flags meta  in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____4165 =
                          let uu____4166 =
                            let uu____4185 = translate_type env3 t0  in
                            (cc, meta1, name1, uu____4185)  in
                          DExternal uu____4166  in
                        FStar_Pervasives_Native.Some uu____4165
                      else
                        ((let uu____4198 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1
                             in
                          FStar_Util.print1_warning
                            "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                            uu____4198);
                         FStar_Pervasives_Native.None))
                   else
                     (try
                        (fun uu___289_4204  ->
                           match () with
                           | () ->
                               let body1 = translate_expr env3 body  in
                               FStar_Pervasives_Native.Some
                                 (DFunction
                                    (cc, meta1, (FStar_List.length tvars),
                                      t1, name1, binders, body1))) ()
                      with
                      | e ->
                          let msg = FStar_Util.print_exn e  in
                          ((let uu____4231 =
                              let uu____4236 =
                                let uu____4237 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1
                                   in
                                FStar_Util.format2
                                  "Error while extracting %s to KreMLin (%s)\n"
                                  uu____4237 msg
                                 in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____4236)
                               in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____4231);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4254;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4257;_} ->
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
                 (fun uu___291_4283  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____4303 =
                       let uu____4308 =
                         let uu____4309 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____4310 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____4309
                           uu____4310
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____4308)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____4303);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4321;
            FStar_Extraction_ML_Syntax.mllb_def = uu____4322;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____4323;
            FStar_Extraction_ML_Syntax.print_typ = uu____4324;_} ->
            ((let uu____4328 =
                let uu____4333 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____4333)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____4328);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____4337 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____4337
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____4344 = ty  in
      match uu____4344 with
      | (uu____4347,uu____4348,uu____4349,uu____4350,flags1,uu____4352) ->
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
                   (let uu____4397 =
                      let uu____4398 =
                        let uu____4415 = translate_flags flags2  in
                        let uu____4418 = translate_type env1 t  in
                        (name1, uu____4415, (FStar_List.length args),
                          uu____4418)
                         in
                      DTypeAlias uu____4398  in
                    FStar_Pervasives_Native.Some uu____4397)
             | (uu____4427,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____4459 =
                   let uu____4460 =
                     let uu____4487 = translate_flags flags2  in
                     let uu____4490 =
                       FStar_List.map
                         (fun uu____4517  ->
                            match uu____4517 with
                            | (f,t) ->
                                let uu____4532 =
                                  let uu____4537 = translate_type env1 t  in
                                  (uu____4537, false)  in
                                (f, uu____4532)) fields
                        in
                     (name1, uu____4487, (FStar_List.length args),
                       uu____4490)
                      in
                   DTypeFlat uu____4460  in
                 FStar_Pervasives_Native.Some uu____4459
             | (uu____4560,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags3 = translate_flags flags2  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____4597 =
                   let uu____4598 =
                     let uu____4631 =
                       FStar_List.map
                         (fun uu____4676  ->
                            match uu____4676 with
                            | (cons1,ts) ->
                                let uu____4715 =
                                  FStar_List.map
                                    (fun uu____4742  ->
                                       match uu____4742 with
                                       | (name2,t) ->
                                           let uu____4757 =
                                             let uu____4762 =
                                               translate_type env1 t  in
                                             (uu____4762, false)  in
                                           (name2, uu____4757)) ts
                                   in
                                (cons1, uu____4715)) branches
                        in
                     (name1, flags3, (FStar_List.length args), uu____4631)
                      in
                   DTypeVariant uu____4598  in
                 FStar_Pervasives_Native.Some uu____4597
             | (uu____4801,name,_mangled_name,uu____4804,uu____4805,uu____4806)
                 ->
                 ((let uu____4816 =
                     let uu____4821 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____4821)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____4816);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4825 = find_t env name  in TBound uu____4825
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4827,t2) ->
          let uu____4829 =
            let uu____4834 = translate_type env t1  in
            let uu____4835 = translate_type env t2  in
            (uu____4834, uu____4835)  in
          TArrow uu____4829
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4839 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4839 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4843 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4843 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4849 = FStar_Util.must (mk_width m)  in TInt uu____4849
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4855 = FStar_Util.must (mk_width m)  in TInt uu____4855
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4860 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4860 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____4861::arg::uu____4863::[],p) when
          (((let uu____4869 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4869 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____4871 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4871 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____4873 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4873 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____4875 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4875 = "FStar.HyperStack.ST.s_mref")
          -> let uu____4876 = translate_type env arg  in TBuf uu____4876
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____4878::[],p) when
          ((((((((((let uu____4884 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4884 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____4886 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4886 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____4888 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4888 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____4890 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4890 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____4892 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4892 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____4894 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4894 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____4896 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4896 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____4898 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4898 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____4900 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4900 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____4902 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4902 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____4904 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4904 = "FStar.HyperStack.ST.mmmref")
          -> let uu____4905 = translate_type env arg  in TBuf uu____4905
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((let uu____4912 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4912 = "LowStar.Buffer.buffer") ||
                      (let uu____4914 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____4914 = "FStar.Buffer.buffer"))
                     ||
                     (let uu____4916 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4916 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____4918 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4918 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____4920 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4920 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____4922 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4922 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____4924 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4924 = "FStar.HyperStack.mmref"))
                ||
                (let uu____4926 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4926 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____4928 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4928 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____4930 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4930 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____4932 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4932 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____4934 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4934 = "FStar.HyperStack.ST.mmref")
          -> let uu____4935 = translate_type env arg  in TBuf uu____4935
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4936::arg::[],p) when
          (let uu____4943 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4943 = "FStar.HyperStack.s_ref") ||
            (let uu____4945 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4945 = "FStar.HyperStack.ST.s_ref")
          -> let uu____4946 = translate_type env arg  in TBuf uu____4946
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4947::[],p) when
          let uu____4951 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4951 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4977 = FStar_List.map (translate_type env) args  in
          TTuple uu____4977
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4986 =
              let uu____4999 = FStar_List.map (translate_type env) args  in
              (lid, uu____4999)  in
            TApp uu____4986
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____5014 = FStar_List.map (translate_type env) ts  in
          TTuple uu____5014

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
    fun uu____5030  ->
      match uu____5030 with
      | (name,typ) ->
          let uu____5037 = translate_type env typ  in
          { name; typ = uu____5037; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____5042 = find env name  in EBound uu____5042
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____5047 =
            let uu____5052 = FStar_Util.must (mk_op op)  in
            let uu____5053 = FStar_Util.must (mk_width m)  in
            (uu____5052, uu____5053)  in
          EOp uu____5047
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____5057 =
            let uu____5062 = FStar_Util.must (mk_bool_op op)  in
            (uu____5062, Bool)  in
          EOp uu____5057
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
            let uu____5081 = translate_type env typ  in
            { name; typ = uu____5081; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____5107 =
            let uu____5118 = translate_expr env expr  in
            let uu____5119 = translate_branches env branches  in
            (uu____5118, uu____5119)  in
          EMatch uu____5107
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5133;
                  FStar_Extraction_ML_Syntax.loc = uu____5134;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____5136;
             FStar_Extraction_ML_Syntax.loc = uu____5137;_},arg::[])
          when
          let uu____5143 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5143 = "FStar.Dyn.undyn" ->
          let uu____5144 =
            let uu____5149 = translate_expr env arg  in
            let uu____5150 = translate_type env t  in
            (uu____5149, uu____5150)  in
          ECast uu____5144
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5152;
                  FStar_Extraction_ML_Syntax.loc = uu____5153;_},uu____5154);
             FStar_Extraction_ML_Syntax.mlty = uu____5155;
             FStar_Extraction_ML_Syntax.loc = uu____5156;_},uu____5157)
          when
          let uu____5166 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5166 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5168;
                  FStar_Extraction_ML_Syntax.loc = uu____5169;_},uu____5170);
             FStar_Extraction_ML_Syntax.mlty = uu____5171;
             FStar_Extraction_ML_Syntax.loc = uu____5172;_},arg::[])
          when
          ((let uu____5182 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5182 = "FStar.HyperStack.All.failwith") ||
             (let uu____5184 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5184 = "FStar.Error.unexpected"))
            ||
            (let uu____5186 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5186 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____5188;
               FStar_Extraction_ML_Syntax.loc = uu____5189;_} -> EAbortS msg
           | uu____5190 ->
               let print7 =
                 let uu____5192 =
                   let uu____5193 =
                     let uu____5194 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____5194
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____5193  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____5192
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
                  FStar_Extraction_ML_Syntax.mlty = uu____5200;
                  FStar_Extraction_ML_Syntax.loc = uu____5201;_},uu____5202);
             FStar_Extraction_ML_Syntax.mlty = uu____5203;
             FStar_Extraction_ML_Syntax.loc = uu____5204;_},e1::[])
          when
          (let uu____5214 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5214 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____5216 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5216 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5218;
                  FStar_Extraction_ML_Syntax.loc = uu____5219;_},uu____5220);
             FStar_Extraction_ML_Syntax.mlty = uu____5221;
             FStar_Extraction_ML_Syntax.loc = uu____5222;_},e1::e2::[])
          when
          ((let uu____5233 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5233 = "FStar.Buffer.index") ||
             (let uu____5235 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5235 = "FStar.Buffer.op_Array_Access"))
            ||
            (let uu____5237 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5237 = "LowStar.Buffer.index")
          ->
          let uu____5238 =
            let uu____5243 = translate_expr env e1  in
            let uu____5244 = translate_expr env e2  in
            (uu____5243, uu____5244)  in
          EBufRead uu____5238
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5246;
                  FStar_Extraction_ML_Syntax.loc = uu____5247;_},uu____5248);
             FStar_Extraction_ML_Syntax.mlty = uu____5249;
             FStar_Extraction_ML_Syntax.loc = uu____5250;_},e1::[])
          when
          let uu____5258 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5258 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____5259 =
            let uu____5264 = translate_expr env e1  in
            (uu____5264, (EConstant (UInt32, "0")))  in
          EBufRead uu____5259
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5266;
                  FStar_Extraction_ML_Syntax.loc = uu____5267;_},uu____5268);
             FStar_Extraction_ML_Syntax.mlty = uu____5269;
             FStar_Extraction_ML_Syntax.loc = uu____5270;_},e1::e2::[])
          when
          (let uu____5281 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5281 = "FStar.Buffer.create") ||
            (let uu____5283 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5283 = "LowStar.Buffer.alloca")
          ->
          let uu____5284 =
            let uu____5291 = translate_expr env e1  in
            let uu____5292 = translate_expr env e2  in
            (Stack, uu____5291, uu____5292)  in
          EBufCreate uu____5284
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5294;
                  FStar_Extraction_ML_Syntax.loc = uu____5295;_},uu____5296);
             FStar_Extraction_ML_Syntax.mlty = uu____5297;
             FStar_Extraction_ML_Syntax.loc = uu____5298;_},init1::[])
          when
          let uu____5306 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5306 = "FStar.HyperStack.ST.salloc" ->
          let uu____5307 =
            let uu____5314 = translate_expr env init1  in
            (Stack, uu____5314, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5307
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5316;
                  FStar_Extraction_ML_Syntax.loc = uu____5317;_},uu____5318);
             FStar_Extraction_ML_Syntax.mlty = uu____5319;
             FStar_Extraction_ML_Syntax.loc = uu____5320;_},e2::[])
          when
          (let uu____5330 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5330 = "FStar.Buffer.createL") ||
            (let uu____5332 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5332 = "LowStar.Buffer.alloca_of_list")
          ->
          let uu____5333 =
            let uu____5340 =
              let uu____5343 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____5343  in
            (Stack, uu____5340)  in
          EBufCreateL uu____5333
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5349;
                  FStar_Extraction_ML_Syntax.loc = uu____5350;_},uu____5351);
             FStar_Extraction_ML_Syntax.mlty = uu____5352;
             FStar_Extraction_ML_Syntax.loc = uu____5353;_},uu____5354::e2::[])
          when
          let uu____5362 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5362 = "LowStar.Buffer.gcmalloc_of_list" ->
          let uu____5363 =
            let uu____5370 =
              let uu____5373 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____5373  in
            (Eternal, uu____5370)  in
          EBufCreateL uu____5363
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5379;
                  FStar_Extraction_ML_Syntax.loc = uu____5380;_},uu____5381);
             FStar_Extraction_ML_Syntax.mlty = uu____5382;
             FStar_Extraction_ML_Syntax.loc = uu____5383;_},_rid::init1::[])
          when
          let uu____5392 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5392 = "FStar.HyperStack.ST.ralloc" ->
          let uu____5393 =
            let uu____5400 = translate_expr env init1  in
            (Eternal, uu____5400, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5393
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5402;
                  FStar_Extraction_ML_Syntax.loc = uu____5403;_},uu____5404);
             FStar_Extraction_ML_Syntax.mlty = uu____5405;
             FStar_Extraction_ML_Syntax.loc = uu____5406;_},_e0::e1::e2::[])
          when
          (let uu____5418 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5418 = "FStar.Buffer.rcreate") ||
            (let uu____5420 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5420 = "LowStar.Buffer.gcmalloc")
          ->
          let uu____5421 =
            let uu____5428 = translate_expr env e1  in
            let uu____5429 = translate_expr env e2  in
            (Eternal, uu____5428, uu____5429)  in
          EBufCreate uu____5421
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5431;
                  FStar_Extraction_ML_Syntax.loc = uu____5432;_},uu____5433);
             FStar_Extraction_ML_Syntax.mlty = uu____5434;
             FStar_Extraction_ML_Syntax.loc = uu____5435;_},_rid::init1::[])
          when
          let uu____5444 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5444 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____5445 =
            let uu____5452 = translate_expr env init1  in
            (ManuallyManaged, uu____5452, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5445
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5454;
                  FStar_Extraction_ML_Syntax.loc = uu____5455;_},uu____5456);
             FStar_Extraction_ML_Syntax.mlty = uu____5457;
             FStar_Extraction_ML_Syntax.loc = uu____5458;_},_e0::e1::e2::[])
          when
          (let uu____5470 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5470 = "FStar.Buffer.rcreate_mm") ||
            (let uu____5472 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5472 = "LowStar.Buffer.malloc")
          ->
          let uu____5473 =
            let uu____5480 = translate_expr env e1  in
            let uu____5481 = translate_expr env e2  in
            (ManuallyManaged, uu____5480, uu____5481)  in
          EBufCreate uu____5473
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5483;
                  FStar_Extraction_ML_Syntax.loc = uu____5484;_},uu____5485);
             FStar_Extraction_ML_Syntax.mlty = uu____5486;
             FStar_Extraction_ML_Syntax.loc = uu____5487;_},e2::[])
          when
          let uu____5495 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5495 = "FStar.HyperStack.ST.rfree" ->
          let uu____5496 = translate_expr env e2  in EBufFree uu____5496
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5498;
                  FStar_Extraction_ML_Syntax.loc = uu____5499;_},uu____5500);
             FStar_Extraction_ML_Syntax.mlty = uu____5501;
             FStar_Extraction_ML_Syntax.loc = uu____5502;_},e2::[])
          when
          (let uu____5512 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5512 = "FStar.Buffer.rfree") ||
            (let uu____5514 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5514 = "LowStar.Buffer.free")
          -> let uu____5515 = translate_expr env e2  in EBufFree uu____5515
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5517;
                  FStar_Extraction_ML_Syntax.loc = uu____5518;_},uu____5519);
             FStar_Extraction_ML_Syntax.mlty = uu____5520;
             FStar_Extraction_ML_Syntax.loc = uu____5521;_},e1::e2::_e3::[])
          when
          (let uu____5533 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5533 = "FStar.Buffer.sub") ||
            (let uu____5535 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5535 = "LowStar.Buffer.sub")
          ->
          let uu____5536 =
            let uu____5541 = translate_expr env e1  in
            let uu____5542 = translate_expr env e2  in
            (uu____5541, uu____5542)  in
          EBufSub uu____5536
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5544;
                  FStar_Extraction_ML_Syntax.loc = uu____5545;_},uu____5546);
             FStar_Extraction_ML_Syntax.mlty = uu____5547;
             FStar_Extraction_ML_Syntax.loc = uu____5548;_},e1::e2::[])
          when
          let uu____5557 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5557 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5559;
                  FStar_Extraction_ML_Syntax.loc = uu____5560;_},uu____5561);
             FStar_Extraction_ML_Syntax.mlty = uu____5562;
             FStar_Extraction_ML_Syntax.loc = uu____5563;_},e1::e2::[])
          when
          (let uu____5574 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5574 = "FStar.Buffer.offset") ||
            (let uu____5576 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5576 = "LowStar.Buffer.offset")
          ->
          let uu____5577 =
            let uu____5582 = translate_expr env e1  in
            let uu____5583 = translate_expr env e2  in
            (uu____5582, uu____5583)  in
          EBufSub uu____5577
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5585;
                  FStar_Extraction_ML_Syntax.loc = uu____5586;_},uu____5587);
             FStar_Extraction_ML_Syntax.mlty = uu____5588;
             FStar_Extraction_ML_Syntax.loc = uu____5589;_},e1::e2::e3::[])
          when
          ((let uu____5601 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5601 = "FStar.Buffer.upd") ||
             (let uu____5603 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5603 = "FStar.Buffer.op_Array_Assignment"))
            ||
            (let uu____5605 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5605 = "LowStar.Buffer.upd")
          ->
          let uu____5606 =
            let uu____5613 = translate_expr env e1  in
            let uu____5614 = translate_expr env e2  in
            let uu____5615 = translate_expr env e3  in
            (uu____5613, uu____5614, uu____5615)  in
          EBufWrite uu____5606
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5617;
                  FStar_Extraction_ML_Syntax.loc = uu____5618;_},uu____5619);
             FStar_Extraction_ML_Syntax.mlty = uu____5620;
             FStar_Extraction_ML_Syntax.loc = uu____5621;_},e1::e2::[])
          when
          let uu____5630 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5630 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5631 =
            let uu____5638 = translate_expr env e1  in
            let uu____5639 = translate_expr env e2  in
            (uu____5638, (EConstant (UInt32, "0")), uu____5639)  in
          EBufWrite uu____5631
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5641;
             FStar_Extraction_ML_Syntax.loc = uu____5642;_},uu____5643::[])
          when
          let uu____5646 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5646 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5648;
             FStar_Extraction_ML_Syntax.loc = uu____5649;_},uu____5650::[])
          when
          let uu____5653 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5653 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5655;
                  FStar_Extraction_ML_Syntax.loc = uu____5656;_},uu____5657);
             FStar_Extraction_ML_Syntax.mlty = uu____5658;
             FStar_Extraction_ML_Syntax.loc = uu____5659;_},e1::e2::e3::e4::e5::[])
          when
          (let uu____5673 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5673 = "FStar.Buffer.blit") ||
            (let uu____5675 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5675 = "LowStar.BufferOps.blit")
          ->
          let uu____5676 =
            let uu____5687 = translate_expr env e1  in
            let uu____5688 = translate_expr env e2  in
            let uu____5689 = translate_expr env e3  in
            let uu____5690 = translate_expr env e4  in
            let uu____5691 = translate_expr env e5  in
            (uu____5687, uu____5688, uu____5689, uu____5690, uu____5691)  in
          EBufBlit uu____5676
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5693;
                  FStar_Extraction_ML_Syntax.loc = uu____5694;_},uu____5695);
             FStar_Extraction_ML_Syntax.mlty = uu____5696;
             FStar_Extraction_ML_Syntax.loc = uu____5697;_},e1::e2::e3::[])
          when
          let uu____5707 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5707 = "FStar.Buffer.fill" ->
          let uu____5708 =
            let uu____5715 = translate_expr env e1  in
            let uu____5716 = translate_expr env e2  in
            let uu____5717 = translate_expr env e3  in
            (uu____5715, uu____5716, uu____5717)  in
          EBufFill uu____5708
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5719;
             FStar_Extraction_ML_Syntax.loc = uu____5720;_},uu____5721::[])
          when
          let uu____5724 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5724 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5726;
             FStar_Extraction_ML_Syntax.loc = uu____5727;_},e1::[])
          when
          let uu____5731 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5731 = "Obj.repr" ->
          let uu____5732 =
            let uu____5737 = translate_expr env e1  in (uu____5737, TAny)  in
          ECast uu____5732
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5740;
             FStar_Extraction_ML_Syntax.loc = uu____5741;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5749 = FStar_Util.must (mk_width m)  in
          let uu____5750 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____5749 uu____5750 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5752;
             FStar_Extraction_ML_Syntax.loc = uu____5753;_},args)
          when is_bool_op op ->
          let uu____5761 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____5761 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5763;
             FStar_Extraction_ML_Syntax.loc = uu____5764;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5766;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5767;_}::[])
          when is_machine_int m ->
          let uu____5782 =
            let uu____5787 = FStar_Util.must (mk_width m)  in (uu____5787, c)
             in
          EConstant uu____5782
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5789;
             FStar_Extraction_ML_Syntax.loc = uu____5790;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5792;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5793;_}::[])
          when is_machine_int m ->
          let uu____5808 =
            let uu____5813 = FStar_Util.must (mk_width m)  in (uu____5813, c)
             in
          EConstant uu____5808
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5814;
             FStar_Extraction_ML_Syntax.loc = uu____5815;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5817;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5818;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5824 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5825;
             FStar_Extraction_ML_Syntax.loc = uu____5826;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5828;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5829;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5835 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5837;
             FStar_Extraction_ML_Syntax.loc = uu____5838;_},arg::[])
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
            let uu____5845 =
              let uu____5850 = translate_expr env arg  in
              (uu____5850, (TInt UInt64))  in
            ECast uu____5845
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5852 =
                 let uu____5857 = translate_expr env arg  in
                 (uu____5857, (TInt UInt32))  in
               ECast uu____5852)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5859 =
                   let uu____5864 = translate_expr env arg  in
                   (uu____5864, (TInt UInt16))  in
                 ECast uu____5859)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5866 =
                     let uu____5871 = translate_expr env arg  in
                     (uu____5871, (TInt UInt8))  in
                   ECast uu____5866)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5873 =
                       let uu____5878 = translate_expr env arg  in
                       (uu____5878, (TInt Int64))  in
                     ECast uu____5873)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5880 =
                         let uu____5885 = translate_expr env arg  in
                         (uu____5885, (TInt Int32))  in
                       ECast uu____5880)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5887 =
                           let uu____5892 = translate_expr env arg  in
                           (uu____5892, (TInt Int16))  in
                         ECast uu____5887)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5894 =
                             let uu____5899 = translate_expr env arg  in
                             (uu____5899, (TInt Int8))  in
                           ECast uu____5894)
                        else
                          (let uu____5901 =
                             let uu____5908 =
                               let uu____5911 = translate_expr env arg  in
                               [uu____5911]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5908)
                              in
                           EApp uu____5901)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5922 =
            let uu____5929 = translate_expr env head1  in
            let uu____5930 = FStar_List.map (translate_expr env) args  in
            (uu____5929, uu____5930)  in
          EApp uu____5922
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5941 =
            let uu____5948 = translate_expr env head1  in
            let uu____5949 = FStar_List.map (translate_type env) ty_args  in
            (uu____5948, uu____5949)  in
          ETypApp uu____5941
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5957 =
            let uu____5962 = translate_expr env e1  in
            let uu____5963 = translate_type env t_to  in
            (uu____5962, uu____5963)  in
          ECast uu____5957
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5964,fields) ->
          let uu____5982 =
            let uu____5993 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5994 =
              FStar_List.map
                (fun uu____6013  ->
                   match uu____6013 with
                   | (field,expr) ->
                       let uu____6024 = translate_expr env expr  in
                       (field, uu____6024)) fields
               in
            (uu____5993, uu____5994)  in
          EFlat uu____5982
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____6033 =
            let uu____6040 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____6041 = translate_expr env e1  in
            (uu____6040, uu____6041, (FStar_Pervasives_Native.snd path))  in
          EField uu____6033
      | FStar_Extraction_ML_Syntax.MLE_Let uu____6044 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____6056) ->
          let uu____6061 =
            let uu____6062 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____6062
             in
          failwith uu____6061
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____6068 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____6068
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____6074 = FStar_List.map (translate_expr env) es  in
          ETuple uu____6074
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____6077,cons1),es) ->
          let uu____6088 =
            let uu____6097 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____6098 = FStar_List.map (translate_expr env) es  in
            (uu____6097, cons1, uu____6098)  in
          ECons uu____6088
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____6121 =
            let uu____6130 = translate_expr env1 body  in
            let uu____6131 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____6130, uu____6131)  in
          EFun uu____6121
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____6141 =
            let uu____6148 = translate_expr env e1  in
            let uu____6149 = translate_expr env e2  in
            let uu____6150 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____6148, uu____6149, uu____6150)  in
          EIfThenElse uu____6141
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____6152 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____6159 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____6174 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____6189 =
              let uu____6202 = FStar_List.map (translate_type env) ts  in
              (lid, uu____6202)  in
            TApp uu____6189
          else TQualified lid
      | uu____6214 -> failwith "invalid argument: assert_lid"

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
    fun uu____6240  ->
      match uu____6240 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____6266 = translate_pat env pat  in
            (match uu____6266 with
             | (env1,pat1) ->
                 let uu____6277 = translate_expr env1 expr  in
                 (pat1, uu____6277))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___279_6283  ->
    match uu___279_6283 with
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
          let uu____6347 =
            let uu____6348 =
              let uu____6353 = translate_width sw  in (uu____6353, s)  in
            PConstant uu____6348  in
          (env, uu____6347)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____6357,cons1),ps) ->
          let uu____6368 =
            FStar_List.fold_left
              (fun uu____6388  ->
                 fun p1  ->
                   match uu____6388 with
                   | (env1,acc) ->
                       let uu____6408 = translate_pat env1 p1  in
                       (match uu____6408 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6368 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____6437,ps) ->
          let uu____6455 =
            FStar_List.fold_left
              (fun uu____6489  ->
                 fun uu____6490  ->
                   match (uu____6489, uu____6490) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____6559 = translate_pat env1 p1  in
                       (match uu____6559 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____6455 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____6621 =
            FStar_List.fold_left
              (fun uu____6641  ->
                 fun p1  ->
                   match uu____6641 with
                   | (env1,acc) ->
                       let uu____6661 = translate_pat env1 p1  in
                       (match uu____6661 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6621 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6688 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6693 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____6704 =
            let uu____6705 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____6705
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____6704
          then
            let uu____6717 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____6717
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6730) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6745 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6746 ->
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
          let uu____6767 =
            let uu____6774 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____6774)  in
          EApp uu____6767
