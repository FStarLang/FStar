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
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1340 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1346 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1352 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1359 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1379 -> false
  
let (__proj__EQualified__item___0 :
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1415 -> false
  
let (__proj__EConstant__item___0 :
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1440 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1453 -> false
  
let (__proj__EApp__item___0 :
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1491 -> false
  
let (__proj__ETypApp__item___0 :
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1529 -> false
  
let (__proj__ELet__item___0 :
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1567 -> false
  
let (__proj__EIfThenElse__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1601 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1625 -> false
  
let (__proj__EAssign__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____1657 -> false
  
let (__proj__EBufCreate__item___0 :
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____1693 -> false
  
let (__proj__EBufRead__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____1725 -> false
  
let (__proj__EBufWrite__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____1761 -> false
  
let (__proj__EBufSub__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____1797 -> false
  
let (__proj__EBufBlit__item___0 :
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5) =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____1851 -> false
  
let (__proj__EMatch__item___0 :
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1899 -> false
  
let (__proj__EOp__item___0 :
  expr -> (op,width) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1929 -> false
  
let (__proj__ECast__item___0 :
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1954 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1960 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1967 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1980 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1986 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1993 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____2017 -> false
  
let (__proj__EFlat__item___0 :
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____2067 -> false
  
let (__proj__EField__item___0 :
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____2103 -> false
  
let (__proj__EWhile__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____2135 -> false
  
let (__proj__EBufCreateL__item___0 :
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2169 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2197 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2241 -> false
  
let (__proj__EBufFill__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2273 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2295 -> false
  
let (__proj__EFun__item___0 :
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2333 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____2347 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____2360 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2366 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____2372 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2378 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____2384 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2390 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2396 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2402 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____2408 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____2414 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2420 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2426 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2432 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2438 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2444 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____2450 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____2456 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____2462 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____2468 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____2474 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____2480 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____2486 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____2492 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____2498 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____2504 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2510 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2517 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2531 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2551 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2585 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2611 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list)
  = fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____2647 -> false
  
let (__proj__PConstant__item___0 :
  pattern -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____2672 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2678 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2684 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2690 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2696 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2702 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2708 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2714 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2720 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____2726 -> false
  
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
    match projectee with | TInt _0 -> true | uu____2757 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2771 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2784 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2797 -> false
  
let (__proj__TQualified__item___0 :
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2828 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2834 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2845 -> false
  
let (__proj__TArrow__item___0 :
  typ -> (typ,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2871 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2897 -> false
  
let (__proj__TApp__item___0 :
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____2949 -> false
  
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
  'Auu____3029 'Auu____3030 'Auu____3031 .
    ('Auu____3029,'Auu____3030,'Auu____3031) FStar_Pervasives_Native.tuple3
      -> 'Auu____3029
  = fun uu____3042  -> match uu____3042 with | (x,uu____3050,uu____3051) -> x 
let snd3 :
  'Auu____3060 'Auu____3061 'Auu____3062 .
    ('Auu____3060,'Auu____3061,'Auu____3062) FStar_Pervasives_Native.tuple3
      -> 'Auu____3061
  = fun uu____3073  -> match uu____3073 with | (uu____3080,x,uu____3082) -> x 
let thd3 :
  'Auu____3091 'Auu____3092 'Auu____3093 .
    ('Auu____3091,'Auu____3092,'Auu____3093) FStar_Pervasives_Native.tuple3
      -> 'Auu____3093
  = fun uu____3104  -> match uu____3104 with | (uu____3111,uu____3112,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___264_3120  ->
    match uu___264_3120 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____3123 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___265_3130  ->
    match uu___265_3130 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____3133 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___266_3147  ->
    match uu___266_3147 with
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
    | uu____3150 -> FStar_Pervasives_Native.None
  
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
      let uu___272_3270 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___272_3270.names_t);
        module_name = (uu___272_3270.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___273_3281 = env  in
      {
        names = (uu___273_3281.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___273_3281.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____3292 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____3292 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___275_3309  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___274_3314 ->
          let uu____3315 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____3315
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___277_3327  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___276_3332 ->
          let uu____3333 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____3333
  
let add_binders :
  'Auu____3340 .
    env ->
      (Prims.string,'Auu____3340) FStar_Pervasives_Native.tuple2 Prims.list
        -> env
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____3372  ->
             match uu____3372 with | (name,uu____3378) -> extend env1 name)
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
      | uu____3415 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____3630  ->
    match uu____3630 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3678 = m  in
               match uu____3678 with
               | (path,uu____3692,uu____3693) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___279_3711  ->
                  match () with
                  | () ->
                      (FStar_Util.print1
                         "Attempting to translate module %s\n" m_name;
                       (let uu____3715 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____3715))) ()
             with
             | e ->
                 ((let uu____3724 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3724);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath,(FStar_Extraction_ML_Syntax.mlsig,
                                       FStar_Extraction_ML_Syntax.mlmodule)
                                       FStar_Pervasives_Native.tuple2
                                       FStar_Pervasives_Native.option,
    FStar_Extraction_ML_Syntax.mllib) FStar_Pervasives_Native.tuple3 -> 
    file)
  =
  fun uu____3725  ->
    match uu____3725 with
    | (module_name,modul,uu____3740) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____3767 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags1  ->
    FStar_List.choose
      (fun uu___267_3778  ->
         match uu___267_3778 with
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
         | uu____3785 -> FStar_Pervasives_Native.None) flags1

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags1  ->
    let uu____3789 =
      FStar_List.choose
        (fun uu___268_3794  ->
           match uu___268_3794 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____3798 -> FStar_Pervasives_Native.None) flags1
       in
    match uu____3789 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____3801 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3814 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3816 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____3820) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3842;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____3845;
                FStar_Extraction_ML_Syntax.loc = uu____3846;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3848;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___269_3866  ->
                      match uu___269_3866 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____3867 -> false) meta
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
               let rec find_return_type eff i uu___270_3894 =
                 match uu___270_3894 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3899,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (eff, t)  in
               let uu____3903 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____3903 with
               | (eff,t) ->
                   let t1 = translate_type env2 t  in
                   let binders = translate_binders env2 args  in
                   let env3 = add_binders env2 args  in
                   let name1 = ((env3.module_name), name)  in
                   let cc = translate_cc meta  in
                   let meta1 =
                     match (eff, t1) with
                     | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____3938) ->
                         let uu____3939 = translate_flags meta  in
                         MustDisappear :: uu____3939
                     | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                         let uu____3942 = translate_flags meta  in
                         MustDisappear :: uu____3942
                     | uu____3945 -> translate_flags meta  in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____3954 =
                          let uu____3955 =
                            let uu____3974 = translate_type env3 t0  in
                            (cc, meta1, name1, uu____3974)  in
                          DExternal uu____3955  in
                        FStar_Pervasives_Native.Some uu____3954
                      else
                        ((let uu____3987 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1
                             in
                          FStar_Util.print1_warning
                            "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                            uu____3987);
                         FStar_Pervasives_Native.None))
                   else
                     (try
                        (fun uu___281_3993  ->
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
                          ((let uu____4020 =
                              let uu____4025 =
                                let uu____4026 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1
                                   in
                                FStar_Util.format2
                                  "Error while extracting %s to KreMLin (%s)\n"
                                  uu____4026 msg
                                 in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____4025)
                               in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____4020);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4043;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Coerce
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____4046;
                     FStar_Extraction_ML_Syntax.loc = uu____4047;_},uu____4048,uu____4049);
                FStar_Extraction_ML_Syntax.mlty = uu____4050;
                FStar_Extraction_ML_Syntax.loc = uu____4051;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4053;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___269_4071  ->
                      match uu___269_4071 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____4072 -> false) meta
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
               let rec find_return_type eff i uu___270_4099 =
                 match uu___270_4099 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____4104,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (eff, t)  in
               let uu____4108 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____4108 with
               | (eff,t) ->
                   let t1 = translate_type env2 t  in
                   let binders = translate_binders env2 args  in
                   let env3 = add_binders env2 args  in
                   let name1 = ((env3.module_name), name)  in
                   let cc = translate_cc meta  in
                   let meta1 =
                     match (eff, t1) with
                     | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____4143) ->
                         let uu____4144 = translate_flags meta  in
                         MustDisappear :: uu____4144
                     | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                         let uu____4147 = translate_flags meta  in
                         MustDisappear :: uu____4147
                     | uu____4150 -> translate_flags meta  in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____4159 =
                          let uu____4160 =
                            let uu____4179 = translate_type env3 t0  in
                            (cc, meta1, name1, uu____4179)  in
                          DExternal uu____4160  in
                        FStar_Pervasives_Native.Some uu____4159
                      else
                        ((let uu____4192 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1
                             in
                          FStar_Util.print1_warning
                            "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                            uu____4192);
                         FStar_Pervasives_Native.None))
                   else
                     (try
                        (fun uu___281_4198  ->
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
                          ((let uu____4225 =
                              let uu____4230 =
                                let uu____4231 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1
                                   in
                                FStar_Util.format2
                                  "Error while extracting %s to KreMLin (%s)\n"
                                  uu____4231 msg
                                 in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____4230)
                               in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____4225);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4248;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4251;_} ->
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
                 (fun uu___283_4277  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____4297 =
                       let uu____4302 =
                         let uu____4303 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____4304 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____4303
                           uu____4304
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____4302)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____4297);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4315;
            FStar_Extraction_ML_Syntax.mllb_def = uu____4316;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____4317;
            FStar_Extraction_ML_Syntax.print_typ = uu____4318;_} ->
            ((let uu____4322 =
                let uu____4327 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____4327)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____4322);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____4331 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____4331
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____4338 = ty  in
      match uu____4338 with
      | (uu____4341,uu____4342,uu____4343,uu____4344,flags1,uu____4346) ->
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
                   (let uu____4391 =
                      let uu____4392 =
                        let uu____4409 = translate_flags flags2  in
                        let uu____4412 = translate_type env1 t  in
                        (name1, uu____4409, (FStar_List.length args),
                          uu____4412)
                         in
                      DTypeAlias uu____4392  in
                    FStar_Pervasives_Native.Some uu____4391)
             | (uu____4421,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____4453 =
                   let uu____4454 =
                     let uu____4481 = translate_flags flags2  in
                     let uu____4484 =
                       FStar_List.map
                         (fun uu____4511  ->
                            match uu____4511 with
                            | (f,t) ->
                                let uu____4526 =
                                  let uu____4531 = translate_type env1 t  in
                                  (uu____4531, false)  in
                                (f, uu____4526)) fields
                        in
                     (name1, uu____4481, (FStar_List.length args),
                       uu____4484)
                      in
                   DTypeFlat uu____4454  in
                 FStar_Pervasives_Native.Some uu____4453
             | (uu____4554,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags3 = translate_flags flags2  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____4591 =
                   let uu____4592 =
                     let uu____4625 =
                       FStar_List.map
                         (fun uu____4670  ->
                            match uu____4670 with
                            | (cons1,ts) ->
                                let uu____4709 =
                                  FStar_List.map
                                    (fun uu____4736  ->
                                       match uu____4736 with
                                       | (name2,t) ->
                                           let uu____4751 =
                                             let uu____4756 =
                                               translate_type env1 t  in
                                             (uu____4756, false)  in
                                           (name2, uu____4751)) ts
                                   in
                                (cons1, uu____4709)) branches
                        in
                     (name1, flags3, (FStar_List.length args), uu____4625)
                      in
                   DTypeVariant uu____4592  in
                 FStar_Pervasives_Native.Some uu____4591
             | (uu____4795,name,_mangled_name,uu____4798,uu____4799,uu____4800)
                 ->
                 ((let uu____4810 =
                     let uu____4815 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____4815)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____4810);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4819 = find_t env name  in TBound uu____4819
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4821,t2) ->
          let uu____4823 =
            let uu____4828 = translate_type env t1  in
            let uu____4829 = translate_type env t2  in
            (uu____4828, uu____4829)  in
          TArrow uu____4823
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4833 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4833 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4837 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4837 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4843 = FStar_Util.must (mk_width m)  in TInt uu____4843
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4849 = FStar_Util.must (mk_width m)  in TInt uu____4849
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4854 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4854 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____4855::arg::uu____4857::[],p) when
          (((let uu____4863 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4863 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____4865 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4865 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____4867 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4867 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____4869 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4869 = "FStar.HyperStack.ST.s_mref")
          -> let uu____4870 = translate_type env arg  in TBuf uu____4870
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____4872::[],p) when
          ((((((((((let uu____4878 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4878 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____4880 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4880 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____4882 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4882 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____4884 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4884 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____4886 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4886 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____4888 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4888 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____4890 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4890 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____4892 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4892 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____4894 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4894 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____4896 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4896 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____4898 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4898 = "FStar.HyperStack.ST.mmmref")
          -> let uu____4899 = translate_type env arg  in TBuf uu____4899
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((let uu____4906 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4906 = "LowStar.Buffer.buffer") ||
                      (let uu____4908 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____4908 = "FStar.Buffer.buffer"))
                     ||
                     (let uu____4910 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4910 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____4912 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4912 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____4914 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4914 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____4916 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4916 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____4918 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4918 = "FStar.HyperStack.mmref"))
                ||
                (let uu____4920 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4920 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____4922 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4922 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____4924 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4924 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____4926 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4926 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____4928 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4928 = "FStar.HyperStack.ST.mmref")
          -> let uu____4929 = translate_type env arg  in TBuf uu____4929
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4930::arg::[],p) when
          (let uu____4937 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4937 = "FStar.HyperStack.s_ref") ||
            (let uu____4939 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4939 = "FStar.HyperStack.ST.s_ref")
          -> let uu____4940 = translate_type env arg  in TBuf uu____4940
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4941::[],p) when
          let uu____4945 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4945 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4971 = FStar_List.map (translate_type env) args  in
          TTuple uu____4971
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4980 =
              let uu____4993 = FStar_List.map (translate_type env) args  in
              (lid, uu____4993)  in
            TApp uu____4980
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____5008 = FStar_List.map (translate_type env) ts  in
          TTuple uu____5008

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
    fun uu____5024  ->
      match uu____5024 with
      | (name,typ) ->
          let uu____5031 = translate_type env typ  in
          { name; typ = uu____5031; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____5036 = find env name  in EBound uu____5036
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____5041 =
            let uu____5046 = FStar_Util.must (mk_op op)  in
            let uu____5047 = FStar_Util.must (mk_width m)  in
            (uu____5046, uu____5047)  in
          EOp uu____5041
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____5051 =
            let uu____5056 = FStar_Util.must (mk_bool_op op)  in
            (uu____5056, Bool)  in
          EOp uu____5051
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
            let uu____5075 = translate_type env typ  in
            { name; typ = uu____5075; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____5101 =
            let uu____5112 = translate_expr env expr  in
            let uu____5113 = translate_branches env branches  in
            (uu____5112, uu____5113)  in
          EMatch uu____5101
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5127;
                  FStar_Extraction_ML_Syntax.loc = uu____5128;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____5130;
             FStar_Extraction_ML_Syntax.loc = uu____5131;_},arg::[])
          when
          let uu____5137 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5137 = "FStar.Dyn.undyn" ->
          let uu____5138 =
            let uu____5143 = translate_expr env arg  in
            let uu____5144 = translate_type env t  in
            (uu____5143, uu____5144)  in
          ECast uu____5138
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5146;
                  FStar_Extraction_ML_Syntax.loc = uu____5147;_},uu____5148);
             FStar_Extraction_ML_Syntax.mlty = uu____5149;
             FStar_Extraction_ML_Syntax.loc = uu____5150;_},uu____5151)
          when
          let uu____5160 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5160 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5162;
                  FStar_Extraction_ML_Syntax.loc = uu____5163;_},uu____5164);
             FStar_Extraction_ML_Syntax.mlty = uu____5165;
             FStar_Extraction_ML_Syntax.loc = uu____5166;_},arg::[])
          when
          ((let uu____5176 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5176 = "FStar.HyperStack.All.failwith") ||
             (let uu____5178 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5178 = "FStar.Error.unexpected"))
            ||
            (let uu____5180 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5180 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____5182;
               FStar_Extraction_ML_Syntax.loc = uu____5183;_} -> EAbortS msg
           | uu____5184 ->
               let print7 =
                 let uu____5186 =
                   let uu____5187 =
                     let uu____5188 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____5188
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____5187  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____5186
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
                  FStar_Extraction_ML_Syntax.mlty = uu____5194;
                  FStar_Extraction_ML_Syntax.loc = uu____5195;_},uu____5196);
             FStar_Extraction_ML_Syntax.mlty = uu____5197;
             FStar_Extraction_ML_Syntax.loc = uu____5198;_},e1::[])
          when
          (let uu____5208 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5208 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____5210 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5210 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5212;
                  FStar_Extraction_ML_Syntax.loc = uu____5213;_},uu____5214);
             FStar_Extraction_ML_Syntax.mlty = uu____5215;
             FStar_Extraction_ML_Syntax.loc = uu____5216;_},e1::e2::[])
          when
          ((let uu____5227 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5227 = "FStar.Buffer.index") ||
             (let uu____5229 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5229 = "FStar.Buffer.op_Array_Access"))
            ||
            (let uu____5231 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5231 = "LowStar.Buffer.index")
          ->
          let uu____5232 =
            let uu____5237 = translate_expr env e1  in
            let uu____5238 = translate_expr env e2  in
            (uu____5237, uu____5238)  in
          EBufRead uu____5232
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5240;
                  FStar_Extraction_ML_Syntax.loc = uu____5241;_},uu____5242);
             FStar_Extraction_ML_Syntax.mlty = uu____5243;
             FStar_Extraction_ML_Syntax.loc = uu____5244;_},e1::[])
          when
          let uu____5252 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5252 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____5253 =
            let uu____5258 = translate_expr env e1  in
            (uu____5258, (EConstant (UInt32, "0")))  in
          EBufRead uu____5253
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5260;
                  FStar_Extraction_ML_Syntax.loc = uu____5261;_},uu____5262);
             FStar_Extraction_ML_Syntax.mlty = uu____5263;
             FStar_Extraction_ML_Syntax.loc = uu____5264;_},e1::e2::[])
          when
          (let uu____5275 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5275 = "FStar.Buffer.create") ||
            (let uu____5277 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5277 = "LowStar.Buffer.alloca")
          ->
          let uu____5278 =
            let uu____5285 = translate_expr env e1  in
            let uu____5286 = translate_expr env e2  in
            (Stack, uu____5285, uu____5286)  in
          EBufCreate uu____5278
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5288;
                  FStar_Extraction_ML_Syntax.loc = uu____5289;_},uu____5290);
             FStar_Extraction_ML_Syntax.mlty = uu____5291;
             FStar_Extraction_ML_Syntax.loc = uu____5292;_},init1::[])
          when
          let uu____5300 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5300 = "FStar.HyperStack.ST.salloc" ->
          let uu____5301 =
            let uu____5308 = translate_expr env init1  in
            (Stack, uu____5308, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5301
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
             FStar_Extraction_ML_Syntax.loc = uu____5314;_},e2::[])
          when
          (let uu____5324 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5324 = "FStar.Buffer.createL") ||
            (let uu____5326 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5326 = "LowStar.Buffer.alloca_of_list")
          ->
          let uu____5327 =
            let uu____5334 =
              let uu____5337 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____5337  in
            (Stack, uu____5334)  in
          EBufCreateL uu____5327
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
             FStar_Extraction_ML_Syntax.loc = uu____5347;_},uu____5348::e2::[])
          when
          let uu____5356 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5356 = "LowStar.Buffer.gcmalloc_of_list" ->
          let uu____5357 =
            let uu____5364 =
              let uu____5367 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____5367  in
            (Eternal, uu____5364)  in
          EBufCreateL uu____5357
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5373;
                  FStar_Extraction_ML_Syntax.loc = uu____5374;_},uu____5375);
             FStar_Extraction_ML_Syntax.mlty = uu____5376;
             FStar_Extraction_ML_Syntax.loc = uu____5377;_},_rid::init1::[])
          when
          let uu____5386 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5386 = "FStar.HyperStack.ST.ralloc" ->
          let uu____5387 =
            let uu____5394 = translate_expr env init1  in
            (Eternal, uu____5394, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5387
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5396;
                  FStar_Extraction_ML_Syntax.loc = uu____5397;_},uu____5398);
             FStar_Extraction_ML_Syntax.mlty = uu____5399;
             FStar_Extraction_ML_Syntax.loc = uu____5400;_},_e0::e1::e2::[])
          when
          (let uu____5412 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5412 = "FStar.Buffer.rcreate") ||
            (let uu____5414 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5414 = "LowStar.Buffer.gcmalloc")
          ->
          let uu____5415 =
            let uu____5422 = translate_expr env e1  in
            let uu____5423 = translate_expr env e2  in
            (Eternal, uu____5422, uu____5423)  in
          EBufCreate uu____5415
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5425;
                  FStar_Extraction_ML_Syntax.loc = uu____5426;_},uu____5427);
             FStar_Extraction_ML_Syntax.mlty = uu____5428;
             FStar_Extraction_ML_Syntax.loc = uu____5429;_},_rid::init1::[])
          when
          let uu____5438 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5438 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____5439 =
            let uu____5446 = translate_expr env init1  in
            (ManuallyManaged, uu____5446, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5439
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5448;
                  FStar_Extraction_ML_Syntax.loc = uu____5449;_},uu____5450);
             FStar_Extraction_ML_Syntax.mlty = uu____5451;
             FStar_Extraction_ML_Syntax.loc = uu____5452;_},_e0::e1::e2::[])
          when
          (let uu____5464 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5464 = "FStar.Buffer.rcreate_mm") ||
            (let uu____5466 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5466 = "LowStar.Buffer.malloc")
          ->
          let uu____5467 =
            let uu____5474 = translate_expr env e1  in
            let uu____5475 = translate_expr env e2  in
            (ManuallyManaged, uu____5474, uu____5475)  in
          EBufCreate uu____5467
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5477;
                  FStar_Extraction_ML_Syntax.loc = uu____5478;_},uu____5479);
             FStar_Extraction_ML_Syntax.mlty = uu____5480;
             FStar_Extraction_ML_Syntax.loc = uu____5481;_},e2::[])
          when
          let uu____5489 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5489 = "FStar.HyperStack.ST.rfree" ->
          let uu____5490 = translate_expr env e2  in EBufFree uu____5490
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5492;
                  FStar_Extraction_ML_Syntax.loc = uu____5493;_},uu____5494);
             FStar_Extraction_ML_Syntax.mlty = uu____5495;
             FStar_Extraction_ML_Syntax.loc = uu____5496;_},e2::[])
          when
          (let uu____5506 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5506 = "FStar.Buffer.rfree") ||
            (let uu____5508 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5508 = "LowStar.Buffer.free")
          -> let uu____5509 = translate_expr env e2  in EBufFree uu____5509
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5511;
                  FStar_Extraction_ML_Syntax.loc = uu____5512;_},uu____5513);
             FStar_Extraction_ML_Syntax.mlty = uu____5514;
             FStar_Extraction_ML_Syntax.loc = uu____5515;_},e1::e2::_e3::[])
          when
          (let uu____5527 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5527 = "FStar.Buffer.sub") ||
            (let uu____5529 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5529 = "LowStar.Buffer.sub")
          ->
          let uu____5530 =
            let uu____5535 = translate_expr env e1  in
            let uu____5536 = translate_expr env e2  in
            (uu____5535, uu____5536)  in
          EBufSub uu____5530
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
             FStar_Extraction_ML_Syntax.loc = uu____5542;_},e1::e2::[])
          when
          let uu____5551 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5551 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5553;
                  FStar_Extraction_ML_Syntax.loc = uu____5554;_},uu____5555);
             FStar_Extraction_ML_Syntax.mlty = uu____5556;
             FStar_Extraction_ML_Syntax.loc = uu____5557;_},e1::e2::[])
          when
          (let uu____5568 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5568 = "FStar.Buffer.offset") ||
            (let uu____5570 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5570 = "LowStar.Buffer.offset")
          ->
          let uu____5571 =
            let uu____5576 = translate_expr env e1  in
            let uu____5577 = translate_expr env e2  in
            (uu____5576, uu____5577)  in
          EBufSub uu____5571
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5579;
                  FStar_Extraction_ML_Syntax.loc = uu____5580;_},uu____5581);
             FStar_Extraction_ML_Syntax.mlty = uu____5582;
             FStar_Extraction_ML_Syntax.loc = uu____5583;_},e1::e2::e3::[])
          when
          ((let uu____5595 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5595 = "FStar.Buffer.upd") ||
             (let uu____5597 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5597 = "FStar.Buffer.op_Array_Assignment"))
            ||
            (let uu____5599 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5599 = "LowStar.Buffer.upd")
          ->
          let uu____5600 =
            let uu____5607 = translate_expr env e1  in
            let uu____5608 = translate_expr env e2  in
            let uu____5609 = translate_expr env e3  in
            (uu____5607, uu____5608, uu____5609)  in
          EBufWrite uu____5600
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5611;
                  FStar_Extraction_ML_Syntax.loc = uu____5612;_},uu____5613);
             FStar_Extraction_ML_Syntax.mlty = uu____5614;
             FStar_Extraction_ML_Syntax.loc = uu____5615;_},e1::e2::[])
          when
          let uu____5624 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5624 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5625 =
            let uu____5632 = translate_expr env e1  in
            let uu____5633 = translate_expr env e2  in
            (uu____5632, (EConstant (UInt32, "0")), uu____5633)  in
          EBufWrite uu____5625
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5635;
             FStar_Extraction_ML_Syntax.loc = uu____5636;_},uu____5637::[])
          when
          let uu____5640 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5640 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5642;
             FStar_Extraction_ML_Syntax.loc = uu____5643;_},uu____5644::[])
          when
          let uu____5647 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5647 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5649;
                  FStar_Extraction_ML_Syntax.loc = uu____5650;_},uu____5651);
             FStar_Extraction_ML_Syntax.mlty = uu____5652;
             FStar_Extraction_ML_Syntax.loc = uu____5653;_},e1::e2::e3::e4::e5::[])
          when
          (let uu____5667 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5667 = "FStar.Buffer.blit") ||
            (let uu____5669 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5669 = "LowStar.BufferOps.blit")
          ->
          let uu____5670 =
            let uu____5681 = translate_expr env e1  in
            let uu____5682 = translate_expr env e2  in
            let uu____5683 = translate_expr env e3  in
            let uu____5684 = translate_expr env e4  in
            let uu____5685 = translate_expr env e5  in
            (uu____5681, uu____5682, uu____5683, uu____5684, uu____5685)  in
          EBufBlit uu____5670
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5687;
                  FStar_Extraction_ML_Syntax.loc = uu____5688;_},uu____5689);
             FStar_Extraction_ML_Syntax.mlty = uu____5690;
             FStar_Extraction_ML_Syntax.loc = uu____5691;_},e1::e2::e3::[])
          when
          let uu____5701 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5701 = "FStar.Buffer.fill" ->
          let uu____5702 =
            let uu____5709 = translate_expr env e1  in
            let uu____5710 = translate_expr env e2  in
            let uu____5711 = translate_expr env e3  in
            (uu____5709, uu____5710, uu____5711)  in
          EBufFill uu____5702
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5713;
             FStar_Extraction_ML_Syntax.loc = uu____5714;_},uu____5715::[])
          when
          let uu____5718 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5718 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5720;
             FStar_Extraction_ML_Syntax.loc = uu____5721;_},e1::[])
          when
          let uu____5725 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5725 = "Obj.repr" ->
          let uu____5726 =
            let uu____5731 = translate_expr env e1  in (uu____5731, TAny)  in
          ECast uu____5726
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5734;
             FStar_Extraction_ML_Syntax.loc = uu____5735;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5743 = FStar_Util.must (mk_width m)  in
          let uu____5744 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____5743 uu____5744 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5746;
             FStar_Extraction_ML_Syntax.loc = uu____5747;_},args)
          when is_bool_op op ->
          let uu____5755 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____5755 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5757;
             FStar_Extraction_ML_Syntax.loc = uu____5758;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5760;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5761;_}::[])
          when is_machine_int m ->
          let uu____5776 =
            let uu____5781 = FStar_Util.must (mk_width m)  in (uu____5781, c)
             in
          EConstant uu____5776
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5783;
             FStar_Extraction_ML_Syntax.loc = uu____5784;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5786;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5787;_}::[])
          when is_machine_int m ->
          let uu____5802 =
            let uu____5807 = FStar_Util.must (mk_width m)  in (uu____5807, c)
             in
          EConstant uu____5802
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5808;
             FStar_Extraction_ML_Syntax.loc = uu____5809;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5811;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5812;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5818 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5819;
             FStar_Extraction_ML_Syntax.loc = uu____5820;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5822;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5823;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5829 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5831;
             FStar_Extraction_ML_Syntax.loc = uu____5832;_},arg::[])
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
            let uu____5839 =
              let uu____5844 = translate_expr env arg  in
              (uu____5844, (TInt UInt64))  in
            ECast uu____5839
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5846 =
                 let uu____5851 = translate_expr env arg  in
                 (uu____5851, (TInt UInt32))  in
               ECast uu____5846)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5853 =
                   let uu____5858 = translate_expr env arg  in
                   (uu____5858, (TInt UInt16))  in
                 ECast uu____5853)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5860 =
                     let uu____5865 = translate_expr env arg  in
                     (uu____5865, (TInt UInt8))  in
                   ECast uu____5860)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5867 =
                       let uu____5872 = translate_expr env arg  in
                       (uu____5872, (TInt Int64))  in
                     ECast uu____5867)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5874 =
                         let uu____5879 = translate_expr env arg  in
                         (uu____5879, (TInt Int32))  in
                       ECast uu____5874)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5881 =
                           let uu____5886 = translate_expr env arg  in
                           (uu____5886, (TInt Int16))  in
                         ECast uu____5881)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5888 =
                             let uu____5893 = translate_expr env arg  in
                             (uu____5893, (TInt Int8))  in
                           ECast uu____5888)
                        else
                          (let uu____5895 =
                             let uu____5902 =
                               let uu____5905 = translate_expr env arg  in
                               [uu____5905]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5902)
                              in
                           EApp uu____5895)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5916 =
            let uu____5923 = translate_expr env head1  in
            let uu____5924 = FStar_List.map (translate_expr env) args  in
            (uu____5923, uu____5924)  in
          EApp uu____5916
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5935 =
            let uu____5942 = translate_expr env head1  in
            let uu____5943 = FStar_List.map (translate_type env) ty_args  in
            (uu____5942, uu____5943)  in
          ETypApp uu____5935
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5951 =
            let uu____5956 = translate_expr env e1  in
            let uu____5957 = translate_type env t_to  in
            (uu____5956, uu____5957)  in
          ECast uu____5951
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5958,fields) ->
          let uu____5976 =
            let uu____5987 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5988 =
              FStar_List.map
                (fun uu____6007  ->
                   match uu____6007 with
                   | (field,expr) ->
                       let uu____6018 = translate_expr env expr  in
                       (field, uu____6018)) fields
               in
            (uu____5987, uu____5988)  in
          EFlat uu____5976
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____6027 =
            let uu____6034 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____6035 = translate_expr env e1  in
            (uu____6034, uu____6035, (FStar_Pervasives_Native.snd path))  in
          EField uu____6027
      | FStar_Extraction_ML_Syntax.MLE_Let uu____6038 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____6050) ->
          let uu____6055 =
            let uu____6056 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____6056
             in
          failwith uu____6055
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____6062 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____6062
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____6068 = FStar_List.map (translate_expr env) es  in
          ETuple uu____6068
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____6071,cons1),es) ->
          let uu____6082 =
            let uu____6091 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____6092 = FStar_List.map (translate_expr env) es  in
            (uu____6091, cons1, uu____6092)  in
          ECons uu____6082
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____6115 =
            let uu____6124 = translate_expr env1 body  in
            let uu____6125 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____6124, uu____6125)  in
          EFun uu____6115
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____6135 =
            let uu____6142 = translate_expr env e1  in
            let uu____6143 = translate_expr env e2  in
            let uu____6144 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____6142, uu____6143, uu____6144)  in
          EIfThenElse uu____6135
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____6146 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____6153 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____6168 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____6183 =
              let uu____6196 = FStar_List.map (translate_type env) ts  in
              (lid, uu____6196)  in
            TApp uu____6183
          else TQualified lid
      | uu____6208 -> failwith "invalid argument: assert_lid"

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
    fun uu____6234  ->
      match uu____6234 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____6260 = translate_pat env pat  in
            (match uu____6260 with
             | (env1,pat1) ->
                 let uu____6271 = translate_expr env1 expr  in
                 (pat1, uu____6271))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___271_6277  ->
    match uu___271_6277 with
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
          let uu____6341 =
            let uu____6342 =
              let uu____6347 = translate_width sw  in (uu____6347, s)  in
            PConstant uu____6342  in
          (env, uu____6341)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____6351,cons1),ps) ->
          let uu____6362 =
            FStar_List.fold_left
              (fun uu____6382  ->
                 fun p1  ->
                   match uu____6382 with
                   | (env1,acc) ->
                       let uu____6402 = translate_pat env1 p1  in
                       (match uu____6402 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6362 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____6431,ps) ->
          let uu____6449 =
            FStar_List.fold_left
              (fun uu____6483  ->
                 fun uu____6484  ->
                   match (uu____6483, uu____6484) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____6553 = translate_pat env1 p1  in
                       (match uu____6553 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____6449 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____6615 =
            FStar_List.fold_left
              (fun uu____6635  ->
                 fun p1  ->
                   match uu____6635 with
                   | (env1,acc) ->
                       let uu____6655 = translate_pat env1 p1  in
                       (match uu____6655 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6615 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6682 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6687 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____6698 =
            let uu____6699 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____6699
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____6698
          then
            let uu____6711 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____6711
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6724) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6739 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6740 ->
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
          let uu____6761 =
            let uu____6768 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____6768)  in
          EApp uu____6761
