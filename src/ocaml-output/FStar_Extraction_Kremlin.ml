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
  | DTypeAbstractStruct of (Prims.string Prims.list,Prims.string)
  FStar_Pervasives_Native.tuple2 
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
  | EBufCreateNoInit of (lifetime,expr) FStar_Pervasives_Native.tuple2 
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
    match projectee with | DGlobal _0 -> true | uu____641 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,Prims.int,typ,expr)
      FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____735 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr) FStar_Pervasives_Native.tuple7)
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____843 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,typ) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____931 -> false
  
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
    match projectee with | DExternal _0 -> true | uu____1041 -> false
  
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
    match projectee with | DTypeVariant _0 -> true | uu____1141 -> false
  
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
let (uu___is_DTypeAbstractStruct : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DTypeAbstractStruct _0 -> true
    | uu____1257 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1288 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1294 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1300 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1306 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1312 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1318 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1324 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1330 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1337 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1350 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1357 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1371 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1385 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____1398 -> false
  
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1404 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1410 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1416 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1423 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1443 -> false
  
let (__proj__EQualified__item___0 :
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1479 -> false
  
let (__proj__EConstant__item___0 :
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1504 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1517 -> false
  
let (__proj__EApp__item___0 :
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1555 -> false
  
let (__proj__ETypApp__item___0 :
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1593 -> false
  
let (__proj__ELet__item___0 :
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1631 -> false
  
let (__proj__EIfThenElse__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1665 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1689 -> false
  
let (__proj__EAssign__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____1721 -> false
  
let (__proj__EBufCreate__item___0 :
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____1757 -> false
  
let (__proj__EBufRead__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____1789 -> false
  
let (__proj__EBufWrite__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____1825 -> false
  
let (__proj__EBufSub__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____1861 -> false
  
let (__proj__EBufBlit__item___0 :
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5) =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____1915 -> false
  
let (__proj__EMatch__item___0 :
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1963 -> false
  
let (__proj__EOp__item___0 :
  expr -> (op,width) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1993 -> false
  
let (__proj__ECast__item___0 :
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____2018 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____2024 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____2031 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____2044 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____2050 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____2057 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____2081 -> false
  
let (__proj__EFlat__item___0 :
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____2131 -> false
  
let (__proj__EField__item___0 :
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____2167 -> false
  
let (__proj__EWhile__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____2199 -> false
  
let (__proj__EBufCreateL__item___0 :
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2233 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2261 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2305 -> false
  
let (__proj__EBufFill__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2337 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2359 -> false
  
let (__proj__EFun__item___0 :
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2397 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____2411 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____2429 -> false
  
let (__proj__EBufCreateNoInit__item___0 :
  expr -> (lifetime,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____2454 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2460 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____2466 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2472 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____2478 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2484 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2490 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2496 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____2502 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____2508 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2514 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2520 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2526 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2532 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2538 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____2544 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____2550 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____2556 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____2562 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____2568 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____2574 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____2580 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____2586 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____2592 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____2598 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2604 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2611 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2625 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2645 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2679 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2705 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list)
  = fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____2741 -> false
  
let (__proj__PConstant__item___0 :
  pattern -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____2766 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2772 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2778 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2784 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2790 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2796 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2802 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2808 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2814 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____2820 -> false
  
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
    match projectee with | TInt _0 -> true | uu____2851 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2865 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2878 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2891 -> false
  
let (__proj__TQualified__item___0 :
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2922 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2928 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2939 -> false
  
let (__proj__TArrow__item___0 :
  typ -> (typ,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2965 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2991 -> false
  
let (__proj__TApp__item___0 :
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____3043 -> false
  
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
  'Auu____3123 'Auu____3124 'Auu____3125 .
    ('Auu____3123,'Auu____3124,'Auu____3125) FStar_Pervasives_Native.tuple3
      -> 'Auu____3123
  = fun uu____3136  -> match uu____3136 with | (x,uu____3144,uu____3145) -> x 
let snd3 :
  'Auu____3154 'Auu____3155 'Auu____3156 .
    ('Auu____3154,'Auu____3155,'Auu____3156) FStar_Pervasives_Native.tuple3
      -> 'Auu____3155
  = fun uu____3167  -> match uu____3167 with | (uu____3174,x,uu____3176) -> x 
let thd3 :
  'Auu____3185 'Auu____3186 'Auu____3187 .
    ('Auu____3185,'Auu____3186,'Auu____3187) FStar_Pervasives_Native.tuple3
      -> 'Auu____3187
  = fun uu____3198  -> match uu____3198 with | (uu____3205,uu____3206,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___275_3214  ->
    match uu___275_3214 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____3217 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___276_3224  ->
    match uu___276_3224 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____3227 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___277_3241  ->
    match uu___277_3241 with
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
    | uu____3244 -> FStar_Pervasives_Native.None
  
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
      let uu___283_3364 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___283_3364.names_t);
        module_name = (uu___283_3364.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___284_3375 = env  in
      {
        names = (uu___284_3375.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___284_3375.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____3386 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____3386 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___286_3403  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___285_3408 ->
          let uu____3409 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____3409
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___288_3421  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___287_3426 ->
          let uu____3427 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____3427
  
let add_binders :
  'Auu____3434 .
    env ->
      (Prims.string,'Auu____3434) FStar_Pervasives_Native.tuple2 Prims.list
        -> env
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____3466  ->
             match uu____3466 with | (name,uu____3472) -> extend env1 name)
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
      | uu____3509 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____3724  ->
    match uu____3724 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3772 = m  in
               match uu____3772 with
               | (path,uu____3786,uu____3787) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___290_3805  ->
                  match () with
                  | () ->
                      (FStar_Util.print1
                         "Attempting to translate module %s\n" m_name;
                       (let uu____3809 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____3809))) ()
             with
             | e ->
                 ((let uu____3818 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3818);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath,(FStar_Extraction_ML_Syntax.mlsig,
                                       FStar_Extraction_ML_Syntax.mlmodule)
                                       FStar_Pervasives_Native.tuple2
                                       FStar_Pervasives_Native.option,
    FStar_Extraction_ML_Syntax.mllib) FStar_Pervasives_Native.tuple3 -> 
    file)
  =
  fun uu____3819  ->
    match uu____3819 with
    | (module_name,modul,uu____3834) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____3861 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags1  ->
    FStar_List.choose
      (fun uu___278_3872  ->
         match uu___278_3872 with
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
         | uu____3879 -> FStar_Pervasives_Native.None) flags1

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags1  ->
    let uu____3883 =
      FStar_List.choose
        (fun uu___279_3888  ->
           match uu___279_3888 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____3892 -> FStar_Pervasives_Native.None) flags1
       in
    match uu____3883 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____3895 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3908 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3910 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____3914) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3936;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____3939;
                FStar_Extraction_ML_Syntax.loc = uu____3940;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3942;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___280_3960  ->
                      match uu___280_3960 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____3961 -> false) meta
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
               let rec find_return_type eff i uu___281_3988 =
                 match uu___281_3988 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3993,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (eff, t)  in
               let uu____3997 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____3997 with
               | (eff,t) ->
                   let t1 = translate_type env2 t  in
                   let binders = translate_binders env2 args  in
                   let env3 = add_binders env2 args  in
                   let name1 = ((env3.module_name), name)  in
                   let cc = translate_cc meta  in
                   let meta1 =
                     match (eff, t1) with
                     | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____4032) ->
                         let uu____4033 = translate_flags meta  in
                         MustDisappear :: uu____4033
                     | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                         let uu____4036 = translate_flags meta  in
                         MustDisappear :: uu____4036
                     | uu____4039 -> translate_flags meta  in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____4048 =
                          let uu____4049 =
                            let uu____4068 = translate_type env3 t0  in
                            (cc, meta1, name1, uu____4068)  in
                          DExternal uu____4049  in
                        FStar_Pervasives_Native.Some uu____4048
                      else
                        ((let uu____4081 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1
                             in
                          FStar_Util.print1_warning
                            "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                            uu____4081);
                         FStar_Pervasives_Native.None))
                   else
                     (try
                        (fun uu___292_4087  ->
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
                          ((let uu____4114 =
                              let uu____4119 =
                                let uu____4120 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1
                                   in
                                FStar_Util.format2
                                  "Error while extracting %s to KreMLin (%s)\n"
                                  uu____4120 msg
                                 in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____4119)
                               in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____4114);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4137;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Coerce
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____4140;
                     FStar_Extraction_ML_Syntax.loc = uu____4141;_},uu____4142,uu____4143);
                FStar_Extraction_ML_Syntax.mlty = uu____4144;
                FStar_Extraction_ML_Syntax.loc = uu____4145;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4147;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___280_4165  ->
                      match uu___280_4165 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____4166 -> false) meta
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
               let rec find_return_type eff i uu___281_4193 =
                 match uu___281_4193 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____4198,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (eff, t)  in
               let uu____4202 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____4202 with
               | (eff,t) ->
                   let t1 = translate_type env2 t  in
                   let binders = translate_binders env2 args  in
                   let env3 = add_binders env2 args  in
                   let name1 = ((env3.module_name), name)  in
                   let cc = translate_cc meta  in
                   let meta1 =
                     match (eff, t1) with
                     | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____4237) ->
                         let uu____4238 = translate_flags meta  in
                         MustDisappear :: uu____4238
                     | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                         let uu____4241 = translate_flags meta  in
                         MustDisappear :: uu____4241
                     | uu____4244 -> translate_flags meta  in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____4253 =
                          let uu____4254 =
                            let uu____4273 = translate_type env3 t0  in
                            (cc, meta1, name1, uu____4273)  in
                          DExternal uu____4254  in
                        FStar_Pervasives_Native.Some uu____4253
                      else
                        ((let uu____4286 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1
                             in
                          FStar_Util.print1_warning
                            "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                            uu____4286);
                         FStar_Pervasives_Native.None))
                   else
                     (try
                        (fun uu___292_4292  ->
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
                          ((let uu____4319 =
                              let uu____4324 =
                                let uu____4325 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1
                                   in
                                FStar_Util.format2
                                  "Error while extracting %s to KreMLin (%s)\n"
                                  uu____4325 msg
                                 in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____4324)
                               in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____4319);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4342;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4345;_} ->
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
                 (fun uu___294_4371  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____4391 =
                       let uu____4396 =
                         let uu____4397 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____4398 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____4397
                           uu____4398
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____4396)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____4391);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4409;
            FStar_Extraction_ML_Syntax.mllb_def = uu____4410;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____4411;
            FStar_Extraction_ML_Syntax.print_typ = uu____4412;_} ->
            ((let uu____4416 =
                let uu____4421 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____4421)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____4416);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____4425 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____4425
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____4432 = ty  in
      match uu____4432 with
      | (uu____4435,uu____4436,uu____4437,uu____4438,flags1,uu____4440) ->
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
                 if
                   assumed &&
                     (FStar_List.mem FStar_Extraction_ML_Syntax.CAbstract
                        flags2)
                 then
                   FStar_Pervasives_Native.Some (DTypeAbstractStruct name1)
                 else
                   if assumed
                   then
                     (let name2 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                      FStar_Util.print1_warning
                        "Not extracting type definition %s to KreMLin (assumed type)\n"
                        name2;
                      FStar_Pervasives_Native.None)
                   else
                     (let uu____4488 =
                        let uu____4489 =
                          let uu____4506 = translate_flags flags2  in
                          let uu____4509 = translate_type env1 t  in
                          (name1, uu____4506, (FStar_List.length args),
                            uu____4509)
                           in
                        DTypeAlias uu____4489  in
                      FStar_Pervasives_Native.Some uu____4488)
             | (uu____4518,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____4550 =
                   let uu____4551 =
                     let uu____4578 = translate_flags flags2  in
                     let uu____4581 =
                       FStar_List.map
                         (fun uu____4608  ->
                            match uu____4608 with
                            | (f,t) ->
                                let uu____4623 =
                                  let uu____4628 = translate_type env1 t  in
                                  (uu____4628, false)  in
                                (f, uu____4623)) fields
                        in
                     (name1, uu____4578, (FStar_List.length args),
                       uu____4581)
                      in
                   DTypeFlat uu____4551  in
                 FStar_Pervasives_Native.Some uu____4550
             | (uu____4651,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags3 = translate_flags flags2  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____4688 =
                   let uu____4689 =
                     let uu____4722 =
                       FStar_List.map
                         (fun uu____4767  ->
                            match uu____4767 with
                            | (cons1,ts) ->
                                let uu____4806 =
                                  FStar_List.map
                                    (fun uu____4833  ->
                                       match uu____4833 with
                                       | (name2,t) ->
                                           let uu____4848 =
                                             let uu____4853 =
                                               translate_type env1 t  in
                                             (uu____4853, false)  in
                                           (name2, uu____4848)) ts
                                   in
                                (cons1, uu____4806)) branches
                        in
                     (name1, flags3, (FStar_List.length args), uu____4722)
                      in
                   DTypeVariant uu____4689  in
                 FStar_Pervasives_Native.Some uu____4688
             | (uu____4892,name,_mangled_name,uu____4895,uu____4896,uu____4897)
                 ->
                 ((let uu____4907 =
                     let uu____4912 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____4912)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____4907);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4916 = find_t env name  in TBound uu____4916
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4918,t2) ->
          let uu____4920 =
            let uu____4925 = translate_type env t1  in
            let uu____4926 = translate_type env t2  in
            (uu____4925, uu____4926)  in
          TArrow uu____4920
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4930 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4930 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4934 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4934 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4940 = FStar_Util.must (mk_width m)  in TInt uu____4940
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4946 = FStar_Util.must (mk_width m)  in TInt uu____4946
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4951 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4951 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____4952::arg::uu____4954::[],p) when
          (((let uu____4960 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4960 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____4962 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4962 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____4964 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4964 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____4966 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4966 = "FStar.HyperStack.ST.s_mref")
          -> let uu____4967 = translate_type env arg  in TBuf uu____4967
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____4969::[],p) when
          ((((((((((let uu____4975 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4975 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____4977 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4977 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____4979 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4979 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____4981 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4981 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____4983 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4983 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____4985 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4985 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____4987 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4987 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____4989 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4989 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____4991 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4991 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____4993 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4993 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____4995 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4995 = "FStar.HyperStack.ST.mmmref")
          -> let uu____4996 = translate_type env arg  in TBuf uu____4996
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____4998::uu____4999::[],p) when
          let uu____5003 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5003 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____5004 = translate_type env arg  in TBuf uu____5004
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____5011 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____5011 = "FStar.Buffer.buffer") ||
                        (let uu____5013 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____5013 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____5015 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____5015 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____5017 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____5017 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____5019 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____5019 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____5021 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____5021 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____5023 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____5023 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____5025 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____5025 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____5027 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____5027 = "FStar.HyperStack.mmref"))
                ||
                (let uu____5029 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____5029 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____5031 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____5031 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____5033 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____5033 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____5035 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5035 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____5037 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5037 = "FStar.HyperStack.ST.mmref")
          -> let uu____5038 = translate_type env arg  in TBuf uu____5038
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____5039::arg::[],p) when
          (let uu____5046 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5046 = "FStar.HyperStack.s_ref") ||
            (let uu____5048 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5048 = "FStar.HyperStack.ST.s_ref")
          -> let uu____5049 = translate_type env arg  in TBuf uu____5049
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____5050::[],p) when
          let uu____5054 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5054 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____5080 = FStar_List.map (translate_type env) args  in
          TTuple uu____5080
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____5089 =
              let uu____5102 = FStar_List.map (translate_type env) args  in
              (lid, uu____5102)  in
            TApp uu____5089
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____5117 = FStar_List.map (translate_type env) ts  in
          TTuple uu____5117

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
    fun uu____5133  ->
      match uu____5133 with
      | (name,typ) ->
          let uu____5140 = translate_type env typ  in
          { name; typ = uu____5140; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____5145 = find env name  in EBound uu____5145
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____5150 =
            let uu____5155 = FStar_Util.must (mk_op op)  in
            let uu____5156 = FStar_Util.must (mk_width m)  in
            (uu____5155, uu____5156)  in
          EOp uu____5150
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____5160 =
            let uu____5165 = FStar_Util.must (mk_bool_op op)  in
            (uu____5165, Bool)  in
          EOp uu____5160
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
            let uu____5184 = translate_type env typ  in
            { name; typ = uu____5184; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____5210 =
            let uu____5221 = translate_expr env expr  in
            let uu____5222 = translate_branches env branches  in
            (uu____5221, uu____5222)  in
          EMatch uu____5210
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5236;
                  FStar_Extraction_ML_Syntax.loc = uu____5237;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____5239;
             FStar_Extraction_ML_Syntax.loc = uu____5240;_},arg::[])
          when
          let uu____5246 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5246 = "FStar.Dyn.undyn" ->
          let uu____5247 =
            let uu____5252 = translate_expr env arg  in
            let uu____5253 = translate_type env t  in
            (uu____5252, uu____5253)  in
          ECast uu____5247
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5255;
                  FStar_Extraction_ML_Syntax.loc = uu____5256;_},uu____5257);
             FStar_Extraction_ML_Syntax.mlty = uu____5258;
             FStar_Extraction_ML_Syntax.loc = uu____5259;_},uu____5260)
          when
          let uu____5269 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5269 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5271;
                  FStar_Extraction_ML_Syntax.loc = uu____5272;_},uu____5273);
             FStar_Extraction_ML_Syntax.mlty = uu____5274;
             FStar_Extraction_ML_Syntax.loc = uu____5275;_},arg::[])
          when
          ((let uu____5285 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5285 = "FStar.HyperStack.All.failwith") ||
             (let uu____5287 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5287 = "FStar.Error.unexpected"))
            ||
            (let uu____5289 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5289 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____5291;
               FStar_Extraction_ML_Syntax.loc = uu____5292;_} -> EAbortS msg
           | uu____5293 ->
               let print7 =
                 let uu____5295 =
                   let uu____5296 =
                     let uu____5297 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____5297
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____5296  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____5295
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
                  FStar_Extraction_ML_Syntax.mlty = uu____5303;
                  FStar_Extraction_ML_Syntax.loc = uu____5304;_},uu____5305);
             FStar_Extraction_ML_Syntax.mlty = uu____5306;
             FStar_Extraction_ML_Syntax.loc = uu____5307;_},e1::[])
          when
          (let uu____5317 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5317 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____5319 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5319 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
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
             FStar_Extraction_ML_Syntax.loc = uu____5325;_},e1::e2::[])
          when
          (((let uu____5336 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5336 = "FStar.Buffer.index") ||
              (let uu____5338 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____5338 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____5340 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5340 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____5342 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5342 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____5343 =
            let uu____5348 = translate_expr env e1  in
            let uu____5349 = translate_expr env e2  in
            (uu____5348, uu____5349)  in
          EBufRead uu____5343
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5351;
                  FStar_Extraction_ML_Syntax.loc = uu____5352;_},uu____5353);
             FStar_Extraction_ML_Syntax.mlty = uu____5354;
             FStar_Extraction_ML_Syntax.loc = uu____5355;_},e1::[])
          when
          let uu____5363 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5363 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____5364 =
            let uu____5369 = translate_expr env e1  in
            (uu____5369, (EConstant (UInt32, "0")))  in
          EBufRead uu____5364
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5371;
                  FStar_Extraction_ML_Syntax.loc = uu____5372;_},uu____5373);
             FStar_Extraction_ML_Syntax.mlty = uu____5374;
             FStar_Extraction_ML_Syntax.loc = uu____5375;_},e1::e2::[])
          when
          (((let uu____5386 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5386 = "FStar.Buffer.create") ||
              (let uu____5388 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____5388 = "LowStar.Monotonic.Buffer.malloca"))
             ||
             (let uu____5390 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5390 = "LowStar.ImmutableBuffer.ialloca"))
            ||
            (let uu____5392 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5392 = "LowStar.UninitializedBuffer.ualloca")
          ->
          let uu____5393 =
            let uu____5400 = translate_expr env e1  in
            let uu____5401 = translate_expr env e2  in
            (Stack, uu____5400, uu____5401)  in
          EBufCreate uu____5393
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5403;
                  FStar_Extraction_ML_Syntax.loc = uu____5404;_},uu____5405);
             FStar_Extraction_ML_Syntax.mlty = uu____5406;
             FStar_Extraction_ML_Syntax.loc = uu____5407;_},init1::[])
          when
          let uu____5415 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5415 = "FStar.HyperStack.ST.salloc" ->
          let uu____5416 =
            let uu____5423 = translate_expr env init1  in
            (Stack, uu____5423, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5416
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
             FStar_Extraction_ML_Syntax.loc = uu____5429;_},e2::[])
          when
          ((let uu____5439 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5439 = "FStar.Buffer.createL") ||
             (let uu____5441 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5441 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____5443 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5443 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____5444 =
            let uu____5451 =
              let uu____5454 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____5454  in
            (Stack, uu____5451)  in
          EBufCreateL uu____5444
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5460;
                  FStar_Extraction_ML_Syntax.loc = uu____5461;_},uu____5462);
             FStar_Extraction_ML_Syntax.mlty = uu____5463;
             FStar_Extraction_ML_Syntax.loc = uu____5464;_},_erid::e2::[])
          when
          (let uu____5475 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5475 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____5477 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5477 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____5478 =
            let uu____5485 =
              let uu____5488 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____5488  in
            (Eternal, uu____5485)  in
          EBufCreateL uu____5478
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
             FStar_Extraction_ML_Syntax.loc = uu____5498;_},_rid::init1::[])
          when
          let uu____5507 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5507 = "FStar.HyperStack.ST.ralloc" ->
          let uu____5508 =
            let uu____5515 = translate_expr env init1  in
            (Eternal, uu____5515, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5508
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
             FStar_Extraction_ML_Syntax.loc = uu____5521;_},_e0::e1::e2::[])
          when
          ((let uu____5533 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5533 = "FStar.Buffer.rcreate") ||
             (let uu____5535 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5535 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____5537 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5537 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____5538 =
            let uu____5545 = translate_expr env e1  in
            let uu____5546 = translate_expr env e2  in
            (Eternal, uu____5545, uu____5546)  in
          EBufCreate uu____5538
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5548;
                  FStar_Extraction_ML_Syntax.loc = uu____5549;_},uu____5550);
             FStar_Extraction_ML_Syntax.mlty = uu____5551;
             FStar_Extraction_ML_Syntax.loc = uu____5552;_},_erid::elen::[])
          when
          let uu____5561 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5561 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____5562 =
            let uu____5567 = translate_expr env elen  in
            (Eternal, uu____5567)  in
          EBufCreateNoInit uu____5562
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5569;
                  FStar_Extraction_ML_Syntax.loc = uu____5570;_},uu____5571);
             FStar_Extraction_ML_Syntax.mlty = uu____5572;
             FStar_Extraction_ML_Syntax.loc = uu____5573;_},_rid::init1::[])
          when
          let uu____5582 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5582 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____5583 =
            let uu____5590 = translate_expr env init1  in
            (ManuallyManaged, uu____5590, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5583
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
             FStar_Extraction_ML_Syntax.loc = uu____5596;_},_e0::e1::e2::[])
          when
          ((((let uu____5608 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5608 = "FStar.Buffer.rcreate_mm") ||
               (let uu____5610 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____5610 = "LowStar.Monotonic.Buffer.mmalloc"))
              ||
              (let uu____5612 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____5612 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____5614 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5614 = "LowStar.ImmutableBuffer.imalloc"))
            ||
            (let uu____5616 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5616 = "LowStar.UninitializedBuffer.umalloc")
          ->
          let uu____5617 =
            let uu____5624 = translate_expr env e1  in
            let uu____5625 = translate_expr env e2  in
            (ManuallyManaged, uu____5624, uu____5625)  in
          EBufCreate uu____5617
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5627;
                  FStar_Extraction_ML_Syntax.loc = uu____5628;_},uu____5629);
             FStar_Extraction_ML_Syntax.mlty = uu____5630;
             FStar_Extraction_ML_Syntax.loc = uu____5631;_},e2::[])
          when
          let uu____5639 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5639 = "FStar.HyperStack.ST.rfree" ->
          let uu____5640 = translate_expr env e2  in EBufFree uu____5640
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5642;
                  FStar_Extraction_ML_Syntax.loc = uu____5643;_},uu____5644);
             FStar_Extraction_ML_Syntax.mlty = uu____5645;
             FStar_Extraction_ML_Syntax.loc = uu____5646;_},e2::[])
          when
          (let uu____5656 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5656 = "FStar.Buffer.rfree") ||
            (let uu____5658 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5658 = "LowStar.Monotonic.Buffer.free")
          -> let uu____5659 = translate_expr env e2  in EBufFree uu____5659
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5661;
                  FStar_Extraction_ML_Syntax.loc = uu____5662;_},uu____5663);
             FStar_Extraction_ML_Syntax.mlty = uu____5664;
             FStar_Extraction_ML_Syntax.loc = uu____5665;_},e1::e2::_e3::[])
          when
          let uu____5675 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5675 = "FStar.Buffer.sub" ->
          let uu____5676 =
            let uu____5681 = translate_expr env e1  in
            let uu____5682 = translate_expr env e2  in
            (uu____5681, uu____5682)  in
          EBufSub uu____5676
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5684;
                  FStar_Extraction_ML_Syntax.loc = uu____5685;_},uu____5686);
             FStar_Extraction_ML_Syntax.mlty = uu____5687;
             FStar_Extraction_ML_Syntax.loc = uu____5688;_},e1::e2::_e3::[])
          when
          let uu____5698 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5698 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____5699 =
            let uu____5704 = translate_expr env e1  in
            let uu____5705 = translate_expr env e2  in
            (uu____5704, uu____5705)  in
          EBufSub uu____5699
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5707;
                  FStar_Extraction_ML_Syntax.loc = uu____5708;_},uu____5709);
             FStar_Extraction_ML_Syntax.mlty = uu____5710;
             FStar_Extraction_ML_Syntax.loc = uu____5711;_},e1::e2::[])
          when
          let uu____5720 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5720 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5722;
                  FStar_Extraction_ML_Syntax.loc = uu____5723;_},uu____5724);
             FStar_Extraction_ML_Syntax.mlty = uu____5725;
             FStar_Extraction_ML_Syntax.loc = uu____5726;_},e1::e2::[])
          when
          let uu____5735 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5735 = "FStar.Buffer.offset" ->
          let uu____5736 =
            let uu____5741 = translate_expr env e1  in
            let uu____5742 = translate_expr env e2  in
            (uu____5741, uu____5742)  in
          EBufSub uu____5736
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5744;
                  FStar_Extraction_ML_Syntax.loc = uu____5745;_},uu____5746);
             FStar_Extraction_ML_Syntax.mlty = uu____5747;
             FStar_Extraction_ML_Syntax.loc = uu____5748;_},e1::e2::[])
          when
          let uu____5757 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5757 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____5758 =
            let uu____5763 = translate_expr env e1  in
            let uu____5764 = translate_expr env e2  in
            (uu____5763, uu____5764)  in
          EBufSub uu____5758
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5766;
                  FStar_Extraction_ML_Syntax.loc = uu____5767;_},uu____5768);
             FStar_Extraction_ML_Syntax.mlty = uu____5769;
             FStar_Extraction_ML_Syntax.loc = uu____5770;_},e1::e2::e3::[])
          when
          (((let uu____5782 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5782 = "FStar.Buffer.upd") ||
              (let uu____5784 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____5784 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____5786 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5786 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____5788 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5788 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____5789 =
            let uu____5796 = translate_expr env e1  in
            let uu____5797 = translate_expr env e2  in
            let uu____5798 = translate_expr env e3  in
            (uu____5796, uu____5797, uu____5798)  in
          EBufWrite uu____5789
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5800;
                  FStar_Extraction_ML_Syntax.loc = uu____5801;_},uu____5802);
             FStar_Extraction_ML_Syntax.mlty = uu____5803;
             FStar_Extraction_ML_Syntax.loc = uu____5804;_},e1::e2::[])
          when
          let uu____5813 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5813 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5814 =
            let uu____5821 = translate_expr env e1  in
            let uu____5822 = translate_expr env e2  in
            (uu____5821, (EConstant (UInt32, "0")), uu____5822)  in
          EBufWrite uu____5814
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5824;
             FStar_Extraction_ML_Syntax.loc = uu____5825;_},uu____5826::[])
          when
          let uu____5829 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5829 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5831;
             FStar_Extraction_ML_Syntax.loc = uu____5832;_},uu____5833::[])
          when
          let uu____5836 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5836 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5838;
                  FStar_Extraction_ML_Syntax.loc = uu____5839;_},uu____5840);
             FStar_Extraction_ML_Syntax.mlty = uu____5841;
             FStar_Extraction_ML_Syntax.loc = uu____5842;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____5856 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5856 = "FStar.Buffer.blit") ||
             (let uu____5858 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5858 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____5860 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5860 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____5861 =
            let uu____5872 = translate_expr env e1  in
            let uu____5873 = translate_expr env e2  in
            let uu____5874 = translate_expr env e3  in
            let uu____5875 = translate_expr env e4  in
            let uu____5876 = translate_expr env e5  in
            (uu____5872, uu____5873, uu____5874, uu____5875, uu____5876)  in
          EBufBlit uu____5861
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5878;
                  FStar_Extraction_ML_Syntax.loc = uu____5879;_},uu____5880);
             FStar_Extraction_ML_Syntax.mlty = uu____5881;
             FStar_Extraction_ML_Syntax.loc = uu____5882;_},e1::e2::e3::[])
          when
          let uu____5892 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5892 = "FStar.Buffer.fill" ->
          let uu____5893 =
            let uu____5900 = translate_expr env e1  in
            let uu____5901 = translate_expr env e2  in
            let uu____5902 = translate_expr env e3  in
            (uu____5900, uu____5901, uu____5902)  in
          EBufFill uu____5893
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5904;
             FStar_Extraction_ML_Syntax.loc = uu____5905;_},uu____5906::[])
          when
          let uu____5909 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5909 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5911;
                  FStar_Extraction_ML_Syntax.loc = uu____5912;_},uu____5913);
             FStar_Extraction_ML_Syntax.mlty = uu____5914;
             FStar_Extraction_ML_Syntax.loc = uu____5915;_},_ebuf::_eseq::[])
          when
          (((let uu____5926 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5926 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____5928 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____5928 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____5930 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5930 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____5932 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5932 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5934;
             FStar_Extraction_ML_Syntax.loc = uu____5935;_},e1::[])
          when
          let uu____5939 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5939 = "Obj.repr" ->
          let uu____5940 =
            let uu____5945 = translate_expr env e1  in (uu____5945, TAny)  in
          ECast uu____5940
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5948;
             FStar_Extraction_ML_Syntax.loc = uu____5949;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5957 = FStar_Util.must (mk_width m)  in
          let uu____5958 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____5957 uu____5958 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5960;
             FStar_Extraction_ML_Syntax.loc = uu____5961;_},args)
          when is_bool_op op ->
          let uu____5969 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____5969 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5971;
             FStar_Extraction_ML_Syntax.loc = uu____5972;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5974;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5975;_}::[])
          when is_machine_int m ->
          let uu____5990 =
            let uu____5995 = FStar_Util.must (mk_width m)  in (uu____5995, c)
             in
          EConstant uu____5990
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5997;
             FStar_Extraction_ML_Syntax.loc = uu____5998;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____6000;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____6001;_}::[])
          when is_machine_int m ->
          let uu____6016 =
            let uu____6021 = FStar_Util.must (mk_width m)  in (uu____6021, c)
             in
          EConstant uu____6016
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____6022;
             FStar_Extraction_ML_Syntax.loc = uu____6023;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____6025;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____6026;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____6032 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____6033;
             FStar_Extraction_ML_Syntax.loc = uu____6034;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____6036;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____6037;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____6043 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____6045;
             FStar_Extraction_ML_Syntax.loc = uu____6046;_},arg::[])
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
            let uu____6053 =
              let uu____6058 = translate_expr env arg  in
              (uu____6058, (TInt UInt64))  in
            ECast uu____6053
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____6060 =
                 let uu____6065 = translate_expr env arg  in
                 (uu____6065, (TInt UInt32))  in
               ECast uu____6060)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____6067 =
                   let uu____6072 = translate_expr env arg  in
                   (uu____6072, (TInt UInt16))  in
                 ECast uu____6067)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____6074 =
                     let uu____6079 = translate_expr env arg  in
                     (uu____6079, (TInt UInt8))  in
                   ECast uu____6074)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____6081 =
                       let uu____6086 = translate_expr env arg  in
                       (uu____6086, (TInt Int64))  in
                     ECast uu____6081)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____6088 =
                         let uu____6093 = translate_expr env arg  in
                         (uu____6093, (TInt Int32))  in
                       ECast uu____6088)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____6095 =
                           let uu____6100 = translate_expr env arg  in
                           (uu____6100, (TInt Int16))  in
                         ECast uu____6095)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____6102 =
                             let uu____6107 = translate_expr env arg  in
                             (uu____6107, (TInt Int8))  in
                           ECast uu____6102)
                        else
                          (let uu____6109 =
                             let uu____6116 =
                               let uu____6119 = translate_expr env arg  in
                               [uu____6119]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____6116)
                              in
                           EApp uu____6109)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____6130 =
            let uu____6137 = translate_expr env head1  in
            let uu____6138 = FStar_List.map (translate_expr env) args  in
            (uu____6137, uu____6138)  in
          EApp uu____6130
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____6149 =
            let uu____6156 = translate_expr env head1  in
            let uu____6157 = FStar_List.map (translate_type env) ty_args  in
            (uu____6156, uu____6157)  in
          ETypApp uu____6149
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____6165 =
            let uu____6170 = translate_expr env e1  in
            let uu____6171 = translate_type env t_to  in
            (uu____6170, uu____6171)  in
          ECast uu____6165
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____6172,fields) ->
          let uu____6190 =
            let uu____6201 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____6202 =
              FStar_List.map
                (fun uu____6221  ->
                   match uu____6221 with
                   | (field,expr) ->
                       let uu____6232 = translate_expr env expr  in
                       (field, uu____6232)) fields
               in
            (uu____6201, uu____6202)  in
          EFlat uu____6190
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____6241 =
            let uu____6248 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____6249 = translate_expr env e1  in
            (uu____6248, uu____6249, (FStar_Pervasives_Native.snd path))  in
          EField uu____6241
      | FStar_Extraction_ML_Syntax.MLE_Let uu____6252 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____6264) ->
          let uu____6269 =
            let uu____6270 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____6270
             in
          failwith uu____6269
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____6276 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____6276
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____6282 = FStar_List.map (translate_expr env) es  in
          ETuple uu____6282
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____6285,cons1),es) ->
          let uu____6296 =
            let uu____6305 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____6306 = FStar_List.map (translate_expr env) es  in
            (uu____6305, cons1, uu____6306)  in
          ECons uu____6296
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____6329 =
            let uu____6338 = translate_expr env1 body  in
            let uu____6339 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____6338, uu____6339)  in
          EFun uu____6329
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____6349 =
            let uu____6356 = translate_expr env e1  in
            let uu____6357 = translate_expr env e2  in
            let uu____6358 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____6356, uu____6357, uu____6358)  in
          EIfThenElse uu____6349
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____6360 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____6367 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____6382 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____6397 =
              let uu____6410 = FStar_List.map (translate_type env) ts  in
              (lid, uu____6410)  in
            TApp uu____6397
          else TQualified lid
      | uu____6422 -> failwith "invalid argument: assert_lid"

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
    fun uu____6448  ->
      match uu____6448 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____6474 = translate_pat env pat  in
            (match uu____6474 with
             | (env1,pat1) ->
                 let uu____6485 = translate_expr env1 expr  in
                 (pat1, uu____6485))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___282_6491  ->
    match uu___282_6491 with
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
          let uu____6555 =
            let uu____6556 =
              let uu____6561 = translate_width sw  in (uu____6561, s)  in
            PConstant uu____6556  in
          (env, uu____6555)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____6565,cons1),ps) ->
          let uu____6576 =
            FStar_List.fold_left
              (fun uu____6596  ->
                 fun p1  ->
                   match uu____6596 with
                   | (env1,acc) ->
                       let uu____6616 = translate_pat env1 p1  in
                       (match uu____6616 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6576 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____6645,ps) ->
          let uu____6663 =
            FStar_List.fold_left
              (fun uu____6697  ->
                 fun uu____6698  ->
                   match (uu____6697, uu____6698) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____6767 = translate_pat env1 p1  in
                       (match uu____6767 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____6663 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____6829 =
            FStar_List.fold_left
              (fun uu____6849  ->
                 fun p1  ->
                   match uu____6849 with
                   | (env1,acc) ->
                       let uu____6869 = translate_pat env1 p1  in
                       (match uu____6869 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6829 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6896 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6901 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____6912 =
            let uu____6913 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____6913
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____6912
          then
            let uu____6925 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____6925
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6938) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6953 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6954 ->
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
          let uu____6974 =
            let uu____6981 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____6981)  in
          EApp uu____6974
