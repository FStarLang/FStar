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
  fun uu___276_3214  ->
    match uu___276_3214 with
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
  fun uu___277_3224  ->
    match uu___277_3224 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____3227 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___278_3241  ->
    match uu___278_3241 with
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
      let uu___284_3364 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___284_3364.names_t);
        module_name = (uu___284_3364.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___285_3375 = env  in
      {
        names = (uu___285_3375.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___285_3375.module_name)
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
        (fun uu___287_3403  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___286_3408 ->
          let uu____3409 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____3409
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___289_3421  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___288_3426 ->
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
               (fun uu___291_3805  ->
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
      (fun uu___279_3872  ->
         match uu___279_3872 with
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
        (fun uu___280_3888  ->
           match uu___280_3888 with
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
                   (fun uu___281_3960  ->
                      match uu___281_3960 with
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
               let rec find_return_type eff i uu___282_3990 =
                 match uu___282_3990 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3997,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____4010 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____4010 with
               | (i,eff,t) ->
                   if i > (Prims.parse_int "0")
                   then
                     let msg =
                       "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                        in
                     ((let uu____4030 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____4030 msg);
                      FStar_Pervasives_Native.None)
                   else
                     (let t1 = translate_type env2 t  in
                      let binders = translate_binders env2 args  in
                      let env3 = add_binders env2 args  in
                      let cc = translate_cc meta  in
                      let meta1 =
                        match (eff, t1) with
                        | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____4045) ->
                            let uu____4046 = translate_flags meta  in
                            MustDisappear :: uu____4046
                        | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                            let uu____4049 = translate_flags meta  in
                            MustDisappear :: uu____4049
                        | uu____4052 -> translate_flags meta  in
                      if assumed
                      then
                        (if (FStar_List.length tvars) = (Prims.parse_int "0")
                         then
                           let uu____4061 =
                             let uu____4062 =
                               let uu____4081 = translate_type env3 t0  in
                               (cc, meta1, name1, uu____4081)  in
                             DExternal uu____4062  in
                           FStar_Pervasives_Native.Some uu____4061
                         else
                           ((let uu____4094 =
                               FStar_Extraction_ML_Syntax.string_of_mlpath
                                 name1
                                in
                             FStar_Util.print1_warning
                               "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                               uu____4094);
                            FStar_Pervasives_Native.None))
                      else
                        (try
                           (fun uu___293_4100  ->
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
                             ((let uu____4127 =
                                 let uu____4132 =
                                   let uu____4133 =
                                     FStar_Extraction_ML_Syntax.string_of_mlpath
                                       name1
                                      in
                                   FStar_Util.format2
                                     "Error while extracting %s to KreMLin (%s)\n"
                                     uu____4133 msg
                                    in
                                 (FStar_Errors.Warning_FunctionNotExtacted,
                                   uu____4132)
                                  in
                               FStar_Errors.log_issue FStar_Range.dummyRange
                                 uu____4127);
                              (let msg1 =
                                 Prims.strcat
                                   "This function was not extracted:\n" msg
                                  in
                               FStar_Pervasives_Native.Some
                                 (DFunction
                                    (cc, meta1, (FStar_List.length tvars),
                                      t1, name1, binders, (EAbortS msg1))))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4150;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Coerce
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____4153;
                     FStar_Extraction_ML_Syntax.loc = uu____4154;_},uu____4155,uu____4156);
                FStar_Extraction_ML_Syntax.mlty = uu____4157;
                FStar_Extraction_ML_Syntax.loc = uu____4158;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4160;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___281_4178  ->
                      match uu___281_4178 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____4179 -> false) meta
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
               let rec find_return_type eff i uu___282_4208 =
                 match uu___282_4208 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____4215,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____4228 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____4228 with
               | (i,eff,t) ->
                   if i > (Prims.parse_int "0")
                   then
                     let msg =
                       "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                        in
                     ((let uu____4248 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____4248 msg);
                      FStar_Pervasives_Native.None)
                   else
                     (let t1 = translate_type env2 t  in
                      let binders = translate_binders env2 args  in
                      let env3 = add_binders env2 args  in
                      let cc = translate_cc meta  in
                      let meta1 =
                        match (eff, t1) with
                        | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____4263) ->
                            let uu____4264 = translate_flags meta  in
                            MustDisappear :: uu____4264
                        | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                            let uu____4267 = translate_flags meta  in
                            MustDisappear :: uu____4267
                        | uu____4270 -> translate_flags meta  in
                      if assumed
                      then
                        (if (FStar_List.length tvars) = (Prims.parse_int "0")
                         then
                           let uu____4279 =
                             let uu____4280 =
                               let uu____4299 = translate_type env3 t0  in
                               (cc, meta1, name1, uu____4299)  in
                             DExternal uu____4280  in
                           FStar_Pervasives_Native.Some uu____4279
                         else
                           ((let uu____4312 =
                               FStar_Extraction_ML_Syntax.string_of_mlpath
                                 name1
                                in
                             FStar_Util.print1_warning
                               "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                               uu____4312);
                            FStar_Pervasives_Native.None))
                      else
                        (try
                           (fun uu___293_4318  ->
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
                             ((let uu____4345 =
                                 let uu____4350 =
                                   let uu____4351 =
                                     FStar_Extraction_ML_Syntax.string_of_mlpath
                                       name1
                                      in
                                   FStar_Util.format2
                                     "Error while extracting %s to KreMLin (%s)\n"
                                     uu____4351 msg
                                    in
                                 (FStar_Errors.Warning_FunctionNotExtacted,
                                   uu____4350)
                                  in
                               FStar_Errors.log_issue FStar_Range.dummyRange
                                 uu____4345);
                              (let msg1 =
                                 Prims.strcat
                                   "This function was not extracted:\n" msg
                                  in
                               FStar_Pervasives_Native.Some
                                 (DFunction
                                    (cc, meta1, (FStar_List.length tvars),
                                      t1, name1, binders, (EAbortS msg1))))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4368;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4371;_} ->
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
                 (fun uu___295_4397  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____4417 =
                       let uu____4422 =
                         let uu____4423 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____4424 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____4423
                           uu____4424
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____4422)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____4417);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4435;
            FStar_Extraction_ML_Syntax.mllb_def = uu____4436;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____4437;
            FStar_Extraction_ML_Syntax.print_typ = uu____4438;_} ->
            ((let uu____4442 =
                let uu____4447 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____4447)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____4442);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____4451 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____4451
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____4458 = ty  in
      match uu____4458 with
      | (uu____4461,uu____4462,uu____4463,uu____4464,flags1,uu____4466) ->
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
                     (let uu____4514 =
                        let uu____4515 =
                          let uu____4532 = translate_flags flags2  in
                          let uu____4535 = translate_type env1 t  in
                          (name1, uu____4532, (FStar_List.length args),
                            uu____4535)
                           in
                        DTypeAlias uu____4515  in
                      FStar_Pervasives_Native.Some uu____4514)
             | (uu____4544,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____4576 =
                   let uu____4577 =
                     let uu____4604 = translate_flags flags2  in
                     let uu____4607 =
                       FStar_List.map
                         (fun uu____4634  ->
                            match uu____4634 with
                            | (f,t) ->
                                let uu____4649 =
                                  let uu____4654 = translate_type env1 t  in
                                  (uu____4654, false)  in
                                (f, uu____4649)) fields
                        in
                     (name1, uu____4604, (FStar_List.length args),
                       uu____4607)
                      in
                   DTypeFlat uu____4577  in
                 FStar_Pervasives_Native.Some uu____4576
             | (uu____4677,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags3 = translate_flags flags2  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____4714 =
                   let uu____4715 =
                     let uu____4748 =
                       FStar_List.map
                         (fun uu____4793  ->
                            match uu____4793 with
                            | (cons1,ts) ->
                                let uu____4832 =
                                  FStar_List.map
                                    (fun uu____4859  ->
                                       match uu____4859 with
                                       | (name2,t) ->
                                           let uu____4874 =
                                             let uu____4879 =
                                               translate_type env1 t  in
                                             (uu____4879, false)  in
                                           (name2, uu____4874)) ts
                                   in
                                (cons1, uu____4832)) branches
                        in
                     (name1, flags3, (FStar_List.length args), uu____4748)
                      in
                   DTypeVariant uu____4715  in
                 FStar_Pervasives_Native.Some uu____4714
             | (uu____4918,name,_mangled_name,uu____4921,uu____4922,uu____4923)
                 ->
                 ((let uu____4933 =
                     let uu____4938 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____4938)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____4933);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4942 = find_t env name  in TBound uu____4942
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4944,t2) ->
          let uu____4946 =
            let uu____4951 = translate_type env t1  in
            let uu____4952 = translate_type env t2  in
            (uu____4951, uu____4952)  in
          TArrow uu____4946
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4956 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4956 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4960 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4960 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4966 = FStar_Util.must (mk_width m)  in TInt uu____4966
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4972 = FStar_Util.must (mk_width m)  in TInt uu____4972
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4977 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4977 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____4978::arg::uu____4980::[],p) when
          (((let uu____4986 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4986 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____4988 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4988 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____4990 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4990 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____4992 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4992 = "FStar.HyperStack.ST.s_mref")
          -> let uu____4993 = translate_type env arg  in TBuf uu____4993
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____4995::[],p) when
          ((((((((((let uu____5001 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____5001 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____5003 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____5003 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____5005 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____5005 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____5007 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____5007 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____5009 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____5009 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____5011 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____5011 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____5013 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____5013 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____5015 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____5015 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____5017 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____5017 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____5019 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5019 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____5021 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5021 = "FStar.HyperStack.ST.mmmref")
          -> let uu____5022 = translate_type env arg  in TBuf uu____5022
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____5024::uu____5025::[],p) when
          let uu____5029 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5029 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____5030 = translate_type env arg  in TBuf uu____5030
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____5037 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____5037 = "FStar.Buffer.buffer") ||
                        (let uu____5039 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____5039 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____5041 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____5041 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____5043 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____5043 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____5045 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____5045 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____5047 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____5047 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____5049 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____5049 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____5051 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____5051 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____5053 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____5053 = "FStar.HyperStack.mmref"))
                ||
                (let uu____5055 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____5055 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____5057 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____5057 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____5059 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____5059 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____5061 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5061 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____5063 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5063 = "FStar.HyperStack.ST.mmref")
          -> let uu____5064 = translate_type env arg  in TBuf uu____5064
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____5065::arg::[],p) when
          (let uu____5072 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5072 = "FStar.HyperStack.s_ref") ||
            (let uu____5074 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5074 = "FStar.HyperStack.ST.s_ref")
          -> let uu____5075 = translate_type env arg  in TBuf uu____5075
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____5076::[],p) when
          let uu____5080 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5080 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____5106 = FStar_List.map (translate_type env) args  in
          TTuple uu____5106
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____5115 =
              let uu____5128 = FStar_List.map (translate_type env) args  in
              (lid, uu____5128)  in
            TApp uu____5115
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____5143 = FStar_List.map (translate_type env) ts  in
          TTuple uu____5143

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
    fun uu____5159  ->
      match uu____5159 with
      | (name,typ) ->
          let uu____5166 = translate_type env typ  in
          { name; typ = uu____5166; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____5171 = find env name  in EBound uu____5171
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____5176 =
            let uu____5181 = FStar_Util.must (mk_op op)  in
            let uu____5182 = FStar_Util.must (mk_width m)  in
            (uu____5181, uu____5182)  in
          EOp uu____5176
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____5186 =
            let uu____5191 = FStar_Util.must (mk_bool_op op)  in
            (uu____5191, Bool)  in
          EOp uu____5186
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
            let uu____5210 = translate_type env typ  in
            { name; typ = uu____5210; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____5236 =
            let uu____5247 = translate_expr env expr  in
            let uu____5248 = translate_branches env branches  in
            (uu____5247, uu____5248)  in
          EMatch uu____5236
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5262;
                  FStar_Extraction_ML_Syntax.loc = uu____5263;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____5265;
             FStar_Extraction_ML_Syntax.loc = uu____5266;_},arg::[])
          when
          let uu____5272 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5272 = "FStar.Dyn.undyn" ->
          let uu____5273 =
            let uu____5278 = translate_expr env arg  in
            let uu____5279 = translate_type env t  in
            (uu____5278, uu____5279)  in
          ECast uu____5273
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5281;
                  FStar_Extraction_ML_Syntax.loc = uu____5282;_},uu____5283);
             FStar_Extraction_ML_Syntax.mlty = uu____5284;
             FStar_Extraction_ML_Syntax.loc = uu____5285;_},uu____5286)
          when
          let uu____5295 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5295 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5297;
                  FStar_Extraction_ML_Syntax.loc = uu____5298;_},uu____5299);
             FStar_Extraction_ML_Syntax.mlty = uu____5300;
             FStar_Extraction_ML_Syntax.loc = uu____5301;_},arg::[])
          when
          ((let uu____5311 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5311 = "FStar.HyperStack.All.failwith") ||
             (let uu____5313 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5313 = "FStar.Error.unexpected"))
            ||
            (let uu____5315 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5315 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____5317;
               FStar_Extraction_ML_Syntax.loc = uu____5318;_} -> EAbortS msg
           | uu____5319 ->
               let print7 =
                 let uu____5321 =
                   let uu____5322 =
                     let uu____5323 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____5323
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____5322  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____5321
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
                  FStar_Extraction_ML_Syntax.mlty = uu____5329;
                  FStar_Extraction_ML_Syntax.loc = uu____5330;_},uu____5331);
             FStar_Extraction_ML_Syntax.mlty = uu____5332;
             FStar_Extraction_ML_Syntax.loc = uu____5333;_},e1::[])
          when
          (let uu____5343 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5343 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____5345 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5345 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5347;
                  FStar_Extraction_ML_Syntax.loc = uu____5348;_},uu____5349);
             FStar_Extraction_ML_Syntax.mlty = uu____5350;
             FStar_Extraction_ML_Syntax.loc = uu____5351;_},e1::e2::[])
          when
          (((let uu____5362 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5362 = "FStar.Buffer.index") ||
              (let uu____5364 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____5364 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____5366 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5366 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____5368 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5368 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____5369 =
            let uu____5374 = translate_expr env e1  in
            let uu____5375 = translate_expr env e2  in
            (uu____5374, uu____5375)  in
          EBufRead uu____5369
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5377;
                  FStar_Extraction_ML_Syntax.loc = uu____5378;_},uu____5379);
             FStar_Extraction_ML_Syntax.mlty = uu____5380;
             FStar_Extraction_ML_Syntax.loc = uu____5381;_},e1::[])
          when
          let uu____5389 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5389 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____5390 =
            let uu____5395 = translate_expr env e1  in
            (uu____5395, (EConstant (UInt32, "0")))  in
          EBufRead uu____5390
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5397;
                  FStar_Extraction_ML_Syntax.loc = uu____5398;_},uu____5399);
             FStar_Extraction_ML_Syntax.mlty = uu____5400;
             FStar_Extraction_ML_Syntax.loc = uu____5401;_},e1::e2::[])
          when
          (((let uu____5412 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5412 = "FStar.Buffer.create") ||
              (let uu____5414 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____5414 = "LowStar.Monotonic.Buffer.malloca"))
             ||
             (let uu____5416 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5416 = "LowStar.ImmutableBuffer.ialloca"))
            ||
            (let uu____5418 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5418 = "LowStar.UninitializedBuffer.ualloca")
          ->
          let uu____5419 =
            let uu____5426 = translate_expr env e1  in
            let uu____5427 = translate_expr env e2  in
            (Stack, uu____5426, uu____5427)  in
          EBufCreate uu____5419
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5429;
                  FStar_Extraction_ML_Syntax.loc = uu____5430;_},uu____5431);
             FStar_Extraction_ML_Syntax.mlty = uu____5432;
             FStar_Extraction_ML_Syntax.loc = uu____5433;_},init1::[])
          when
          let uu____5441 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5441 = "FStar.HyperStack.ST.salloc" ->
          let uu____5442 =
            let uu____5449 = translate_expr env init1  in
            (Stack, uu____5449, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5442
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5451;
                  FStar_Extraction_ML_Syntax.loc = uu____5452;_},uu____5453);
             FStar_Extraction_ML_Syntax.mlty = uu____5454;
             FStar_Extraction_ML_Syntax.loc = uu____5455;_},e2::[])
          when
          ((let uu____5465 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5465 = "FStar.Buffer.createL") ||
             (let uu____5467 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5467 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____5469 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5469 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____5470 =
            let uu____5477 =
              let uu____5480 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____5480  in
            (Stack, uu____5477)  in
          EBufCreateL uu____5470
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5486;
                  FStar_Extraction_ML_Syntax.loc = uu____5487;_},uu____5488);
             FStar_Extraction_ML_Syntax.mlty = uu____5489;
             FStar_Extraction_ML_Syntax.loc = uu____5490;_},_erid::e2::[])
          when
          (let uu____5501 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5501 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____5503 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5503 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____5504 =
            let uu____5511 =
              let uu____5514 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____5514  in
            (Eternal, uu____5511)  in
          EBufCreateL uu____5504
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
             FStar_Extraction_ML_Syntax.loc = uu____5524;_},_rid::init1::[])
          when
          let uu____5533 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5533 = "FStar.HyperStack.ST.ralloc" ->
          let uu____5534 =
            let uu____5541 = translate_expr env init1  in
            (Eternal, uu____5541, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5534
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5543;
                  FStar_Extraction_ML_Syntax.loc = uu____5544;_},uu____5545);
             FStar_Extraction_ML_Syntax.mlty = uu____5546;
             FStar_Extraction_ML_Syntax.loc = uu____5547;_},_e0::e1::e2::[])
          when
          ((let uu____5559 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5559 = "FStar.Buffer.rcreate") ||
             (let uu____5561 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5561 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____5563 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5563 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____5564 =
            let uu____5571 = translate_expr env e1  in
            let uu____5572 = translate_expr env e2  in
            (Eternal, uu____5571, uu____5572)  in
          EBufCreate uu____5564
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5574;
                  FStar_Extraction_ML_Syntax.loc = uu____5575;_},uu____5576);
             FStar_Extraction_ML_Syntax.mlty = uu____5577;
             FStar_Extraction_ML_Syntax.loc = uu____5578;_},_erid::elen::[])
          when
          let uu____5587 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5587 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____5588 =
            let uu____5593 = translate_expr env elen  in
            (Eternal, uu____5593)  in
          EBufCreateNoInit uu____5588
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5595;
                  FStar_Extraction_ML_Syntax.loc = uu____5596;_},uu____5597);
             FStar_Extraction_ML_Syntax.mlty = uu____5598;
             FStar_Extraction_ML_Syntax.loc = uu____5599;_},_rid::init1::[])
          when
          let uu____5608 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5608 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____5609 =
            let uu____5616 = translate_expr env init1  in
            (ManuallyManaged, uu____5616, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5609
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5618;
                  FStar_Extraction_ML_Syntax.loc = uu____5619;_},uu____5620);
             FStar_Extraction_ML_Syntax.mlty = uu____5621;
             FStar_Extraction_ML_Syntax.loc = uu____5622;_},_e0::e1::e2::[])
          when
          ((((let uu____5634 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5634 = "FStar.Buffer.rcreate_mm") ||
               (let uu____5636 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____5636 = "LowStar.Monotonic.Buffer.mmalloc"))
              ||
              (let uu____5638 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____5638 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____5640 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5640 = "LowStar.ImmutableBuffer.imalloc"))
            ||
            (let uu____5642 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5642 = "LowStar.UninitializedBuffer.umalloc")
          ->
          let uu____5643 =
            let uu____5650 = translate_expr env e1  in
            let uu____5651 = translate_expr env e2  in
            (ManuallyManaged, uu____5650, uu____5651)  in
          EBufCreate uu____5643
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5653;
                  FStar_Extraction_ML_Syntax.loc = uu____5654;_},uu____5655);
             FStar_Extraction_ML_Syntax.mlty = uu____5656;
             FStar_Extraction_ML_Syntax.loc = uu____5657;_},e2::[])
          when
          let uu____5665 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5665 = "FStar.HyperStack.ST.rfree" ->
          let uu____5666 = translate_expr env e2  in EBufFree uu____5666
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5668;
                  FStar_Extraction_ML_Syntax.loc = uu____5669;_},uu____5670);
             FStar_Extraction_ML_Syntax.mlty = uu____5671;
             FStar_Extraction_ML_Syntax.loc = uu____5672;_},e2::[])
          when
          (let uu____5682 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5682 = "FStar.Buffer.rfree") ||
            (let uu____5684 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5684 = "LowStar.Monotonic.Buffer.free")
          -> let uu____5685 = translate_expr env e2  in EBufFree uu____5685
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
             FStar_Extraction_ML_Syntax.loc = uu____5691;_},e1::e2::_e3::[])
          when
          let uu____5701 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5701 = "FStar.Buffer.sub" ->
          let uu____5702 =
            let uu____5707 = translate_expr env e1  in
            let uu____5708 = translate_expr env e2  in
            (uu____5707, uu____5708)  in
          EBufSub uu____5702
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5710;
                  FStar_Extraction_ML_Syntax.loc = uu____5711;_},uu____5712);
             FStar_Extraction_ML_Syntax.mlty = uu____5713;
             FStar_Extraction_ML_Syntax.loc = uu____5714;_},e1::e2::_e3::[])
          when
          let uu____5724 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5724 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____5725 =
            let uu____5730 = translate_expr env e1  in
            let uu____5731 = translate_expr env e2  in
            (uu____5730, uu____5731)  in
          EBufSub uu____5725
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5733;
                  FStar_Extraction_ML_Syntax.loc = uu____5734;_},uu____5735);
             FStar_Extraction_ML_Syntax.mlty = uu____5736;
             FStar_Extraction_ML_Syntax.loc = uu____5737;_},e1::e2::[])
          when
          let uu____5746 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5746 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5748;
                  FStar_Extraction_ML_Syntax.loc = uu____5749;_},uu____5750);
             FStar_Extraction_ML_Syntax.mlty = uu____5751;
             FStar_Extraction_ML_Syntax.loc = uu____5752;_},e1::e2::[])
          when
          let uu____5761 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5761 = "FStar.Buffer.offset" ->
          let uu____5762 =
            let uu____5767 = translate_expr env e1  in
            let uu____5768 = translate_expr env e2  in
            (uu____5767, uu____5768)  in
          EBufSub uu____5762
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5770;
                  FStar_Extraction_ML_Syntax.loc = uu____5771;_},uu____5772);
             FStar_Extraction_ML_Syntax.mlty = uu____5773;
             FStar_Extraction_ML_Syntax.loc = uu____5774;_},e1::e2::[])
          when
          let uu____5783 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5783 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____5784 =
            let uu____5789 = translate_expr env e1  in
            let uu____5790 = translate_expr env e2  in
            (uu____5789, uu____5790)  in
          EBufSub uu____5784
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5792;
                  FStar_Extraction_ML_Syntax.loc = uu____5793;_},uu____5794);
             FStar_Extraction_ML_Syntax.mlty = uu____5795;
             FStar_Extraction_ML_Syntax.loc = uu____5796;_},e1::e2::e3::[])
          when
          (((let uu____5808 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5808 = "FStar.Buffer.upd") ||
              (let uu____5810 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____5810 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____5812 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5812 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____5814 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5814 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____5815 =
            let uu____5822 = translate_expr env e1  in
            let uu____5823 = translate_expr env e2  in
            let uu____5824 = translate_expr env e3  in
            (uu____5822, uu____5823, uu____5824)  in
          EBufWrite uu____5815
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5826;
                  FStar_Extraction_ML_Syntax.loc = uu____5827;_},uu____5828);
             FStar_Extraction_ML_Syntax.mlty = uu____5829;
             FStar_Extraction_ML_Syntax.loc = uu____5830;_},e1::e2::[])
          when
          let uu____5839 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5839 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5840 =
            let uu____5847 = translate_expr env e1  in
            let uu____5848 = translate_expr env e2  in
            (uu____5847, (EConstant (UInt32, "0")), uu____5848)  in
          EBufWrite uu____5840
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5850;
             FStar_Extraction_ML_Syntax.loc = uu____5851;_},uu____5852::[])
          when
          let uu____5855 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5855 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5857;
             FStar_Extraction_ML_Syntax.loc = uu____5858;_},uu____5859::[])
          when
          let uu____5862 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5862 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5864;
                  FStar_Extraction_ML_Syntax.loc = uu____5865;_},uu____5866);
             FStar_Extraction_ML_Syntax.mlty = uu____5867;
             FStar_Extraction_ML_Syntax.loc = uu____5868;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____5882 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5882 = "FStar.Buffer.blit") ||
             (let uu____5884 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5884 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____5886 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5886 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____5887 =
            let uu____5898 = translate_expr env e1  in
            let uu____5899 = translate_expr env e2  in
            let uu____5900 = translate_expr env e3  in
            let uu____5901 = translate_expr env e4  in
            let uu____5902 = translate_expr env e5  in
            (uu____5898, uu____5899, uu____5900, uu____5901, uu____5902)  in
          EBufBlit uu____5887
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5904;
                  FStar_Extraction_ML_Syntax.loc = uu____5905;_},uu____5906);
             FStar_Extraction_ML_Syntax.mlty = uu____5907;
             FStar_Extraction_ML_Syntax.loc = uu____5908;_},e1::e2::e3::[])
          when
          let uu____5918 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5918 = "FStar.Buffer.fill" ->
          let uu____5919 =
            let uu____5926 = translate_expr env e1  in
            let uu____5927 = translate_expr env e2  in
            let uu____5928 = translate_expr env e3  in
            (uu____5926, uu____5927, uu____5928)  in
          EBufFill uu____5919
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5930;
             FStar_Extraction_ML_Syntax.loc = uu____5931;_},uu____5932::[])
          when
          let uu____5935 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5935 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5937;
                  FStar_Extraction_ML_Syntax.loc = uu____5938;_},uu____5939);
             FStar_Extraction_ML_Syntax.mlty = uu____5940;
             FStar_Extraction_ML_Syntax.loc = uu____5941;_},_ebuf::_eseq::[])
          when
          (((let uu____5952 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5952 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____5954 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____5954 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____5956 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5956 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____5958 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5958 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5960;
             FStar_Extraction_ML_Syntax.loc = uu____5961;_},e1::[])
          when
          let uu____5965 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5965 = "Obj.repr" ->
          let uu____5966 =
            let uu____5971 = translate_expr env e1  in (uu____5971, TAny)  in
          ECast uu____5966
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5974;
             FStar_Extraction_ML_Syntax.loc = uu____5975;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5983 = FStar_Util.must (mk_width m)  in
          let uu____5984 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____5983 uu____5984 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5986;
             FStar_Extraction_ML_Syntax.loc = uu____5987;_},args)
          when is_bool_op op ->
          let uu____5995 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____5995 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
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
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____6023;
             FStar_Extraction_ML_Syntax.loc = uu____6024;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____6026;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____6027;_}::[])
          when is_machine_int m ->
          let uu____6042 =
            let uu____6047 = FStar_Util.must (mk_width m)  in (uu____6047, c)
             in
          EConstant uu____6042
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____6048;
             FStar_Extraction_ML_Syntax.loc = uu____6049;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____6051;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____6052;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____6058 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____6059;
             FStar_Extraction_ML_Syntax.loc = uu____6060;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____6062;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____6063;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____6069 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____6071;
             FStar_Extraction_ML_Syntax.loc = uu____6072;_},arg::[])
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
            let uu____6079 =
              let uu____6084 = translate_expr env arg  in
              (uu____6084, (TInt UInt64))  in
            ECast uu____6079
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____6086 =
                 let uu____6091 = translate_expr env arg  in
                 (uu____6091, (TInt UInt32))  in
               ECast uu____6086)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____6093 =
                   let uu____6098 = translate_expr env arg  in
                   (uu____6098, (TInt UInt16))  in
                 ECast uu____6093)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____6100 =
                     let uu____6105 = translate_expr env arg  in
                     (uu____6105, (TInt UInt8))  in
                   ECast uu____6100)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____6107 =
                       let uu____6112 = translate_expr env arg  in
                       (uu____6112, (TInt Int64))  in
                     ECast uu____6107)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____6114 =
                         let uu____6119 = translate_expr env arg  in
                         (uu____6119, (TInt Int32))  in
                       ECast uu____6114)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____6121 =
                           let uu____6126 = translate_expr env arg  in
                           (uu____6126, (TInt Int16))  in
                         ECast uu____6121)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____6128 =
                             let uu____6133 = translate_expr env arg  in
                             (uu____6133, (TInt Int8))  in
                           ECast uu____6128)
                        else
                          (let uu____6135 =
                             let uu____6142 =
                               let uu____6145 = translate_expr env arg  in
                               [uu____6145]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____6142)
                              in
                           EApp uu____6135)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____6156 =
            let uu____6163 = translate_expr env head1  in
            let uu____6164 = FStar_List.map (translate_expr env) args  in
            (uu____6163, uu____6164)  in
          EApp uu____6156
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____6175 =
            let uu____6182 = translate_expr env head1  in
            let uu____6183 = FStar_List.map (translate_type env) ty_args  in
            (uu____6182, uu____6183)  in
          ETypApp uu____6175
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____6191 =
            let uu____6196 = translate_expr env e1  in
            let uu____6197 = translate_type env t_to  in
            (uu____6196, uu____6197)  in
          ECast uu____6191
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____6198,fields) ->
          let uu____6216 =
            let uu____6227 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____6228 =
              FStar_List.map
                (fun uu____6247  ->
                   match uu____6247 with
                   | (field,expr) ->
                       let uu____6258 = translate_expr env expr  in
                       (field, uu____6258)) fields
               in
            (uu____6227, uu____6228)  in
          EFlat uu____6216
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____6267 =
            let uu____6274 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____6275 = translate_expr env e1  in
            (uu____6274, uu____6275, (FStar_Pervasives_Native.snd path))  in
          EField uu____6267
      | FStar_Extraction_ML_Syntax.MLE_Let uu____6278 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____6290) ->
          let uu____6295 =
            let uu____6296 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____6296
             in
          failwith uu____6295
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____6302 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____6302
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____6308 = FStar_List.map (translate_expr env) es  in
          ETuple uu____6308
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____6311,cons1),es) ->
          let uu____6322 =
            let uu____6331 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____6332 = FStar_List.map (translate_expr env) es  in
            (uu____6331, cons1, uu____6332)  in
          ECons uu____6322
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____6355 =
            let uu____6364 = translate_expr env1 body  in
            let uu____6365 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____6364, uu____6365)  in
          EFun uu____6355
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____6375 =
            let uu____6382 = translate_expr env e1  in
            let uu____6383 = translate_expr env e2  in
            let uu____6384 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____6382, uu____6383, uu____6384)  in
          EIfThenElse uu____6375
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____6386 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____6393 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____6408 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____6423 =
              let uu____6436 = FStar_List.map (translate_type env) ts  in
              (lid, uu____6436)  in
            TApp uu____6423
          else TQualified lid
      | uu____6448 -> failwith "invalid argument: assert_lid"

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
    fun uu____6474  ->
      match uu____6474 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____6500 = translate_pat env pat  in
            (match uu____6500 with
             | (env1,pat1) ->
                 let uu____6511 = translate_expr env1 expr  in
                 (pat1, uu____6511))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___283_6517  ->
    match uu___283_6517 with
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
          let uu____6581 =
            let uu____6582 =
              let uu____6587 = translate_width sw  in (uu____6587, s)  in
            PConstant uu____6582  in
          (env, uu____6581)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____6591,cons1),ps) ->
          let uu____6602 =
            FStar_List.fold_left
              (fun uu____6622  ->
                 fun p1  ->
                   match uu____6622 with
                   | (env1,acc) ->
                       let uu____6642 = translate_pat env1 p1  in
                       (match uu____6642 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6602 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____6671,ps) ->
          let uu____6689 =
            FStar_List.fold_left
              (fun uu____6723  ->
                 fun uu____6724  ->
                   match (uu____6723, uu____6724) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____6793 = translate_pat env1 p1  in
                       (match uu____6793 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____6689 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____6855 =
            FStar_List.fold_left
              (fun uu____6875  ->
                 fun p1  ->
                   match uu____6875 with
                   | (env1,acc) ->
                       let uu____6895 = translate_pat env1 p1  in
                       (match uu____6895 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6855 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6922 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6927 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____6938 =
            let uu____6939 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____6939
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____6938
          then
            let uu____6951 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____6951
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6964) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6979 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6980 ->
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
          let uu____7000 =
            let uu____7007 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____7007)  in
          EApp uu____7000
