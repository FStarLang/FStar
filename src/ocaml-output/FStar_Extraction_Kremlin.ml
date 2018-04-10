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
    match projectee with | DGlobal _0 -> true | uu____561 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,Prims.int,typ,expr)
      FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____655 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr) FStar_Pervasives_Native.tuple7)
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____763 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,typ) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____851 -> false
  
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
    match projectee with | DExternal _0 -> true | uu____961 -> false
  
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
    match projectee with | DTypeVariant _0 -> true | uu____1061 -> false
  
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
    match projectee with | StdCall  -> true | uu____1170 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1176 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1182 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1188 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1194 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1200 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1206 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1212 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1219 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1232 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1239 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1253 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1267 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1280 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1286 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1292 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1299 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1319 -> false
  
let (__proj__EQualified__item___0 :
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1355 -> false
  
let (__proj__EConstant__item___0 :
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1380 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1393 -> false
  
let (__proj__EApp__item___0 :
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1431 -> false
  
let (__proj__ETypApp__item___0 :
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1469 -> false
  
let (__proj__ELet__item___0 :
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1507 -> false
  
let (__proj__EIfThenElse__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1541 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1565 -> false
  
let (__proj__EAssign__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____1597 -> false
  
let (__proj__EBufCreate__item___0 :
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____1633 -> false
  
let (__proj__EBufRead__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____1665 -> false
  
let (__proj__EBufWrite__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____1701 -> false
  
let (__proj__EBufSub__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____1737 -> false
  
let (__proj__EBufBlit__item___0 :
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5) =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____1791 -> false
  
let (__proj__EMatch__item___0 :
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1839 -> false
  
let (__proj__EOp__item___0 :
  expr -> (op,width) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1869 -> false
  
let (__proj__ECast__item___0 :
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1894 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1900 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1907 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1920 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1926 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1933 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1957 -> false
  
let (__proj__EFlat__item___0 :
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____2007 -> false
  
let (__proj__EField__item___0 :
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____2043 -> false
  
let (__proj__EWhile__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____2075 -> false
  
let (__proj__EBufCreateL__item___0 :
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2109 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2137 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2181 -> false
  
let (__proj__EBufFill__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2213 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2235 -> false
  
let (__proj__EFun__item___0 :
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2273 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____2287 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____2300 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2306 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____2312 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2318 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____2324 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2330 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2336 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2342 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____2348 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____2354 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2360 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2366 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2372 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2378 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2384 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____2390 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____2396 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____2402 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____2408 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____2414 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____2420 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____2426 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____2432 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____2438 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____2444 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2450 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2457 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2471 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2491 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2525 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2551 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list)
  = fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____2587 -> false
  
let (__proj__PConstant__item___0 :
  pattern -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____2612 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2618 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2624 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2630 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2636 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2642 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2648 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2654 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2660 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____2666 -> false
  
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
    match projectee with | TInt _0 -> true | uu____2687 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2701 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2714 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2727 -> false
  
let (__proj__TQualified__item___0 :
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2758 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2764 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2775 -> false
  
let (__proj__TArrow__item___0 :
  typ -> (typ,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2801 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2827 -> false
  
let (__proj__TApp__item___0 :
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____2879 -> false
  
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
  'Auu____2959 'Auu____2960 'Auu____2961 .
    ('Auu____2959,'Auu____2960,'Auu____2961) FStar_Pervasives_Native.tuple3
      -> 'Auu____2959
  = fun uu____2972  -> match uu____2972 with | (x,uu____2980,uu____2981) -> x 
let snd3 :
  'Auu____2990 'Auu____2991 'Auu____2992 .
    ('Auu____2990,'Auu____2991,'Auu____2992) FStar_Pervasives_Native.tuple3
      -> 'Auu____2991
  = fun uu____3003  -> match uu____3003 with | (uu____3010,x,uu____3012) -> x 
let thd3 :
  'Auu____3021 'Auu____3022 'Auu____3023 .
    ('Auu____3021,'Auu____3022,'Auu____3023) FStar_Pervasives_Native.tuple3
      -> 'Auu____3023
  = fun uu____3034  -> match uu____3034 with | (uu____3041,uu____3042,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___35_3050  ->
    match uu___35_3050 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____3053 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___36_3060  ->
    match uu___36_3060 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____3063 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___37_3077  ->
    match uu___37_3077 with
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
    | uu____3080 -> FStar_Pervasives_Native.None
  
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
      let uu___42_3196 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___42_3196.names_t);
        module_name = (uu___42_3196.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___43_3207 = env  in
      {
        names = (uu___43_3207.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___43_3207.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____3218 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____3218 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____3242 ->
          let uu____3243 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____3243
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____3262 ->
          let uu____3263 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____3263
  
let add_binders :
  'Auu____3270 .
    env ->
      (Prims.string,'Auu____3270) FStar_Pervasives_Native.tuple2 Prims.list
        -> env
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____3302  ->
             match uu____3302 with | (name,uu____3308) -> extend env1 name)
        env binders
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____3513  ->
    match uu____3513 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3561 = m  in
               match uu____3561 with
               | (path,uu____3575,uu____3576) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               let uu____3597 =
                 FStar_Util.print1 "Attempting to translate module %s\n"
                   m_name
                  in
               let uu____3598 = translate_module m  in
               FStar_Pervasives_Native.Some uu____3598
             with
             | e ->
                 let uu____3606 =
                   let uu____3607 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3607
                    in
                 FStar_Pervasives_Native.None) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath,(FStar_Extraction_ML_Syntax.mlsig,
                                       FStar_Extraction_ML_Syntax.mlmodule)
                                       FStar_Pervasives_Native.tuple2
                                       FStar_Pervasives_Native.option,
    FStar_Extraction_ML_Syntax.mllib) FStar_Pervasives_Native.tuple3 -> 
    file)
  =
  fun uu____3608  ->
    match uu____3608 with
    | (module_name,modul,uu____3623) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____3654 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags1  ->
    FStar_List.choose
      (fun uu___38_3669  ->
         match uu___38_3669 with
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
         | uu____3676 -> FStar_Pervasives_Native.None) flags1

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3687 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3689 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____3693) ->
          let uu____3706 =
            FStar_Util.print1_warning
              "Skipping the translation of exception: %s\n" m
             in
          []

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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3715;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____3718;
                FStar_Extraction_ML_Syntax.loc = uu____3719;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3721;_} ->
            let assumed =
              FStar_Util.for_some
                (fun uu___39_3740  ->
                   match uu___39_3740 with
                   | FStar_Extraction_ML_Syntax.Assumed  -> true
                   | uu____3741 -> false) meta
               in
            let env1 =
              if flavor = FStar_Extraction_ML_Syntax.Rec
              then extend env name
              else env  in
            let env2 =
              FStar_List.fold_left
                (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars
               in
            let rec find_return_type eff i uu___40_3765 =
              match uu___40_3765 with
              | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3770,eff1,t) when
                  i > (Prims.parse_int "0") ->
                  find_return_type eff1 (i - (Prims.parse_int "1")) t
              | t -> (eff, t)  in
            let uu____3774 =
              find_return_type FStar_Extraction_ML_Syntax.E_PURE
                (FStar_List.length args) t0
               in
            (match uu____3774 with
             | (eff,t) ->
                 let t1 = translate_type env2 t  in
                 let binders = translate_binders env2 args  in
                 let env3 = add_binders env2 args  in
                 let name1 = ((env3.module_name), name)  in
                 let meta1 =
                   match (eff, t1) with
                   | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____3806) ->
                       let uu____3807 = translate_flags meta  in
                       MustDisappear :: uu____3807
                   | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                       let uu____3810 = translate_flags meta  in
                       MustDisappear :: uu____3810
                   | uu____3813 -> translate_flags meta  in
                 if assumed
                 then
                   (if (FStar_List.length tvars) = (Prims.parse_int "0")
                    then
                      let uu____3822 =
                        let uu____3823 =
                          let uu____3842 = translate_type env3 t0  in
                          (FStar_Pervasives_Native.None, meta1, name1,
                            uu____3842)
                           in
                        DExternal uu____3823  in
                      FStar_Pervasives_Native.Some uu____3822
                    else
                      (let uu____3854 =
                         let uu____3855 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         FStar_Util.print1_warning
                           "No writing anything for %s (polymorphic assume)\n"
                           uu____3855
                          in
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
                        let uu____3887 =
                          let uu____3888 =
                            let uu____3893 =
                              let uu____3894 =
                                FStar_Extraction_ML_Syntax.string_of_mlpath
                                  name1
                                 in
                              FStar_Util.format2
                                "Writing a stub for %s (%s)\n" uu____3894 msg
                               in
                            (FStar_Errors.Warning_FunctionNotExtacted,
                              uu____3893)
                             in
                          FStar_Errors.log_issue FStar_Range.dummyRange
                            uu____3888
                           in
                        let msg1 =
                          Prims.strcat "This function was not extracted:\n"
                            msg
                           in
                        FStar_Pervasives_Native.Some
                          (DFunction
                             (FStar_Pervasives_Native.None, meta1,
                               (FStar_List.length tvars), t1, name1, binders,
                               (EAbortS msg1)))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3911;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Coerce
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____3914;
                     FStar_Extraction_ML_Syntax.loc = uu____3915;_},uu____3916,uu____3917);
                FStar_Extraction_ML_Syntax.mlty = uu____3918;
                FStar_Extraction_ML_Syntax.loc = uu____3919;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3921;_} ->
            let assumed =
              FStar_Util.for_some
                (fun uu___39_3940  ->
                   match uu___39_3940 with
                   | FStar_Extraction_ML_Syntax.Assumed  -> true
                   | uu____3941 -> false) meta
               in
            let env1 =
              if flavor = FStar_Extraction_ML_Syntax.Rec
              then extend env name
              else env  in
            let env2 =
              FStar_List.fold_left
                (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars
               in
            let rec find_return_type eff i uu___40_3965 =
              match uu___40_3965 with
              | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3970,eff1,t) when
                  i > (Prims.parse_int "0") ->
                  find_return_type eff1 (i - (Prims.parse_int "1")) t
              | t -> (eff, t)  in
            let uu____3974 =
              find_return_type FStar_Extraction_ML_Syntax.E_PURE
                (FStar_List.length args) t0
               in
            (match uu____3974 with
             | (eff,t) ->
                 let t1 = translate_type env2 t  in
                 let binders = translate_binders env2 args  in
                 let env3 = add_binders env2 args  in
                 let name1 = ((env3.module_name), name)  in
                 let meta1 =
                   match (eff, t1) with
                   | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____4006) ->
                       let uu____4007 = translate_flags meta  in
                       MustDisappear :: uu____4007
                   | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                       let uu____4010 = translate_flags meta  in
                       MustDisappear :: uu____4010
                   | uu____4013 -> translate_flags meta  in
                 if assumed
                 then
                   (if (FStar_List.length tvars) = (Prims.parse_int "0")
                    then
                      let uu____4022 =
                        let uu____4023 =
                          let uu____4042 = translate_type env3 t0  in
                          (FStar_Pervasives_Native.None, meta1, name1,
                            uu____4042)
                           in
                        DExternal uu____4023  in
                      FStar_Pervasives_Native.Some uu____4022
                    else
                      (let uu____4054 =
                         let uu____4055 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         FStar_Util.print1_warning
                           "No writing anything for %s (polymorphic assume)\n"
                           uu____4055
                          in
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
                        let uu____4087 =
                          let uu____4088 =
                            let uu____4093 =
                              let uu____4094 =
                                FStar_Extraction_ML_Syntax.string_of_mlpath
                                  name1
                                 in
                              FStar_Util.format2
                                "Writing a stub for %s (%s)\n" uu____4094 msg
                               in
                            (FStar_Errors.Warning_FunctionNotExtacted,
                              uu____4093)
                             in
                          FStar_Errors.log_issue FStar_Range.dummyRange
                            uu____4088
                           in
                        let msg1 =
                          Prims.strcat "This function was not extracted:\n"
                            msg
                           in
                        FStar_Pervasives_Native.Some
                          (DFunction
                             (FStar_Pervasives_Native.None, meta1,
                               (FStar_List.length tvars), t1, name1, binders,
                               (EAbortS msg1)))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4111;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4114;_} ->
            let meta1 = translate_flags meta  in
            let env1 =
              FStar_List.fold_left
                (fun env1  -> fun name1  -> extend_t env1 name1) env tvars
               in
            let t1 = translate_type env1 t  in
            let name1 = ((env1.module_name), name)  in
            (try
               let expr1 = translate_expr env1 expr  in
               FStar_Pervasives_Native.Some
                 (DGlobal
                    (meta1, name1, (FStar_List.length tvars), t1, expr1))
             with
             | e ->
                 let uu____4160 =
                   let uu____4161 =
                     let uu____4166 =
                       let uu____4167 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       let uu____4168 = FStar_Util.print_exn e  in
                       FStar_Util.format2
                         "Not translating definition for %s (%s)\n"
                         uu____4167 uu____4168
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____4166)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____4161
                    in
                 FStar_Pervasives_Native.Some
                   (DGlobal
                      (meta1, name1, (FStar_List.length tvars), t1, EAny)))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4179;
            FStar_Extraction_ML_Syntax.mllb_def = uu____4180;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____4181;
            FStar_Extraction_ML_Syntax.print_typ = uu____4182;_} ->
            let uu____4185 =
              let uu____4186 =
                let uu____4191 =
                  FStar_Util.format1 "Not translating definition for %s\n"
                    name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____4191)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____4186  in
            let uu____4192 =
              match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____4199 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____4199
              | FStar_Pervasives_Native.None  -> ()  in
            FStar_Pervasives_Native.None

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
            let uu____4235 =
              FStar_Util.print1_warning
                "Not translating type definition (assumed) for %s\n" name2
               in
            FStar_Pervasives_Native.None
          else
            (let uu____4237 =
               let uu____4238 =
                 let uu____4255 = translate_flags flags1  in
                 let uu____4258 = translate_type env1 t  in
                 (name1, uu____4255, (FStar_List.length args), uu____4258)
                  in
               DTypeAlias uu____4238  in
             FStar_Pervasives_Native.Some uu____4237)
      | (uu____4267,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args
             in
          let uu____4299 =
            let uu____4300 =
              let uu____4327 = translate_flags flags1  in
              let uu____4330 =
                FStar_List.map
                  (fun uu____4357  ->
                     match uu____4357 with
                     | (f,t) ->
                         let uu____4372 =
                           let uu____4377 = translate_type env1 t  in
                           (uu____4377, false)  in
                         (f, uu____4372)) fields
                 in
              (name1, uu____4327, (FStar_List.length args), uu____4330)  in
            DTypeFlat uu____4300  in
          FStar_Pervasives_Native.Some uu____4299
      | (uu____4400,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
          let name1 = ((env.module_name), name)  in
          let flags2 = translate_flags flags1  in
          let env1 = FStar_List.fold_left extend_t env args  in
          let uu____4437 =
            let uu____4438 =
              let uu____4471 =
                FStar_List.map
                  (fun uu____4516  ->
                     match uu____4516 with
                     | (cons1,ts) ->
                         let uu____4555 =
                           FStar_List.map
                             (fun uu____4582  ->
                                match uu____4582 with
                                | (name2,t) ->
                                    let uu____4597 =
                                      let uu____4602 = translate_type env1 t
                                         in
                                      (uu____4602, false)  in
                                    (name2, uu____4597)) ts
                            in
                         (cons1, uu____4555)) branches
                 in
              (name1, flags2, (FStar_List.length args), uu____4471)  in
            DTypeVariant uu____4438  in
          FStar_Pervasives_Native.Some uu____4437
      | (uu____4641,name,_mangled_name,uu____4644,uu____4645,uu____4646) ->
          let uu____4655 =
            let uu____4656 =
              let uu____4661 =
                FStar_Util.format1 "Not translating type definition for %s\n"
                  name
                 in
              (FStar_Errors.Warning_DefinitionNotTranslated, uu____4661)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____4656  in
          FStar_Pervasives_Native.None

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4665 = find_t env name  in TBound uu____4665
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4667,t2) ->
          let uu____4669 =
            let uu____4674 = translate_type env t1  in
            let uu____4675 = translate_type env t2  in
            (uu____4674, uu____4675)  in
          TArrow uu____4669
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4679 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4679 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4683 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4683 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4695 = FStar_Util.must (mk_width m)  in TInt uu____4695
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4707 = FStar_Util.must (mk_width m)  in TInt uu____4707
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4712 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4712 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____4713::arg::uu____4715::[],p) when
          (((let uu____4721 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4721 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____4723 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4723 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____4725 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4725 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____4727 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4727 = "FStar.HyperStack.ST.s_mref")
          -> let uu____4728 = translate_type env arg  in TBuf uu____4728
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____4730::[],p) when
          ((((((((((let uu____4736 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4736 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____4738 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4738 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____4740 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4740 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____4742 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4742 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____4744 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4744 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____4746 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4746 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____4748 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4748 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____4750 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4750 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____4752 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4752 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____4754 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4754 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____4756 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4756 = "FStar.HyperStack.ST.mmmref")
          -> let uu____4757 = translate_type env arg  in TBuf uu____4757
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          ((((((((((let uu____4764 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4764 = "FStar.Buffer.buffer") ||
                     (let uu____4766 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4766 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____4768 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4768 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____4770 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4770 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____4772 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4772 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____4774 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4774 = "FStar.HyperStack.mmref"))
                ||
                (let uu____4776 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4776 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____4778 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4778 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____4780 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4780 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____4782 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4782 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____4784 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4784 = "FStar.HyperStack.ST.mmref")
          -> let uu____4785 = translate_type env arg  in TBuf uu____4785
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4786::arg::[],p) when
          (let uu____4793 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4793 = "FStar.HyperStack.s_ref") ||
            (let uu____4795 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4795 = "FStar.HyperStack.ST.s_ref")
          -> let uu____4796 = translate_type env arg  in TBuf uu____4796
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4797::[],p) when
          let uu____4801 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4801 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4839 = FStar_List.map (translate_type env) args  in
          TTuple uu____4839
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4848 =
              let uu____4861 = FStar_List.map (translate_type env) args  in
              (lid, uu____4861)  in
            TApp uu____4848
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4870 = FStar_List.map (translate_type env) ts  in
          TTuple uu____4870

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
    fun uu____4886  ->
      match uu____4886 with
      | (name,typ) ->
          let uu____4893 = translate_type env typ  in
          { name; typ = uu____4893 }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____4898 = find env name  in EBound uu____4898
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4903 =
            let uu____4908 = FStar_Util.must (mk_op op)  in
            let uu____4909 = FStar_Util.must (mk_width m)  in
            (uu____4908, uu____4909)  in
          EOp uu____4903
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4913 =
            let uu____4918 = FStar_Util.must (mk_bool_op op)  in
            (uu____4918, Bool)  in
          EOp uu____4913
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
            let uu____4945 = translate_type env typ  in
            { name; typ = uu____4945 }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4971 =
            let uu____4982 = translate_expr env expr  in
            let uu____4983 = translate_branches env branches  in
            (uu____4982, uu____4983)  in
          EMatch uu____4971
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4997;
                  FStar_Extraction_ML_Syntax.loc = uu____4998;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____5000;
             FStar_Extraction_ML_Syntax.loc = uu____5001;_},arg::[])
          when
          let uu____5007 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5007 = "FStar.Dyn.undyn" ->
          let uu____5008 =
            let uu____5013 = translate_expr env arg  in
            let uu____5014 = translate_type env t  in
            (uu____5013, uu____5014)  in
          ECast uu____5008
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5016;
                  FStar_Extraction_ML_Syntax.loc = uu____5017;_},uu____5018);
             FStar_Extraction_ML_Syntax.mlty = uu____5019;
             FStar_Extraction_ML_Syntax.loc = uu____5020;_},uu____5021)
          when
          let uu____5030 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5030 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5032;
                  FStar_Extraction_ML_Syntax.loc = uu____5033;_},uu____5034);
             FStar_Extraction_ML_Syntax.mlty = uu____5035;
             FStar_Extraction_ML_Syntax.loc = uu____5036;_},arg::[])
          when
          ((let uu____5046 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____5046 = "FStar.HyperStack.All.failwith") ||
             (let uu____5048 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____5048 = "FStar.Error.unexpected"))
            ||
            (let uu____5050 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5050 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____5052;
               FStar_Extraction_ML_Syntax.loc = uu____5053;_} -> EAbortS msg
           | uu____5054 ->
               let print7 =
                 let uu____5056 =
                   let uu____5057 =
                     let uu____5058 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____5058
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____5057  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____5056
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
                  FStar_Extraction_ML_Syntax.mlty = uu____5064;
                  FStar_Extraction_ML_Syntax.loc = uu____5065;_},uu____5066);
             FStar_Extraction_ML_Syntax.mlty = uu____5067;
             FStar_Extraction_ML_Syntax.loc = uu____5068;_},e1::e2::[])
          when
          (let uu____5079 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5079 = "FStar.Buffer.index") ||
            (let uu____5081 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5081 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____5082 =
            let uu____5087 = translate_expr env e1  in
            let uu____5088 = translate_expr env e2  in
            (uu____5087, uu____5088)  in
          EBufRead uu____5082
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
             FStar_Extraction_ML_Syntax.loc = uu____5094;_},e1::[])
          when
          let uu____5102 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5102 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____5103 =
            let uu____5108 = translate_expr env e1  in
            (uu____5108, (EConstant (UInt32, "0")))  in
          EBufRead uu____5103
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5110;
                  FStar_Extraction_ML_Syntax.loc = uu____5111;_},uu____5112);
             FStar_Extraction_ML_Syntax.mlty = uu____5113;
             FStar_Extraction_ML_Syntax.loc = uu____5114;_},e1::e2::[])
          when
          let uu____5123 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5123 = "FStar.Buffer.create" ->
          let uu____5124 =
            let uu____5131 = translate_expr env e1  in
            let uu____5132 = translate_expr env e2  in
            (Stack, uu____5131, uu____5132)  in
          EBufCreate uu____5124
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5134;
                  FStar_Extraction_ML_Syntax.loc = uu____5135;_},uu____5136);
             FStar_Extraction_ML_Syntax.mlty = uu____5137;
             FStar_Extraction_ML_Syntax.loc = uu____5138;_},init1::[])
          when
          let uu____5146 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5146 = "FStar.HyperStack.ST.salloc" ->
          let uu____5147 =
            let uu____5154 = translate_expr env init1  in
            (Stack, uu____5154, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5147
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5156;
                  FStar_Extraction_ML_Syntax.loc = uu____5157;_},uu____5158);
             FStar_Extraction_ML_Syntax.mlty = uu____5159;
             FStar_Extraction_ML_Syntax.loc = uu____5160;_},e2::[])
          when
          let uu____5168 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5168 = "FStar.Buffer.createL" ->
          let rec list_elements acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____5208 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a list literal!"
             in
          let list_elements1 = list_elements []  in
          let uu____5217 =
            let uu____5224 =
              let uu____5227 = list_elements1 e2  in
              FStar_List.map (translate_expr env) uu____5227  in
            (Stack, uu____5224)  in
          EBufCreateL uu____5217
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5233;
                  FStar_Extraction_ML_Syntax.loc = uu____5234;_},uu____5235);
             FStar_Extraction_ML_Syntax.mlty = uu____5236;
             FStar_Extraction_ML_Syntax.loc = uu____5237;_},_rid::init1::[])
          when
          let uu____5246 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5246 = "FStar.HyperStack.ST.ralloc" ->
          let uu____5247 =
            let uu____5254 = translate_expr env init1  in
            (Eternal, uu____5254, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5247
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5256;
                  FStar_Extraction_ML_Syntax.loc = uu____5257;_},uu____5258);
             FStar_Extraction_ML_Syntax.mlty = uu____5259;
             FStar_Extraction_ML_Syntax.loc = uu____5260;_},_e0::e1::e2::[])
          when
          let uu____5270 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5270 = "FStar.Buffer.rcreate" ->
          let uu____5271 =
            let uu____5278 = translate_expr env e1  in
            let uu____5279 = translate_expr env e2  in
            (Eternal, uu____5278, uu____5279)  in
          EBufCreate uu____5271
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
             FStar_Extraction_ML_Syntax.loc = uu____5285;_},_rid::init1::[])
          when
          let uu____5294 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5294 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____5295 =
            let uu____5302 = translate_expr env init1  in
            (ManuallyManaged, uu____5302, (EConstant (UInt32, "1")))  in
          EBufCreate uu____5295
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5304;
                  FStar_Extraction_ML_Syntax.loc = uu____5305;_},uu____5306);
             FStar_Extraction_ML_Syntax.mlty = uu____5307;
             FStar_Extraction_ML_Syntax.loc = uu____5308;_},_e0::e1::e2::[])
          when
          let uu____5318 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5318 = "FStar.Buffer.rcreate_mm" ->
          let uu____5319 =
            let uu____5326 = translate_expr env e1  in
            let uu____5327 = translate_expr env e2  in
            (ManuallyManaged, uu____5326, uu____5327)  in
          EBufCreate uu____5319
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
             FStar_Extraction_ML_Syntax.loc = uu____5333;_},e2::[])
          when
          let uu____5341 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5341 = "FStar.HyperStack.ST.rfree" ->
          let uu____5342 = translate_expr env e2  in EBufFree uu____5342
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5344;
                  FStar_Extraction_ML_Syntax.loc = uu____5345;_},uu____5346);
             FStar_Extraction_ML_Syntax.mlty = uu____5347;
             FStar_Extraction_ML_Syntax.loc = uu____5348;_},e2::[])
          when
          let uu____5356 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5356 = "FStar.Buffer.rfree" ->
          let uu____5357 = translate_expr env e2  in EBufFree uu____5357
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5359;
                  FStar_Extraction_ML_Syntax.loc = uu____5360;_},uu____5361);
             FStar_Extraction_ML_Syntax.mlty = uu____5362;
             FStar_Extraction_ML_Syntax.loc = uu____5363;_},e1::e2::_e3::[])
          when
          let uu____5373 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5373 = "FStar.Buffer.sub" ->
          let uu____5374 =
            let uu____5379 = translate_expr env e1  in
            let uu____5380 = translate_expr env e2  in
            (uu____5379, uu____5380)  in
          EBufSub uu____5374
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5382;
                  FStar_Extraction_ML_Syntax.loc = uu____5383;_},uu____5384);
             FStar_Extraction_ML_Syntax.mlty = uu____5385;
             FStar_Extraction_ML_Syntax.loc = uu____5386;_},e1::e2::[])
          when
          let uu____5395 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5395 = "FStar.Buffer.join" -> translate_expr env e1
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
          let uu____5410 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5410 = "FStar.Buffer.offset" ->
          let uu____5411 =
            let uu____5416 = translate_expr env e1  in
            let uu____5417 = translate_expr env e2  in
            (uu____5416, uu____5417)  in
          EBufSub uu____5411
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5419;
                  FStar_Extraction_ML_Syntax.loc = uu____5420;_},uu____5421);
             FStar_Extraction_ML_Syntax.mlty = uu____5422;
             FStar_Extraction_ML_Syntax.loc = uu____5423;_},e1::e2::e3::[])
          when
          (let uu____5435 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5435 = "FStar.Buffer.upd") ||
            (let uu____5437 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5437 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____5438 =
            let uu____5445 = translate_expr env e1  in
            let uu____5446 = translate_expr env e2  in
            let uu____5447 = translate_expr env e3  in
            (uu____5445, uu____5446, uu____5447)  in
          EBufWrite uu____5438
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5449;
                  FStar_Extraction_ML_Syntax.loc = uu____5450;_},uu____5451);
             FStar_Extraction_ML_Syntax.mlty = uu____5452;
             FStar_Extraction_ML_Syntax.loc = uu____5453;_},e1::e2::[])
          when
          let uu____5462 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5462 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5463 =
            let uu____5470 = translate_expr env e1  in
            let uu____5471 = translate_expr env e2  in
            (uu____5470, (EConstant (UInt32, "0")), uu____5471)  in
          EBufWrite uu____5463
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5473;
             FStar_Extraction_ML_Syntax.loc = uu____5474;_},uu____5475::[])
          when
          let uu____5478 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5478 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5480;
             FStar_Extraction_ML_Syntax.loc = uu____5481;_},uu____5482::[])
          when
          let uu____5485 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5485 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5487;
                  FStar_Extraction_ML_Syntax.loc = uu____5488;_},uu____5489);
             FStar_Extraction_ML_Syntax.mlty = uu____5490;
             FStar_Extraction_ML_Syntax.loc = uu____5491;_},e1::e2::e3::e4::e5::[])
          when
          let uu____5503 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5503 = "FStar.Buffer.blit" ->
          let uu____5504 =
            let uu____5515 = translate_expr env e1  in
            let uu____5516 = translate_expr env e2  in
            let uu____5517 = translate_expr env e3  in
            let uu____5518 = translate_expr env e4  in
            let uu____5519 = translate_expr env e5  in
            (uu____5515, uu____5516, uu____5517, uu____5518, uu____5519)  in
          EBufBlit uu____5504
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5521;
                  FStar_Extraction_ML_Syntax.loc = uu____5522;_},uu____5523);
             FStar_Extraction_ML_Syntax.mlty = uu____5524;
             FStar_Extraction_ML_Syntax.loc = uu____5525;_},e1::e2::e3::[])
          when
          let uu____5535 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5535 = "FStar.Buffer.fill" ->
          let uu____5536 =
            let uu____5543 = translate_expr env e1  in
            let uu____5544 = translate_expr env e2  in
            let uu____5545 = translate_expr env e3  in
            (uu____5543, uu____5544, uu____5545)  in
          EBufFill uu____5536
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5547;
             FStar_Extraction_ML_Syntax.loc = uu____5548;_},uu____5549::[])
          when
          let uu____5552 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5552 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5554;
             FStar_Extraction_ML_Syntax.loc = uu____5555;_},e1::[])
          when
          let uu____5559 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5559 = "Obj.repr" ->
          let uu____5560 =
            let uu____5565 = translate_expr env e1  in (uu____5565, TAny)  in
          ECast uu____5560
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5568;
             FStar_Extraction_ML_Syntax.loc = uu____5569;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5577 = FStar_Util.must (mk_width m)  in
          let uu____5578 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____5577 uu____5578 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5580;
             FStar_Extraction_ML_Syntax.loc = uu____5581;_},args)
          when is_bool_op op ->
          let uu____5589 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____5589 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5591;
             FStar_Extraction_ML_Syntax.loc = uu____5592;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5594;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5595;_}::[])
          when is_machine_int m ->
          let uu____5610 =
            let uu____5615 = FStar_Util.must (mk_width m)  in (uu____5615, c)
             in
          EConstant uu____5610
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5617;
             FStar_Extraction_ML_Syntax.loc = uu____5618;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5620;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5621;_}::[])
          when is_machine_int m ->
          let uu____5636 =
            let uu____5641 = FStar_Util.must (mk_width m)  in (uu____5641, c)
             in
          EConstant uu____5636
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5642;
             FStar_Extraction_ML_Syntax.loc = uu____5643;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5645;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5646;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5652 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5653;
             FStar_Extraction_ML_Syntax.loc = uu____5654;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5656;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5657;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5663 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5665;
             FStar_Extraction_ML_Syntax.loc = uu____5666;_},arg::[])
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
            let uu____5673 =
              let uu____5678 = translate_expr env arg  in
              (uu____5678, (TInt UInt64))  in
            ECast uu____5673
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5680 =
                 let uu____5685 = translate_expr env arg  in
                 (uu____5685, (TInt UInt32))  in
               ECast uu____5680)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5687 =
                   let uu____5692 = translate_expr env arg  in
                   (uu____5692, (TInt UInt16))  in
                 ECast uu____5687)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5694 =
                     let uu____5699 = translate_expr env arg  in
                     (uu____5699, (TInt UInt8))  in
                   ECast uu____5694)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5701 =
                       let uu____5706 = translate_expr env arg  in
                       (uu____5706, (TInt Int64))  in
                     ECast uu____5701)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5708 =
                         let uu____5713 = translate_expr env arg  in
                         (uu____5713, (TInt Int32))  in
                       ECast uu____5708)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5715 =
                           let uu____5720 = translate_expr env arg  in
                           (uu____5720, (TInt Int16))  in
                         ECast uu____5715)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5722 =
                             let uu____5727 = translate_expr env arg  in
                             (uu____5727, (TInt Int8))  in
                           ECast uu____5722)
                        else
                          (let uu____5729 =
                             let uu____5736 =
                               let uu____5739 = translate_expr env arg  in
                               [uu____5739]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5736)
                              in
                           EApp uu____5729)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5750 =
            let uu____5757 = translate_expr env head1  in
            let uu____5758 = FStar_List.map (translate_expr env) args  in
            (uu____5757, uu____5758)  in
          EApp uu____5750
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5769 =
            let uu____5776 = translate_expr env head1  in
            let uu____5777 = FStar_List.map (translate_type env) ty_args  in
            (uu____5776, uu____5777)  in
          ETypApp uu____5769
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5785 =
            let uu____5790 = translate_expr env e1  in
            let uu____5791 = translate_type env t_to  in
            (uu____5790, uu____5791)  in
          ECast uu____5785
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5792,fields) ->
          let uu____5810 =
            let uu____5821 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5822 =
              FStar_List.map
                (fun uu____5841  ->
                   match uu____5841 with
                   | (field,expr) ->
                       let uu____5852 = translate_expr env expr  in
                       (field, uu____5852)) fields
               in
            (uu____5821, uu____5822)  in
          EFlat uu____5810
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5861 =
            let uu____5868 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____5869 = translate_expr env e1  in
            (uu____5868, uu____5869, (FStar_Pervasives_Native.snd path))  in
          EField uu____5861
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5872 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5884) ->
          let uu____5889 =
            let uu____5890 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5890
             in
          failwith uu____5889
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5896 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____5896
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5902 = FStar_List.map (translate_expr env) es  in
          ETuple uu____5902
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5905,cons1),es) ->
          let uu____5922 =
            let uu____5931 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5932 = FStar_List.map (translate_expr env) es  in
            (uu____5931, cons1, uu____5932)  in
          ECons uu____5922
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____5955 =
            let uu____5964 = translate_expr env1 body  in
            let uu____5965 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____5964, uu____5965)  in
          EFun uu____5955
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5975 =
            let uu____5982 = translate_expr env e1  in
            let uu____5983 = translate_expr env e2  in
            let uu____5984 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____5982, uu____5983, uu____5984)  in
          EIfThenElse uu____5975
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5986 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5993 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____6008 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____6023 =
              let uu____6036 = FStar_List.map (translate_type env) ts  in
              (lid, uu____6036)  in
            TApp uu____6023
          else TQualified lid
      | uu____6042 -> failwith "invalid argument: assert_lid"

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
    fun uu____6068  ->
      match uu____6068 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____6094 = translate_pat env pat  in
            (match uu____6094 with
             | (env1,pat1) ->
                 let uu____6105 = translate_expr env1 expr  in
                 (pat1, uu____6105))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___41_6111  ->
    match uu___41_6111 with
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
          let uu____6175 =
            let uu____6176 =
              let uu____6181 = translate_width sw  in (uu____6181, s)  in
            PConstant uu____6176  in
          (env, uu____6175)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in (env1, (PVar { name; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____6185,cons1),ps) ->
          let uu____6202 =
            FStar_List.fold_left
              (fun uu____6222  ->
                 fun p1  ->
                   match uu____6222 with
                   | (env1,acc) ->
                       let uu____6242 = translate_pat env1 p1  in
                       (match uu____6242 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6202 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____6271,ps) ->
          let uu____6289 =
            FStar_List.fold_left
              (fun uu____6323  ->
                 fun uu____6324  ->
                   match (uu____6323, uu____6324) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____6393 = translate_pat env1 p1  in
                       (match uu____6393 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____6289 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____6455 =
            FStar_List.fold_left
              (fun uu____6475  ->
                 fun p1  ->
                   match uu____6475 with
                   | (env1,acc) ->
                       let uu____6495 = translate_pat env1 p1  in
                       (match uu____6495 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6455 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6522 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6527 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        let uu____6537 =
          let uu____6538 =
            let uu____6539 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____6539
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____6538
          then
            let uu____6551 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____6551
          else ()  in
        EString s
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6563) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6578 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6579 ->
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
          let uu____6599 =
            let uu____6606 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____6606)  in
          EApp uu____6599
