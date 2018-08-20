open Prims
type decl =
  | DGlobal of (flag Prims.list,
  (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
  Prims.int, typ, expr) FStar_Pervasives_Native.tuple5 
  | DFunction of (cc FStar_Pervasives_Native.option, flag Prims.list,
  Prims.int, typ,
  (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
  binder Prims.list, expr) FStar_Pervasives_Native.tuple7 
  | DTypeAlias of
  ((Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
  flag Prims.list, Prims.int, typ) FStar_Pervasives_Native.tuple4 
  | DTypeFlat of
  ((Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
  flag Prims.list, Prims.int,
  (Prims.string, (typ, Prims.bool) FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple4 
  | DExternal of (cc FStar_Pervasives_Native.option, flag Prims.list,
  (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
  typ) FStar_Pervasives_Native.tuple4 
  | DTypeVariant of
  ((Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
  flag Prims.list, Prims.int,
  (Prims.string,
    (Prims.string, (typ, Prims.bool) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2 Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple4 
  | DTypeAbstractStruct of (Prims.string Prims.list, Prims.string)
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
  | EQualified of (Prims.string Prims.list, Prims.string)
  FStar_Pervasives_Native.tuple2 
  | EConstant of (width, Prims.string) FStar_Pervasives_Native.tuple2 
  | EUnit 
  | EApp of (expr, expr Prims.list) FStar_Pervasives_Native.tuple2 
  | ETypApp of (expr, typ Prims.list) FStar_Pervasives_Native.tuple2 
  | ELet of (binder, expr, expr) FStar_Pervasives_Native.tuple3 
  | EIfThenElse of (expr, expr, expr) FStar_Pervasives_Native.tuple3 
  | ESequence of expr Prims.list 
  | EAssign of (expr, expr) FStar_Pervasives_Native.tuple2 
  | EBufCreate of (lifetime, expr, expr) FStar_Pervasives_Native.tuple3 
  | EBufRead of (expr, expr) FStar_Pervasives_Native.tuple2 
  | EBufWrite of (expr, expr, expr) FStar_Pervasives_Native.tuple3 
  | EBufSub of (expr, expr) FStar_Pervasives_Native.tuple2 
  | EBufBlit of (expr, expr, expr, expr, expr) FStar_Pervasives_Native.tuple5
  
  | EMatch of (expr,
  (pattern, expr) FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | EOp of (op, width) FStar_Pervasives_Native.tuple2 
  | ECast of (expr, typ) FStar_Pervasives_Native.tuple2 
  | EPushFrame 
  | EPopFrame 
  | EBool of Prims.bool 
  | EAny 
  | EAbort 
  | EReturn of expr 
  | EFlat of (typ,
  (Prims.string, expr) FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple2 
  | EField of (typ, expr, Prims.string) FStar_Pervasives_Native.tuple3 
  | EWhile of (expr, expr) FStar_Pervasives_Native.tuple2 
  | EBufCreateL of (lifetime, expr Prims.list) FStar_Pervasives_Native.tuple2
  
  | ETuple of expr Prims.list 
  | ECons of (typ, Prims.string, expr Prims.list)
  FStar_Pervasives_Native.tuple3 
  | EBufFill of (expr, expr, expr) FStar_Pervasives_Native.tuple3 
  | EString of Prims.string 
  | EFun of (binder Prims.list, expr, typ) FStar_Pervasives_Native.tuple3 
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
  | PCons of (Prims.string, pattern Prims.list)
  FStar_Pervasives_Native.tuple2 
  | PTuple of pattern Prims.list 
  | PRecord of (Prims.string, pattern) FStar_Pervasives_Native.tuple2
  Prims.list 
  | PConstant of (width, Prims.string) FStar_Pervasives_Native.tuple2 
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
  | TQualified of (Prims.string Prims.list, Prims.string)
  FStar_Pervasives_Native.tuple2 
  | TBool 
  | TAny 
  | TArrow of (typ, typ) FStar_Pervasives_Native.tuple2 
  | TBound of Prims.int 
  | TApp of
  ((Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
  typ Prims.list) FStar_Pervasives_Native.tuple2 
  | TTuple of typ Prims.list 
let (uu___is_DGlobal : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DGlobal _0 -> true | uu____632 -> false
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list,
      (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
      Prims.int, typ, expr) FStar_Pervasives_Native.tuple5)
  = fun projectee -> match projectee with | DGlobal _0 -> _0
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DFunction _0 -> true | uu____726 -> false
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option, flag Prims.list, Prims.int, typ,
      (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list, expr) FStar_Pervasives_Native.tuple7)
  = fun projectee -> match projectee with | DFunction _0 -> _0
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeAlias _0 -> true | uu____834 -> false
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list, Prims.int, typ) FStar_Pervasives_Native.tuple4)
  = fun projectee -> match projectee with | DTypeAlias _0 -> _0
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeFlat _0 -> true | uu____922 -> false
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list, Prims.int,
      (Prims.string, (typ, Prims.bool) FStar_Pervasives_Native.tuple2)
        FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple4)
  = fun projectee -> match projectee with | DTypeFlat _0 -> _0
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DExternal _0 -> true | uu____1032 -> false
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option, flag Prims.list,
      (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
      typ) FStar_Pervasives_Native.tuple4)
  = fun projectee -> match projectee with | DExternal _0 -> _0
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeVariant _0 -> true | uu____1132 -> false
let (__proj__DTypeVariant__item___0 :
  decl ->
    ((Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list, Prims.int,
      (Prims.string,
        (Prims.string, (typ, Prims.bool) FStar_Pervasives_Native.tuple2)
          FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple4)
  = fun projectee -> match projectee with | DTypeVariant _0 -> _0
let (uu___is_DTypeAbstractStruct : decl -> Prims.bool) =
  fun projectee ->
    match projectee with
    | DTypeAbstractStruct _0 -> true
    | uu____1248 -> false
let (__proj__DTypeAbstractStruct__item___0 :
  decl ->
    (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | DTypeAbstractStruct _0 -> _0
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee ->
    match projectee with | StdCall -> true | uu____1279 -> false
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee -> match projectee with | CDecl -> true | uu____1285 -> false
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee ->
    match projectee with | FastCall -> true | uu____1291 -> false
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Private -> true | uu____1297 -> false
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | WipeBody -> true | uu____1303 -> false
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | CInline -> true | uu____1309 -> false
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Substitute -> true | uu____1315 -> false
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | GCType -> true | uu____1321 -> false
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Comment _0 -> true | uu____1328 -> false
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Comment _0 -> _0
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | MustDisappear -> true | uu____1341 -> false
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Const _0 -> true | uu____1348 -> false
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Const _0 -> _0
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Prologue _0 -> true | uu____1362 -> false
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Prologue _0 -> _0
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Epilogue _0 -> true | uu____1376 -> false
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Epilogue _0 -> _0
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Abstract -> true | uu____1389 -> false
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee ->
    match projectee with | Eternal -> true | uu____1395 -> false
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee -> match projectee with | Stack -> true | uu____1401 -> false
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee ->
    match projectee with | ManuallyManaged -> true | uu____1407 -> false
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBound _0 -> true | uu____1414 -> false
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee -> match projectee with | EBound _0 -> _0
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EQualified _0 -> true | uu____1434 -> false
let (__proj__EQualified__item___0 :
  expr ->
    (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | EQualified _0 -> _0
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EConstant _0 -> true | uu____1470 -> false
let (__proj__EConstant__item___0 :
  expr -> (width, Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | EConstant _0 -> _0
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee -> match projectee with | EUnit -> true | uu____1495 -> false
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EApp _0 -> true | uu____1508 -> false
let (__proj__EApp__item___0 :
  expr -> (expr, expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | EApp _0 -> _0
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ETypApp _0 -> true | uu____1546 -> false
let (__proj__ETypApp__item___0 :
  expr -> (expr, typ Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | ETypApp _0 -> _0
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ELet _0 -> true | uu____1584 -> false
let (__proj__ELet__item___0 :
  expr -> (binder, expr, expr) FStar_Pervasives_Native.tuple3) =
  fun projectee -> match projectee with | ELet _0 -> _0
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EIfThenElse _0 -> true | uu____1622 -> false
let (__proj__EIfThenElse__item___0 :
  expr -> (expr, expr, expr) FStar_Pervasives_Native.tuple3) =
  fun projectee -> match projectee with | EIfThenElse _0 -> _0
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ESequence _0 -> true | uu____1656 -> false
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee -> match projectee with | ESequence _0 -> _0
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EAssign _0 -> true | uu____1680 -> false
let (__proj__EAssign__item___0 :
  expr -> (expr, expr) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | EAssign _0 -> _0
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufCreate _0 -> true | uu____1712 -> false
let (__proj__EBufCreate__item___0 :
  expr -> (lifetime, expr, expr) FStar_Pervasives_Native.tuple3) =
  fun projectee -> match projectee with | EBufCreate _0 -> _0
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufRead _0 -> true | uu____1748 -> false
let (__proj__EBufRead__item___0 :
  expr -> (expr, expr) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | EBufRead _0 -> _0
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufWrite _0 -> true | uu____1780 -> false
let (__proj__EBufWrite__item___0 :
  expr -> (expr, expr, expr) FStar_Pervasives_Native.tuple3) =
  fun projectee -> match projectee with | EBufWrite _0 -> _0
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufSub _0 -> true | uu____1816 -> false
let (__proj__EBufSub__item___0 :
  expr -> (expr, expr) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | EBufSub _0 -> _0
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufBlit _0 -> true | uu____1852 -> false
let (__proj__EBufBlit__item___0 :
  expr -> (expr, expr, expr, expr, expr) FStar_Pervasives_Native.tuple5) =
  fun projectee -> match projectee with | EBufBlit _0 -> _0
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EMatch _0 -> true | uu____1906 -> false
let (__proj__EMatch__item___0 :
  expr ->
    (expr, (pattern, expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | EMatch _0 -> _0
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EOp _0 -> true | uu____1954 -> false
let (__proj__EOp__item___0 :
  expr -> (op, width) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | EOp _0 -> _0
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ECast _0 -> true | uu____1984 -> false
let (__proj__ECast__item___0 :
  expr -> (expr, typ) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | ECast _0 -> _0
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EPushFrame -> true | uu____2009 -> false
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EPopFrame -> true | uu____2015 -> false
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBool _0 -> true | uu____2022 -> false
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee -> match projectee with | EBool _0 -> _0
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee -> match projectee with | EAny -> true | uu____2035 -> false
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EAbort -> true | uu____2041 -> false
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EReturn _0 -> true | uu____2048 -> false
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee -> match projectee with | EReturn _0 -> _0
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EFlat _0 -> true | uu____2072 -> false
let (__proj__EFlat__item___0 :
  expr ->
    (typ, (Prims.string, expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | EFlat _0 -> _0
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EField _0 -> true | uu____2122 -> false
let (__proj__EField__item___0 :
  expr -> (typ, expr, Prims.string) FStar_Pervasives_Native.tuple3) =
  fun projectee -> match projectee with | EField _0 -> _0
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EWhile _0 -> true | uu____2158 -> false
let (__proj__EWhile__item___0 :
  expr -> (expr, expr) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | EWhile _0 -> _0
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufCreateL _0 -> true | uu____2190 -> false
let (__proj__EBufCreateL__item___0 :
  expr -> (lifetime, expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | EBufCreateL _0 -> _0
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ETuple _0 -> true | uu____2224 -> false
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee -> match projectee with | ETuple _0 -> _0
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ECons _0 -> true | uu____2252 -> false
let (__proj__ECons__item___0 :
  expr -> (typ, Prims.string, expr Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee -> match projectee with | ECons _0 -> _0
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufFill _0 -> true | uu____2296 -> false
let (__proj__EBufFill__item___0 :
  expr -> (expr, expr, expr) FStar_Pervasives_Native.tuple3) =
  fun projectee -> match projectee with | EBufFill _0 -> _0
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EString _0 -> true | uu____2328 -> false
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee -> match projectee with | EString _0 -> _0
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EFun _0 -> true | uu____2350 -> false
let (__proj__EFun__item___0 :
  expr -> (binder Prims.list, expr, typ) FStar_Pervasives_Native.tuple3) =
  fun projectee -> match projectee with | EFun _0 -> _0
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EAbortS _0 -> true | uu____2388 -> false
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee -> match projectee with | EAbortS _0 -> _0
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufFree _0 -> true | uu____2402 -> false
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee -> match projectee with | EBufFree _0 -> _0
let (uu___is_Add : op -> Prims.bool) =
  fun projectee -> match projectee with | Add -> true | uu____2415 -> false
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee -> match projectee with | AddW -> true | uu____2421 -> false
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee -> match projectee with | Sub -> true | uu____2427 -> false
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee -> match projectee with | SubW -> true | uu____2433 -> false
let (uu___is_Div : op -> Prims.bool) =
  fun projectee -> match projectee with | Div -> true | uu____2439 -> false
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee -> match projectee with | DivW -> true | uu____2445 -> false
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee -> match projectee with | Mult -> true | uu____2451 -> false
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee -> match projectee with | MultW -> true | uu____2457 -> false
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee -> match projectee with | Mod -> true | uu____2463 -> false
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee -> match projectee with | BOr -> true | uu____2469 -> false
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee -> match projectee with | BAnd -> true | uu____2475 -> false
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee -> match projectee with | BXor -> true | uu____2481 -> false
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee ->
    match projectee with | BShiftL -> true | uu____2487 -> false
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee ->
    match projectee with | BShiftR -> true | uu____2493 -> false
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee -> match projectee with | BNot -> true | uu____2499 -> false
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee -> match projectee with | Eq -> true | uu____2505 -> false
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee -> match projectee with | Neq -> true | uu____2511 -> false
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee -> match projectee with | Lt -> true | uu____2517 -> false
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee -> match projectee with | Lte -> true | uu____2523 -> false
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee -> match projectee with | Gt -> true | uu____2529 -> false
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee -> match projectee with | Gte -> true | uu____2535 -> false
let (uu___is_And : op -> Prims.bool) =
  fun projectee -> match projectee with | And -> true | uu____2541 -> false
let (uu___is_Or : op -> Prims.bool) =
  fun projectee -> match projectee with | Or -> true | uu____2547 -> false
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee -> match projectee with | Xor -> true | uu____2553 -> false
let (uu___is_Not : op -> Prims.bool) =
  fun projectee -> match projectee with | Not -> true | uu____2559 -> false
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PUnit -> true | uu____2565 -> false
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PBool _0 -> true | uu____2572 -> false
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PBool _0 -> _0
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PVar _0 -> true | uu____2586 -> false
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee -> match projectee with | PVar _0 -> _0
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PCons _0 -> true | uu____2606 -> false
let (__proj__PCons__item___0 :
  pattern ->
    (Prims.string, pattern Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | PCons _0 -> _0
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PTuple _0 -> true | uu____2640 -> false
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee -> match projectee with | PTuple _0 -> _0
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PRecord _0 -> true | uu____2666 -> false
let (__proj__PRecord__item___0 :
  pattern ->
    (Prims.string, pattern) FStar_Pervasives_Native.tuple2 Prims.list)
  = fun projectee -> match projectee with | PRecord _0 -> _0
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PConstant _0 -> true | uu____2702 -> false
let (__proj__PConstant__item___0 :
  pattern -> (width, Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | PConstant _0 -> _0
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee -> match projectee with | UInt8 -> true | uu____2727 -> false
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee ->
    match projectee with | UInt16 -> true | uu____2733 -> false
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee ->
    match projectee with | UInt32 -> true | uu____2739 -> false
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee ->
    match projectee with | UInt64 -> true | uu____2745 -> false
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int8 -> true | uu____2751 -> false
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int16 -> true | uu____2757 -> false
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int32 -> true | uu____2763 -> false
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int64 -> true | uu____2769 -> false
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee -> match projectee with | Bool -> true | uu____2775 -> false
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee -> match projectee with | CInt -> true | uu____2781 -> false
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ; mut = __fname__mut;_} ->
        __fname__name
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ; mut = __fname__mut;_} ->
        __fname__typ
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ; mut = __fname__mut;_} ->
        __fname__mut
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TInt _0 -> true | uu____2812 -> false
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee -> match projectee with | TInt _0 -> _0
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TBuf _0 -> true | uu____2826 -> false
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee -> match projectee with | TBuf _0 -> _0
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee -> match projectee with | TUnit -> true | uu____2839 -> false
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TQualified _0 -> true | uu____2852 -> false
let (__proj__TQualified__item___0 :
  typ ->
    (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | TQualified _0 -> _0
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee -> match projectee with | TBool -> true | uu____2883 -> false
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee -> match projectee with | TAny -> true | uu____2889 -> false
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TArrow _0 -> true | uu____2900 -> false
let (__proj__TArrow__item___0 :
  typ -> (typ, typ) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | TArrow _0 -> _0
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TBound _0 -> true | uu____2926 -> false
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee -> match projectee with | TBound _0 -> _0
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TApp _0 -> true | uu____2952 -> false
let (__proj__TApp__item___0 :
  typ ->
    ((Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | TApp _0 -> _0
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TTuple _0 -> true | uu____3004 -> false
let (__proj__TTuple__item___0 : typ -> typ Prims.list) =
  fun projectee -> match projectee with | TTuple _0 -> _0
type program = decl Prims.list
type ident = Prims.string
type fields_t =
  (Prims.string, (typ, Prims.bool) FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2 Prims.list
type branches_t =
  (Prims.string,
    (Prims.string, (typ, Prims.bool) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2 Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list
type fsdoc = Prims.string
type branch = (pattern, expr) FStar_Pervasives_Native.tuple2
type branches = (pattern, expr) FStar_Pervasives_Native.tuple2 Prims.list
type constant = (width, Prims.string) FStar_Pervasives_Native.tuple2
type var = Prims.int
type lident =
  (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2
type version = Prims.int
let (current_version : version) = (Prims.parse_int "27")
type file = (Prims.string, program) FStar_Pervasives_Native.tuple2
type binary_format =
  (version, file Prims.list) FStar_Pervasives_Native.tuple2
let fst3 :
  'Auu____3084 'Auu____3085 'Auu____3086 .
    ('Auu____3084, 'Auu____3085, 'Auu____3086) FStar_Pervasives_Native.tuple3
      -> 'Auu____3084
  =
  fun uu____3097 -> match uu____3097 with | (x, uu____3105, uu____3106) -> x
let snd3 :
  'Auu____3115 'Auu____3116 'Auu____3117 .
    ('Auu____3115, 'Auu____3116, 'Auu____3117) FStar_Pervasives_Native.tuple3
      -> 'Auu____3116
  =
  fun uu____3128 -> match uu____3128 with | (uu____3135, x, uu____3137) -> x
let thd3 :
  'Auu____3146 'Auu____3147 'Auu____3148 .
    ('Auu____3146, 'Auu____3147, 'Auu____3148) FStar_Pervasives_Native.tuple3
      -> 'Auu____3148
  =
  fun uu____3159 -> match uu____3159 with | (uu____3166, uu____3167, x) -> x
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___274_3175 ->
    match uu___274_3175 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____3178 -> FStar_Pervasives_Native.None
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___275_3185 ->
    match uu___275_3185 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____3188 -> FStar_Pervasives_Native.None
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op -> (mk_bool_op op) <> FStar_Pervasives_Native.None
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___276_3202 ->
    match uu___276_3202 with
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
    | uu____3205 -> FStar_Pervasives_Native.None
let (is_op : Prims.string -> Prims.bool) =
  fun op -> (mk_op op) <> FStar_Pervasives_Native.None
let (is_machine_int : Prims.string -> Prims.bool) =
  fun m -> (mk_width m) <> FStar_Pervasives_Native.None
type env =
  {
  names: name Prims.list ;
  names_t: Prims.string Prims.list ;
  module_name: Prims.string Prims.list }
and name = {
  pretty: Prims.string }
let (__proj__Mkenv__item__names : env -> name Prims.list) =
  fun projectee ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__names
let (__proj__Mkenv__item__names_t : env -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__names_t
let (__proj__Mkenv__item__module_name : env -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__module_name
let (__proj__Mkname__item__pretty : name -> Prims.string) =
  fun projectee ->
    match projectee with | { pretty = __fname__pretty;_} -> __fname__pretty
let (empty : Prims.string Prims.list -> env) =
  fun module_name -> { names = []; names_t = []; module_name }
let (extend : env -> Prims.string -> env) =
  fun env ->
    fun x ->
      let uu___282_3325 = env in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___282_3325.names_t);
        module_name = (uu___282_3325.module_name)
      }
let (extend_t : env -> Prims.string -> env) =
  fun env ->
    fun x ->
      let uu___283_3336 = env in
      {
        names = (uu___283_3336.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___283_3336.module_name)
      }
let (find_name : env -> Prims.string -> name) =
  fun env ->
    fun x ->
      let uu____3347 =
        FStar_List.tryFind (fun name -> name.pretty = x) env.names in
      match uu____3347 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None ->
          failwith "internal error: name not found"
let (find : env -> Prims.string -> Prims.int) =
  fun env ->
    fun x ->
      try
        (fun uu___285_3364 ->
           match () with
           | () -> FStar_List.index (fun name -> name.pretty = x) env.names)
          ()
      with
      | uu___284_3369 ->
          let uu____3370 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____3370
let (find_t : env -> Prims.string -> Prims.int) =
  fun env ->
    fun x ->
      try
        (fun uu___287_3382 ->
           match () with
           | () -> FStar_List.index (fun name -> name = x) env.names_t) ()
      with
      | uu___286_3387 ->
          let uu____3388 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____3388
let add_binders :
  'Auu____3395 .
    env ->
      (Prims.string, 'Auu____3395) FStar_Pervasives_Native.tuple2 Prims.list
        -> env
  =
  fun env ->
    fun binders ->
      FStar_List.fold_left
        (fun env1 ->
           fun uu____3427 ->
             match uu____3427 with | (name, uu____3433) -> extend env1 name)
        env binders
let (list_elements :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr Prims.list)
  =
  fun e2 ->
    let rec list_elements acc e21 =
      match e21.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_CTor
          (("Prims"::[], "Cons"), hd1::tl1::[]) ->
          list_elements (hd1 :: acc) tl1
      | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[], "Nil"), []) ->
          FStar_List.rev acc
      | uu____3470 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!" in
    list_elements [] e2
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____3685 ->
    match uu____3685 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m ->
             let m_name =
               let uu____3733 = m in
               match uu____3733 with
               | (path, uu____3747, uu____3748) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path in
             try
               (fun uu___289_3766 ->
                  match () with
                  | () ->
                      (FStar_Util.print1
                         "Attempting to translate module %s\n" m_name;
                       (let uu____3770 = translate_module m in
                        FStar_Pervasives_Native.Some uu____3770))) ()
             with
             | e ->
                 ((let uu____3779 = FStar_Util.print_exn e in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3779);
                  FStar_Pervasives_Native.None)) modules
and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath,
    (FStar_Extraction_ML_Syntax.mlsig, FStar_Extraction_ML_Syntax.mlmodule)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
    FStar_Extraction_ML_Syntax.mllib) FStar_Pervasives_Native.tuple3 -> 
    file)
  =
  fun uu____3780 ->
    match uu____3780 with
    | (module_name, modul, uu____3795) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name] in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature, decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____3822 ->
              failwith "Unexpected standalone interface or nested modules" in
        ((FStar_String.concat "_" module_name1), program)
and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags1 ->
    FStar_List.choose
      (fun uu___277_3833 ->
         match uu___277_3833 with
         | FStar_Extraction_ML_Syntax.Private ->
             FStar_Pervasives_Native.Some Private
         | FStar_Extraction_ML_Syntax.NoExtract ->
             FStar_Pervasives_Native.Some WipeBody
         | FStar_Extraction_ML_Syntax.CInline ->
             FStar_Pervasives_Native.Some CInline
         | FStar_Extraction_ML_Syntax.Substitute ->
             FStar_Pervasives_Native.Some Substitute
         | FStar_Extraction_ML_Syntax.GCType ->
             FStar_Pervasives_Native.Some GCType
         | FStar_Extraction_ML_Syntax.Comment s ->
             FStar_Pervasives_Native.Some (Comment s)
         | FStar_Extraction_ML_Syntax.StackInline ->
             FStar_Pervasives_Native.Some MustDisappear
         | FStar_Extraction_ML_Syntax.CConst s ->
             FStar_Pervasives_Native.Some (Const s)
         | FStar_Extraction_ML_Syntax.CPrologue s ->
             FStar_Pervasives_Native.Some (Prologue s)
         | FStar_Extraction_ML_Syntax.CEpilogue s ->
             FStar_Pervasives_Native.Some (Epilogue s)
         | FStar_Extraction_ML_Syntax.CAbstract ->
             FStar_Pervasives_Native.Some Abstract
         | uu____3840 -> FStar_Pervasives_Native.None) flags1
and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags1 ->
    let uu____3844 =
      FStar_List.choose
        (fun uu___278_3849 ->
           match uu___278_3849 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____3853 -> FStar_Pervasives_Native.None) flags1 in
    match uu____3844 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____3856 -> FStar_Pervasives_Native.None
and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env ->
    fun d ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor, lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3869 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3871 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m, uu____3875) ->
          (FStar_Util.print1_warning
             "Not extracting exception %s to KreMLin (exceptions unsupported)\n"
             m;
           [])
and (translate_let :
  env ->
    FStar_Extraction_ML_Syntax.mlletflavor ->
      FStar_Extraction_ML_Syntax.mllb -> decl FStar_Pervasives_Native.option)
  =
  fun env ->
    fun flavor ->
      fun lb ->
        match lb with
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3897;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args, body);
                FStar_Extraction_ML_Syntax.mlty = uu____3900;
                FStar_Extraction_ML_Syntax.loc = uu____3901;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3903;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___279_3921 ->
                      match uu___279_3921 with
                      | FStar_Extraction_ML_Syntax.Assumed -> true
                      | uu____3922 -> false) meta in
               let env1 =
                 if flavor = FStar_Extraction_ML_Syntax.Rec
                 then extend env name
                 else env in
               let env2 =
                 FStar_List.fold_left
                   (fun env2 -> fun name1 -> extend_t env2 name1) env1 tvars in
               let rec find_return_type eff i uu___280_3949 =
                 match uu___280_3949 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3954, eff1, t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (eff, t) in
               let uu____3958 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0 in
               match uu____3958 with
               | (eff, t) ->
                   let t1 = translate_type env2 t in
                   let binders = translate_binders env2 args in
                   let env3 = add_binders env2 args in
                   let name1 = ((env3.module_name), name) in
                   let cc = translate_cc meta in
                   let meta1 =
                     match (eff, t1) with
                     | (FStar_Extraction_ML_Syntax.E_GHOST, uu____3993) ->
                         let uu____3994 = translate_flags meta in
                         MustDisappear :: uu____3994
                     | (FStar_Extraction_ML_Syntax.E_PURE, TUnit) ->
                         let uu____3997 = translate_flags meta in
                         MustDisappear :: uu____3997
                     | uu____4000 -> translate_flags meta in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____4009 =
                          let uu____4010 =
                            let uu____4029 = translate_type env3 t0 in
                            (cc, meta1, name1, uu____4029) in
                          DExternal uu____4010 in
                        FStar_Pervasives_Native.Some uu____4009
                      else
                        ((let uu____4042 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1 in
                          FStar_Util.print1_warning
                            "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                            uu____4042);
                         FStar_Pervasives_Native.None))
                   else
                     (try
                        (fun uu___291_4048 ->
                           match () with
                           | () ->
                               let body1 = translate_expr env3 body in
                               FStar_Pervasives_Native.Some
                                 (DFunction
                                    (cc, meta1, (FStar_List.length tvars),
                                      t1, name1, binders, body1))) ()
                      with
                      | e ->
                          let msg = FStar_Util.print_exn e in
                          ((let uu____4075 =
                              let uu____4080 =
                                let uu____4081 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1 in
                                FStar_Util.format2
                                  "Error while extracting %s to KreMLin (%s)\n"
                                  uu____4081 msg in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____4080) in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____4075);
                           (let msg1 =
                              Prims.strcat
                                "This function was not extracted:\n" msg in
                            FStar_Pervasives_Native.Some
                              (DFunction
                                 (cc, meta1, (FStar_List.length tvars), t1,
                                   name1, binders, (EAbortS msg1)))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4098;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Coerce
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (args, body);
                     FStar_Extraction_ML_Syntax.mlty = uu____4101;
                     FStar_Extraction_ML_Syntax.loc = uu____4102;_},
                   uu____4103, uu____4104);
                FStar_Extraction_ML_Syntax.mlty = uu____4105;
                FStar_Extraction_ML_Syntax.loc = uu____4106;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4108;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___279_4126 ->
                      match uu___279_4126 with
                      | FStar_Extraction_ML_Syntax.Assumed -> true
                      | uu____4127 -> false) meta in
               let env1 =
                 if flavor = FStar_Extraction_ML_Syntax.Rec
                 then extend env name
                 else env in
               let env2 =
                 FStar_List.fold_left
                   (fun env2 -> fun name1 -> extend_t env2 name1) env1 tvars in
               let rec find_return_type eff i uu___280_4154 =
                 match uu___280_4154 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____4159, eff1, t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (eff, t) in
               let uu____4163 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0 in
               match uu____4163 with
               | (eff, t) ->
                   let t1 = translate_type env2 t in
                   let binders = translate_binders env2 args in
                   let env3 = add_binders env2 args in
                   let name1 = ((env3.module_name), name) in
                   let cc = translate_cc meta in
                   let meta1 =
                     match (eff, t1) with
                     | (FStar_Extraction_ML_Syntax.E_GHOST, uu____4198) ->
                         let uu____4199 = translate_flags meta in
                         MustDisappear :: uu____4199
                     | (FStar_Extraction_ML_Syntax.E_PURE, TUnit) ->
                         let uu____4202 = translate_flags meta in
                         MustDisappear :: uu____4202
                     | uu____4205 -> translate_flags meta in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____4214 =
                          let uu____4215 =
                            let uu____4234 = translate_type env3 t0 in
                            (cc, meta1, name1, uu____4234) in
                          DExternal uu____4215 in
                        FStar_Pervasives_Native.Some uu____4214
                      else
                        ((let uu____4247 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1 in
                          FStar_Util.print1_warning
                            "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                            uu____4247);
                         FStar_Pervasives_Native.None))
                   else
                     (try
                        (fun uu___291_4253 ->
                           match () with
                           | () ->
                               let body1 = translate_expr env3 body in
                               FStar_Pervasives_Native.Some
                                 (DFunction
                                    (cc, meta1, (FStar_List.length tvars),
                                      t1, name1, binders, body1))) ()
                      with
                      | e ->
                          let msg = FStar_Util.print_exn e in
                          ((let uu____4280 =
                              let uu____4285 =
                                let uu____4286 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1 in
                                FStar_Util.format2
                                  "Error while extracting %s to KreMLin (%s)\n"
                                  uu____4286 msg in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____4285) in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____4280);
                           (let msg1 =
                              Prims.strcat
                                "This function was not extracted:\n" msg in
                            FStar_Pervasives_Native.Some
                              (DFunction
                                 (cc, meta1, (FStar_List.length tvars), t1,
                                   name1, binders, (EAbortS msg1)))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4303;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4306;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let meta1 = translate_flags meta in
               let env1 =
                 FStar_List.fold_left
                   (fun env1 -> fun name1 -> extend_t env1 name1) env tvars in
               let t1 = translate_type env1 t in
               let name1 = ((env1.module_name), name) in
               try
                 (fun uu___293_4332 ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____4352 =
                       let uu____4357 =
                         let uu____4358 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1 in
                         let uu____4359 = FStar_Util.print_exn e in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____4358
                           uu____4359 in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____4357) in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____4352);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4370;
            FStar_Extraction_ML_Syntax.mllb_def = uu____4371;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____4372;
            FStar_Extraction_ML_Syntax.print_typ = uu____4373;_} ->
            ((let uu____4377 =
                let uu____4382 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____4382) in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____4377);
             (match ts with
              | FStar_Pervasives_Native.Some (idents, t) ->
                  let uu____4386 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____4386
              | FStar_Pervasives_Native.None -> ());
             FStar_Pervasives_Native.None)
and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env ->
    fun ty ->
      let uu____4393 = ty in
      match uu____4393 with
      | (uu____4396, uu____4397, uu____4398, uu____4399, flags1, uu____4401)
          ->
          if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract flags1
          then FStar_Pervasives_Native.None
          else
            (match ty with
             | (assumed, name, _mangled_name, args, flags2,
                FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Abbrev t)) ->
                 let name1 = ((env.module_name), name) in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1 -> fun name2 -> extend_t env1 name2) env args in
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
                        FStar_Extraction_ML_Syntax.string_of_mlpath name1 in
                      FStar_Util.print1_warning
                        "Not extracting type definition %s to KreMLin (assumed type)\n"
                        name2;
                      FStar_Pervasives_Native.None)
                   else
                     (let uu____4449 =
                        let uu____4450 =
                          let uu____4467 = translate_flags flags2 in
                          let uu____4470 = translate_type env1 t in
                          (name1, uu____4467, (FStar_List.length args),
                            uu____4470) in
                        DTypeAlias uu____4450 in
                      FStar_Pervasives_Native.Some uu____4449)
             | (uu____4479, name, _mangled_name, args, flags2,
                FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name) in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1 -> fun name2 -> extend_t env1 name2) env args in
                 let uu____4511 =
                   let uu____4512 =
                     let uu____4539 = translate_flags flags2 in
                     let uu____4542 =
                       FStar_List.map
                         (fun uu____4569 ->
                            match uu____4569 with
                            | (f, t) ->
                                let uu____4584 =
                                  let uu____4589 = translate_type env1 t in
                                  (uu____4589, false) in
                                (f, uu____4584)) fields in
                     (name1, uu____4539, (FStar_List.length args),
                       uu____4542) in
                   DTypeFlat uu____4512 in
                 FStar_Pervasives_Native.Some uu____4511
             | (uu____4612, name, _mangled_name, args, flags2,
                FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name) in
                 let flags3 = translate_flags flags2 in
                 let env1 = FStar_List.fold_left extend_t env args in
                 let uu____4649 =
                   let uu____4650 =
                     let uu____4683 =
                       FStar_List.map
                         (fun uu____4728 ->
                            match uu____4728 with
                            | (cons1, ts) ->
                                let uu____4767 =
                                  FStar_List.map
                                    (fun uu____4794 ->
                                       match uu____4794 with
                                       | (name2, t) ->
                                           let uu____4809 =
                                             let uu____4814 =
                                               translate_type env1 t in
                                             (uu____4814, false) in
                                           (name2, uu____4809)) ts in
                                (cons1, uu____4767)) branches in
                     (name1, flags3, (FStar_List.length args), uu____4683) in
                   DTypeVariant uu____4650 in
                 FStar_Pervasives_Native.Some uu____4649
             | (uu____4853, name, _mangled_name, uu____4856, uu____4857,
                uu____4858) ->
                 ((let uu____4868 =
                     let uu____4873 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____4873) in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____4868);
                  FStar_Pervasives_Native.None))
and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4877 = find_t env name in TBound uu____4877
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____4879, t2) ->
          let uu____4881 =
            let uu____4886 = translate_type env t1 in
            let uu____4887 = translate_type env t2 in
            (uu____4886, uu____4887) in
          TArrow uu____4881
      | FStar_Extraction_ML_Syntax.MLTY_Erased -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu____4891 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4891 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu____4895 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4895 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], ("FStar"::m::[], "t"))
          when is_machine_int m ->
          let uu____4901 = FStar_Util.must (mk_width m) in TInt uu____4901
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], ("FStar"::m::[], "t'"))
          when is_machine_int m ->
          let uu____4907 = FStar_Util.must (mk_width m) in TInt uu____4907
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu____4912 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4912 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____4913::arg::uu____4915::[], p) when
          (((let uu____4921 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4921 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____4923 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____4923 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____4925 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____4925 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____4927 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4927 = "FStar.HyperStack.ST.s_mref")
          -> let uu____4928 = translate_type env arg in TBuf uu____4928
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____4930::[], p) when
          ((((((((((let uu____4936 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4936 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____4938 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p in
                      uu____4938 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____4940 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p in
                     uu____4940 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____4942 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4942 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____4944 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p in
                   uu____4944 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____4946 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p in
                  uu____4946 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____4948 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____4948 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____4950 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu____4950 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____4952 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____4952 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____4954 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____4954 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____4956 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4956 = "FStar.HyperStack.ST.mmmref")
          -> let uu____4957 = translate_type env arg in TBuf uu____4957
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          (((((((((((let uu____4964 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p in
                     uu____4964 = "LowStar.Buffer.buffer") ||
                      (let uu____4966 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p in
                       uu____4966 = "FStar.Buffer.buffer"))
                     ||
                     (let uu____4968 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p in
                      uu____4968 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____4970 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p in
                     uu____4970 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____4972 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4972 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____4974 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p in
                   uu____4974 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____4976 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p in
                  uu____4976 = "FStar.HyperStack.mmref"))
                ||
                (let uu____4978 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____4978 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____4980 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu____4980 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____4982 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____4982 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____4984 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____4984 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____4986 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4986 = "FStar.HyperStack.ST.mmref")
          -> let uu____4987 = translate_type env arg in TBuf uu____4987
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4988::arg::[], p) when
          (let uu____4995 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4995 = "FStar.HyperStack.s_ref") ||
            (let uu____4997 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4997 = "FStar.HyperStack.ST.s_ref")
          -> let uu____4998 = translate_type env arg in TBuf uu____4998
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4999::[], p) when
          let uu____5003 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5003 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, (ns, t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____5029 = FStar_List.map (translate_type env) args in
          TTuple uu____5029
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____5038 =
              let uu____5051 = FStar_List.map (translate_type env) args in
              (lid, uu____5051) in
            TApp uu____5038
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____5066 = FStar_List.map (translate_type env) ts in
          TTuple uu____5066
and (translate_binders :
  env ->
    (FStar_Extraction_ML_Syntax.mlident, FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2 Prims.list -> binder Prims.list)
  = fun env -> fun args -> FStar_List.map (translate_binder env) args
and (translate_binder :
  env ->
    (FStar_Extraction_ML_Syntax.mlident, FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2 -> binder)
  =
  fun env ->
    fun uu____5082 ->
      match uu____5082 with
      | (name, typ) ->
          let uu____5089 = translate_type env typ in
          { name; typ = uu____5089; mut = false }
and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env ->
    fun e ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____5094 = find env name in EBound uu____5094
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], op) when
          (is_machine_int m) && (is_op op) ->
          let uu____5099 =
            let uu____5104 = FStar_Util.must (mk_op op) in
            let uu____5105 = FStar_Util.must (mk_width m) in
            (uu____5104, uu____5105) in
          EOp uu____5099
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[], op) when
          is_bool_op op ->
          let uu____5109 =
            let uu____5114 = FStar_Util.must (mk_bool_op op) in
            (uu____5114, Bool) in
          EOp uu____5109
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,
            { FStar_Extraction_ML_Syntax.mllb_name = name;
              FStar_Extraction_ML_Syntax.mllb_tysc =
                FStar_Pervasives_Native.Some ([], typ);
              FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit;
              FStar_Extraction_ML_Syntax.mllb_def = body;
              FStar_Extraction_ML_Syntax.mllb_meta = flags1;
              FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),
           continuation)
          ->
          let binder =
            let uu____5133 = translate_type env typ in
            { name; typ = uu____5133; mut = false } in
          let body1 = translate_expr env body in
          let env1 = extend env name in
          let continuation1 = translate_expr env1 continuation in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr, branches) ->
          let uu____5159 =
            let uu____5170 = translate_expr env expr in
            let uu____5171 = translate_branches env branches in
            (uu____5170, uu____5171) in
          EMatch uu____5159
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5185;
                  FStar_Extraction_ML_Syntax.loc = uu____5186;_},
                t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____5188;
             FStar_Extraction_ML_Syntax.loc = uu____5189;_},
           arg::[])
          when
          let uu____5195 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5195 = "FStar.Dyn.undyn" ->
          let uu____5196 =
            let uu____5201 = translate_expr env arg in
            let uu____5202 = translate_type env t in (uu____5201, uu____5202) in
          ECast uu____5196
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5204;
                  FStar_Extraction_ML_Syntax.loc = uu____5205;_},
                uu____5206);
             FStar_Extraction_ML_Syntax.mlty = uu____5207;
             FStar_Extraction_ML_Syntax.loc = uu____5208;_},
           uu____5209)
          when
          let uu____5218 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5218 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5220;
                  FStar_Extraction_ML_Syntax.loc = uu____5221;_},
                uu____5222);
             FStar_Extraction_ML_Syntax.mlty = uu____5223;
             FStar_Extraction_ML_Syntax.loc = uu____5224;_},
           arg::[])
          when
          ((let uu____5234 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____5234 = "FStar.HyperStack.All.failwith") ||
             (let uu____5236 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____5236 = "FStar.Error.unexpected"))
            ||
            (let uu____5238 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5238 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____5240;
               FStar_Extraction_ML_Syntax.loc = uu____5241;_} -> EAbortS msg
           | uu____5242 ->
               let print7 =
                 let uu____5244 =
                   let uu____5245 =
                     let uu____5246 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____5246 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____5245 in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____5244 in
               let print8 =
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top
                   (FStar_Extraction_ML_Syntax.MLE_App (print7, [arg])) in
               let t = translate_expr env print8 in ESequence [t; EAbort])
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5252;
                  FStar_Extraction_ML_Syntax.loc = uu____5253;_},
                uu____5254);
             FStar_Extraction_ML_Syntax.mlty = uu____5255;
             FStar_Extraction_ML_Syntax.loc = uu____5256;_},
           e1::[])
          when
          (let uu____5266 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5266 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____5268 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5268 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5270;
                  FStar_Extraction_ML_Syntax.loc = uu____5271;_},
                uu____5272);
             FStar_Extraction_ML_Syntax.mlty = uu____5273;
             FStar_Extraction_ML_Syntax.loc = uu____5274;_},
           e1::e2::[])
          when
          ((let uu____5285 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____5285 = "FStar.Buffer.index") ||
             (let uu____5287 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____5287 = "FStar.Buffer.op_Array_Access"))
            ||
            (let uu____5289 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5289 = "LowStar.Buffer.index")
          ->
          let uu____5290 =
            let uu____5295 = translate_expr env e1 in
            let uu____5296 = translate_expr env e2 in
            (uu____5295, uu____5296) in
          EBufRead uu____5290
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5298;
                  FStar_Extraction_ML_Syntax.loc = uu____5299;_},
                uu____5300);
             FStar_Extraction_ML_Syntax.mlty = uu____5301;
             FStar_Extraction_ML_Syntax.loc = uu____5302;_},
           e1::[])
          when
          let uu____5310 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5310 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____5311 =
            let uu____5316 = translate_expr env e1 in
            (uu____5316, (EConstant (UInt32, "0"))) in
          EBufRead uu____5311
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5318;
                  FStar_Extraction_ML_Syntax.loc = uu____5319;_},
                uu____5320);
             FStar_Extraction_ML_Syntax.mlty = uu____5321;
             FStar_Extraction_ML_Syntax.loc = uu____5322;_},
           e1::e2::[])
          when
          (let uu____5333 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5333 = "FStar.Buffer.create") ||
            (let uu____5335 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5335 = "LowStar.Buffer.alloca")
          ->
          let uu____5336 =
            let uu____5343 = translate_expr env e1 in
            let uu____5344 = translate_expr env e2 in
            (Stack, uu____5343, uu____5344) in
          EBufCreate uu____5336
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5346;
                  FStar_Extraction_ML_Syntax.loc = uu____5347;_},
                uu____5348);
             FStar_Extraction_ML_Syntax.mlty = uu____5349;
             FStar_Extraction_ML_Syntax.loc = uu____5350;_},
           init1::[])
          when
          let uu____5358 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5358 = "FStar.HyperStack.ST.salloc" ->
          let uu____5359 =
            let uu____5366 = translate_expr env init1 in
            (Stack, uu____5366, (EConstant (UInt32, "1"))) in
          EBufCreate uu____5359
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5368;
                  FStar_Extraction_ML_Syntax.loc = uu____5369;_},
                uu____5370);
             FStar_Extraction_ML_Syntax.mlty = uu____5371;
             FStar_Extraction_ML_Syntax.loc = uu____5372;_},
           e2::[])
          when
          (let uu____5382 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5382 = "FStar.Buffer.createL") ||
            (let uu____5384 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5384 = "LowStar.Buffer.alloca_of_list")
          ->
          let uu____5385 =
            let uu____5392 =
              let uu____5395 = list_elements e2 in
              FStar_List.map (translate_expr env) uu____5395 in
            (Stack, uu____5392) in
          EBufCreateL uu____5385
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5401;
                  FStar_Extraction_ML_Syntax.loc = uu____5402;_},
                uu____5403);
             FStar_Extraction_ML_Syntax.mlty = uu____5404;
             FStar_Extraction_ML_Syntax.loc = uu____5405;_},
           uu____5406::e2::[])
          when
          let uu____5414 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5414 = "LowStar.Buffer.gcmalloc_of_list" ->
          let uu____5415 =
            let uu____5422 =
              let uu____5425 = list_elements e2 in
              FStar_List.map (translate_expr env) uu____5425 in
            (Eternal, uu____5422) in
          EBufCreateL uu____5415
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5431;
                  FStar_Extraction_ML_Syntax.loc = uu____5432;_},
                uu____5433);
             FStar_Extraction_ML_Syntax.mlty = uu____5434;
             FStar_Extraction_ML_Syntax.loc = uu____5435;_},
           _rid::init1::[])
          when
          let uu____5444 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5444 = "FStar.HyperStack.ST.ralloc" ->
          let uu____5445 =
            let uu____5452 = translate_expr env init1 in
            (Eternal, uu____5452, (EConstant (UInt32, "1"))) in
          EBufCreate uu____5445
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5454;
                  FStar_Extraction_ML_Syntax.loc = uu____5455;_},
                uu____5456);
             FStar_Extraction_ML_Syntax.mlty = uu____5457;
             FStar_Extraction_ML_Syntax.loc = uu____5458;_},
           _e0::e1::e2::[])
          when
          (let uu____5470 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5470 = "FStar.Buffer.rcreate") ||
            (let uu____5472 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5472 = "LowStar.Buffer.gcmalloc")
          ->
          let uu____5473 =
            let uu____5480 = translate_expr env e1 in
            let uu____5481 = translate_expr env e2 in
            (Eternal, uu____5480, uu____5481) in
          EBufCreate uu____5473
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5483;
                  FStar_Extraction_ML_Syntax.loc = uu____5484;_},
                uu____5485);
             FStar_Extraction_ML_Syntax.mlty = uu____5486;
             FStar_Extraction_ML_Syntax.loc = uu____5487;_},
           _rid::init1::[])
          when
          let uu____5496 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5496 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____5497 =
            let uu____5504 = translate_expr env init1 in
            (ManuallyManaged, uu____5504, (EConstant (UInt32, "1"))) in
          EBufCreate uu____5497
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5506;
                  FStar_Extraction_ML_Syntax.loc = uu____5507;_},
                uu____5508);
             FStar_Extraction_ML_Syntax.mlty = uu____5509;
             FStar_Extraction_ML_Syntax.loc = uu____5510;_},
           _e0::e1::e2::[])
          when
          (let uu____5522 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5522 = "FStar.Buffer.rcreate_mm") ||
            (let uu____5524 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5524 = "LowStar.Buffer.malloc")
          ->
          let uu____5525 =
            let uu____5532 = translate_expr env e1 in
            let uu____5533 = translate_expr env e2 in
            (ManuallyManaged, uu____5532, uu____5533) in
          EBufCreate uu____5525
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5535;
                  FStar_Extraction_ML_Syntax.loc = uu____5536;_},
                uu____5537);
             FStar_Extraction_ML_Syntax.mlty = uu____5538;
             FStar_Extraction_ML_Syntax.loc = uu____5539;_},
           e2::[])
          when
          let uu____5547 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5547 = "FStar.HyperStack.ST.rfree" ->
          let uu____5548 = translate_expr env e2 in EBufFree uu____5548
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5550;
                  FStar_Extraction_ML_Syntax.loc = uu____5551;_},
                uu____5552);
             FStar_Extraction_ML_Syntax.mlty = uu____5553;
             FStar_Extraction_ML_Syntax.loc = uu____5554;_},
           e2::[])
          when
          (let uu____5564 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5564 = "FStar.Buffer.rfree") ||
            (let uu____5566 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5566 = "LowStar.Buffer.free")
          -> let uu____5567 = translate_expr env e2 in EBufFree uu____5567
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5569;
                  FStar_Extraction_ML_Syntax.loc = uu____5570;_},
                uu____5571);
             FStar_Extraction_ML_Syntax.mlty = uu____5572;
             FStar_Extraction_ML_Syntax.loc = uu____5573;_},
           e1::e2::_e3::[])
          when
          (let uu____5585 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5585 = "FStar.Buffer.sub") ||
            (let uu____5587 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5587 = "LowStar.Buffer.sub")
          ->
          let uu____5588 =
            let uu____5593 = translate_expr env e1 in
            let uu____5594 = translate_expr env e2 in
            (uu____5593, uu____5594) in
          EBufSub uu____5588
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5596;
                  FStar_Extraction_ML_Syntax.loc = uu____5597;_},
                uu____5598);
             FStar_Extraction_ML_Syntax.mlty = uu____5599;
             FStar_Extraction_ML_Syntax.loc = uu____5600;_},
           e1::e2::[])
          when
          let uu____5609 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5609 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5611;
                  FStar_Extraction_ML_Syntax.loc = uu____5612;_},
                uu____5613);
             FStar_Extraction_ML_Syntax.mlty = uu____5614;
             FStar_Extraction_ML_Syntax.loc = uu____5615;_},
           e1::e2::[])
          when
          (let uu____5626 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5626 = "FStar.Buffer.offset") ||
            (let uu____5628 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5628 = "LowStar.Buffer.offset")
          ->
          let uu____5629 =
            let uu____5634 = translate_expr env e1 in
            let uu____5635 = translate_expr env e2 in
            (uu____5634, uu____5635) in
          EBufSub uu____5629
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5637;
                  FStar_Extraction_ML_Syntax.loc = uu____5638;_},
                uu____5639);
             FStar_Extraction_ML_Syntax.mlty = uu____5640;
             FStar_Extraction_ML_Syntax.loc = uu____5641;_},
           e1::e2::e3::[])
          when
          ((let uu____5653 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____5653 = "FStar.Buffer.upd") ||
             (let uu____5655 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____5655 = "FStar.Buffer.op_Array_Assignment"))
            ||
            (let uu____5657 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5657 = "LowStar.Buffer.upd'")
          ->
          let uu____5658 =
            let uu____5665 = translate_expr env e1 in
            let uu____5666 = translate_expr env e2 in
            let uu____5667 = translate_expr env e3 in
            (uu____5665, uu____5666, uu____5667) in
          EBufWrite uu____5658
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5669;
                  FStar_Extraction_ML_Syntax.loc = uu____5670;_},
                uu____5671);
             FStar_Extraction_ML_Syntax.mlty = uu____5672;
             FStar_Extraction_ML_Syntax.loc = uu____5673;_},
           e1::e2::[])
          when
          let uu____5682 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5682 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5683 =
            let uu____5690 = translate_expr env e1 in
            let uu____5691 = translate_expr env e2 in
            (uu____5690, (EConstant (UInt32, "0")), uu____5691) in
          EBufWrite uu____5683
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5693;
             FStar_Extraction_ML_Syntax.loc = uu____5694;_},
           uu____5695::[])
          when
          let uu____5698 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5698 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5700;
             FStar_Extraction_ML_Syntax.loc = uu____5701;_},
           uu____5702::[])
          when
          let uu____5705 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5705 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5707;
                  FStar_Extraction_ML_Syntax.loc = uu____5708;_},
                uu____5709);
             FStar_Extraction_ML_Syntax.mlty = uu____5710;
             FStar_Extraction_ML_Syntax.loc = uu____5711;_},
           e1::e2::e3::e4::e5::[])
          when
          (let uu____5725 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5725 = "FStar.Buffer.blit") ||
            (let uu____5727 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5727 = "LowStar.Buffer.blit")
          ->
          let uu____5728 =
            let uu____5739 = translate_expr env e1 in
            let uu____5740 = translate_expr env e2 in
            let uu____5741 = translate_expr env e3 in
            let uu____5742 = translate_expr env e4 in
            let uu____5743 = translate_expr env e5 in
            (uu____5739, uu____5740, uu____5741, uu____5742, uu____5743) in
          EBufBlit uu____5728
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5745;
                  FStar_Extraction_ML_Syntax.loc = uu____5746;_},
                uu____5747);
             FStar_Extraction_ML_Syntax.mlty = uu____5748;
             FStar_Extraction_ML_Syntax.loc = uu____5749;_},
           e1::e2::e3::[])
          when
          let uu____5759 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5759 = "FStar.Buffer.fill" ->
          let uu____5760 =
            let uu____5767 = translate_expr env e1 in
            let uu____5768 = translate_expr env e2 in
            let uu____5769 = translate_expr env e3 in
            (uu____5767, uu____5768, uu____5769) in
          EBufFill uu____5760
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5771;
             FStar_Extraction_ML_Syntax.loc = uu____5772;_},
           uu____5773::[])
          when
          let uu____5776 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5776 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5778;
             FStar_Extraction_ML_Syntax.loc = uu____5779;_},
           e1::[])
          when
          let uu____5783 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5783 = "Obj.repr" ->
          let uu____5784 =
            let uu____5789 = translate_expr env e1 in (uu____5789, TAny) in
          ECast uu____5784
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], op);
             FStar_Extraction_ML_Syntax.mlty = uu____5792;
             FStar_Extraction_ML_Syntax.loc = uu____5793;_},
           args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5801 = FStar_Util.must (mk_width m) in
          let uu____5802 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____5801 uu____5802 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[], op);
             FStar_Extraction_ML_Syntax.mlty = uu____5804;
             FStar_Extraction_ML_Syntax.loc = uu____5805;_},
           args)
          when is_bool_op op ->
          let uu____5813 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____5813 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[], "int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5815;
             FStar_Extraction_ML_Syntax.loc = uu____5816;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_Int
               (c, FStar_Pervasives_Native.None));
             FStar_Extraction_ML_Syntax.mlty = uu____5818;
             FStar_Extraction_ML_Syntax.loc = uu____5819;_}::[])
          when is_machine_int m ->
          let uu____5834 =
            let uu____5839 = FStar_Util.must (mk_width m) in (uu____5839, c) in
          EConstant uu____5834
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[], "uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5841;
             FStar_Extraction_ML_Syntax.loc = uu____5842;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_Int
               (c, FStar_Pervasives_Native.None));
             FStar_Extraction_ML_Syntax.mlty = uu____5844;
             FStar_Extraction_ML_Syntax.loc = uu____5845;_}::[])
          when is_machine_int m ->
          let uu____5860 =
            let uu____5865 = FStar_Util.must (mk_width m) in (uu____5865, c) in
          EConstant uu____5860
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[], "string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5866;
             FStar_Extraction_ML_Syntax.loc = uu____5867;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu____5869;
             FStar_Extraction_ML_Syntax.loc = uu____5870;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5876 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[], "of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5877;
             FStar_Extraction_ML_Syntax.loc = uu____5878;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu____5880;
             FStar_Extraction_ML_Syntax.loc = uu____5881;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5887 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[], c);
             FStar_Extraction_ML_Syntax.mlty = uu____5889;
             FStar_Extraction_ML_Syntax.loc = uu____5890;_},
           arg::[])
          ->
          let is_known_type =
            (((((((FStar_Util.starts_with c "uint8") ||
                    (FStar_Util.starts_with c "uint16"))
                   || (FStar_Util.starts_with c "uint32"))
                  || (FStar_Util.starts_with c "uint64"))
                 || (FStar_Util.starts_with c "int8"))
                || (FStar_Util.starts_with c "int16"))
               || (FStar_Util.starts_with c "int32"))
              || (FStar_Util.starts_with c "int64") in
          if (FStar_Util.ends_with c "uint64") && is_known_type
          then
            let uu____5897 =
              let uu____5902 = translate_expr env arg in
              (uu____5902, (TInt UInt64)) in
            ECast uu____5897
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5904 =
                 let uu____5909 = translate_expr env arg in
                 (uu____5909, (TInt UInt32)) in
               ECast uu____5904)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5911 =
                   let uu____5916 = translate_expr env arg in
                   (uu____5916, (TInt UInt16)) in
                 ECast uu____5911)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5918 =
                     let uu____5923 = translate_expr env arg in
                     (uu____5923, (TInt UInt8)) in
                   ECast uu____5918)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5925 =
                       let uu____5930 = translate_expr env arg in
                       (uu____5930, (TInt Int64)) in
                     ECast uu____5925)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5932 =
                         let uu____5937 = translate_expr env arg in
                         (uu____5937, (TInt Int32)) in
                       ECast uu____5932)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5939 =
                           let uu____5944 = translate_expr env arg in
                           (uu____5944, (TInt Int16)) in
                         ECast uu____5939)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5946 =
                             let uu____5951 = translate_expr env arg in
                             (uu____5951, (TInt Int8)) in
                           ECast uu____5946)
                        else
                          (let uu____5953 =
                             let uu____5960 =
                               let uu____5963 = translate_expr env arg in
                               [uu____5963] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5960) in
                           EApp uu____5953)
      | FStar_Extraction_ML_Syntax.MLE_App (head1, args) ->
          let uu____5974 =
            let uu____5981 = translate_expr env head1 in
            let uu____5982 = FStar_List.map (translate_expr env) args in
            (uu____5981, uu____5982) in
          EApp uu____5974
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1, ty_args) ->
          let uu____5993 =
            let uu____6000 = translate_expr env head1 in
            let uu____6001 = FStar_List.map (translate_type env) ty_args in
            (uu____6000, uu____6001) in
          ETypApp uu____5993
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t_from, t_to) ->
          let uu____6009 =
            let uu____6014 = translate_expr env e1 in
            let uu____6015 = translate_type env t_to in
            (uu____6014, uu____6015) in
          ECast uu____6009
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____6016, fields) ->
          let uu____6034 =
            let uu____6045 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____6046 =
              FStar_List.map
                (fun uu____6065 ->
                   match uu____6065 with
                   | (field, expr) ->
                       let uu____6076 = translate_expr env expr in
                       (field, uu____6076)) fields in
            (uu____6045, uu____6046) in
          EFlat uu____6034
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1, path) ->
          let uu____6085 =
            let uu____6092 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____6093 = translate_expr env e1 in
            (uu____6092, uu____6093, (FStar_Pervasives_Native.snd path)) in
          EField uu____6085
      | FStar_Extraction_ML_Syntax.MLE_Let uu____6096 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1, uu____6108) ->
          let uu____6113 =
            let uu____6114 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1 in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____6114 in
          failwith uu____6113
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____6120 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____6120
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____6126 = FStar_List.map (translate_expr env) es in
          ETuple uu____6126
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____6129, cons1), es) ->
          let uu____6140 =
            let uu____6149 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____6150 = FStar_List.map (translate_expr env) es in
            (uu____6149, cons1, uu____6150) in
          ECons uu____6140
      | FStar_Extraction_ML_Syntax.MLE_Fun (args, body) ->
          let binders = translate_binders env args in
          let env1 = add_binders env args in
          let uu____6173 =
            let uu____6182 = translate_expr env1 body in
            let uu____6183 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty in
            (binders, uu____6182, uu____6183) in
          EFun uu____6173
      | FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) ->
          let uu____6193 =
            let uu____6200 = translate_expr env e1 in
            let uu____6201 = translate_expr env e2 in
            let uu____6202 =
              match e3 with
              | FStar_Pervasives_Native.None -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31 in
            (uu____6200, uu____6201, uu____6202) in
          EIfThenElse uu____6193
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____6204 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____6211 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____6226 ->
          failwith "todo: translate_expr [MLE_Coerce]"
and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____6241 =
              let uu____6254 = FStar_List.map (translate_type env) ts in
              (lid, uu____6254) in
            TApp uu____6241
          else TQualified lid
      | uu____6266 -> failwith "invalid argument: assert_lid"
and (translate_branches :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern,
      FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option,
      FStar_Extraction_ML_Syntax.mlexpr) FStar_Pervasives_Native.tuple3
      Prims.list -> (pattern, expr) FStar_Pervasives_Native.tuple2 Prims.list)
  = fun env -> fun branches -> FStar_List.map (translate_branch env) branches
and (translate_branch :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern,
      FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option,
      FStar_Extraction_ML_Syntax.mlexpr) FStar_Pervasives_Native.tuple3 ->
      (pattern, expr) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun uu____6292 ->
      match uu____6292 with
      | (pat, guard, expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____6318 = translate_pat env pat in
            (match uu____6318 with
             | (env1, pat1) ->
                 let uu____6329 = translate_expr env1 expr in
                 (pat1, uu____6329))
          else failwith "todo: translate_branch"
and (translate_width :
  (FStar_Const.signedness, FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___281_6335 ->
    match uu___281_6335 with
    | FStar_Pervasives_Native.None -> CInt
    | FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int8) ->
        Int8
    | FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int16) ->
        Int16
    | FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int32) ->
        Int32
    | FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int64) ->
        Int64
    | FStar_Pervasives_Native.Some (FStar_Const.Unsigned, FStar_Const.Int8)
        -> UInt8
    | FStar_Pervasives_Native.Some (FStar_Const.Unsigned, FStar_Const.Int16)
        -> UInt16
    | FStar_Pervasives_Native.Some (FStar_Const.Unsigned, FStar_Const.Int32)
        -> UInt32
    | FStar_Pervasives_Native.Some (FStar_Const.Unsigned, FStar_Const.Int64)
        -> UInt64
and (translate_pat :
  env ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      (env, pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun p ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Unit) -> (env, PUnit)
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Bool b) -> (env, (PBool b))
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Int (s, sw)) ->
          let uu____6399 =
            let uu____6400 =
              let uu____6405 = translate_width sw in (uu____6405, s) in
            PConstant uu____6400 in
          (env, uu____6399)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild ->
          let env1 = extend env "_" in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____6409, cons1), ps) ->
          let uu____6420 =
            FStar_List.fold_left
              (fun uu____6440 ->
                 fun p1 ->
                   match uu____6440 with
                   | (env1, acc) ->
                       let uu____6460 = translate_pat env1 p1 in
                       (match uu____6460 with
                        | (env2, p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____6420 with
           | (env1, ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____6489, ps) ->
          let uu____6507 =
            FStar_List.fold_left
              (fun uu____6541 ->
                 fun uu____6542 ->
                   match (uu____6541, uu____6542) with
                   | ((env1, acc), (field, p1)) ->
                       let uu____6611 = translate_pat env1 p1 in
                       (match uu____6611 with
                        | (env2, p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps in
          (match uu____6507 with
           | (env1, ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____6673 =
            FStar_List.fold_left
              (fun uu____6693 ->
                 fun p1 ->
                   match uu____6693 with
                   | (env1, acc) ->
                       let uu____6713 = translate_pat env1 p1 in
                       (match uu____6713 with
                        | (env2, p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____6673 with
           | (env1, ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6740 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6745 ->
          failwith "todo: translate_pat [MLP_Branch]"
and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____6756 =
            let uu____6757 = FStar_String.list_of_string s in
            FStar_All.pipe_right uu____6757
              (FStar_Util.for_some
                 (fun c1 ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0")))) in
          if uu____6756
          then
            let uu____6769 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s in
            failwith uu____6769
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1 in
        let s = FStar_Util.string_of_int i in
        let c2 = EConstant (UInt32, s) in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int") in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s, FStar_Pervasives_Native.Some uu____6782) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6797 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6798 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.None) ->
        EConstant (CInt, s)
and (mk_op_app :
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr)
  =
  fun env ->
    fun w ->
      fun op ->
        fun args ->
          let uu____6819 =
            let uu____6826 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____6826) in
          EApp uu____6819