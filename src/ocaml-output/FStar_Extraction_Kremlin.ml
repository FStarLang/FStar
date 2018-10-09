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
    match projectee with | DGlobal _0 -> true | uu____696 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,Prims.int,typ,expr)
      FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____808 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr) FStar_Pervasives_Native.tuple7)
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____934 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,typ) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____1042 -> false
  
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
    match projectee with | DExternal _0 -> true | uu____1175 -> false
  
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
    match projectee with | DTypeVariant _0 -> true | uu____1293 -> false
  
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
    | uu____1435 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1478 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1489 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1500 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1511 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1522 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1533 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1544 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1555 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1568 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1590 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1603 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1627 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1651 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____1673 -> false
  
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1684 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1695 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1706 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1719 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1750 -> false
  
let (__proj__EQualified__item___0 :
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1799 -> false
  
let (__proj__EConstant__item___0 :
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1833 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1851 -> false
  
let (__proj__EApp__item___0 :
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1895 -> false
  
let (__proj__ETypApp__item___0 :
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1939 -> false
  
let (__proj__ELet__item___0 :
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1983 -> false
  
let (__proj__EIfThenElse__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____2023 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____2053 -> false
  
let (__proj__EAssign__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____2091 -> false
  
let (__proj__EBufCreate__item___0 :
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____2133 -> false
  
let (__proj__EBufRead__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____2171 -> false
  
let (__proj__EBufWrite__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____2213 -> false
  
let (__proj__EBufSub__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____2255 -> false
  
let (__proj__EBufBlit__item___0 :
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5) =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____2315 -> false
  
let (__proj__EMatch__item___0 :
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____2369 -> false
  
let (__proj__EOp__item___0 :
  expr -> (op,width) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____2405 -> false
  
let (__proj__ECast__item___0 :
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____2436 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____2447 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____2460 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____2482 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____2493 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____2505 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____2536 -> false
  
let (__proj__EFlat__item___0 :
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____2596 -> false
  
let (__proj__EField__item___0 :
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____2641 -> false
  
let (__proj__EWhile__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____2679 -> false
  
let (__proj__EBufCreateL__item___0 :
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2719 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2754 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2807 -> false
  
let (__proj__EBufFill__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2846 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2877 -> false
  
let (__proj__EFun__item___0 :
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2922 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____2945 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____2969 -> false
  
let (__proj__EBufCreateNoInit__item___0 :
  expr -> (lifetime,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____3000 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____3011 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____3022 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____3033 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____3044 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____3055 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____3066 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____3077 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____3088 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____3099 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____3110 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____3121 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____3132 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____3143 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____3154 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____3165 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____3176 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____3187 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____3198 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____3209 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____3220 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____3231 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____3242 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____3253 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____3264 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____3275 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____3288 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____3311 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____3338 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____3381 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____3414 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list)
  = fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____3460 -> false
  
let (__proj__PConstant__item___0 :
  pattern -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____3494 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____3505 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____3516 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____3527 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____3538 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____3549 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____3560 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____3571 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____3582 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____3593 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____3642 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____3662 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____3681 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____3701 -> false
  
let (__proj__TQualified__item___0 :
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____3744 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____3755 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____3771 -> false
  
let (__proj__TArrow__item___0 :
  typ -> (typ,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____3804 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____3841 -> false
  
let (__proj__TApp__item___0 :
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____3905 -> false
  
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
  'Auu____4008 'Auu____4009 'Auu____4010 .
    ('Auu____4008,'Auu____4009,'Auu____4010) FStar_Pervasives_Native.tuple3
      -> 'Auu____4008
  = fun uu____4021  -> match uu____4021 with | (x,uu____4029,uu____4030) -> x 
let snd3 :
  'Auu____4040 'Auu____4041 'Auu____4042 .
    ('Auu____4040,'Auu____4041,'Auu____4042) FStar_Pervasives_Native.tuple3
      -> 'Auu____4041
  = fun uu____4053  -> match uu____4053 with | (uu____4060,x,uu____4062) -> x 
let thd3 :
  'Auu____4072 'Auu____4073 'Auu____4074 .
    ('Auu____4072,'Auu____4073,'Auu____4074) FStar_Pervasives_Native.tuple3
      -> 'Auu____4074
  = fun uu____4085  -> match uu____4085 with | (uu____4092,uu____4093,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___282_4103  ->
    match uu___282_4103 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____4115 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___283_4125  ->
    match uu___283_4125 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____4134 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___284_4155  ->
    match uu___284_4155 with
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
    | uu____4200 -> FStar_Pervasives_Native.None
  
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
    match projectee with | { names; names_t; module_name;_} -> names
  
let (__proj__Mkenv__item__names_t : env -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with | { names; names_t; module_name;_} -> names_t
  
let (__proj__Mkenv__item__module_name : env -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with | { names; names_t; module_name;_} -> module_name
  
let (__proj__Mkname__item__pretty : name -> Prims.string) =
  fun projectee  -> match projectee with | { pretty = pretty1;_} -> pretty1 
let (empty : Prims.string Prims.list -> env) =
  fun module_name  -> { names = []; names_t = []; module_name } 
let (extend : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___290_4356 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___290_4356.names_t);
        module_name = (uu___290_4356.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___291_4370 = env  in
      {
        names = (uu___291_4370.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___291_4370.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____4385 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____4385 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___293_4409  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___292_4416 ->
          let uu____4418 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4418
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___295_4438  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___294_4447 ->
          let uu____4449 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4449
  
let add_binders :
  'Auu____4460 .
    env ->
      (Prims.string,'Auu____4460) FStar_Pervasives_Native.tuple2 Prims.list
        -> env
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____4495  ->
             match uu____4495 with | (name,uu____4502) -> extend env1 name)
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
      | uu____4554 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____4773  ->
    match uu____4773 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____4822 = m  in
               match uu____4822 with
               | (path,uu____4837,uu____4838) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___297_4856  ->
                  match () with
                  | () ->
                      (FStar_Util.print1
                         "Attempting to translate module %s\n" m_name;
                       (let uu____4861 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____4861))) ()
             with
             | e ->
                 ((let uu____4870 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____4870);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath,(FStar_Extraction_ML_Syntax.mlsig,
                                       FStar_Extraction_ML_Syntax.mlmodule)
                                       FStar_Pervasives_Native.tuple2
                                       FStar_Pervasives_Native.option,
    FStar_Extraction_ML_Syntax.mllib) FStar_Pervasives_Native.tuple3 -> 
    file)
  =
  fun uu____4873  ->
    match uu____4873 with
    | (module_name,modul,uu____4888) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____4923 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags1  ->
    FStar_List.choose
      (fun uu___285_4937  ->
         match uu___285_4937 with
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
         | uu____4948 -> FStar_Pervasives_Native.None) flags1

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags1  ->
    let uu____4952 =
      FStar_List.choose
        (fun uu___286_4959  ->
           match uu___286_4959 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____4966 -> FStar_Pervasives_Native.None) flags1
       in
    match uu____4952 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____4979 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____4993 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____4995 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____5000) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5027;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____5030;
                FStar_Extraction_ML_Syntax.loc = uu____5031;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5033;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___287_5059  ->
                      match uu___287_5059 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____5062 -> false) meta
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
               let rec find_return_type eff i uu___288_5098 =
                 match uu___288_5098 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5107,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____5127 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____5127 with
               | (i,eff,t) ->
                   (if i > (Prims.parse_int "0")
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____5153 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____5153 msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5171) ->
                           let uu____5172 = translate_flags meta  in
                           MustDisappear :: uu____5172
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____5175 = translate_flags meta  in
                           MustDisappear :: uu____5175
                       | uu____5178 -> translate_flags meta  in
                     if assumed
                     then
                       (if (FStar_List.length tvars) = (Prims.parse_int "0")
                        then
                          let uu____5192 =
                            let uu____5193 =
                              let uu____5214 = translate_type env3 t0  in
                              (cc, meta1, name1, uu____5214)  in
                            DExternal uu____5193  in
                          FStar_Pervasives_Native.Some uu____5192
                        else
                          ((let uu____5230 =
                              FStar_Extraction_ML_Syntax.string_of_mlpath
                                name1
                               in
                            FStar_Util.print1_warning
                              "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                              uu____5230);
                           FStar_Pervasives_Native.None))
                     else
                       (try
                          (fun uu___299_5239  ->
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
                            ((let uu____5271 =
                                let uu____5277 =
                                  let uu____5279 =
                                    FStar_Extraction_ML_Syntax.string_of_mlpath
                                      name1
                                     in
                                  FStar_Util.format2
                                    "Error while extracting %s to KreMLin (%s)\n"
                                    uu____5279 msg
                                   in
                                (FStar_Errors.Warning_FunctionNotExtacted,
                                  uu____5277)
                                 in
                              FStar_Errors.log_issue FStar_Range.dummyRange
                                uu____5271);
                             (let msg1 =
                                Prims.strcat
                                  "This function was not extracted:\n" msg
                                 in
                              FStar_Pervasives_Native.Some
                                (DFunction
                                   (cc, meta1, (FStar_List.length tvars), t1,
                                     name1, binders, (EAbortS msg1)))))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5305;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Coerce
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____5308;
                     FStar_Extraction_ML_Syntax.loc = uu____5309;_},uu____5310,uu____5311);
                FStar_Extraction_ML_Syntax.mlty = uu____5312;
                FStar_Extraction_ML_Syntax.loc = uu____5313;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5315;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___287_5341  ->
                      match uu___287_5341 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____5344 -> false) meta
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
               let rec find_return_type eff i uu___288_5380 =
                 match uu___288_5380 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5389,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____5409 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____5409 with
               | (i,eff,t) ->
                   (if i > (Prims.parse_int "0")
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____5435 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____5435 msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5453) ->
                           let uu____5454 = translate_flags meta  in
                           MustDisappear :: uu____5454
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____5457 = translate_flags meta  in
                           MustDisappear :: uu____5457
                       | uu____5460 -> translate_flags meta  in
                     if assumed
                     then
                       (if (FStar_List.length tvars) = (Prims.parse_int "0")
                        then
                          let uu____5474 =
                            let uu____5475 =
                              let uu____5496 = translate_type env3 t0  in
                              (cc, meta1, name1, uu____5496)  in
                            DExternal uu____5475  in
                          FStar_Pervasives_Native.Some uu____5474
                        else
                          ((let uu____5512 =
                              FStar_Extraction_ML_Syntax.string_of_mlpath
                                name1
                               in
                            FStar_Util.print1_warning
                              "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                              uu____5512);
                           FStar_Pervasives_Native.None))
                     else
                       (try
                          (fun uu___299_5521  ->
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
                            ((let uu____5553 =
                                let uu____5559 =
                                  let uu____5561 =
                                    FStar_Extraction_ML_Syntax.string_of_mlpath
                                      name1
                                     in
                                  FStar_Util.format2
                                    "Error while extracting %s to KreMLin (%s)\n"
                                    uu____5561 msg
                                   in
                                (FStar_Errors.Warning_FunctionNotExtacted,
                                  uu____5559)
                                 in
                              FStar_Errors.log_issue FStar_Range.dummyRange
                                uu____5553);
                             (let msg1 =
                                Prims.strcat
                                  "This function was not extracted:\n" msg
                                 in
                              FStar_Pervasives_Native.Some
                                (DFunction
                                   (cc, meta1, (FStar_List.length tvars), t1,
                                     name1, binders, (EAbortS msg1)))))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5587;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5590;_} ->
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
                 (fun uu___301_5627  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____5651 =
                       let uu____5657 =
                         let uu____5659 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____5661 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____5659
                           uu____5661
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____5657)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____5651);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5679;
            FStar_Extraction_ML_Syntax.mllb_def = uu____5680;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____5681;
            FStar_Extraction_ML_Syntax.print_typ = uu____5682;_} ->
            ((let uu____5689 =
                let uu____5695 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____5695)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____5689);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____5702 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____5702
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____5716 = ty  in
      match uu____5716 with
      | (uu____5719,uu____5720,uu____5721,uu____5722,flags1,uu____5724) ->
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
                     (let uu____5798 =
                        let uu____5799 =
                          let uu____5819 = translate_flags flags2  in
                          let uu____5822 = translate_type env1 t  in
                          (name1, uu____5819, (FStar_List.length args),
                            uu____5822)
                           in
                        DTypeAlias uu____5799  in
                      FStar_Pervasives_Native.Some uu____5798)
             | (uu____5835,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____5880 =
                   let uu____5881 =
                     let uu____5913 = translate_flags flags2  in
                     let uu____5916 =
                       FStar_List.map
                         (fun uu____5948  ->
                            match uu____5948 with
                            | (f,t) ->
                                let uu____5968 =
                                  let uu____5974 = translate_type env1 t  in
                                  (uu____5974, false)  in
                                (f, uu____5968)) fields
                        in
                     (name1, uu____5913, (FStar_List.length args),
                       uu____5916)
                      in
                   DTypeFlat uu____5881  in
                 FStar_Pervasives_Native.Some uu____5880
             | (uu____6007,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags3 = translate_flags flags2  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____6057 =
                   let uu____6058 =
                     let uu____6097 =
                       FStar_List.map
                         (fun uu____6150  ->
                            match uu____6150 with
                            | (cons1,ts) ->
                                let uu____6198 =
                                  FStar_List.map
                                    (fun uu____6230  ->
                                       match uu____6230 with
                                       | (name2,t) ->
                                           let uu____6250 =
                                             let uu____6256 =
                                               translate_type env1 t  in
                                             (uu____6256, false)  in
                                           (name2, uu____6250)) ts
                                   in
                                (cons1, uu____6198)) branches
                        in
                     (name1, flags3, (FStar_List.length args), uu____6097)
                      in
                   DTypeVariant uu____6058  in
                 FStar_Pervasives_Native.Some uu____6057
             | (uu____6309,name,_mangled_name,uu____6312,uu____6313,uu____6314)
                 ->
                 ((let uu____6330 =
                     let uu____6336 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____6336)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____6330);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____6344 = find_t env name  in TBound uu____6344
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____6347,t2) ->
          let uu____6349 =
            let uu____6354 = translate_type env t1  in
            let uu____6355 = translate_type env t2  in
            (uu____6354, uu____6355)  in
          TArrow uu____6349
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6359 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6359 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6366 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6366 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____6383 = FStar_Util.must (mk_width m)  in TInt uu____6383
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____6397 = FStar_Util.must (mk_width m)  in TInt uu____6397
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6402 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6402 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____6406::arg::uu____6408::[],p) when
          (((let uu____6414 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6414 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____6419 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6419 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____6424 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6424 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____6429 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6429 = "FStar.HyperStack.ST.s_mref")
          -> let uu____6433 = translate_type env arg  in TBuf uu____6433
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____6435::[],p) when
          ((((((((((let uu____6441 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6441 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____6446 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6446 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____6451 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6451 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____6456 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6456 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____6461 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6461 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____6466 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6466 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____6471 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6471 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____6476 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6476 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____6481 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6481 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____6486 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6486 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____6491 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6491 = "FStar.HyperStack.ST.mmmref")
          -> let uu____6495 = translate_type env arg  in TBuf uu____6495
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____6497::uu____6498::[],p) when
          let uu____6502 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6502 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____6506 = translate_type env arg  in TBuf uu____6506
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____6513 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6513 = "FStar.Buffer.buffer") ||
                        (let uu____6518 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____6518 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____6523 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____6523 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____6528 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6528 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____6533 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6533 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____6538 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6538 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____6543 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6543 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____6548 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6548 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____6553 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6553 = "FStar.HyperStack.mmref"))
                ||
                (let uu____6558 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6558 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____6563 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6563 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____6568 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6568 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____6573 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6573 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____6578 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6578 = "FStar.HyperStack.ST.mmref")
          -> let uu____6582 = translate_type env arg  in TBuf uu____6582
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6583::arg::[],p) when
          (let uu____6590 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6590 = "FStar.HyperStack.s_ref") ||
            (let uu____6595 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6595 = "FStar.HyperStack.ST.s_ref")
          -> let uu____6599 = translate_type env arg  in TBuf uu____6599
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6600::[],p) when
          let uu____6604 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6604 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____6656 = FStar_List.map (translate_type env) args  in
          TTuple uu____6656
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____6667 =
              let uu____6682 = FStar_List.map (translate_type env) args  in
              (lid, uu____6682)  in
            TApp uu____6667
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____6700 = FStar_List.map (translate_type env) ts  in
          TTuple uu____6700

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
    fun uu____6718  ->
      match uu____6718 with
      | (name,typ) ->
          let uu____6728 = translate_type env typ  in
          { name; typ = uu____6728; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____6735 = find env name  in EBound uu____6735
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____6749 =
            let uu____6754 = FStar_Util.must (mk_op op)  in
            let uu____6755 = FStar_Util.must (mk_width m)  in
            (uu____6754, uu____6755)  in
          EOp uu____6749
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____6765 =
            let uu____6770 = FStar_Util.must (mk_bool_op op)  in
            (uu____6770, Bool)  in
          EOp uu____6765
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
            let uu____6793 = translate_type env typ  in
            { name; typ = uu____6793; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____6820 =
            let uu____6831 = translate_expr env expr  in
            let uu____6832 = translate_branches env branches  in
            (uu____6831, uu____6832)  in
          EMatch uu____6820
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6846;
                  FStar_Extraction_ML_Syntax.loc = uu____6847;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6849;
             FStar_Extraction_ML_Syntax.loc = uu____6850;_},arg::[])
          when
          let uu____6856 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6856 = "FStar.Dyn.undyn" ->
          let uu____6860 =
            let uu____6865 = translate_expr env arg  in
            let uu____6866 = translate_type env t  in
            (uu____6865, uu____6866)  in
          ECast uu____6860
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6868;
                  FStar_Extraction_ML_Syntax.loc = uu____6869;_},uu____6870);
             FStar_Extraction_ML_Syntax.mlty = uu____6871;
             FStar_Extraction_ML_Syntax.loc = uu____6872;_},uu____6873)
          when
          let uu____6882 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6882 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6887;
                  FStar_Extraction_ML_Syntax.loc = uu____6888;_},uu____6889);
             FStar_Extraction_ML_Syntax.mlty = uu____6890;
             FStar_Extraction_ML_Syntax.loc = uu____6891;_},arg::[])
          when
          ((let uu____6901 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6901 = "FStar.HyperStack.All.failwith") ||
             (let uu____6906 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6906 = "FStar.Error.unexpected"))
            ||
            (let uu____6911 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6911 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____6916;
               FStar_Extraction_ML_Syntax.loc = uu____6917;_} -> EAbortS msg
           | uu____6919 ->
               let print7 =
                 let uu____6921 =
                   let uu____6922 =
                     let uu____6923 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____6923
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____6922  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____6921
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
                  FStar_Extraction_ML_Syntax.mlty = uu____6930;
                  FStar_Extraction_ML_Syntax.loc = uu____6931;_},uu____6932);
             FStar_Extraction_ML_Syntax.mlty = uu____6933;
             FStar_Extraction_ML_Syntax.loc = uu____6934;_},e1::[])
          when
          (let uu____6944 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6944 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____6949 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6949 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6954;
                  FStar_Extraction_ML_Syntax.loc = uu____6955;_},uu____6956);
             FStar_Extraction_ML_Syntax.mlty = uu____6957;
             FStar_Extraction_ML_Syntax.loc = uu____6958;_},e1::e2::[])
          when
          (((let uu____6969 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6969 = "FStar.Buffer.index") ||
              (let uu____6974 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6974 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____6979 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6979 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____6984 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6984 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____6988 =
            let uu____6993 = translate_expr env e1  in
            let uu____6994 = translate_expr env e2  in
            (uu____6993, uu____6994)  in
          EBufRead uu____6988
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6996;
                  FStar_Extraction_ML_Syntax.loc = uu____6997;_},uu____6998);
             FStar_Extraction_ML_Syntax.mlty = uu____6999;
             FStar_Extraction_ML_Syntax.loc = uu____7000;_},e1::[])
          when
          let uu____7008 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7008 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____7012 =
            let uu____7017 = translate_expr env e1  in
            (uu____7017, (EConstant (UInt32, "0")))  in
          EBufRead uu____7012
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7021;
                  FStar_Extraction_ML_Syntax.loc = uu____7022;_},uu____7023);
             FStar_Extraction_ML_Syntax.mlty = uu____7024;
             FStar_Extraction_ML_Syntax.loc = uu____7025;_},e1::e2::[])
          when
          ((let uu____7036 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7036 = "FStar.Buffer.create") ||
             (let uu____7041 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7041 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____7046 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7046 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____7050 =
            let uu____7057 = translate_expr env e1  in
            let uu____7058 = translate_expr env e2  in
            (Stack, uu____7057, uu____7058)  in
          EBufCreate uu____7050
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7060;
                  FStar_Extraction_ML_Syntax.loc = uu____7061;_},uu____7062);
             FStar_Extraction_ML_Syntax.mlty = uu____7063;
             FStar_Extraction_ML_Syntax.loc = uu____7064;_},elen::[])
          when
          let uu____7072 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7072 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____7076 =
            let uu____7081 = translate_expr env elen  in (Stack, uu____7081)
             in
          EBufCreateNoInit uu____7076
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7083;
                  FStar_Extraction_ML_Syntax.loc = uu____7084;_},uu____7085);
             FStar_Extraction_ML_Syntax.mlty = uu____7086;
             FStar_Extraction_ML_Syntax.loc = uu____7087;_},init1::[])
          when
          let uu____7095 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7095 = "FStar.HyperStack.ST.salloc" ->
          let uu____7099 =
            let uu____7106 = translate_expr env init1  in
            (Stack, uu____7106, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7099
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7110;
                  FStar_Extraction_ML_Syntax.loc = uu____7111;_},uu____7112);
             FStar_Extraction_ML_Syntax.mlty = uu____7113;
             FStar_Extraction_ML_Syntax.loc = uu____7114;_},e2::[])
          when
          ((let uu____7124 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7124 = "FStar.Buffer.createL") ||
             (let uu____7129 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7129 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____7134 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7134 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____7138 =
            let uu____7145 =
              let uu____7148 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7148  in
            (Stack, uu____7145)  in
          EBufCreateL uu____7138
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7154;
                  FStar_Extraction_ML_Syntax.loc = uu____7155;_},uu____7156);
             FStar_Extraction_ML_Syntax.mlty = uu____7157;
             FStar_Extraction_ML_Syntax.loc = uu____7158;_},_erid::e2::[])
          when
          (let uu____7169 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7169 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____7174 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7174 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____7178 =
            let uu____7185 =
              let uu____7188 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7188  in
            (Eternal, uu____7185)  in
          EBufCreateL uu____7178
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7194;
                  FStar_Extraction_ML_Syntax.loc = uu____7195;_},uu____7196);
             FStar_Extraction_ML_Syntax.mlty = uu____7197;
             FStar_Extraction_ML_Syntax.loc = uu____7198;_},_rid::init1::[])
          when
          let uu____7207 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7207 = "FStar.HyperStack.ST.ralloc" ->
          let uu____7211 =
            let uu____7218 = translate_expr env init1  in
            (Eternal, uu____7218, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7211
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7222;
                  FStar_Extraction_ML_Syntax.loc = uu____7223;_},uu____7224);
             FStar_Extraction_ML_Syntax.mlty = uu____7225;
             FStar_Extraction_ML_Syntax.loc = uu____7226;_},_e0::e1::e2::[])
          when
          ((let uu____7238 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7238 = "FStar.Buffer.rcreate") ||
             (let uu____7243 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7243 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____7248 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7248 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____7252 =
            let uu____7259 = translate_expr env e1  in
            let uu____7260 = translate_expr env e2  in
            (Eternal, uu____7259, uu____7260)  in
          EBufCreate uu____7252
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7262;
                  FStar_Extraction_ML_Syntax.loc = uu____7263;_},uu____7264);
             FStar_Extraction_ML_Syntax.mlty = uu____7265;
             FStar_Extraction_ML_Syntax.loc = uu____7266;_},_erid::elen::[])
          when
          let uu____7275 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7275 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____7279 =
            let uu____7284 = translate_expr env elen  in
            (Eternal, uu____7284)  in
          EBufCreateNoInit uu____7279
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7286;
                  FStar_Extraction_ML_Syntax.loc = uu____7287;_},uu____7288);
             FStar_Extraction_ML_Syntax.mlty = uu____7289;
             FStar_Extraction_ML_Syntax.loc = uu____7290;_},_rid::init1::[])
          when
          let uu____7299 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7299 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____7303 =
            let uu____7310 = translate_expr env init1  in
            (ManuallyManaged, uu____7310, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7303
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7314;
                  FStar_Extraction_ML_Syntax.loc = uu____7315;_},uu____7316);
             FStar_Extraction_ML_Syntax.mlty = uu____7317;
             FStar_Extraction_ML_Syntax.loc = uu____7318;_},_e0::e1::e2::[])
          when
          (((let uu____7330 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7330 = "FStar.Buffer.rcreate_mm") ||
              (let uu____7335 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7335 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____7340 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7340 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____7345 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7345 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____7349 =
            let uu____7356 = translate_expr env e1  in
            let uu____7357 = translate_expr env e2  in
            (ManuallyManaged, uu____7356, uu____7357)  in
          EBufCreate uu____7349
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7359;
                  FStar_Extraction_ML_Syntax.loc = uu____7360;_},uu____7361);
             FStar_Extraction_ML_Syntax.mlty = uu____7362;
             FStar_Extraction_ML_Syntax.loc = uu____7363;_},_erid::elen::[])
          when
          let uu____7372 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7372 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____7376 =
            let uu____7381 = translate_expr env elen  in
            (ManuallyManaged, uu____7381)  in
          EBufCreateNoInit uu____7376
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7383;
                  FStar_Extraction_ML_Syntax.loc = uu____7384;_},uu____7385);
             FStar_Extraction_ML_Syntax.mlty = uu____7386;
             FStar_Extraction_ML_Syntax.loc = uu____7387;_},e2::[])
          when
          let uu____7395 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7395 = "FStar.HyperStack.ST.rfree" ->
          let uu____7399 = translate_expr env e2  in EBufFree uu____7399
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7401;
                  FStar_Extraction_ML_Syntax.loc = uu____7402;_},uu____7403);
             FStar_Extraction_ML_Syntax.mlty = uu____7404;
             FStar_Extraction_ML_Syntax.loc = uu____7405;_},e2::[])
          when
          (let uu____7415 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7415 = "FStar.Buffer.rfree") ||
            (let uu____7420 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7420 = "LowStar.Monotonic.Buffer.free")
          -> let uu____7424 = translate_expr env e2  in EBufFree uu____7424
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7426;
                  FStar_Extraction_ML_Syntax.loc = uu____7427;_},uu____7428);
             FStar_Extraction_ML_Syntax.mlty = uu____7429;
             FStar_Extraction_ML_Syntax.loc = uu____7430;_},e1::e2::_e3::[])
          when
          let uu____7440 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7440 = "FStar.Buffer.sub" ->
          let uu____7444 =
            let uu____7449 = translate_expr env e1  in
            let uu____7450 = translate_expr env e2  in
            (uu____7449, uu____7450)  in
          EBufSub uu____7444
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7452;
                  FStar_Extraction_ML_Syntax.loc = uu____7453;_},uu____7454);
             FStar_Extraction_ML_Syntax.mlty = uu____7455;
             FStar_Extraction_ML_Syntax.loc = uu____7456;_},e1::e2::_e3::[])
          when
          let uu____7466 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7466 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____7470 =
            let uu____7475 = translate_expr env e1  in
            let uu____7476 = translate_expr env e2  in
            (uu____7475, uu____7476)  in
          EBufSub uu____7470
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7478;
                  FStar_Extraction_ML_Syntax.loc = uu____7479;_},uu____7480);
             FStar_Extraction_ML_Syntax.mlty = uu____7481;
             FStar_Extraction_ML_Syntax.loc = uu____7482;_},e1::e2::[])
          when
          let uu____7491 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7491 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7496;
                  FStar_Extraction_ML_Syntax.loc = uu____7497;_},uu____7498);
             FStar_Extraction_ML_Syntax.mlty = uu____7499;
             FStar_Extraction_ML_Syntax.loc = uu____7500;_},e1::e2::[])
          when
          let uu____7509 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7509 = "FStar.Buffer.offset" ->
          let uu____7513 =
            let uu____7518 = translate_expr env e1  in
            let uu____7519 = translate_expr env e2  in
            (uu____7518, uu____7519)  in
          EBufSub uu____7513
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7521;
                  FStar_Extraction_ML_Syntax.loc = uu____7522;_},uu____7523);
             FStar_Extraction_ML_Syntax.mlty = uu____7524;
             FStar_Extraction_ML_Syntax.loc = uu____7525;_},e1::e2::[])
          when
          let uu____7534 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7534 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____7538 =
            let uu____7543 = translate_expr env e1  in
            let uu____7544 = translate_expr env e2  in
            (uu____7543, uu____7544)  in
          EBufSub uu____7538
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7546;
                  FStar_Extraction_ML_Syntax.loc = uu____7547;_},uu____7548);
             FStar_Extraction_ML_Syntax.mlty = uu____7549;
             FStar_Extraction_ML_Syntax.loc = uu____7550;_},e1::e2::e3::[])
          when
          (((let uu____7562 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7562 = "FStar.Buffer.upd") ||
              (let uu____7567 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7567 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____7572 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7572 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____7577 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7577 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____7581 =
            let uu____7588 = translate_expr env e1  in
            let uu____7589 = translate_expr env e2  in
            let uu____7590 = translate_expr env e3  in
            (uu____7588, uu____7589, uu____7590)  in
          EBufWrite uu____7581
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7592;
                  FStar_Extraction_ML_Syntax.loc = uu____7593;_},uu____7594);
             FStar_Extraction_ML_Syntax.mlty = uu____7595;
             FStar_Extraction_ML_Syntax.loc = uu____7596;_},e1::e2::[])
          when
          let uu____7605 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7605 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____7609 =
            let uu____7616 = translate_expr env e1  in
            let uu____7617 = translate_expr env e2  in
            (uu____7616, (EConstant (UInt32, "0")), uu____7617)  in
          EBufWrite uu____7609
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7621;
             FStar_Extraction_ML_Syntax.loc = uu____7622;_},uu____7623::[])
          when
          let uu____7626 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7626 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7631;
             FStar_Extraction_ML_Syntax.loc = uu____7632;_},uu____7633::[])
          when
          let uu____7636 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7636 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7641;
                  FStar_Extraction_ML_Syntax.loc = uu____7642;_},uu____7643);
             FStar_Extraction_ML_Syntax.mlty = uu____7644;
             FStar_Extraction_ML_Syntax.loc = uu____7645;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____7659 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7659 = "FStar.Buffer.blit") ||
             (let uu____7664 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7664 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____7669 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7669 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____7673 =
            let uu____7684 = translate_expr env e1  in
            let uu____7685 = translate_expr env e2  in
            let uu____7686 = translate_expr env e3  in
            let uu____7687 = translate_expr env e4  in
            let uu____7688 = translate_expr env e5  in
            (uu____7684, uu____7685, uu____7686, uu____7687, uu____7688)  in
          EBufBlit uu____7673
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7690;
                  FStar_Extraction_ML_Syntax.loc = uu____7691;_},uu____7692);
             FStar_Extraction_ML_Syntax.mlty = uu____7693;
             FStar_Extraction_ML_Syntax.loc = uu____7694;_},e1::e2::e3::[])
          when
          let uu____7704 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7704 = "FStar.Buffer.fill" ->
          let uu____7708 =
            let uu____7715 = translate_expr env e1  in
            let uu____7716 = translate_expr env e2  in
            let uu____7717 = translate_expr env e3  in
            (uu____7715, uu____7716, uu____7717)  in
          EBufFill uu____7708
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7719;
             FStar_Extraction_ML_Syntax.loc = uu____7720;_},uu____7721::[])
          when
          let uu____7724 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7724 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7729;
                  FStar_Extraction_ML_Syntax.loc = uu____7730;_},uu____7731);
             FStar_Extraction_ML_Syntax.mlty = uu____7732;
             FStar_Extraction_ML_Syntax.loc = uu____7733;_},_ebuf::_eseq::[])
          when
          (((let uu____7744 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7744 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____7749 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7749 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____7754 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7754 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____7759 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7759 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7764;
             FStar_Extraction_ML_Syntax.loc = uu____7765;_},e1::[])
          when
          let uu____7769 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7769 = "Obj.repr" ->
          let uu____7773 =
            let uu____7778 = translate_expr env e1  in (uu____7778, TAny)  in
          ECast uu____7773
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7781;
             FStar_Extraction_ML_Syntax.loc = uu____7782;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____7798 = FStar_Util.must (mk_width m)  in
          let uu____7799 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____7798 uu____7799 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7801;
             FStar_Extraction_ML_Syntax.loc = uu____7802;_},args)
          when is_bool_op op ->
          let uu____7816 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____7816 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7818;
             FStar_Extraction_ML_Syntax.loc = uu____7819;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7821;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7822;_}::[])
          when is_machine_int m ->
          let uu____7847 =
            let uu____7853 = FStar_Util.must (mk_width m)  in (uu____7853, c)
             in
          EConstant uu____7847
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7856;
             FStar_Extraction_ML_Syntax.loc = uu____7857;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7859;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7860;_}::[])
          when is_machine_int m ->
          let uu____7885 =
            let uu____7891 = FStar_Util.must (mk_width m)  in (uu____7891, c)
             in
          EConstant uu____7885
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7893;
             FStar_Extraction_ML_Syntax.loc = uu____7894;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7896;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7897;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7910 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7912;
             FStar_Extraction_ML_Syntax.loc = uu____7913;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7915;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7916;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7931 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____7934;
             FStar_Extraction_ML_Syntax.loc = uu____7935;_},arg::[])
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
            let uu____7963 =
              let uu____7968 = translate_expr env arg  in
              (uu____7968, (TInt UInt64))  in
            ECast uu____7963
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____7973 =
                 let uu____7978 = translate_expr env arg  in
                 (uu____7978, (TInt UInt32))  in
               ECast uu____7973)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____7983 =
                   let uu____7988 = translate_expr env arg  in
                   (uu____7988, (TInt UInt16))  in
                 ECast uu____7983)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____7993 =
                     let uu____7998 = translate_expr env arg  in
                     (uu____7998, (TInt UInt8))  in
                   ECast uu____7993)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____8003 =
                       let uu____8008 = translate_expr env arg  in
                       (uu____8008, (TInt Int64))  in
                     ECast uu____8003)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____8013 =
                         let uu____8018 = translate_expr env arg  in
                         (uu____8018, (TInt Int32))  in
                       ECast uu____8013)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____8023 =
                           let uu____8028 = translate_expr env arg  in
                           (uu____8028, (TInt Int16))  in
                         ECast uu____8023)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____8033 =
                             let uu____8038 = translate_expr env arg  in
                             (uu____8038, (TInt Int8))  in
                           ECast uu____8033)
                        else
                          (let uu____8041 =
                             let uu____8048 =
                               let uu____8051 = translate_expr env arg  in
                               [uu____8051]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____8048)
                              in
                           EApp uu____8041)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____8071 =
            let uu____8078 = translate_expr env head1  in
            let uu____8079 = FStar_List.map (translate_expr env) args  in
            (uu____8078, uu____8079)  in
          EApp uu____8071
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____8090 =
            let uu____8097 = translate_expr env head1  in
            let uu____8098 = FStar_List.map (translate_type env) ty_args  in
            (uu____8097, uu____8098)  in
          ETypApp uu____8090
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____8106 =
            let uu____8111 = translate_expr env e1  in
            let uu____8112 = translate_type env t_to  in
            (uu____8111, uu____8112)  in
          ECast uu____8106
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____8113,fields) ->
          let uu____8135 =
            let uu____8147 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8148 =
              FStar_List.map
                (fun uu____8170  ->
                   match uu____8170 with
                   | (field,expr) ->
                       let uu____8185 = translate_expr env expr  in
                       (field, uu____8185)) fields
               in
            (uu____8147, uu____8148)  in
          EFlat uu____8135
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____8196 =
            let uu____8204 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____8205 = translate_expr env e1  in
            (uu____8204, uu____8205, (FStar_Pervasives_Native.snd path))  in
          EField uu____8196
      | FStar_Extraction_ML_Syntax.MLE_Let uu____8211 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____8224) ->
          let uu____8229 =
            let uu____8231 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____8231
             in
          failwith uu____8229
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____8243 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____8243
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____8249 = FStar_List.map (translate_expr env) es  in
          ETuple uu____8249
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____8252,cons1),es) ->
          let uu____8267 =
            let uu____8277 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8278 = FStar_List.map (translate_expr env) es  in
            (uu____8277, cons1, uu____8278)  in
          ECons uu____8267
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____8304 =
            let uu____8313 = translate_expr env1 body  in
            let uu____8314 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____8313, uu____8314)  in
          EFun uu____8304
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____8324 =
            let uu____8331 = translate_expr env e1  in
            let uu____8332 = translate_expr env e2  in
            let uu____8333 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____8331, uu____8332, uu____8333)  in
          EIfThenElse uu____8324
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____8335 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____8343 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____8359 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____8377 =
              let uu____8392 = FStar_List.map (translate_type env) ts  in
              (lid, uu____8392)  in
            TApp uu____8377
          else TQualified lid
      | uu____8407 -> failwith "invalid argument: assert_lid"

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
    fun uu____8434  ->
      match uu____8434 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____8461 = translate_pat env pat  in
            (match uu____8461 with
             | (env1,pat1) ->
                 let uu____8472 = translate_expr env1 expr  in
                 (pat1, uu____8472))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___289_8480  ->
    match uu___289_8480 with
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
          let uu____8547 =
            let uu____8548 =
              let uu____8554 = translate_width sw  in (uu____8554, s)  in
            PConstant uu____8548  in
          (env, uu____8547)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____8564,cons1),ps) ->
          let uu____8579 =
            FStar_List.fold_left
              (fun uu____8599  ->
                 fun p1  ->
                   match uu____8599 with
                   | (env1,acc) ->
                       let uu____8619 = translate_pat env1 p1  in
                       (match uu____8619 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8579 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____8649,ps) ->
          let uu____8671 =
            FStar_List.fold_left
              (fun uu____8708  ->
                 fun uu____8709  ->
                   match (uu____8708, uu____8709) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____8789 = translate_pat env1 p1  in
                       (match uu____8789 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____8671 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____8860 =
            FStar_List.fold_left
              (fun uu____8880  ->
                 fun p1  ->
                   match uu____8880 with
                   | (env1,acc) ->
                       let uu____8900 = translate_pat env1 p1  in
                       (match uu____8900 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8860 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____8927 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____8933 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____8947 =
            let uu____8949 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____8949
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____8947
          then
            let uu____8964 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____8964
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____8991) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____9009 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____9011 ->
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
          let uu____9035 =
            let uu____9042 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____9042)  in
          EApp uu____9035
