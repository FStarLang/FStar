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
  fun uu___280_4103  ->
    match uu___280_4103 with
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
  fun uu___281_4125  ->
    match uu___281_4125 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____4134 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___282_4155  ->
    match uu___282_4155 with
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
      let uu___288_4356 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___288_4356.names_t);
        module_name = (uu___288_4356.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___289_4370 = env  in
      {
        names = (uu___289_4370.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___289_4370.module_name)
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
        (fun uu___291_4409  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___290_4416 ->
          let uu____4418 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4418
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___293_4438  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___292_4447 ->
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
               (fun uu___295_4856  ->
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
      (fun uu___283_4937  ->
         match uu___283_4937 with
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
        (fun uu___284_4959  ->
           match uu___284_4959 with
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
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5030;_} when
            FStar_Util.for_some
              (fun uu___285_5035  ->
                 match uu___285_5035 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____5038 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            if (FStar_List.length tvars) = (Prims.parse_int "0")
            then
              let uu____5059 =
                let uu____5060 =
                  let uu____5081 = translate_cc meta  in
                  let uu____5084 = translate_flags meta  in
                  let uu____5087 = translate_type env t0  in
                  (uu____5081, uu____5084, name1, uu____5087)  in
                DExternal uu____5060  in
              FStar_Pervasives_Native.Some uu____5059
            else
              ((let uu____5103 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____5103);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5109;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____5112;
                FStar_Extraction_ML_Syntax.loc = uu____5113;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5115;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let env1 =
                 if flavor = FStar_Extraction_ML_Syntax.Rec
                 then extend env name
                 else env  in
               let env2 =
                 FStar_List.fold_left
                   (fun env2  -> fun name1  -> extend_t env2 name1) env1
                   tvars
                  in
               let rec find_return_type eff i uu___286_5172 =
                 match uu___286_5172 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5181,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____5201 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____5201 with
               | (i,eff,t) ->
                   (if i > (Prims.parse_int "0")
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____5227 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____5227 msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5245) ->
                           let uu____5246 = translate_flags meta  in
                           MustDisappear :: uu____5246
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____5249 = translate_flags meta  in
                           MustDisappear :: uu____5249
                       | uu____5252 -> translate_flags meta  in
                     try
                       (fun uu___297_5261  ->
                          match () with
                          | () ->
                              let body1 = translate_expr env3 body  in
                              FStar_Pervasives_Native.Some
                                (DFunction
                                   (cc, meta1, (FStar_List.length tvars), t1,
                                     name1, binders, body1))) ()
                     with
                     | e ->
                         let msg = FStar_Util.print_exn e  in
                         ((let uu____5293 =
                             let uu____5299 =
                               let uu____5301 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____5301 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____5299)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____5293);
                          (let msg1 =
                             Prims.strcat
                               "This function was not extracted:\n" msg
                              in
                           FStar_Pervasives_Native.Some
                             (DFunction
                                (cc, meta1, (FStar_List.length tvars), t1,
                                  name1, binders, (EAbortS msg1))))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5327;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5330;_} ->
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
                 (fun uu___299_5367  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____5391 =
                       let uu____5397 =
                         let uu____5399 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____5401 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____5399
                           uu____5401
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____5397)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____5391);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5419;
            FStar_Extraction_ML_Syntax.mllb_def = uu____5420;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____5421;
            FStar_Extraction_ML_Syntax.print_typ = uu____5422;_} ->
            ((let uu____5429 =
                let uu____5435 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____5435)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____5429);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____5442 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____5442
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____5456 = ty  in
      match uu____5456 with
      | (uu____5459,uu____5460,uu____5461,uu____5462,flags1,uu____5464) ->
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
                     (let uu____5538 =
                        let uu____5539 =
                          let uu____5559 = translate_flags flags2  in
                          let uu____5562 = translate_type env1 t  in
                          (name1, uu____5559, (FStar_List.length args),
                            uu____5562)
                           in
                        DTypeAlias uu____5539  in
                      FStar_Pervasives_Native.Some uu____5538)
             | (uu____5575,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____5620 =
                   let uu____5621 =
                     let uu____5653 = translate_flags flags2  in
                     let uu____5656 =
                       FStar_List.map
                         (fun uu____5688  ->
                            match uu____5688 with
                            | (f,t) ->
                                let uu____5708 =
                                  let uu____5714 = translate_type env1 t  in
                                  (uu____5714, false)  in
                                (f, uu____5708)) fields
                        in
                     (name1, uu____5653, (FStar_List.length args),
                       uu____5656)
                      in
                   DTypeFlat uu____5621  in
                 FStar_Pervasives_Native.Some uu____5620
             | (uu____5747,name,_mangled_name,args,flags2,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags3 = translate_flags flags2  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____5797 =
                   let uu____5798 =
                     let uu____5837 =
                       FStar_List.map
                         (fun uu____5890  ->
                            match uu____5890 with
                            | (cons1,ts) ->
                                let uu____5938 =
                                  FStar_List.map
                                    (fun uu____5970  ->
                                       match uu____5970 with
                                       | (name2,t) ->
                                           let uu____5990 =
                                             let uu____5996 =
                                               translate_type env1 t  in
                                             (uu____5996, false)  in
                                           (name2, uu____5990)) ts
                                   in
                                (cons1, uu____5938)) branches
                        in
                     (name1, flags3, (FStar_List.length args), uu____5837)
                      in
                   DTypeVariant uu____5798  in
                 FStar_Pervasives_Native.Some uu____5797
             | (uu____6049,name,_mangled_name,uu____6052,uu____6053,uu____6054)
                 ->
                 ((let uu____6070 =
                     let uu____6076 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____6076)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____6070);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____6084 = find_t env name  in TBound uu____6084
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____6087,t2) ->
          let uu____6089 =
            let uu____6094 = translate_type env t1  in
            let uu____6095 = translate_type env t2  in
            (uu____6094, uu____6095)  in
          TArrow uu____6089
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6099 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6099 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6106 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6106 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____6123 = FStar_Util.must (mk_width m)  in TInt uu____6123
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____6137 = FStar_Util.must (mk_width m)  in TInt uu____6137
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6142 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6142 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____6146::arg::uu____6148::[],p) when
          (((let uu____6154 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6154 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____6159 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6159 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____6164 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6164 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____6169 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6169 = "FStar.HyperStack.ST.s_mref")
          -> let uu____6173 = translate_type env arg  in TBuf uu____6173
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____6175::[],p) when
          ((((((((((let uu____6181 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6181 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____6186 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6186 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____6191 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6191 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____6196 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6196 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____6201 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6201 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____6206 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6206 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____6211 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6211 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____6216 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6216 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____6221 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6221 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____6226 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6226 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____6231 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6231 = "FStar.HyperStack.ST.mmmref")
          -> let uu____6235 = translate_type env arg  in TBuf uu____6235
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____6237::uu____6238::[],p) when
          let uu____6242 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6242 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____6246 = translate_type env arg  in TBuf uu____6246
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____6253 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6253 = "FStar.Buffer.buffer") ||
                        (let uu____6258 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____6258 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____6263 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____6263 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____6268 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6268 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____6273 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6273 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____6278 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6278 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____6283 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6283 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____6288 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6288 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____6293 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6293 = "FStar.HyperStack.mmref"))
                ||
                (let uu____6298 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6298 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____6303 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6303 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____6308 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6308 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____6313 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6313 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____6318 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6318 = "FStar.HyperStack.ST.mmref")
          -> let uu____6322 = translate_type env arg  in TBuf uu____6322
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6323::arg::[],p) when
          (let uu____6330 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6330 = "FStar.HyperStack.s_ref") ||
            (let uu____6335 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6335 = "FStar.HyperStack.ST.s_ref")
          -> let uu____6339 = translate_type env arg  in TBuf uu____6339
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6340::[],p) when
          let uu____6344 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6344 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____6396 = FStar_List.map (translate_type env) args  in
          TTuple uu____6396
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____6407 =
              let uu____6422 = FStar_List.map (translate_type env) args  in
              (lid, uu____6422)  in
            TApp uu____6407
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____6440 = FStar_List.map (translate_type env) ts  in
          TTuple uu____6440

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
    fun uu____6458  ->
      match uu____6458 with
      | (name,typ) ->
          let uu____6468 = translate_type env typ  in
          { name; typ = uu____6468; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____6475 = find env name  in EBound uu____6475
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____6489 =
            let uu____6494 = FStar_Util.must (mk_op op)  in
            let uu____6495 = FStar_Util.must (mk_width m)  in
            (uu____6494, uu____6495)  in
          EOp uu____6489
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____6505 =
            let uu____6510 = FStar_Util.must (mk_bool_op op)  in
            (uu____6510, Bool)  in
          EOp uu____6505
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
            let uu____6533 = translate_type env typ  in
            { name; typ = uu____6533; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____6560 =
            let uu____6571 = translate_expr env expr  in
            let uu____6572 = translate_branches env branches  in
            (uu____6571, uu____6572)  in
          EMatch uu____6560
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6586;
                  FStar_Extraction_ML_Syntax.loc = uu____6587;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6589;
             FStar_Extraction_ML_Syntax.loc = uu____6590;_},arg::[])
          when
          let uu____6596 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6596 = "FStar.Dyn.undyn" ->
          let uu____6600 =
            let uu____6605 = translate_expr env arg  in
            let uu____6606 = translate_type env t  in
            (uu____6605, uu____6606)  in
          ECast uu____6600
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6608;
                  FStar_Extraction_ML_Syntax.loc = uu____6609;_},uu____6610);
             FStar_Extraction_ML_Syntax.mlty = uu____6611;
             FStar_Extraction_ML_Syntax.loc = uu____6612;_},uu____6613)
          when
          let uu____6622 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6622 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6627;
                  FStar_Extraction_ML_Syntax.loc = uu____6628;_},uu____6629);
             FStar_Extraction_ML_Syntax.mlty = uu____6630;
             FStar_Extraction_ML_Syntax.loc = uu____6631;_},arg::[])
          when
          ((let uu____6641 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6641 = "FStar.HyperStack.All.failwith") ||
             (let uu____6646 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6646 = "FStar.Error.unexpected"))
            ||
            (let uu____6651 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6651 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____6656;
               FStar_Extraction_ML_Syntax.loc = uu____6657;_} -> EAbortS msg
           | uu____6659 ->
               let print7 =
                 let uu____6661 =
                   let uu____6662 =
                     let uu____6663 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____6663
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____6662  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____6661
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
                  FStar_Extraction_ML_Syntax.mlty = uu____6670;
                  FStar_Extraction_ML_Syntax.loc = uu____6671;_},uu____6672);
             FStar_Extraction_ML_Syntax.mlty = uu____6673;
             FStar_Extraction_ML_Syntax.loc = uu____6674;_},e1::[])
          when
          (let uu____6684 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6684 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____6689 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6689 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6694;
                  FStar_Extraction_ML_Syntax.loc = uu____6695;_},uu____6696);
             FStar_Extraction_ML_Syntax.mlty = uu____6697;
             FStar_Extraction_ML_Syntax.loc = uu____6698;_},e1::e2::[])
          when
          (((let uu____6709 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6709 = "FStar.Buffer.index") ||
              (let uu____6714 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6714 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____6719 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6719 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____6724 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6724 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____6728 =
            let uu____6733 = translate_expr env e1  in
            let uu____6734 = translate_expr env e2  in
            (uu____6733, uu____6734)  in
          EBufRead uu____6728
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6736;
                  FStar_Extraction_ML_Syntax.loc = uu____6737;_},uu____6738);
             FStar_Extraction_ML_Syntax.mlty = uu____6739;
             FStar_Extraction_ML_Syntax.loc = uu____6740;_},e1::[])
          when
          let uu____6748 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6748 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____6752 =
            let uu____6757 = translate_expr env e1  in
            (uu____6757, (EConstant (UInt32, "0")))  in
          EBufRead uu____6752
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6761;
                  FStar_Extraction_ML_Syntax.loc = uu____6762;_},uu____6763);
             FStar_Extraction_ML_Syntax.mlty = uu____6764;
             FStar_Extraction_ML_Syntax.loc = uu____6765;_},e1::e2::[])
          when
          ((let uu____6776 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6776 = "FStar.Buffer.create") ||
             (let uu____6781 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6781 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____6786 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6786 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____6790 =
            let uu____6797 = translate_expr env e1  in
            let uu____6798 = translate_expr env e2  in
            (Stack, uu____6797, uu____6798)  in
          EBufCreate uu____6790
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6800;
                  FStar_Extraction_ML_Syntax.loc = uu____6801;_},uu____6802);
             FStar_Extraction_ML_Syntax.mlty = uu____6803;
             FStar_Extraction_ML_Syntax.loc = uu____6804;_},elen::[])
          when
          let uu____6812 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6812 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____6816 =
            let uu____6821 = translate_expr env elen  in (Stack, uu____6821)
             in
          EBufCreateNoInit uu____6816
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6823;
                  FStar_Extraction_ML_Syntax.loc = uu____6824;_},uu____6825);
             FStar_Extraction_ML_Syntax.mlty = uu____6826;
             FStar_Extraction_ML_Syntax.loc = uu____6827;_},init1::[])
          when
          let uu____6835 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6835 = "FStar.HyperStack.ST.salloc" ->
          let uu____6839 =
            let uu____6846 = translate_expr env init1  in
            (Stack, uu____6846, (EConstant (UInt32, "1")))  in
          EBufCreate uu____6839
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6850;
                  FStar_Extraction_ML_Syntax.loc = uu____6851;_},uu____6852);
             FStar_Extraction_ML_Syntax.mlty = uu____6853;
             FStar_Extraction_ML_Syntax.loc = uu____6854;_},e2::[])
          when
          ((let uu____6864 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6864 = "FStar.Buffer.createL") ||
             (let uu____6869 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6869 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____6874 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6874 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____6878 =
            let uu____6885 =
              let uu____6888 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____6888  in
            (Stack, uu____6885)  in
          EBufCreateL uu____6878
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6894;
                  FStar_Extraction_ML_Syntax.loc = uu____6895;_},uu____6896);
             FStar_Extraction_ML_Syntax.mlty = uu____6897;
             FStar_Extraction_ML_Syntax.loc = uu____6898;_},_erid::e2::[])
          when
          (let uu____6909 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6909 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____6914 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6914 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____6918 =
            let uu____6925 =
              let uu____6928 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____6928  in
            (Eternal, uu____6925)  in
          EBufCreateL uu____6918
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6934;
                  FStar_Extraction_ML_Syntax.loc = uu____6935;_},uu____6936);
             FStar_Extraction_ML_Syntax.mlty = uu____6937;
             FStar_Extraction_ML_Syntax.loc = uu____6938;_},_rid::init1::[])
          when
          let uu____6947 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6947 = "FStar.HyperStack.ST.ralloc" ->
          let uu____6951 =
            let uu____6958 = translate_expr env init1  in
            (Eternal, uu____6958, (EConstant (UInt32, "1")))  in
          EBufCreate uu____6951
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6962;
                  FStar_Extraction_ML_Syntax.loc = uu____6963;_},uu____6964);
             FStar_Extraction_ML_Syntax.mlty = uu____6965;
             FStar_Extraction_ML_Syntax.loc = uu____6966;_},_e0::e1::e2::[])
          when
          ((let uu____6978 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6978 = "FStar.Buffer.rcreate") ||
             (let uu____6983 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6983 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____6988 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6988 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____6992 =
            let uu____6999 = translate_expr env e1  in
            let uu____7000 = translate_expr env e2  in
            (Eternal, uu____6999, uu____7000)  in
          EBufCreate uu____6992
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7002;
                  FStar_Extraction_ML_Syntax.loc = uu____7003;_},uu____7004);
             FStar_Extraction_ML_Syntax.mlty = uu____7005;
             FStar_Extraction_ML_Syntax.loc = uu____7006;_},_erid::elen::[])
          when
          let uu____7015 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7015 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____7019 =
            let uu____7024 = translate_expr env elen  in
            (Eternal, uu____7024)  in
          EBufCreateNoInit uu____7019
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7026;
                  FStar_Extraction_ML_Syntax.loc = uu____7027;_},uu____7028);
             FStar_Extraction_ML_Syntax.mlty = uu____7029;
             FStar_Extraction_ML_Syntax.loc = uu____7030;_},_rid::init1::[])
          when
          let uu____7039 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7039 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____7043 =
            let uu____7050 = translate_expr env init1  in
            (ManuallyManaged, uu____7050, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7043
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7054;
                  FStar_Extraction_ML_Syntax.loc = uu____7055;_},uu____7056);
             FStar_Extraction_ML_Syntax.mlty = uu____7057;
             FStar_Extraction_ML_Syntax.loc = uu____7058;_},_e0::e1::e2::[])
          when
          (((let uu____7070 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7070 = "FStar.Buffer.rcreate_mm") ||
              (let uu____7075 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7075 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____7080 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7080 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____7085 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7085 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____7089 =
            let uu____7096 = translate_expr env e1  in
            let uu____7097 = translate_expr env e2  in
            (ManuallyManaged, uu____7096, uu____7097)  in
          EBufCreate uu____7089
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7099;
                  FStar_Extraction_ML_Syntax.loc = uu____7100;_},uu____7101);
             FStar_Extraction_ML_Syntax.mlty = uu____7102;
             FStar_Extraction_ML_Syntax.loc = uu____7103;_},_erid::elen::[])
          when
          let uu____7112 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7112 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____7116 =
            let uu____7121 = translate_expr env elen  in
            (ManuallyManaged, uu____7121)  in
          EBufCreateNoInit uu____7116
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7123;
                  FStar_Extraction_ML_Syntax.loc = uu____7124;_},uu____7125);
             FStar_Extraction_ML_Syntax.mlty = uu____7126;
             FStar_Extraction_ML_Syntax.loc = uu____7127;_},e2::[])
          when
          let uu____7135 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7135 = "FStar.HyperStack.ST.rfree" ->
          let uu____7139 = translate_expr env e2  in EBufFree uu____7139
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7141;
                  FStar_Extraction_ML_Syntax.loc = uu____7142;_},uu____7143);
             FStar_Extraction_ML_Syntax.mlty = uu____7144;
             FStar_Extraction_ML_Syntax.loc = uu____7145;_},e2::[])
          when
          (let uu____7155 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7155 = "FStar.Buffer.rfree") ||
            (let uu____7160 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7160 = "LowStar.Monotonic.Buffer.free")
          -> let uu____7164 = translate_expr env e2  in EBufFree uu____7164
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7166;
                  FStar_Extraction_ML_Syntax.loc = uu____7167;_},uu____7168);
             FStar_Extraction_ML_Syntax.mlty = uu____7169;
             FStar_Extraction_ML_Syntax.loc = uu____7170;_},e1::e2::_e3::[])
          when
          let uu____7180 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7180 = "FStar.Buffer.sub" ->
          let uu____7184 =
            let uu____7189 = translate_expr env e1  in
            let uu____7190 = translate_expr env e2  in
            (uu____7189, uu____7190)  in
          EBufSub uu____7184
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7192;
                  FStar_Extraction_ML_Syntax.loc = uu____7193;_},uu____7194);
             FStar_Extraction_ML_Syntax.mlty = uu____7195;
             FStar_Extraction_ML_Syntax.loc = uu____7196;_},e1::e2::_e3::[])
          when
          let uu____7206 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7206 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____7210 =
            let uu____7215 = translate_expr env e1  in
            let uu____7216 = translate_expr env e2  in
            (uu____7215, uu____7216)  in
          EBufSub uu____7210
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7218;
                  FStar_Extraction_ML_Syntax.loc = uu____7219;_},uu____7220);
             FStar_Extraction_ML_Syntax.mlty = uu____7221;
             FStar_Extraction_ML_Syntax.loc = uu____7222;_},e1::e2::[])
          when
          let uu____7231 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7231 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7236;
                  FStar_Extraction_ML_Syntax.loc = uu____7237;_},uu____7238);
             FStar_Extraction_ML_Syntax.mlty = uu____7239;
             FStar_Extraction_ML_Syntax.loc = uu____7240;_},e1::e2::[])
          when
          let uu____7249 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7249 = "FStar.Buffer.offset" ->
          let uu____7253 =
            let uu____7258 = translate_expr env e1  in
            let uu____7259 = translate_expr env e2  in
            (uu____7258, uu____7259)  in
          EBufSub uu____7253
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7261;
                  FStar_Extraction_ML_Syntax.loc = uu____7262;_},uu____7263);
             FStar_Extraction_ML_Syntax.mlty = uu____7264;
             FStar_Extraction_ML_Syntax.loc = uu____7265;_},e1::e2::[])
          when
          let uu____7274 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7274 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____7278 =
            let uu____7283 = translate_expr env e1  in
            let uu____7284 = translate_expr env e2  in
            (uu____7283, uu____7284)  in
          EBufSub uu____7278
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
             FStar_Extraction_ML_Syntax.loc = uu____7290;_},e1::e2::e3::[])
          when
          (((let uu____7302 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7302 = "FStar.Buffer.upd") ||
              (let uu____7307 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7307 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____7312 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7312 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____7317 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7317 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____7321 =
            let uu____7328 = translate_expr env e1  in
            let uu____7329 = translate_expr env e2  in
            let uu____7330 = translate_expr env e3  in
            (uu____7328, uu____7329, uu____7330)  in
          EBufWrite uu____7321
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7332;
                  FStar_Extraction_ML_Syntax.loc = uu____7333;_},uu____7334);
             FStar_Extraction_ML_Syntax.mlty = uu____7335;
             FStar_Extraction_ML_Syntax.loc = uu____7336;_},e1::e2::[])
          when
          let uu____7345 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7345 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____7349 =
            let uu____7356 = translate_expr env e1  in
            let uu____7357 = translate_expr env e2  in
            (uu____7356, (EConstant (UInt32, "0")), uu____7357)  in
          EBufWrite uu____7349
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7361;
             FStar_Extraction_ML_Syntax.loc = uu____7362;_},uu____7363::[])
          when
          let uu____7366 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7366 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7371;
             FStar_Extraction_ML_Syntax.loc = uu____7372;_},uu____7373::[])
          when
          let uu____7376 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7376 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7381;
                  FStar_Extraction_ML_Syntax.loc = uu____7382;_},uu____7383);
             FStar_Extraction_ML_Syntax.mlty = uu____7384;
             FStar_Extraction_ML_Syntax.loc = uu____7385;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____7399 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7399 = "FStar.Buffer.blit") ||
             (let uu____7404 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7404 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____7409 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7409 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____7413 =
            let uu____7424 = translate_expr env e1  in
            let uu____7425 = translate_expr env e2  in
            let uu____7426 = translate_expr env e3  in
            let uu____7427 = translate_expr env e4  in
            let uu____7428 = translate_expr env e5  in
            (uu____7424, uu____7425, uu____7426, uu____7427, uu____7428)  in
          EBufBlit uu____7413
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7430;
                  FStar_Extraction_ML_Syntax.loc = uu____7431;_},uu____7432);
             FStar_Extraction_ML_Syntax.mlty = uu____7433;
             FStar_Extraction_ML_Syntax.loc = uu____7434;_},e1::e2::e3::[])
          when
          let uu____7444 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7444 = "FStar.Buffer.fill" ->
          let uu____7448 =
            let uu____7455 = translate_expr env e1  in
            let uu____7456 = translate_expr env e2  in
            let uu____7457 = translate_expr env e3  in
            (uu____7455, uu____7456, uu____7457)  in
          EBufFill uu____7448
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7459;
             FStar_Extraction_ML_Syntax.loc = uu____7460;_},uu____7461::[])
          when
          let uu____7464 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7464 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7469;
                  FStar_Extraction_ML_Syntax.loc = uu____7470;_},uu____7471);
             FStar_Extraction_ML_Syntax.mlty = uu____7472;
             FStar_Extraction_ML_Syntax.loc = uu____7473;_},_ebuf::_eseq::[])
          when
          (((let uu____7484 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7484 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____7489 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7489 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____7494 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7494 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____7499 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7499 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7504;
             FStar_Extraction_ML_Syntax.loc = uu____7505;_},e1::[])
          when
          let uu____7509 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7509 = "Obj.repr" ->
          let uu____7513 =
            let uu____7518 = translate_expr env e1  in (uu____7518, TAny)  in
          ECast uu____7513
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7521;
             FStar_Extraction_ML_Syntax.loc = uu____7522;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____7538 = FStar_Util.must (mk_width m)  in
          let uu____7539 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____7538 uu____7539 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7541;
             FStar_Extraction_ML_Syntax.loc = uu____7542;_},args)
          when is_bool_op op ->
          let uu____7556 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____7556 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7558;
             FStar_Extraction_ML_Syntax.loc = uu____7559;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7561;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7562;_}::[])
          when is_machine_int m ->
          let uu____7587 =
            let uu____7593 = FStar_Util.must (mk_width m)  in (uu____7593, c)
             in
          EConstant uu____7587
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7596;
             FStar_Extraction_ML_Syntax.loc = uu____7597;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7599;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7600;_}::[])
          when is_machine_int m ->
          let uu____7625 =
            let uu____7631 = FStar_Util.must (mk_width m)  in (uu____7631, c)
             in
          EConstant uu____7625
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7633;
             FStar_Extraction_ML_Syntax.loc = uu____7634;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7636;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7637;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7650 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7652;
             FStar_Extraction_ML_Syntax.loc = uu____7653;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7655;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7656;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7671 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____7674;
             FStar_Extraction_ML_Syntax.loc = uu____7675;_},arg::[])
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
            let uu____7703 =
              let uu____7708 = translate_expr env arg  in
              (uu____7708, (TInt UInt64))  in
            ECast uu____7703
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____7713 =
                 let uu____7718 = translate_expr env arg  in
                 (uu____7718, (TInt UInt32))  in
               ECast uu____7713)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____7723 =
                   let uu____7728 = translate_expr env arg  in
                   (uu____7728, (TInt UInt16))  in
                 ECast uu____7723)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____7733 =
                     let uu____7738 = translate_expr env arg  in
                     (uu____7738, (TInt UInt8))  in
                   ECast uu____7733)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____7743 =
                       let uu____7748 = translate_expr env arg  in
                       (uu____7748, (TInt Int64))  in
                     ECast uu____7743)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____7753 =
                         let uu____7758 = translate_expr env arg  in
                         (uu____7758, (TInt Int32))  in
                       ECast uu____7753)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____7763 =
                           let uu____7768 = translate_expr env arg  in
                           (uu____7768, (TInt Int16))  in
                         ECast uu____7763)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____7773 =
                             let uu____7778 = translate_expr env arg  in
                             (uu____7778, (TInt Int8))  in
                           ECast uu____7773)
                        else
                          (let uu____7781 =
                             let uu____7788 =
                               let uu____7791 = translate_expr env arg  in
                               [uu____7791]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____7788)
                              in
                           EApp uu____7781)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____7811 =
            let uu____7818 = translate_expr env head1  in
            let uu____7819 = FStar_List.map (translate_expr env) args  in
            (uu____7818, uu____7819)  in
          EApp uu____7811
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____7830 =
            let uu____7837 = translate_expr env head1  in
            let uu____7838 = FStar_List.map (translate_type env) ty_args  in
            (uu____7837, uu____7838)  in
          ETypApp uu____7830
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____7846 =
            let uu____7851 = translate_expr env e1  in
            let uu____7852 = translate_type env t_to  in
            (uu____7851, uu____7852)  in
          ECast uu____7846
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____7853,fields) ->
          let uu____7875 =
            let uu____7887 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____7888 =
              FStar_List.map
                (fun uu____7910  ->
                   match uu____7910 with
                   | (field,expr) ->
                       let uu____7925 = translate_expr env expr  in
                       (field, uu____7925)) fields
               in
            (uu____7887, uu____7888)  in
          EFlat uu____7875
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____7936 =
            let uu____7944 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____7945 = translate_expr env e1  in
            (uu____7944, uu____7945, (FStar_Pervasives_Native.snd path))  in
          EField uu____7936
      | FStar_Extraction_ML_Syntax.MLE_Let uu____7951 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____7964) ->
          let uu____7969 =
            let uu____7971 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____7971
             in
          failwith uu____7969
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____7983 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____7983
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____7989 = FStar_List.map (translate_expr env) es  in
          ETuple uu____7989
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____7992,cons1),es) ->
          let uu____8007 =
            let uu____8017 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8018 = FStar_List.map (translate_expr env) es  in
            (uu____8017, cons1, uu____8018)  in
          ECons uu____8007
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____8044 =
            let uu____8053 = translate_expr env1 body  in
            let uu____8054 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____8053, uu____8054)  in
          EFun uu____8044
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____8064 =
            let uu____8071 = translate_expr env e1  in
            let uu____8072 = translate_expr env e2  in
            let uu____8073 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____8071, uu____8072, uu____8073)  in
          EIfThenElse uu____8064
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____8075 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____8083 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____8099 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____8117 =
              let uu____8132 = FStar_List.map (translate_type env) ts  in
              (lid, uu____8132)  in
            TApp uu____8117
          else TQualified lid
      | uu____8147 -> failwith "invalid argument: assert_lid"

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
    fun uu____8174  ->
      match uu____8174 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____8201 = translate_pat env pat  in
            (match uu____8201 with
             | (env1,pat1) ->
                 let uu____8212 = translate_expr env1 expr  in
                 (pat1, uu____8212))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___287_8220  ->
    match uu___287_8220 with
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
          let uu____8287 =
            let uu____8288 =
              let uu____8294 = translate_width sw  in (uu____8294, s)  in
            PConstant uu____8288  in
          (env, uu____8287)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____8304,cons1),ps) ->
          let uu____8319 =
            FStar_List.fold_left
              (fun uu____8339  ->
                 fun p1  ->
                   match uu____8339 with
                   | (env1,acc) ->
                       let uu____8359 = translate_pat env1 p1  in
                       (match uu____8359 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8319 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____8389,ps) ->
          let uu____8411 =
            FStar_List.fold_left
              (fun uu____8448  ->
                 fun uu____8449  ->
                   match (uu____8448, uu____8449) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____8529 = translate_pat env1 p1  in
                       (match uu____8529 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____8411 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____8600 =
            FStar_List.fold_left
              (fun uu____8620  ->
                 fun p1  ->
                   match uu____8620 with
                   | (env1,acc) ->
                       let uu____8640 = translate_pat env1 p1  in
                       (match uu____8640 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8600 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____8667 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____8673 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____8687 =
            let uu____8689 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____8689
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____8687
          then
            let uu____8704 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____8704
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____8731) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____8749 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____8751 ->
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
          let uu____8775 =
            let uu____8782 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____8782)  in
          EApp uu____8775
