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
  | MustDisappear [@@deriving show]
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
  typ: typ ;
  mut: Prims.bool }[@@deriving show]
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
    match projectee with | DGlobal _0 -> true | uu____551 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,Prims.int,typ,expr)
      FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____643 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr) FStar_Pervasives_Native.tuple7)
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____749 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,typ) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____835 -> false
  
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
    match projectee with | DExternal _0 -> true | uu____943 -> false
  
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
    match projectee with | DTypeVariant _0 -> true | uu____1041 -> false
  
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
    match projectee with | StdCall  -> true | uu____1148 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1152 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1156 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1160 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1164 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1168 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1172 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1176 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1181 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1192 -> false
  
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1196 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1200 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1204 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1209 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1227 -> false
  
let (__proj__EQualified__item___0 :
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1261 -> false
  
let (__proj__EConstant__item___0 :
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1284 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1295 -> false
  
let (__proj__EApp__item___0 :
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1331 -> false
  
let (__proj__ETypApp__item___0 :
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1367 -> false
  
let (__proj__ELet__item___0 :
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1403 -> false
  
let (__proj__EIfThenElse__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1435 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1457 -> false
  
let (__proj__EAssign__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____1487 -> false
  
let (__proj__EBufCreate__item___0 :
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____1521 -> false
  
let (__proj__EBufRead__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____1551 -> false
  
let (__proj__EBufWrite__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____1585 -> false
  
let (__proj__EBufSub__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____1619 -> false
  
let (__proj__EBufBlit__item___0 :
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5) =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____1671 -> false
  
let (__proj__EMatch__item___0 :
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1717 -> false
  
let (__proj__EOp__item___0 :
  expr -> (op,width) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1745 -> false
  
let (__proj__ECast__item___0 :
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1768 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1772 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1777 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1788 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1792 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1797 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1819 -> false
  
let (__proj__EFlat__item___0 :
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____1867 -> false
  
let (__proj__EField__item___0 :
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____1901 -> false
  
let (__proj__EWhile__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____1931 -> false
  
let (__proj__EBufCreateL__item___0 :
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____1963 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____1989 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2031 -> false
  
let (__proj__EBufFill__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2061 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2081 -> false
  
let (__proj__EFun__item___0 :
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2117 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____2129 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____2140 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2144 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____2148 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2152 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____2156 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2160 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2164 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2168 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____2172 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____2176 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2180 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2184 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2188 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2192 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2196 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____2200 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____2204 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____2208 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____2212 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____2216 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____2220 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____2224 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____2228 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____2232 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____2236 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2240 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2245 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2257 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2275 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2307 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2331 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list)
  = fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____2365 -> false
  
let (__proj__PConstant__item___0 :
  pattern -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____2388 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2392 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2396 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2400 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2404 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2408 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2412 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2416 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2420 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____2424 -> false
  
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
    match projectee with | TInt _0 -> true | uu____2447 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2459 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2470 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2481 -> false
  
let (__proj__TQualified__item___0 :
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2510 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2514 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2523 -> false
  
let (__proj__TArrow__item___0 :
  typ -> (typ,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2547 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2571 -> false
  
let (__proj__TApp__item___0 :
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____2621 -> false
  
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
  'Auu____2697 'Auu____2698 'Auu____2699 .
    ('Auu____2699,'Auu____2698,'Auu____2697) FStar_Pervasives_Native.tuple3
      -> 'Auu____2699
  = fun uu____2709  -> match uu____2709 with | (x,uu____2717,uu____2718) -> x 
let snd3 :
  'Auu____2723 'Auu____2724 'Auu____2725 .
    ('Auu____2725,'Auu____2724,'Auu____2723) FStar_Pervasives_Native.tuple3
      -> 'Auu____2724
  = fun uu____2735  -> match uu____2735 with | (uu____2742,x,uu____2744) -> x 
let thd3 :
  'Auu____2749 'Auu____2750 'Auu____2751 .
    ('Auu____2751,'Auu____2750,'Auu____2749) FStar_Pervasives_Native.tuple3
      -> 'Auu____2749
  = fun uu____2761  -> match uu____2761 with | (uu____2768,uu____2769,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___35_2775  ->
    match uu___35_2775 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____2778 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___36_2783  ->
    match uu___36_2783 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____2786 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___37_2796  ->
    match uu___37_2796 with
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
    | uu____2799 -> FStar_Pervasives_Native.None
  
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
  pretty: Prims.string ;
  mut: Prims.bool }[@@deriving show]
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
    match projectee with
    | { pretty = __fname__pretty; mut = __fname__mut;_} -> __fname__pretty
  
let (__proj__Mkname__item__mut : name -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { pretty = __fname__pretty; mut = __fname__mut;_} -> __fname__mut
  
let (empty : Prims.string Prims.list -> env) =
  fun module_name  -> { names = []; names_t = []; module_name } 
let (extend : env -> Prims.string -> Prims.bool -> env) =
  fun env  ->
    fun x  ->
      fun is_mut  ->
        let uu___44_2910 = env  in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___44_2910.names_t);
          module_name = (uu___44_2910.module_name)
        }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___45_2917 = env  in
      {
        names = (uu___45_2917.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___45_2917.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____2924 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____2924 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (is_mutable : env -> Prims.string -> Prims.bool) =
  fun env  -> fun x  -> let uu____2936 = find_name env x  in uu____2936.mut 
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____2951 ->
          let uu____2952 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____2952
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____2967 ->
          let uu____2968 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____2968
  
let add_binders :
  'Auu____2972 .
    env ->
      (Prims.string,'Auu____2972) FStar_Pervasives_Native.tuple2 Prims.list
        -> env
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____3002  ->
             match uu____3002 with
             | (name,uu____3008) -> extend env1 name false) env binders
  
let rec (is_unit_type : FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun uu___38_3011  ->
    match uu___38_3011 with
    | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
        let uu____3015 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
        uu____3015 = "Prims.unit" -> true
    | FStar_Extraction_ML_Syntax.MLTY_Fun
        (uu____3016,FStar_Extraction_ML_Syntax.E_GHOST ,uu____3017) -> true
    | FStar_Extraction_ML_Syntax.MLTY_Fun
        (uu____3018,FStar_Extraction_ML_Syntax.E_PURE ,t) -> is_unit_type t
    | uu____3020 -> false
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____3161  ->
    match uu____3161 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3209 = m  in
               match uu____3209 with
               | (path,uu____3223,uu____3224) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____3246 = translate_module m  in
                FStar_Pervasives_Native.Some uu____3246)
             with
             | e ->
                 ((let uu____3255 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3255);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath,(FStar_Extraction_ML_Syntax.mlsig,
                                       FStar_Extraction_ML_Syntax.mlmodule)
                                       FStar_Pervasives_Native.tuple2
                                       FStar_Pervasives_Native.option,
    FStar_Extraction_ML_Syntax.mllib) FStar_Pervasives_Native.tuple3 -> 
    file)
  =
  fun uu____3256  ->
    match uu____3256 with
    | (module_name,modul,uu____3271) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____3302 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags1  ->
    FStar_List.choose
      (fun uu___39_3317  ->
         match uu___39_3317 with
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
         | uu____3321 -> FStar_Pervasives_Native.None) flags1

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3332 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3334 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____3338) ->
          (FStar_Util.print1_warning
             "Skipping the translation of exception: %s\n" m;
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3360;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____3363;
                FStar_Extraction_ML_Syntax.loc = uu____3364;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3366;_} ->
            let assumed =
              FStar_Util.for_some
                (fun uu___40_3385  ->
                   match uu___40_3385 with
                   | FStar_Extraction_ML_Syntax.Assumed  -> true
                   | uu____3386 -> false) meta
               in
            let env1 =
              if flavor = FStar_Extraction_ML_Syntax.Rec
              then extend env name false
              else env  in
            let env2 =
              FStar_List.fold_left
                (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars
               in
            let rec find_return_type eff i uu___41_3407 =
              match uu___41_3407 with
              | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3412,eff1,t) when
                  i > (Prims.parse_int "0") ->
                  find_return_type eff1 (i - (Prims.parse_int "1")) t
              | t -> (eff, t)  in
            let uu____3416 =
              find_return_type FStar_Extraction_ML_Syntax.E_PURE
                (FStar_List.length args) t0
               in
            (match uu____3416 with
             | (eff,t) ->
                 let t1 = translate_type env2 t  in
                 let binders = translate_binders env2 args  in
                 let env3 = add_binders env2 args  in
                 let name1 = ((env3.module_name), name)  in
                 let meta1 =
                   let is_unit =
                     match eff with
                     | FStar_Extraction_ML_Syntax.E_GHOST  -> true
                     | FStar_Extraction_ML_Syntax.E_PURE  -> is_unit_type t0
                     | uu____3447 -> false  in
                   if is_unit
                   then
                     let uu____3450 = translate_flags meta  in MustDisappear
                       :: uu____3450
                   else translate_flags meta  in
                 if assumed
                 then
                   (if (FStar_List.length tvars) = (Prims.parse_int "0")
                    then
                      let uu____3458 =
                        let uu____3459 =
                          let uu____3478 = translate_type env3 t0  in
                          (FStar_Pervasives_Native.None, meta1, name1,
                            uu____3478)
                           in
                        DExternal uu____3459  in
                      FStar_Pervasives_Native.Some uu____3458
                    else
                      ((let uu____3491 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath name1
                           in
                        FStar_Util.print1_warning
                          "No writing anything for %s (polymorphic assume)\n"
                          uu____3491);
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
                        ((let uu____3524 =
                            let uu____3529 =
                              let uu____3530 =
                                FStar_Extraction_ML_Syntax.string_of_mlpath
                                  name1
                                 in
                              FStar_Util.format2
                                "Writing a stub for %s (%s)\n" uu____3530 msg
                               in
                            (FStar_Errors.Warning_FunctionNotExtacted,
                              uu____3529)
                             in
                          FStar_Errors.log_issue FStar_Range.dummyRange
                            uu____3524);
                         (let msg1 =
                            Prims.strcat "This function was not extracted:\n"
                              msg
                             in
                          FStar_Pervasives_Native.Some
                            (DFunction
                               (FStar_Pervasives_Native.None, meta1,
                                 (FStar_List.length tvars), t1, name1,
                                 binders, (EAbortS msg1)))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3547;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Coerce
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____3550;
                     FStar_Extraction_ML_Syntax.loc = uu____3551;_},uu____3552,uu____3553);
                FStar_Extraction_ML_Syntax.mlty = uu____3554;
                FStar_Extraction_ML_Syntax.loc = uu____3555;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3557;_} ->
            let assumed =
              FStar_Util.for_some
                (fun uu___40_3576  ->
                   match uu___40_3576 with
                   | FStar_Extraction_ML_Syntax.Assumed  -> true
                   | uu____3577 -> false) meta
               in
            let env1 =
              if flavor = FStar_Extraction_ML_Syntax.Rec
              then extend env name false
              else env  in
            let env2 =
              FStar_List.fold_left
                (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars
               in
            let rec find_return_type eff i uu___41_3598 =
              match uu___41_3598 with
              | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3603,eff1,t) when
                  i > (Prims.parse_int "0") ->
                  find_return_type eff1 (i - (Prims.parse_int "1")) t
              | t -> (eff, t)  in
            let uu____3607 =
              find_return_type FStar_Extraction_ML_Syntax.E_PURE
                (FStar_List.length args) t0
               in
            (match uu____3607 with
             | (eff,t) ->
                 let t1 = translate_type env2 t  in
                 let binders = translate_binders env2 args  in
                 let env3 = add_binders env2 args  in
                 let name1 = ((env3.module_name), name)  in
                 let meta1 =
                   let is_unit =
                     match eff with
                     | FStar_Extraction_ML_Syntax.E_GHOST  -> true
                     | FStar_Extraction_ML_Syntax.E_PURE  -> is_unit_type t0
                     | uu____3638 -> false  in
                   if is_unit
                   then
                     let uu____3641 = translate_flags meta  in MustDisappear
                       :: uu____3641
                   else translate_flags meta  in
                 if assumed
                 then
                   (if (FStar_List.length tvars) = (Prims.parse_int "0")
                    then
                      let uu____3649 =
                        let uu____3650 =
                          let uu____3669 = translate_type env3 t0  in
                          (FStar_Pervasives_Native.None, meta1, name1,
                            uu____3669)
                           in
                        DExternal uu____3650  in
                      FStar_Pervasives_Native.Some uu____3649
                    else
                      ((let uu____3682 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath name1
                           in
                        FStar_Util.print1_warning
                          "No writing anything for %s (polymorphic assume)\n"
                          uu____3682);
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
                        ((let uu____3715 =
                            let uu____3720 =
                              let uu____3721 =
                                FStar_Extraction_ML_Syntax.string_of_mlpath
                                  name1
                                 in
                              FStar_Util.format2
                                "Writing a stub for %s (%s)\n" uu____3721 msg
                               in
                            (FStar_Errors.Warning_FunctionNotExtacted,
                              uu____3720)
                             in
                          FStar_Errors.log_issue FStar_Range.dummyRange
                            uu____3715);
                         (let msg1 =
                            Prims.strcat "This function was not extracted:\n"
                              msg
                             in
                          FStar_Pervasives_Native.Some
                            (DFunction
                               (FStar_Pervasives_Native.None, meta1,
                                 (FStar_List.length tvars), t1, name1,
                                 binders, (EAbortS msg1)))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3738;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3741;_} ->
            let meta1 = translate_flags meta  in
            let meta2 =
              let uu____3752 = is_unit_type t  in
              if uu____3752 then MustDisappear :: meta1 else meta1  in
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
                    (meta2, name1, (FStar_List.length tvars), t1, expr1))
             with
             | e ->
                 ((let uu____3795 =
                     let uu____3800 =
                       let uu____3801 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       let uu____3802 = FStar_Util.print_exn e  in
                       FStar_Util.format2
                         "Not translating definition for %s (%s)\n"
                         uu____3801 uu____3802
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____3800)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____3795);
                  FStar_Pervasives_Native.Some
                    (DGlobal
                       (meta2, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3813;
            FStar_Extraction_ML_Syntax.mllb_def = uu____3814;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____3815;
            FStar_Extraction_ML_Syntax.print_typ = uu____3816;_} ->
            ((let uu____3820 =
                let uu____3825 =
                  FStar_Util.format1 "Not translating definition for %s\n"
                    name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____3825)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____3820);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____3833 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____3833
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

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
            (FStar_Util.print1_warning
               "Not translating type definition (assumed) for %s\n" name2;
             FStar_Pervasives_Native.None)
          else
            (let uu____3871 =
               let uu____3872 =
                 let uu____3889 = translate_flags flags1  in
                 let uu____3892 = translate_type env1 t  in
                 (name1, uu____3889, (FStar_List.length args), uu____3892)
                  in
               DTypeAlias uu____3872  in
             FStar_Pervasives_Native.Some uu____3871)
      | (uu____3901,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args
             in
          let uu____3933 =
            let uu____3934 =
              let uu____3961 = translate_flags flags1  in
              let uu____3964 =
                FStar_List.map
                  (fun uu____3991  ->
                     match uu____3991 with
                     | (f,t) ->
                         let uu____4006 =
                           let uu____4011 = translate_type env1 t  in
                           (uu____4011, false)  in
                         (f, uu____4006)) fields
                 in
              (name1, uu____3961, (FStar_List.length args), uu____3964)  in
            DTypeFlat uu____3934  in
          FStar_Pervasives_Native.Some uu____3933
      | (uu____4034,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
          let name1 = ((env.module_name), name)  in
          let flags2 = translate_flags flags1  in
          let env1 = FStar_List.fold_left extend_t env args  in
          let uu____4071 =
            let uu____4072 =
              let uu____4105 =
                FStar_List.map
                  (fun uu____4150  ->
                     match uu____4150 with
                     | (cons1,ts) ->
                         let uu____4189 =
                           FStar_List.map
                             (fun uu____4216  ->
                                match uu____4216 with
                                | (name2,t) ->
                                    let uu____4231 =
                                      let uu____4236 = translate_type env1 t
                                         in
                                      (uu____4236, false)  in
                                    (name2, uu____4231)) ts
                            in
                         (cons1, uu____4189)) branches
                 in
              (name1, flags2, (FStar_List.length args), uu____4105)  in
            DTypeVariant uu____4072  in
          FStar_Pervasives_Native.Some uu____4071
      | (uu____4275,name,_mangled_name,uu____4278,uu____4279,uu____4280) ->
          ((let uu____4290 =
              let uu____4295 =
                FStar_Util.format1 "Not translating type definition for %s\n"
                  name
                 in
              (FStar_Errors.Warning_DefinitionNotTranslated, uu____4295)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____4290);
           FStar_Pervasives_Native.None)

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4299 = find_t env name  in TBound uu____4299
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4301,t2) ->
          let uu____4303 =
            let uu____4308 = translate_type env t1  in
            let uu____4309 = translate_type env t2  in
            (uu____4308, uu____4309)  in
          TArrow uu____4303
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4313 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4313 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4317 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4317 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4329 = FStar_Util.must (mk_width m)  in TInt uu____4329
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4341 = FStar_Util.must (mk_width m)  in TInt uu____4341
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4346 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4346 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____4347::arg::uu____4349::[],p) when
          (((let uu____4355 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4355 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____4357 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4357 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____4359 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4359 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____4361 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4361 = "FStar.HyperStack.ST.s_mref")
          -> let uu____4362 = translate_type env arg  in TBuf uu____4362
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____4364::[],p) when
          ((((((((((let uu____4370 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4370 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____4372 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4372 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____4374 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4374 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____4376 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4376 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____4378 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4378 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____4380 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4380 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____4382 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4382 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____4384 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4384 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____4386 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4386 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____4388 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4388 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____4390 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4390 = "FStar.HyperStack.ST.mmmref")
          -> let uu____4391 = translate_type env arg  in TBuf uu____4391
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          ((((((((((let uu____4398 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4398 = "FStar.Buffer.buffer") ||
                     (let uu____4400 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4400 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____4402 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4402 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____4404 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4404 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____4406 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4406 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____4408 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4408 = "FStar.HyperStack.mmref"))
                ||
                (let uu____4410 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4410 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____4412 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4412 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____4414 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4414 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____4416 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4416 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____4418 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4418 = "FStar.HyperStack.ST.mmref")
          -> let uu____4419 = translate_type env arg  in TBuf uu____4419
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4420::arg::[],p) when
          (let uu____4427 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4427 = "FStar.HyperStack.s_ref") ||
            (let uu____4429 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4429 = "FStar.HyperStack.ST.s_ref")
          -> let uu____4430 = translate_type env arg  in TBuf uu____4430
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4431::[],p) when
          let uu____4435 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4435 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4473 = FStar_List.map (translate_type env) args  in
          TTuple uu____4473
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4482 =
              let uu____4495 = FStar_List.map (translate_type env) args  in
              (lid, uu____4495)  in
            TApp uu____4482
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4504 = FStar_List.map (translate_type env) ts  in
          TTuple uu____4504

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
    fun uu____4520  ->
      match uu____4520 with
      | (name,typ) ->
          let uu____4527 = translate_type env typ  in
          { name; typ = uu____4527; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____4532 = find env name  in EBound uu____4532
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4537 =
            let uu____4542 = FStar_Util.must (mk_op op)  in
            let uu____4543 = FStar_Util.must (mk_width m)  in
            (uu____4542, uu____4543)  in
          EOp uu____4537
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4547 =
            let uu____4552 = FStar_Util.must (mk_bool_op op)  in
            (uu____4552, Bool)  in
          EOp uu____4547
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
          let is_mut =
            FStar_Util.for_some
              (fun uu___42_4580  ->
                 match uu___42_4580 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____4581 -> false) flags1
             in
          let uu____4582 =
            if is_mut
            then
              let uu____4591 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____4596 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4596 = "FStar.ST.stackref" -> t
                | uu____4597 ->
                    let uu____4598 =
                      let uu____4599 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ
                         in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____4599
                       in
                    failwith uu____4598
                 in
              let uu____4602 =
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
                      (uu____4603,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____4605;
                    FStar_Extraction_ML_Syntax.loc = uu____4606;_} -> body1
                | uu____4609 ->
                    failwith "unexpected: bad desugaring of Mutable"
                 in
              (uu____4591, uu____4602)
            else (typ, body)  in
          (match uu____4582 with
           | (typ1,body1) ->
               let binder =
                 let uu____4614 = translate_type env typ1  in
                 { name; typ = uu____4614; mut = is_mut }  in
               let body2 = translate_expr env body1  in
               let env1 = extend env name is_mut  in
               let continuation1 = translate_expr env1 continuation  in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4640 =
            let uu____4651 = translate_expr env expr  in
            let uu____4652 = translate_branches env branches  in
            (uu____4651, uu____4652)  in
          EMatch uu____4640
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4666;
                  FStar_Extraction_ML_Syntax.loc = uu____4667;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____4669;
             FStar_Extraction_ML_Syntax.loc = uu____4670;_},arg::[])
          when
          let uu____4676 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4676 = "FStar.Dyn.undyn" ->
          let uu____4677 =
            let uu____4682 = translate_expr env arg  in
            let uu____4683 = translate_type env t  in
            (uu____4682, uu____4683)  in
          ECast uu____4677
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4685;
                  FStar_Extraction_ML_Syntax.loc = uu____4686;_},uu____4687);
             FStar_Extraction_ML_Syntax.mlty = uu____4688;
             FStar_Extraction_ML_Syntax.loc = uu____4689;_},uu____4690)
          when
          let uu____4699 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4699 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4701;
                  FStar_Extraction_ML_Syntax.loc = uu____4702;_},uu____4703);
             FStar_Extraction_ML_Syntax.mlty = uu____4704;
             FStar_Extraction_ML_Syntax.loc = uu____4705;_},arg::[])
          when
          ((let uu____4715 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____4715 = "FStar.HyperStack.All.failwith") ||
             (let uu____4717 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4717 = "FStar.Error.unexpected"))
            ||
            (let uu____4719 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4719 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____4721;
               FStar_Extraction_ML_Syntax.loc = uu____4722;_} -> EAbortS msg
           | uu____4723 ->
               let print7 =
                 let uu____4725 =
                   let uu____4726 =
                     let uu____4727 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____4727
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____4726  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____4725
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
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4733;
             FStar_Extraction_ML_Syntax.loc = uu____4734;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                v1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4736;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4737;_}::[])
          when
          (let uu____4742 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4742 = "FStar.HyperStack.ST.op_Bang") && (is_mutable env v1)
          -> let uu____4743 = find env v1  in EBound uu____4743
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4745;
             FStar_Extraction_ML_Syntax.loc = uu____4746;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                v1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4748;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4749;_}::e1::[])
          when
          (let uu____4755 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4755 = "FStar.HyperStack.ST.op_Colon_Equals") &&
            (is_mutable env v1)
          ->
          let uu____4756 =
            let uu____4761 =
              let uu____4762 = find env v1  in EBound uu____4762  in
            let uu____4763 = translate_expr env e1  in
            (uu____4761, uu____4763)  in
          EAssign uu____4756
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4765;
                  FStar_Extraction_ML_Syntax.loc = uu____4766;_},uu____4767);
             FStar_Extraction_ML_Syntax.mlty = uu____4768;
             FStar_Extraction_ML_Syntax.loc = uu____4769;_},e1::e2::[])
          when
          (let uu____4780 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4780 = "FStar.Buffer.index") ||
            (let uu____4782 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4782 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____4783 =
            let uu____4788 = translate_expr env e1  in
            let uu____4789 = translate_expr env e2  in
            (uu____4788, uu____4789)  in
          EBufRead uu____4783
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4791;
                  FStar_Extraction_ML_Syntax.loc = uu____4792;_},uu____4793);
             FStar_Extraction_ML_Syntax.mlty = uu____4794;
             FStar_Extraction_ML_Syntax.loc = uu____4795;_},e1::[])
          when
          let uu____4803 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4803 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____4804 =
            let uu____4809 = translate_expr env e1  in
            (uu____4809, (EConstant (UInt32, "0")))  in
          EBufRead uu____4804
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4811;
                  FStar_Extraction_ML_Syntax.loc = uu____4812;_},uu____4813);
             FStar_Extraction_ML_Syntax.mlty = uu____4814;
             FStar_Extraction_ML_Syntax.loc = uu____4815;_},e1::e2::[])
          when
          let uu____4824 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4824 = "FStar.Buffer.create" ->
          let uu____4825 =
            let uu____4832 = translate_expr env e1  in
            let uu____4833 = translate_expr env e2  in
            (Stack, uu____4832, uu____4833)  in
          EBufCreate uu____4825
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4835;
                  FStar_Extraction_ML_Syntax.loc = uu____4836;_},uu____4837);
             FStar_Extraction_ML_Syntax.mlty = uu____4838;
             FStar_Extraction_ML_Syntax.loc = uu____4839;_},init1::[])
          when
          let uu____4847 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4847 = "FStar.HyperStack.ST.salloc" ->
          let uu____4848 =
            let uu____4855 = translate_expr env init1  in
            (Eternal, uu____4855, (EConstant (UInt32, "1")))  in
          EBufCreate uu____4848
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4857;
                  FStar_Extraction_ML_Syntax.loc = uu____4858;_},uu____4859);
             FStar_Extraction_ML_Syntax.mlty = uu____4860;
             FStar_Extraction_ML_Syntax.loc = uu____4861;_},_rid::init1::[])
          when
          let uu____4870 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4870 = "FStar.HyperStack.ST.ralloc" ->
          let uu____4871 =
            let uu____4878 = translate_expr env init1  in
            (Eternal, uu____4878, (EConstant (UInt32, "1")))  in
          EBufCreate uu____4871
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4880;
                  FStar_Extraction_ML_Syntax.loc = uu____4881;_},uu____4882);
             FStar_Extraction_ML_Syntax.mlty = uu____4883;
             FStar_Extraction_ML_Syntax.loc = uu____4884;_},_e0::e1::e2::[])
          when
          let uu____4894 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4894 = "FStar.Buffer.rcreate" ->
          let uu____4895 =
            let uu____4902 = translate_expr env e1  in
            let uu____4903 = translate_expr env e2  in
            (Eternal, uu____4902, uu____4903)  in
          EBufCreate uu____4895
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4905;
                  FStar_Extraction_ML_Syntax.loc = uu____4906;_},uu____4907);
             FStar_Extraction_ML_Syntax.mlty = uu____4908;
             FStar_Extraction_ML_Syntax.loc = uu____4909;_},_e0::e1::e2::[])
          when
          let uu____4919 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4919 = "FStar.Buffer.rcreate_mm" ->
          let uu____4920 =
            let uu____4927 = translate_expr env e1  in
            let uu____4928 = translate_expr env e2  in
            (ManuallyManaged, uu____4927, uu____4928)  in
          EBufCreate uu____4920
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4930;
                  FStar_Extraction_ML_Syntax.loc = uu____4931;_},uu____4932);
             FStar_Extraction_ML_Syntax.mlty = uu____4933;
             FStar_Extraction_ML_Syntax.loc = uu____4934;_},e2::[])
          when
          let uu____4942 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4942 = "FStar.Buffer.createL" ->
          let rec list_elements acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____4980 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!"
             in
          let list_elements1 = list_elements []  in
          let uu____4988 =
            let uu____4995 =
              let uu____4998 = list_elements1 e2  in
              FStar_List.map (translate_expr env) uu____4998  in
            (Stack, uu____4995)  in
          EBufCreateL uu____4988
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5004;
                  FStar_Extraction_ML_Syntax.loc = uu____5005;_},uu____5006);
             FStar_Extraction_ML_Syntax.mlty = uu____5007;
             FStar_Extraction_ML_Syntax.loc = uu____5008;_},e2::[])
          when
          let uu____5016 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5016 = "FStar.Buffer.rfree" ->
          let uu____5017 = translate_expr env e2  in EBufFree uu____5017
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5019;
                  FStar_Extraction_ML_Syntax.loc = uu____5020;_},uu____5021);
             FStar_Extraction_ML_Syntax.mlty = uu____5022;
             FStar_Extraction_ML_Syntax.loc = uu____5023;_},e1::e2::_e3::[])
          when
          let uu____5033 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5033 = "FStar.Buffer.sub" ->
          let uu____5034 =
            let uu____5039 = translate_expr env e1  in
            let uu____5040 = translate_expr env e2  in
            (uu____5039, uu____5040)  in
          EBufSub uu____5034
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5042;
                  FStar_Extraction_ML_Syntax.loc = uu____5043;_},uu____5044);
             FStar_Extraction_ML_Syntax.mlty = uu____5045;
             FStar_Extraction_ML_Syntax.loc = uu____5046;_},e1::e2::[])
          when
          let uu____5055 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5055 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5057;
                  FStar_Extraction_ML_Syntax.loc = uu____5058;_},uu____5059);
             FStar_Extraction_ML_Syntax.mlty = uu____5060;
             FStar_Extraction_ML_Syntax.loc = uu____5061;_},e1::e2::[])
          when
          let uu____5070 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5070 = "FStar.Buffer.offset" ->
          let uu____5071 =
            let uu____5076 = translate_expr env e1  in
            let uu____5077 = translate_expr env e2  in
            (uu____5076, uu____5077)  in
          EBufSub uu____5071
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5079;
                  FStar_Extraction_ML_Syntax.loc = uu____5080;_},uu____5081);
             FStar_Extraction_ML_Syntax.mlty = uu____5082;
             FStar_Extraction_ML_Syntax.loc = uu____5083;_},e1::e2::e3::[])
          when
          (let uu____5095 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5095 = "FStar.Buffer.upd") ||
            (let uu____5097 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5097 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____5098 =
            let uu____5105 = translate_expr env e1  in
            let uu____5106 = translate_expr env e2  in
            let uu____5107 = translate_expr env e3  in
            (uu____5105, uu____5106, uu____5107)  in
          EBufWrite uu____5098
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5109;
                  FStar_Extraction_ML_Syntax.loc = uu____5110;_},uu____5111);
             FStar_Extraction_ML_Syntax.mlty = uu____5112;
             FStar_Extraction_ML_Syntax.loc = uu____5113;_},e1::e2::[])
          when
          let uu____5122 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5122 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5123 =
            let uu____5130 = translate_expr env e1  in
            let uu____5131 = translate_expr env e2  in
            (uu____5130, (EConstant (UInt32, "0")), uu____5131)  in
          EBufWrite uu____5123
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5133;
             FStar_Extraction_ML_Syntax.loc = uu____5134;_},uu____5135::[])
          when
          let uu____5138 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5138 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5140;
             FStar_Extraction_ML_Syntax.loc = uu____5141;_},uu____5142::[])
          when
          let uu____5145 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5145 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5147;
                  FStar_Extraction_ML_Syntax.loc = uu____5148;_},uu____5149);
             FStar_Extraction_ML_Syntax.mlty = uu____5150;
             FStar_Extraction_ML_Syntax.loc = uu____5151;_},e1::e2::e3::e4::e5::[])
          when
          let uu____5163 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5163 = "FStar.Buffer.blit" ->
          let uu____5164 =
            let uu____5175 = translate_expr env e1  in
            let uu____5176 = translate_expr env e2  in
            let uu____5177 = translate_expr env e3  in
            let uu____5178 = translate_expr env e4  in
            let uu____5179 = translate_expr env e5  in
            (uu____5175, uu____5176, uu____5177, uu____5178, uu____5179)  in
          EBufBlit uu____5164
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5181;
                  FStar_Extraction_ML_Syntax.loc = uu____5182;_},uu____5183);
             FStar_Extraction_ML_Syntax.mlty = uu____5184;
             FStar_Extraction_ML_Syntax.loc = uu____5185;_},e1::e2::e3::[])
          when
          let uu____5195 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5195 = "FStar.Buffer.fill" ->
          let uu____5196 =
            let uu____5203 = translate_expr env e1  in
            let uu____5204 = translate_expr env e2  in
            let uu____5205 = translate_expr env e3  in
            (uu____5203, uu____5204, uu____5205)  in
          EBufFill uu____5196
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5207;
             FStar_Extraction_ML_Syntax.loc = uu____5208;_},uu____5209::[])
          when
          let uu____5212 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5212 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5214;
             FStar_Extraction_ML_Syntax.loc = uu____5215;_},e1::[])
          when
          let uu____5219 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5219 = "Obj.repr" ->
          let uu____5220 =
            let uu____5225 = translate_expr env e1  in (uu____5225, TAny)  in
          ECast uu____5220
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5228;
             FStar_Extraction_ML_Syntax.loc = uu____5229;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5237 = FStar_Util.must (mk_width m)  in
          let uu____5238 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____5237 uu____5238 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5240;
             FStar_Extraction_ML_Syntax.loc = uu____5241;_},args)
          when is_bool_op op ->
          let uu____5249 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____5249 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5251;
             FStar_Extraction_ML_Syntax.loc = uu____5252;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5254;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5255;_}::[])
          when is_machine_int m ->
          let uu____5270 =
            let uu____5275 = FStar_Util.must (mk_width m)  in (uu____5275, c)
             in
          EConstant uu____5270
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5277;
             FStar_Extraction_ML_Syntax.loc = uu____5278;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5280;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5281;_}::[])
          when is_machine_int m ->
          let uu____5296 =
            let uu____5301 = FStar_Util.must (mk_width m)  in (uu____5301, c)
             in
          EConstant uu____5296
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5302;
             FStar_Extraction_ML_Syntax.loc = uu____5303;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5305;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5306;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5312 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5313;
             FStar_Extraction_ML_Syntax.loc = uu____5314;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5316;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5317;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5323 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5325;
             FStar_Extraction_ML_Syntax.loc = uu____5326;_},arg::[])
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
            let uu____5333 =
              let uu____5338 = translate_expr env arg  in
              (uu____5338, (TInt UInt64))  in
            ECast uu____5333
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5340 =
                 let uu____5345 = translate_expr env arg  in
                 (uu____5345, (TInt UInt32))  in
               ECast uu____5340)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5347 =
                   let uu____5352 = translate_expr env arg  in
                   (uu____5352, (TInt UInt16))  in
                 ECast uu____5347)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5354 =
                     let uu____5359 = translate_expr env arg  in
                     (uu____5359, (TInt UInt8))  in
                   ECast uu____5354)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5361 =
                       let uu____5366 = translate_expr env arg  in
                       (uu____5366, (TInt Int64))  in
                     ECast uu____5361)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5368 =
                         let uu____5373 = translate_expr env arg  in
                         (uu____5373, (TInt Int32))  in
                       ECast uu____5368)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5375 =
                           let uu____5380 = translate_expr env arg  in
                           (uu____5380, (TInt Int16))  in
                         ECast uu____5375)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5382 =
                             let uu____5387 = translate_expr env arg  in
                             (uu____5387, (TInt Int8))  in
                           ECast uu____5382)
                        else
                          (let uu____5389 =
                             let uu____5396 =
                               let uu____5399 = translate_expr env arg  in
                               [uu____5399]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5396)
                              in
                           EApp uu____5389)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5410 =
            let uu____5417 = translate_expr env head1  in
            let uu____5418 = FStar_List.map (translate_expr env) args  in
            (uu____5417, uu____5418)  in
          EApp uu____5410
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5429 =
            let uu____5436 = translate_expr env head1  in
            let uu____5437 = FStar_List.map (translate_type env) ty_args  in
            (uu____5436, uu____5437)  in
          ETypApp uu____5429
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5445 =
            let uu____5450 = translate_expr env e1  in
            let uu____5451 = translate_type env t_to  in
            (uu____5450, uu____5451)  in
          ECast uu____5445
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5452,fields) ->
          let uu____5470 =
            let uu____5481 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5482 =
              FStar_List.map
                (fun uu____5501  ->
                   match uu____5501 with
                   | (field,expr) ->
                       let uu____5512 = translate_expr env expr  in
                       (field, uu____5512)) fields
               in
            (uu____5481, uu____5482)  in
          EFlat uu____5470
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5521 =
            let uu____5528 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____5529 = translate_expr env e1  in
            (uu____5528, uu____5529, (FStar_Pervasives_Native.snd path))  in
          EField uu____5521
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5532 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5544) ->
          let uu____5549 =
            let uu____5550 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5550
             in
          failwith uu____5549
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5556 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____5556
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5562 = FStar_List.map (translate_expr env) es  in
          ETuple uu____5562
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5565,cons1),es) ->
          let uu____5582 =
            let uu____5591 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5592 = FStar_List.map (translate_expr env) es  in
            (uu____5591, cons1, uu____5592)  in
          ECons uu____5582
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____5615 =
            let uu____5624 = translate_expr env1 body  in
            let uu____5625 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____5624, uu____5625)  in
          EFun uu____5615
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5635 =
            let uu____5642 = translate_expr env e1  in
            let uu____5643 = translate_expr env e2  in
            let uu____5644 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____5642, uu____5643, uu____5644)  in
          EIfThenElse uu____5635
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5646 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5653 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____5668 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____5683 =
              let uu____5696 = FStar_List.map (translate_type env) ts  in
              (lid, uu____5696)  in
            TApp uu____5683
          else TQualified lid
      | uu____5702 -> failwith "invalid argument: assert_lid"

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
    fun uu____5728  ->
      match uu____5728 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____5754 = translate_pat env pat  in
            (match uu____5754 with
             | (env1,pat1) ->
                 let uu____5765 = translate_expr env1 expr  in
                 (pat1, uu____5765))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___43_5771  ->
    match uu___43_5771 with
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
          let uu____5835 =
            let uu____5836 =
              let uu____5841 = translate_width sw  in (uu____5841, s)  in
            PConstant uu____5836  in
          (env, uu____5835)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name false  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_" false  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5845,cons1),ps) ->
          let uu____5862 =
            FStar_List.fold_left
              (fun uu____5882  ->
                 fun p1  ->
                   match uu____5882 with
                   | (env1,acc) ->
                       let uu____5902 = translate_pat env1 p1  in
                       (match uu____5902 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____5862 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____5931,ps) ->
          let uu____5949 =
            FStar_List.fold_left
              (fun uu____5983  ->
                 fun uu____5984  ->
                   match (uu____5983, uu____5984) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____6053 = translate_pat env1 p1  in
                       (match uu____6053 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____5949 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____6115 =
            FStar_List.fold_left
              (fun uu____6135  ->
                 fun p1  ->
                   match uu____6135 with
                   | (env1,acc) ->
                       let uu____6155 = translate_pat env1 p1  in
                       (match uu____6155 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6115 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6182 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6187 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____6198 =
            let uu____6199 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____6199
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____6198
          then
            let uu____6211 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____6211
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6223) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6238 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6239 ->
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
          let uu____6259 =
            let uu____6266 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____6266)  in
          EApp uu____6259
