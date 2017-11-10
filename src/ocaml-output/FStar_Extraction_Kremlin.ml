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
  | Stack [@@deriving show]
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
  | EAbortS of Prims.string [@@deriving show]
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
  Prims.list [@@deriving show]
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
let uu___is_DGlobal : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DGlobal _0 -> true | uu____539 -> false
  
let __proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,Prims.int,typ,expr)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let uu___is_DFunction : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____631 -> false
  
let __proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr) FStar_Pervasives_Native.tuple7
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let uu___is_DTypeAlias : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____737 -> false
  
let __proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,typ) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let uu___is_DTypeFlat : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____823 -> false
  
let __proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,(Prims.string,(typ,Prims.bool)
                                                FStar_Pervasives_Native.tuple2)
                                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let uu___is_DExternal : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____931 -> false
  
let __proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,(Prims.string
                                                          Prims.list,
                                                         Prims.string)
                                                         FStar_Pervasives_Native.tuple2,
      typ) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let uu___is_DTypeVariant : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____1029 -> false
  
let __proj__DTypeVariant__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,(Prims.string,(Prims.string,(typ,Prims.bool)
                                                              FStar_Pervasives_Native.tuple2)
                                                FStar_Pervasives_Native.tuple2
                                                Prims.list)
                                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DTypeVariant _0 -> _0 
let uu___is_StdCall : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1136 -> false
  
let uu___is_CDecl : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1140 -> false
  
let uu___is_FastCall : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1144 -> false
  
let uu___is_Private : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1148 -> false
  
let uu___is_WipeBody : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1152 -> false
  
let uu___is_CInline : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1156 -> false
  
let uu___is_Substitute : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1160 -> false
  
let uu___is_GCType : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1164 -> false
  
let uu___is_Comment : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1169 -> false
  
let __proj__Comment__item___0 : flag -> Prims.string =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let uu___is_MustDisappear : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1180 -> false
  
let uu___is_Eternal : lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1184 -> false
  
let uu___is_Stack : lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1188 -> false
  
let uu___is_EBound : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1193 -> false
  
let __proj__EBound__item___0 : expr -> Prims.int =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let uu___is_EQualified : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1211 -> false
  
let __proj__EQualified__item___0 :
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EQualified _0 -> _0 
let uu___is_EConstant : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1245 -> false
  
let __proj__EConstant__item___0 :
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let uu___is_EUnit : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1268 -> false
  
let uu___is_EApp : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1279 -> false
  
let __proj__EApp__item___0 :
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let uu___is_ETypApp : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1315 -> false
  
let __proj__ETypApp__item___0 :
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let uu___is_ELet : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1351 -> false
  
let __proj__ELet__item___0 :
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let uu___is_EIfThenElse : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1387 -> false
  
let __proj__EIfThenElse__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let uu___is_ESequence : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1419 -> false
  
let __proj__ESequence__item___0 : expr -> expr Prims.list =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let uu___is_EAssign : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1441 -> false
  
let __proj__EAssign__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let uu___is_EBufCreate : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____1471 -> false
  
let __proj__EBufCreate__item___0 :
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let uu___is_EBufRead : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____1505 -> false
  
let __proj__EBufRead__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let uu___is_EBufWrite : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____1535 -> false
  
let __proj__EBufWrite__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let uu___is_EBufSub : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____1569 -> false
  
let __proj__EBufSub__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let uu___is_EBufBlit : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____1603 -> false
  
let __proj__EBufBlit__item___0 :
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5 =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let uu___is_EMatch : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____1655 -> false
  
let __proj__EMatch__item___0 :
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let uu___is_EOp : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1701 -> false
  
let __proj__EOp__item___0 : expr -> (op,width) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EOp _0 -> _0 
let uu___is_ECast : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1729 -> false
  
let __proj__ECast__item___0 :
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let uu___is_EPushFrame : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1752 -> false
  
let uu___is_EPopFrame : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1756 -> false
  
let uu___is_EBool : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1761 -> false
  
let __proj__EBool__item___0 : expr -> Prims.bool =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let uu___is_EAny : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1772 -> false
  
let uu___is_EAbort : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1776 -> false
  
let uu___is_EReturn : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1781 -> false
  
let __proj__EReturn__item___0 : expr -> expr =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let uu___is_EFlat : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1803 -> false
  
let __proj__EFlat__item___0 :
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EFlat _0 -> _0 
let uu___is_EField : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____1851 -> false
  
let __proj__EField__item___0 :
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EField _0 -> _0 
let uu___is_EWhile : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____1885 -> false
  
let __proj__EWhile__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let uu___is_EBufCreateL : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____1915 -> false
  
let __proj__EBufCreateL__item___0 :
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let uu___is_ETuple : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____1947 -> false
  
let __proj__ETuple__item___0 : expr -> expr Prims.list =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let uu___is_ECons : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____1973 -> false
  
let __proj__ECons__item___0 :
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let uu___is_EBufFill : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2015 -> false
  
let __proj__EBufFill__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let uu___is_EString : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2045 -> false
  
let __proj__EString__item___0 : expr -> Prims.string =
  fun projectee  -> match projectee with | EString _0 -> _0 
let uu___is_EFun : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2065 -> false
  
let __proj__EFun__item___0 :
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let uu___is_EAbortS : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2101 -> false
  
let __proj__EAbortS__item___0 : expr -> Prims.string =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let uu___is_Add : op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____2112 -> false 
let uu___is_AddW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2116 -> false
  
let uu___is_Sub : op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____2120 -> false 
let uu___is_SubW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2124 -> false
  
let uu___is_Div : op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____2128 -> false 
let uu___is_DivW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2132 -> false
  
let uu___is_Mult : op -> Prims.bool =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2136 -> false
  
let uu___is_MultW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2140 -> false
  
let uu___is_Mod : op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____2144 -> false 
let uu___is_BOr : op -> Prims.bool =
  fun projectee  -> match projectee with | BOr  -> true | uu____2148 -> false 
let uu___is_BAnd : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2152 -> false
  
let uu___is_BXor : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2156 -> false
  
let uu___is_BShiftL : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2160 -> false
  
let uu___is_BShiftR : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2164 -> false
  
let uu___is_BNot : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2168 -> false
  
let uu___is_Eq : op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2172 -> false 
let uu___is_Neq : op -> Prims.bool =
  fun projectee  -> match projectee with | Neq  -> true | uu____2176 -> false 
let uu___is_Lt : op -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2180 -> false 
let uu___is_Lte : op -> Prims.bool =
  fun projectee  -> match projectee with | Lte  -> true | uu____2184 -> false 
let uu___is_Gt : op -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2188 -> false 
let uu___is_Gte : op -> Prims.bool =
  fun projectee  -> match projectee with | Gte  -> true | uu____2192 -> false 
let uu___is_And : op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____2196 -> false 
let uu___is_Or : op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____2200 -> false 
let uu___is_Xor : op -> Prims.bool =
  fun projectee  -> match projectee with | Xor  -> true | uu____2204 -> false 
let uu___is_Not : op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____2208 -> false 
let uu___is_PUnit : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2212 -> false
  
let uu___is_PBool : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2217 -> false
  
let __proj__PBool__item___0 : pattern -> Prims.bool =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let uu___is_PVar : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2229 -> false
  
let __proj__PVar__item___0 : pattern -> binder =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let uu___is_PCons : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2247 -> false
  
let __proj__PCons__item___0 :
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PCons _0 -> _0 
let uu___is_PTuple : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2279 -> false
  
let __proj__PTuple__item___0 : pattern -> pattern Prims.list =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let uu___is_PRecord : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2303 -> false
  
let __proj__PRecord__item___0 :
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list
  = fun projectee  -> match projectee with | PRecord _0 -> _0 
let uu___is_UInt8 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____2332 -> false
  
let uu___is_UInt16 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2336 -> false
  
let uu___is_UInt32 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2340 -> false
  
let uu___is_UInt64 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2344 -> false
  
let uu___is_Int8 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2348 -> false
  
let uu___is_Int16 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2352 -> false
  
let uu___is_Int32 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2356 -> false
  
let uu___is_Int64 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2360 -> false
  
let uu___is_Bool : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2364 -> false
  
let uu___is_CInt : width -> Prims.bool =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____2368 -> false
  
let __proj__Mkbinder__item__name : binder -> Prims.string =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ; mut = __fname__mut;_} ->
        __fname__name
  
let __proj__Mkbinder__item__typ : binder -> typ =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ; mut = __fname__mut;_} ->
        __fname__typ
  
let __proj__Mkbinder__item__mut : binder -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; typ = __fname__typ; mut = __fname__mut;_} ->
        __fname__mut
  
let uu___is_TInt : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____2391 -> false
  
let __proj__TInt__item___0 : typ -> width =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let uu___is_TBuf : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2403 -> false
  
let __proj__TBuf__item___0 : typ -> typ =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let uu___is_TUnit : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2414 -> false
  
let uu___is_TQualified : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2425 -> false
  
let __proj__TQualified__item___0 :
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TQualified _0 -> _0 
let uu___is_TBool : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2454 -> false
  
let uu___is_TAny : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2458 -> false
  
let uu___is_TArrow : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2467 -> false
  
let __proj__TArrow__item___0 :
  typ -> (typ,typ) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let uu___is_TBound : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2491 -> false
  
let __proj__TBound__item___0 : typ -> Prims.int =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let uu___is_TApp : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2515 -> false
  
let __proj__TApp__item___0 :
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TApp _0 -> _0 
let uu___is_TTuple : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____2565 -> false
  
let __proj__TTuple__item___0 : typ -> typ Prims.list =
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
let current_version : version = (Prims.parse_int "26") 
type file = (Prims.string,program) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
type binary_format = (version,file Prims.list) FStar_Pervasives_Native.tuple2
[@@deriving show]
let fst3 :
  'Auu____2641 'Auu____2642 'Auu____2643 .
    ('Auu____2643,'Auu____2642,'Auu____2641) FStar_Pervasives_Native.tuple3
      -> 'Auu____2643
  = fun uu____2653  -> match uu____2653 with | (x,uu____2661,uu____2662) -> x 
let snd3 :
  'Auu____2667 'Auu____2668 'Auu____2669 .
    ('Auu____2669,'Auu____2668,'Auu____2667) FStar_Pervasives_Native.tuple3
      -> 'Auu____2668
  = fun uu____2679  -> match uu____2679 with | (uu____2686,x,uu____2688) -> x 
let thd3 :
  'Auu____2693 'Auu____2694 'Auu____2695 .
    ('Auu____2695,'Auu____2694,'Auu____2693) FStar_Pervasives_Native.tuple3
      -> 'Auu____2693
  = fun uu____2705  -> match uu____2705 with | (uu____2712,uu____2713,x) -> x 
let mk_width : Prims.string -> width FStar_Pervasives_Native.option =
  fun uu___401_2719  ->
    match uu___401_2719 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____2722 -> FStar_Pervasives_Native.None
  
let mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___402_2727  ->
    match uu___402_2727 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____2730 -> FStar_Pervasives_Native.None
  
let is_bool_op : Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let mk_op : Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___403_2740  ->
    match uu___403_2740 with
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
    | uu____2743 -> FStar_Pervasives_Native.None
  
let is_op : Prims.string -> Prims.bool =
  fun op  -> (mk_op op) <> FStar_Pervasives_Native.None 
let is_machine_int : Prims.string -> Prims.bool =
  fun m  -> (mk_width m) <> FStar_Pervasives_Native.None 
type env =
  {
  names: name Prims.list ;
  names_t: Prims.string Prims.list ;
  module_name: Prims.string Prims.list }[@@deriving show]
and name = {
  pretty: Prims.string ;
  mut: Prims.bool }[@@deriving show]
let __proj__Mkenv__item__names : env -> name Prims.list =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__names
  
let __proj__Mkenv__item__names_t : env -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__names_t
  
let __proj__Mkenv__item__module_name : env -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { names = __fname__names; names_t = __fname__names_t;
        module_name = __fname__module_name;_} -> __fname__module_name
  
let __proj__Mkname__item__pretty : name -> Prims.string =
  fun projectee  ->
    match projectee with
    | { pretty = __fname__pretty; mut = __fname__mut;_} -> __fname__pretty
  
let __proj__Mkname__item__mut : name -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { pretty = __fname__pretty; mut = __fname__mut;_} -> __fname__mut
  
let empty : Prims.string Prims.list -> env =
  fun module_name  -> { names = []; names_t = []; module_name } 
let extend : env -> Prims.string -> Prims.bool -> env =
  fun env  ->
    fun x  ->
      fun is_mut  ->
        let uu___408_2854 = env  in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___408_2854.names_t);
          module_name = (uu___408_2854.module_name)
        }
  
let extend_t : env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___409_2861 = env  in
      {
        names = (uu___409_2861.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___409_2861.module_name)
      }
  
let find_name : env -> Prims.string -> name =
  fun env  ->
    fun x  ->
      let uu____2868 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____2868 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let is_mutable : env -> Prims.string -> Prims.bool =
  fun env  -> fun x  -> let uu____2880 = find_name env x  in uu____2880.mut 
let find : env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____2895 ->
          let uu____2896 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____2896
  
let find_t : env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____2911 ->
          let uu____2912 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____2912
  
let add_binders :
  'Auu____2916 .
    env ->
      (Prims.string,'Auu____2916) FStar_Pervasives_Native.tuple2 Prims.list
        -> env
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____2946  ->
             match uu____2946 with
             | (name,uu____2952) -> extend env1 name false) env binders
  
let rec translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____3093  ->
    match uu____3093 with
    | FStar_Extraction_ML_Syntax.MLLib modules1 ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3153 = m  in
               match uu____3153 with
               | ((prefix1,final),uu____3174,uu____3175) ->
                   FStar_String.concat "."
                     (FStar_List.append prefix1 [final])
                in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____3207 = translate_module m  in
                FStar_Pervasives_Native.Some uu____3207)
             with
             | e ->
                 ((let uu____3216 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3216);
                  FStar_Pervasives_Native.None)) modules1

and translate_module :
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
    (FStar_Extraction_ML_Syntax.mlsig,FStar_Extraction_ML_Syntax.mlmodule)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,FStar_Extraction_ML_Syntax.mllib)
    FStar_Pervasives_Native.tuple3 -> file
  =
  fun uu____3217  ->
    match uu____3217 with
    | (module_name,modul,uu____3238) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____3281 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list =
  fun flags  ->
    FStar_List.choose
      (fun uu___404_3296  ->
         match uu___404_3296 with
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
         | uu____3300 -> FStar_Pervasives_Native.None) flags

and translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,flags,lbs) ->
          FStar_List.choose (translate_let env flavor flags) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3312 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3314 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____3317 ->
          failwith "todo: translate_decl [MLM_Exn]"

and translate_let :
  env ->
    FStar_Extraction_ML_Syntax.mlletflavor ->
      FStar_Extraction_ML_Syntax.metadata ->
        FStar_Extraction_ML_Syntax.mllb ->
          decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun flavor  ->
      fun flags  ->
        fun lb  ->
          match lb with
          | { FStar_Extraction_ML_Syntax.mllb_name = name;
              FStar_Extraction_ML_Syntax.mllb_tysc =
                FStar_Pervasives_Native.Some (tvars,t0);
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3339;
              FStar_Extraction_ML_Syntax.mllb_def =
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                  FStar_Extraction_ML_Syntax.mlty = uu____3342;
                  FStar_Extraction_ML_Syntax.loc = uu____3343;_};
              FStar_Extraction_ML_Syntax.print_typ = uu____3344;_} ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___405_3363  ->
                     match uu___405_3363 with
                     | FStar_Extraction_ML_Syntax.Assumed  -> true
                     | uu____3364 -> false) flags
                 in
              let env1 =
                if flavor = FStar_Extraction_ML_Syntax.Rec
                then extend env name false
                else env  in
              let env2 =
                FStar_List.fold_left
                  (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars
                 in
              let rec find_return_type i uu___406_3378 =
                match uu___406_3378 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun
                    (uu____3379,uu____3380,t) when i > (Prims.parse_int "0")
                    -> find_return_type (i - (Prims.parse_int "1")) t
                | t -> t  in
              let t =
                let uu____3384 = find_return_type (FStar_List.length args) t0
                   in
                translate_type env2 uu____3384  in
              let binders = translate_binders env2 args  in
              let env3 = add_binders env2 args  in
              let name1 = ((env3.module_name), name)  in
              let flags1 =
                match t0 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun
                    (uu____3407,FStar_Extraction_ML_Syntax.E_GHOST
                     ,uu____3408)
                    ->
                    let uu____3409 = translate_flags flags  in MustDisappear
                      :: uu____3409
                | uu____3412 -> translate_flags flags  in
              if assumed
              then
                (if (FStar_List.length tvars) = (Prims.parse_int "0")
                 then
                   let uu____3417 =
                     let uu____3418 =
                       let uu____3437 = translate_type env3 t0  in
                       (FStar_Pervasives_Native.None, flags1, name1,
                         uu____3437)
                        in
                     DExternal uu____3418  in
                   FStar_Pervasives_Native.Some uu____3417
                 else FStar_Pervasives_Native.None)
              else
                (try
                   let body1 = translate_expr env3 body  in
                   FStar_Pervasives_Native.Some
                     (DFunction
                        (FStar_Pervasives_Native.None, flags1,
                          (FStar_List.length tvars), t, name1, binders,
                          body1))
                 with
                 | e ->
                     let msg = FStar_Util.print_exn e  in
                     (FStar_Util.print2_warning
                        "Writing a stub for %s (%s)\n"
                        (FStar_Pervasives_Native.snd name1) msg;
                      (let msg1 =
                         Prims.strcat "This function was not extracted:\n"
                           msg
                          in
                       FStar_Pervasives_Native.Some
                         (DFunction
                            (FStar_Pervasives_Native.None, flags1,
                              (FStar_List.length tvars), t, name1, binders,
                              (EAbortS msg1))))))
          | { FStar_Extraction_ML_Syntax.mllb_name = name;
              FStar_Extraction_ML_Syntax.mllb_tysc =
                FStar_Pervasives_Native.Some (tvars,t0);
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3499;
              FStar_Extraction_ML_Syntax.mllb_def =
                {
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Coerce
                    ({
                       FStar_Extraction_ML_Syntax.expr =
                         FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                       FStar_Extraction_ML_Syntax.mlty = uu____3502;
                       FStar_Extraction_ML_Syntax.loc = uu____3503;_},uu____3504,uu____3505);
                  FStar_Extraction_ML_Syntax.mlty = uu____3506;
                  FStar_Extraction_ML_Syntax.loc = uu____3507;_};
              FStar_Extraction_ML_Syntax.print_typ = uu____3508;_} ->
              let assumed =
                FStar_Util.for_some
                  (fun uu___405_3527  ->
                     match uu___405_3527 with
                     | FStar_Extraction_ML_Syntax.Assumed  -> true
                     | uu____3528 -> false) flags
                 in
              let env1 =
                if flavor = FStar_Extraction_ML_Syntax.Rec
                then extend env name false
                else env  in
              let env2 =
                FStar_List.fold_left
                  (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars
                 in
              let rec find_return_type i uu___406_3542 =
                match uu___406_3542 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun
                    (uu____3543,uu____3544,t) when i > (Prims.parse_int "0")
                    -> find_return_type (i - (Prims.parse_int "1")) t
                | t -> t  in
              let t =
                let uu____3548 = find_return_type (FStar_List.length args) t0
                   in
                translate_type env2 uu____3548  in
              let binders = translate_binders env2 args  in
              let env3 = add_binders env2 args  in
              let name1 = ((env3.module_name), name)  in
              let flags1 =
                match t0 with
                | FStar_Extraction_ML_Syntax.MLTY_Fun
                    (uu____3571,FStar_Extraction_ML_Syntax.E_GHOST
                     ,uu____3572)
                    ->
                    let uu____3573 = translate_flags flags  in MustDisappear
                      :: uu____3573
                | uu____3576 -> translate_flags flags  in
              if assumed
              then
                (if (FStar_List.length tvars) = (Prims.parse_int "0")
                 then
                   let uu____3581 =
                     let uu____3582 =
                       let uu____3601 = translate_type env3 t0  in
                       (FStar_Pervasives_Native.None, flags1, name1,
                         uu____3601)
                        in
                     DExternal uu____3582  in
                   FStar_Pervasives_Native.Some uu____3581
                 else FStar_Pervasives_Native.None)
              else
                (try
                   let body1 = translate_expr env3 body  in
                   FStar_Pervasives_Native.Some
                     (DFunction
                        (FStar_Pervasives_Native.None, flags1,
                          (FStar_List.length tvars), t, name1, binders,
                          body1))
                 with
                 | e ->
                     let msg = FStar_Util.print_exn e  in
                     (FStar_Util.print2_warning
                        "Writing a stub for %s (%s)\n"
                        (FStar_Pervasives_Native.snd name1) msg;
                      (let msg1 =
                         Prims.strcat "This function was not extracted:\n"
                           msg
                          in
                       FStar_Pervasives_Native.Some
                         (DFunction
                            (FStar_Pervasives_Native.None, flags1,
                              (FStar_List.length tvars), t, name1, binders,
                              (EAbortS msg1))))))
          | { FStar_Extraction_ML_Syntax.mllb_name = name;
              FStar_Extraction_ML_Syntax.mllb_tysc =
                FStar_Pervasives_Native.Some (tvars,t);
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3663;
              FStar_Extraction_ML_Syntax.mllb_def = expr;
              FStar_Extraction_ML_Syntax.print_typ = uu____3665;_} ->
              let flags1 = translate_flags flags  in
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
                      (flags1, name1, (FStar_List.length tvars), t1, expr1))
               with
               | e ->
                   ((let uu____3712 = FStar_Util.print_exn e  in
                     FStar_Util.print2_warning
                       "Not translating definition for %s (%s)\n"
                       (FStar_Pervasives_Native.snd name1) uu____3712);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (flags1, name1, (FStar_List.length tvars), t1, EAny))))
          | { FStar_Extraction_ML_Syntax.mllb_name = name;
              FStar_Extraction_ML_Syntax.mllb_tysc = ts;
              FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3725;
              FStar_Extraction_ML_Syntax.mllb_def = uu____3726;
              FStar_Extraction_ML_Syntax.print_typ = uu____3727;_} ->
              (FStar_Util.print1_warning
                 "Not translating definition for %s\n" name;
               (match ts with
                | FStar_Pervasives_Native.Some (idents,t) ->
                    let uu____3738 =
                      FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                    FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                      (FStar_String.concat ", " idents) uu____3738
                | FStar_Pervasives_Native.None  -> ());
               FStar_Pervasives_Native.None)

and translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ty  ->
      match ty with
      | (assumed,name,_mangled_name,args,flags,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Abbrev t)) ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args
             in
          if assumed
          then FStar_Pervasives_Native.None
          else
            (let uu____3774 =
               let uu____3775 =
                 let uu____3792 = translate_flags flags  in
                 let uu____3795 = translate_type env1 t  in
                 (name1, uu____3792, (FStar_List.length args), uu____3795)
                  in
               DTypeAlias uu____3775  in
             FStar_Pervasives_Native.Some uu____3774)
      | (uu____3804,name,_mangled_name,args,flags,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args
             in
          let uu____3836 =
            let uu____3837 =
              let uu____3864 = translate_flags flags  in
              let uu____3867 =
                FStar_List.map
                  (fun uu____3894  ->
                     match uu____3894 with
                     | (f,t) ->
                         let uu____3909 =
                           let uu____3914 = translate_type env1 t  in
                           (uu____3914, false)  in
                         (f, uu____3909)) fields
                 in
              (name1, uu____3864, (FStar_List.length args), uu____3867)  in
            DTypeFlat uu____3837  in
          FStar_Pervasives_Native.Some uu____3836
      | (uu____3937,name,_mangled_name,args,flags,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
          let name1 = ((env.module_name), name)  in
          let flags1 = translate_flags flags  in
          let env1 = FStar_List.fold_left extend_t env args  in
          let uu____3974 =
            let uu____3975 =
              let uu____4008 =
                FStar_List.map
                  (fun uu____4053  ->
                     match uu____4053 with
                     | (cons1,ts) ->
                         let uu____4092 =
                           FStar_List.map
                             (fun uu____4119  ->
                                match uu____4119 with
                                | (name2,t) ->
                                    let uu____4134 =
                                      let uu____4139 = translate_type env1 t
                                         in
                                      (uu____4139, false)  in
                                    (name2, uu____4134)) ts
                            in
                         (cons1, uu____4092)) branches
                 in
              (name1, flags1, (FStar_List.length args), uu____4008)  in
            DTypeVariant uu____3975  in
          FStar_Pervasives_Native.Some uu____3974
      | (uu____4178,name,_mangled_name,uu____4181,uu____4182,uu____4183) ->
          (FStar_Util.print1_warning
             "Not translating type definition for %s\n" name;
           FStar_Pervasives_Native.None)

and translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4196 = find_t env name  in TBound uu____4196
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4198,t2) ->
          let uu____4200 =
            let uu____4205 = translate_type env t1  in
            let uu____4206 = translate_type env t2  in
            (uu____4205, uu____4206)  in
          TArrow uu____4200
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4210 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4210 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4214 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4214 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4226 = FStar_Util.must (mk_width m)  in TInt uu____4226
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4238 = FStar_Util.must (mk_width m)  in TInt uu____4238
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4243 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4243 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4248 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4248 = "FStar.Buffer.buffer" ->
          let uu____4249 = translate_type env arg  in TBuf uu____4249
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4250::[],p) when
          let uu____4254 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4254 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4292 = FStar_List.map (translate_type env) args  in
          TTuple uu____4292
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4301 =
              let uu____4314 = FStar_List.map (translate_type env) args  in
              (lid, uu____4314)  in
            TApp uu____4301
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4323 = FStar_List.map (translate_type env) ts  in
          TTuple uu____4323

and translate_binders :
  env ->
    (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2 Prims.list -> binder Prims.list
  = fun env  -> fun args  -> FStar_List.map (translate_binder env) args

and translate_binder :
  env ->
    (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2 -> binder
  =
  fun env  ->
    fun uu____4339  ->
      match uu____4339 with
      | (name,typ) ->
          let uu____4346 = translate_type env typ  in
          { name; typ = uu____4346; mut = false }

and translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____4351 = find env name  in EBound uu____4351
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4356 =
            let uu____4361 = FStar_Util.must (mk_op op)  in
            let uu____4362 = FStar_Util.must (mk_width m)  in
            (uu____4361, uu____4362)  in
          EOp uu____4356
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4366 =
            let uu____4371 = FStar_Util.must (mk_bool_op op)  in
            (uu____4371, Bool)  in
          EOp uu____4366
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags,{ FStar_Extraction_ML_Syntax.mllb_name = name;
                           FStar_Extraction_ML_Syntax.mllb_tysc =
                             FStar_Pervasives_Native.Some ([],typ);
                           FStar_Extraction_ML_Syntax.mllb_add_unit =
                             add_unit;
                           FStar_Extraction_ML_Syntax.mllb_def = body;
                           FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let is_mut =
            FStar_Util.for_some
              (fun uu___407_4401  ->
                 match uu___407_4401 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____4402 -> false) flags
             in
          let uu____4403 =
            if is_mut
            then
              let uu____4412 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____4417 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4417 = "FStar.ST.stackref" -> t
                | uu____4418 ->
                    let uu____4419 =
                      let uu____4420 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ
                         in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____4420
                       in
                    failwith uu____4419
                 in
              let uu____4423 =
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
                      (uu____4424,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____4426;
                    FStar_Extraction_ML_Syntax.loc = uu____4427;_} -> body1
                | uu____4430 ->
                    failwith "unexpected: bad desugaring of Mutable"
                 in
              (uu____4412, uu____4423)
            else (typ, body)  in
          (match uu____4403 with
           | (typ1,body1) ->
               let binder =
                 let uu____4435 = translate_type env typ1  in
                 { name; typ = uu____4435; mut = is_mut }  in
               let body2 = translate_expr env body1  in
               let env1 = extend env name is_mut  in
               let continuation1 = translate_expr env1 continuation  in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4461 =
            let uu____4472 = translate_expr env expr  in
            let uu____4473 = translate_branches env branches  in
            (uu____4472, uu____4473)  in
          EMatch uu____4461
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4487;
             FStar_Extraction_ML_Syntax.loc = uu____4488;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                v1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4490;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4491;_}::[])
          when
          (let uu____4496 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4496 = "FStar.HyperStack.ST.op_Bang") && (is_mutable env v1)
          -> let uu____4497 = find env v1  in EBound uu____4497
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4499;
             FStar_Extraction_ML_Syntax.loc = uu____4500;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                v1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4502;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4503;_}::e1::[])
          when
          (let uu____4509 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4509 = "FStar.HyperStack.ST.op_Colon_Equals") &&
            (is_mutable env v1)
          ->
          let uu____4510 =
            let uu____4515 =
              let uu____4516 = find env v1  in EBound uu____4516  in
            let uu____4517 = translate_expr env e1  in
            (uu____4515, uu____4517)  in
          EAssign uu____4510
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4519;
                  FStar_Extraction_ML_Syntax.loc = uu____4520;_},uu____4521);
             FStar_Extraction_ML_Syntax.mlty = uu____4522;
             FStar_Extraction_ML_Syntax.loc = uu____4523;_},e1::e2::[])
          when
          (let uu____4534 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4534 = "FStar.Buffer.index") ||
            (let uu____4536 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4536 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____4537 =
            let uu____4542 = translate_expr env e1  in
            let uu____4543 = translate_expr env e2  in
            (uu____4542, uu____4543)  in
          EBufRead uu____4537
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4545;
                  FStar_Extraction_ML_Syntax.loc = uu____4546;_},uu____4547);
             FStar_Extraction_ML_Syntax.mlty = uu____4548;
             FStar_Extraction_ML_Syntax.loc = uu____4549;_},e1::e2::[])
          when
          let uu____4558 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4558 = "FStar.Buffer.create" ->
          let uu____4559 =
            let uu____4566 = translate_expr env e1  in
            let uu____4567 = translate_expr env e2  in
            (Stack, uu____4566, uu____4567)  in
          EBufCreate uu____4559
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4569;
                  FStar_Extraction_ML_Syntax.loc = uu____4570;_},uu____4571);
             FStar_Extraction_ML_Syntax.mlty = uu____4572;
             FStar_Extraction_ML_Syntax.loc = uu____4573;_},_e0::e1::e2::[])
          when
          let uu____4583 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4583 = "FStar.Buffer.rcreate" ->
          let uu____4584 =
            let uu____4591 = translate_expr env e1  in
            let uu____4592 = translate_expr env e2  in
            (Eternal, uu____4591, uu____4592)  in
          EBufCreate uu____4584
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4594;
                  FStar_Extraction_ML_Syntax.loc = uu____4595;_},uu____4596);
             FStar_Extraction_ML_Syntax.mlty = uu____4597;
             FStar_Extraction_ML_Syntax.loc = uu____4598;_},e2::[])
          when
          let uu____4606 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4606 = "FStar.Buffer.createL" ->
          let rec list_elements1 acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements1 (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____4644 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!"
             in
          let list_elements2 = list_elements1 []  in
          let uu____4652 =
            let uu____4659 =
              let uu____4662 = list_elements2 e2  in
              FStar_List.map (translate_expr env) uu____4662  in
            (Stack, uu____4659)  in
          EBufCreateL uu____4652
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4668;
                  FStar_Extraction_ML_Syntax.loc = uu____4669;_},uu____4670);
             FStar_Extraction_ML_Syntax.mlty = uu____4671;
             FStar_Extraction_ML_Syntax.loc = uu____4672;_},e1::e2::_e3::[])
          when
          let uu____4682 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4682 = "FStar.Buffer.sub" ->
          let uu____4683 =
            let uu____4688 = translate_expr env e1  in
            let uu____4689 = translate_expr env e2  in
            (uu____4688, uu____4689)  in
          EBufSub uu____4683
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4691;
                  FStar_Extraction_ML_Syntax.loc = uu____4692;_},uu____4693);
             FStar_Extraction_ML_Syntax.mlty = uu____4694;
             FStar_Extraction_ML_Syntax.loc = uu____4695;_},e1::e2::[])
          when
          let uu____4704 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4704 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4706;
                  FStar_Extraction_ML_Syntax.loc = uu____4707;_},uu____4708);
             FStar_Extraction_ML_Syntax.mlty = uu____4709;
             FStar_Extraction_ML_Syntax.loc = uu____4710;_},e1::e2::[])
          when
          let uu____4719 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4719 = "FStar.Buffer.offset" ->
          let uu____4720 =
            let uu____4725 = translate_expr env e1  in
            let uu____4726 = translate_expr env e2  in
            (uu____4725, uu____4726)  in
          EBufSub uu____4720
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4728;
                  FStar_Extraction_ML_Syntax.loc = uu____4729;_},uu____4730);
             FStar_Extraction_ML_Syntax.mlty = uu____4731;
             FStar_Extraction_ML_Syntax.loc = uu____4732;_},e1::e2::e3::[])
          when
          (let uu____4744 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4744 = "FStar.Buffer.upd") ||
            (let uu____4746 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4746 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____4747 =
            let uu____4754 = translate_expr env e1  in
            let uu____4755 = translate_expr env e2  in
            let uu____4756 = translate_expr env e3  in
            (uu____4754, uu____4755, uu____4756)  in
          EBufWrite uu____4747
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4758;
             FStar_Extraction_ML_Syntax.loc = uu____4759;_},uu____4760::[])
          when
          let uu____4763 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4763 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4765;
             FStar_Extraction_ML_Syntax.loc = uu____4766;_},uu____4767::[])
          when
          let uu____4770 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4770 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4772;
                  FStar_Extraction_ML_Syntax.loc = uu____4773;_},uu____4774);
             FStar_Extraction_ML_Syntax.mlty = uu____4775;
             FStar_Extraction_ML_Syntax.loc = uu____4776;_},e1::e2::e3::e4::e5::[])
          when
          let uu____4788 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4788 = "FStar.Buffer.blit" ->
          let uu____4789 =
            let uu____4800 = translate_expr env e1  in
            let uu____4801 = translate_expr env e2  in
            let uu____4802 = translate_expr env e3  in
            let uu____4803 = translate_expr env e4  in
            let uu____4804 = translate_expr env e5  in
            (uu____4800, uu____4801, uu____4802, uu____4803, uu____4804)  in
          EBufBlit uu____4789
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4806;
                  FStar_Extraction_ML_Syntax.loc = uu____4807;_},uu____4808);
             FStar_Extraction_ML_Syntax.mlty = uu____4809;
             FStar_Extraction_ML_Syntax.loc = uu____4810;_},e1::e2::e3::[])
          when
          let uu____4820 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4820 = "FStar.Buffer.fill" ->
          let uu____4821 =
            let uu____4828 = translate_expr env e1  in
            let uu____4829 = translate_expr env e2  in
            let uu____4830 = translate_expr env e3  in
            (uu____4828, uu____4829, uu____4830)  in
          EBufFill uu____4821
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4832;
             FStar_Extraction_ML_Syntax.loc = uu____4833;_},uu____4834::[])
          when
          let uu____4837 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4837 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4839;
             FStar_Extraction_ML_Syntax.loc = uu____4840;_},e1::[])
          when
          let uu____4844 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4844 = "Obj.repr" ->
          let uu____4845 =
            let uu____4850 = translate_expr env e1  in (uu____4850, TAny)  in
          ECast uu____4845
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____4853;
             FStar_Extraction_ML_Syntax.loc = uu____4854;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____4862 = FStar_Util.must (mk_width m)  in
          let uu____4863 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____4862 uu____4863 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____4865;
             FStar_Extraction_ML_Syntax.loc = uu____4866;_},args)
          when is_bool_op op ->
          let uu____4874 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____4874 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____4876;
             FStar_Extraction_ML_Syntax.loc = uu____4877;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4879;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4880;_}::[])
          when is_machine_int m ->
          let uu____4895 =
            let uu____4900 = FStar_Util.must (mk_width m)  in (uu____4900, c)
             in
          EConstant uu____4895
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____4902;
             FStar_Extraction_ML_Syntax.loc = uu____4903;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4905;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4906;_}::[])
          when is_machine_int m ->
          let uu____4921 =
            let uu____4926 = FStar_Util.must (mk_width m)  in (uu____4926, c)
             in
          EConstant uu____4921
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____4927;
             FStar_Extraction_ML_Syntax.loc = uu____4928;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4930;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4931;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____4937 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____4938;
             FStar_Extraction_ML_Syntax.loc = uu____4939;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4941;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4942;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____4948 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____4950;
             FStar_Extraction_ML_Syntax.loc = uu____4951;_},arg::[])
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
            let uu____4958 =
              let uu____4963 = translate_expr env arg  in
              (uu____4963, (TInt UInt64))  in
            ECast uu____4958
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____4965 =
                 let uu____4970 = translate_expr env arg  in
                 (uu____4970, (TInt UInt32))  in
               ECast uu____4965)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____4972 =
                   let uu____4977 = translate_expr env arg  in
                   (uu____4977, (TInt UInt16))  in
                 ECast uu____4972)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____4979 =
                     let uu____4984 = translate_expr env arg  in
                     (uu____4984, (TInt UInt8))  in
                   ECast uu____4979)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____4986 =
                       let uu____4991 = translate_expr env arg  in
                       (uu____4991, (TInt Int64))  in
                     ECast uu____4986)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____4993 =
                         let uu____4998 = translate_expr env arg  in
                         (uu____4998, (TInt Int32))  in
                       ECast uu____4993)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5000 =
                           let uu____5005 = translate_expr env arg  in
                           (uu____5005, (TInt Int16))  in
                         ECast uu____5000)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5007 =
                             let uu____5012 = translate_expr env arg  in
                             (uu____5012, (TInt Int8))  in
                           ECast uu____5007)
                        else
                          (let uu____5014 =
                             let uu____5021 =
                               let uu____5024 = translate_expr env arg  in
                               [uu____5024]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5021)
                              in
                           EApp uu____5014)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5035 =
            let uu____5042 = translate_expr env head1  in
            let uu____5043 = FStar_List.map (translate_expr env) args  in
            (uu____5042, uu____5043)  in
          EApp uu____5035
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5054 =
            let uu____5061 = translate_expr env head1  in
            let uu____5062 = FStar_List.map (translate_type env) ty_args  in
            (uu____5061, uu____5062)  in
          ETypApp uu____5054
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5070 =
            let uu____5075 = translate_expr env e1  in
            let uu____5076 = translate_type env t_to  in
            (uu____5075, uu____5076)  in
          ECast uu____5070
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5077,fields) ->
          let uu____5095 =
            let uu____5106 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5107 =
              FStar_List.map
                (fun uu____5126  ->
                   match uu____5126 with
                   | (field,expr) ->
                       let uu____5137 = translate_expr env expr  in
                       (field, uu____5137)) fields
               in
            (uu____5106, uu____5107)  in
          EFlat uu____5095
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5146 =
            let uu____5153 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____5154 = translate_expr env e1  in
            (uu____5153, uu____5154, (FStar_Pervasives_Native.snd path))  in
          EField uu____5146
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5157 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5171) ->
          let uu____5176 =
            let uu____5177 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5177
             in
          failwith uu____5176
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5183 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____5183
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5189 = FStar_List.map (translate_expr env) es  in
          ETuple uu____5189
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5192,cons1),es) ->
          let uu____5209 =
            let uu____5218 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5219 = FStar_List.map (translate_expr env) es  in
            (uu____5218, cons1, uu____5219)  in
          ECons uu____5209
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____5242 =
            let uu____5251 = translate_expr env1 body  in
            let uu____5252 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____5251, uu____5252)  in
          EFun uu____5242
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5262 =
            let uu____5269 = translate_expr env e1  in
            let uu____5270 = translate_expr env e2  in
            let uu____5271 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____5269, uu____5270, uu____5271)  in
          EIfThenElse uu____5262
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5273 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5280 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____5295 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____5310 =
              let uu____5323 = FStar_List.map (translate_type env) ts  in
              (lid, uu____5323)  in
            TApp uu____5310
          else TQualified lid
      | uu____5329 -> failwith "invalid argument: assert_lid"

and translate_branches :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern,FStar_Extraction_ML_Syntax.mlexpr
                                            FStar_Pervasives_Native.option,
      FStar_Extraction_ML_Syntax.mlexpr) FStar_Pervasives_Native.tuple3
      Prims.list -> (pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  -> fun branches  -> FStar_List.map (translate_branch env) branches

and translate_branch :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern,FStar_Extraction_ML_Syntax.mlexpr
                                            FStar_Pervasives_Native.option,
      FStar_Extraction_ML_Syntax.mlexpr) FStar_Pervasives_Native.tuple3 ->
      (pattern,expr) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____5355  ->
      match uu____5355 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____5381 = translate_pat env pat  in
            (match uu____5381 with
             | (env1,pat1) ->
                 let uu____5392 = translate_expr env1 expr  in
                 (pat1, uu____5392))
          else failwith "todo: translate_branch"

and translate_pat :
  env ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      (env,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Unit ) -> (env, PUnit)
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Bool b) -> (env, (PBool b))
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name false  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_" false  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5408,cons1),ps) ->
          let uu____5425 =
            FStar_List.fold_left
              (fun uu____5445  ->
                 fun p1  ->
                   match uu____5445 with
                   | (env1,acc) ->
                       let uu____5465 = translate_pat env1 p1  in
                       (match uu____5465 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____5425 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____5494,ps) ->
          let uu____5512 =
            FStar_List.fold_left
              (fun uu____5546  ->
                 fun uu____5547  ->
                   match (uu____5546, uu____5547) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____5616 = translate_pat env1 p1  in
                       (match uu____5616 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____5512 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____5678 =
            FStar_List.fold_left
              (fun uu____5698  ->
                 fun p1  ->
                   match uu____5698 with
                   | (env1,acc) ->
                       let uu____5718 = translate_pat env1 p1  in
                       (match uu____5718 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____5678 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____5745 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____5750 ->
          failwith "todo: translate_pat [MLP_Branch]"

and translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____5760) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____5775 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____5776 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____5777 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____5778 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (s,FStar_Pervasives_Native.None ) ->
        EConstant (CInt, s)

and mk_op_app :
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr
  =
  fun env  ->
    fun w  ->
      fun op  ->
        fun args  ->
          let uu____5798 =
            let uu____5805 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____5805)  in
          EApp uu____5798
