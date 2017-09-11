open Prims
type decl =
  | DGlobal of
  (flag Prims.list,(Prims.string Prims.list,Prims.string)
                     FStar_Pervasives_Native.tuple2,typ,expr)
  FStar_Pervasives_Native.tuple4 
  | DFunction of
  (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,(Prims.string
                                                                    Prims.list,
                                                                    Prims.string)
                                                                    FStar_Pervasives_Native.tuple2,
  binder Prims.list,expr) FStar_Pervasives_Native.tuple7 
  | DTypeAlias of
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
  Prims.int,typ) FStar_Pervasives_Native.tuple3 
  | DTypeFlat of
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
  Prims.int,(Prims.string,(typ,Prims.bool) FStar_Pervasives_Native.tuple2)
              FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple3 
  | DExternal of
  (cc FStar_Pervasives_Native.option,(Prims.string Prims.list,Prims.string)
                                       FStar_Pervasives_Native.tuple2,
  typ) FStar_Pervasives_Native.tuple3 
  | DTypeVariant of
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
  Prims.int,(Prims.string,(Prims.string,(typ,Prims.bool)
                                          FStar_Pervasives_Native.tuple2)
                            FStar_Pervasives_Native.tuple2 Prims.list)
              FStar_Pervasives_Native.tuple2 Prims.list)
  FStar_Pervasives_Native.tuple3 
and cc =
  | StdCall 
  | CDecl 
  | FastCall 
and flag =
  | Private 
  | NoExtract 
  | CInline 
  | Substitute 
and lifetime =
  | Eternal 
  | Stack 
and expr =
  | EBound of Prims.int 
  | EQualified of (Prims.string Prims.list,Prims.string)
  FStar_Pervasives_Native.tuple2 
  | EConstant of (width,Prims.string) FStar_Pervasives_Native.tuple2 
  | EUnit 
  | EApp of (expr,expr Prims.list) FStar_Pervasives_Native.tuple2 
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
  | Int 
  | UInt 
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
  | TZ 
  | TBound of Prims.int 
  | TApp of
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
  typ Prims.list) FStar_Pervasives_Native.tuple2 
  | TTuple of typ Prims.list 
let uu___is_DGlobal : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DGlobal _0 -> true | uu____506 -> false
  
let __proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,typ,expr)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let uu___is_DFunction : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____594 -> false
  
let __proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr) FStar_Pervasives_Native.tuple7
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let uu___is_DTypeAlias : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____698 -> false
  
let __proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      Prims.int,typ) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let uu___is_DTypeFlat : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____770 -> false
  
let __proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      Prims.int,(Prims.string,(typ,Prims.bool) FStar_Pervasives_Native.tuple2)
                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let uu___is_DExternal : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____864 -> false
  
let __proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,(Prims.string Prims.list,Prims.string)
                                         FStar_Pervasives_Native.tuple2,
      typ) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let uu___is_DTypeVariant : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____948 -> false
  
let __proj__DTypeVariant__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      Prims.int,(Prims.string,(Prims.string,(typ,Prims.bool)
                                              FStar_Pervasives_Native.tuple2)
                                FStar_Pervasives_Native.tuple2 Prims.list)
                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DTypeVariant _0 -> _0 
let uu___is_StdCall : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1045 -> false
  
let uu___is_CDecl : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1050 -> false
  
let uu___is_FastCall : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1055 -> false
  
let uu___is_Private : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1060 -> false
  
let uu___is_NoExtract : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____1065 -> false
  
let uu___is_CInline : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1070 -> false
  
let uu___is_Substitute : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1075 -> false
  
let uu___is_Eternal : lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1080 -> false
  
let uu___is_Stack : lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1085 -> false
  
let uu___is_EBound : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1091 -> false
  
let __proj__EBound__item___0 : expr -> Prims.int =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let uu___is_EQualified : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1111 -> false
  
let __proj__EQualified__item___0 :
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EQualified _0 -> _0 
let uu___is_EConstant : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1147 -> false
  
let __proj__EConstant__item___0 :
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let uu___is_EUnit : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1172 -> false
  
let uu___is_EApp : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1184 -> false
  
let __proj__EApp__item___0 :
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let uu___is_ELet : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1222 -> false
  
let __proj__ELet__item___0 :
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let uu___is_EIfThenElse : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1260 -> false
  
let __proj__EIfThenElse__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let uu___is_ESequence : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1294 -> false
  
let __proj__ESequence__item___0 : expr -> expr Prims.list =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let uu___is_EAssign : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1318 -> false
  
let __proj__EAssign__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let uu___is_EBufCreate : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____1350 -> false
  
let __proj__EBufCreate__item___0 :
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let uu___is_EBufRead : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____1386 -> false
  
let __proj__EBufRead__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let uu___is_EBufWrite : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____1418 -> false
  
let __proj__EBufWrite__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let uu___is_EBufSub : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____1454 -> false
  
let __proj__EBufSub__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let uu___is_EBufBlit : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____1490 -> false
  
let __proj__EBufBlit__item___0 :
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5 =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let uu___is_EMatch : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____1544 -> false
  
let __proj__EMatch__item___0 :
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let uu___is_EOp : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1592 -> false
  
let __proj__EOp__item___0 : expr -> (op,width) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EOp _0 -> _0 
let uu___is_ECast : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1622 -> false
  
let __proj__ECast__item___0 :
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let uu___is_EPushFrame : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1647 -> false
  
let uu___is_EPopFrame : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1652 -> false
  
let uu___is_EBool : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1658 -> false
  
let __proj__EBool__item___0 : expr -> Prims.bool =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let uu___is_EAny : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1671 -> false
  
let uu___is_EAbort : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1676 -> false
  
let uu___is_EReturn : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1682 -> false
  
let __proj__EReturn__item___0 : expr -> expr =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let uu___is_EFlat : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1706 -> false
  
let __proj__EFlat__item___0 :
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EFlat _0 -> _0 
let uu___is_EField : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____1756 -> false
  
let __proj__EField__item___0 :
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EField _0 -> _0 
let uu___is_EWhile : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____1792 -> false
  
let __proj__EWhile__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let uu___is_EBufCreateL : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____1824 -> false
  
let __proj__EBufCreateL__item___0 :
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let uu___is_ETuple : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____1858 -> false
  
let __proj__ETuple__item___0 : expr -> expr Prims.list =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let uu___is_ECons : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____1886 -> false
  
let __proj__ECons__item___0 :
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let uu___is_EBufFill : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____1930 -> false
  
let __proj__EBufFill__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let uu___is_EString : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____1962 -> false
  
let __proj__EString__item___0 : expr -> Prims.string =
  fun projectee  -> match projectee with | EString _0 -> _0 
let uu___is_EFun : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____1984 -> false
  
let __proj__EFun__item___0 :
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let uu___is_EAbortS : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2022 -> false
  
let __proj__EAbortS__item___0 : expr -> Prims.string =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let uu___is_Add : op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____2035 -> false 
let uu___is_AddW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2040 -> false
  
let uu___is_Sub : op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____2045 -> false 
let uu___is_SubW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2050 -> false
  
let uu___is_Div : op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____2055 -> false 
let uu___is_DivW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2060 -> false
  
let uu___is_Mult : op -> Prims.bool =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2065 -> false
  
let uu___is_MultW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2070 -> false
  
let uu___is_Mod : op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____2075 -> false 
let uu___is_BOr : op -> Prims.bool =
  fun projectee  -> match projectee with | BOr  -> true | uu____2080 -> false 
let uu___is_BAnd : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2085 -> false
  
let uu___is_BXor : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2090 -> false
  
let uu___is_BShiftL : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2095 -> false
  
let uu___is_BShiftR : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2100 -> false
  
let uu___is_BNot : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2105 -> false
  
let uu___is_Eq : op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2110 -> false 
let uu___is_Neq : op -> Prims.bool =
  fun projectee  -> match projectee with | Neq  -> true | uu____2115 -> false 
let uu___is_Lt : op -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2120 -> false 
let uu___is_Lte : op -> Prims.bool =
  fun projectee  -> match projectee with | Lte  -> true | uu____2125 -> false 
let uu___is_Gt : op -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2130 -> false 
let uu___is_Gte : op -> Prims.bool =
  fun projectee  -> match projectee with | Gte  -> true | uu____2135 -> false 
let uu___is_And : op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____2140 -> false 
let uu___is_Or : op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____2145 -> false 
let uu___is_Xor : op -> Prims.bool =
  fun projectee  -> match projectee with | Xor  -> true | uu____2150 -> false 
let uu___is_Not : op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____2155 -> false 
let uu___is_PUnit : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2160 -> false
  
let uu___is_PBool : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2166 -> false
  
let __proj__PBool__item___0 : pattern -> Prims.bool =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let uu___is_PVar : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2180 -> false
  
let __proj__PVar__item___0 : pattern -> binder =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let uu___is_PCons : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2200 -> false
  
let __proj__PCons__item___0 :
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PCons _0 -> _0 
let uu___is_PTuple : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2234 -> false
  
let __proj__PTuple__item___0 : pattern -> pattern Prims.list =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let uu___is_PRecord : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2260 -> false
  
let __proj__PRecord__item___0 :
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list
  = fun projectee  -> match projectee with | PRecord _0 -> _0 
let uu___is_UInt8 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____2291 -> false
  
let uu___is_UInt16 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2296 -> false
  
let uu___is_UInt32 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2301 -> false
  
let uu___is_UInt64 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2306 -> false
  
let uu___is_Int8 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2311 -> false
  
let uu___is_Int16 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2316 -> false
  
let uu___is_Int32 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2321 -> false
  
let uu___is_Int64 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2326 -> false
  
let uu___is_Bool : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2331 -> false
  
let uu___is_Int : width -> Prims.bool =
  fun projectee  -> match projectee with | Int  -> true | uu____2336 -> false 
let uu___is_UInt : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt  -> true | uu____2341 -> false
  
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
    match projectee with | TInt _0 -> true | uu____2368 -> false
  
let __proj__TInt__item___0 : typ -> width =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let uu___is_TBuf : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2382 -> false
  
let __proj__TBuf__item___0 : typ -> typ =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let uu___is_TUnit : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2395 -> false
  
let uu___is_TQualified : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2407 -> false
  
let __proj__TQualified__item___0 :
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TQualified _0 -> _0 
let uu___is_TBool : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2438 -> false
  
let uu___is_TAny : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2443 -> false
  
let uu___is_TArrow : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2453 -> false
  
let __proj__TArrow__item___0 :
  typ -> (typ,typ) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let uu___is_TZ : typ -> Prims.bool =
  fun projectee  -> match projectee with | TZ  -> true | uu____2478 -> false 
let uu___is_TBound : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2484 -> false
  
let __proj__TBound__item___0 : typ -> Prims.int =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let uu___is_TApp : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2510 -> false
  
let __proj__TApp__item___0 :
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TApp _0 -> _0 
let uu___is_TTuple : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____2562 -> false
  
let __proj__TTuple__item___0 : typ -> typ Prims.list =
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
type branch = (pattern,expr) FStar_Pervasives_Native.tuple2
type branches = (pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list
type constant = (width,Prims.string) FStar_Pervasives_Native.tuple2
type var = Prims.int
type lident =
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
type version = Prims.int
let current_version : version = (Prims.parse_int "21") 
type file = (Prims.string,program) FStar_Pervasives_Native.tuple2
type binary_format = (version,file Prims.list) FStar_Pervasives_Native.tuple2
let fst3 :
  'Auu____2643 'Auu____2644 'Auu____2645 .
    ('Auu____2645,'Auu____2644,'Auu____2643) FStar_Pervasives_Native.tuple3
      -> 'Auu____2645
  = fun uu____2655  -> match uu____2655 with | (x,uu____2663,uu____2664) -> x 
let snd3 :
  'Auu____2673 'Auu____2674 'Auu____2675 .
    ('Auu____2675,'Auu____2674,'Auu____2673) FStar_Pervasives_Native.tuple3
      -> 'Auu____2674
  = fun uu____2685  -> match uu____2685 with | (uu____2692,x,uu____2694) -> x 
let thd3 :
  'Auu____2703 'Auu____2704 'Auu____2705 .
    ('Auu____2705,'Auu____2704,'Auu____2703) FStar_Pervasives_Native.tuple3
      -> 'Auu____2703
  = fun uu____2715  -> match uu____2715 with | (uu____2722,uu____2723,x) -> x 
let mk_width : Prims.string -> width FStar_Pervasives_Native.option =
  fun uu___124_2730  ->
    match uu___124_2730 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____2733 -> FStar_Pervasives_Native.None
  
let mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___125_2739  ->
    match uu___125_2739 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____2742 -> FStar_Pervasives_Native.None
  
let is_bool_op : Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let mk_op : Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___126_2754  ->
    match uu___126_2754 with
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
    | uu____2757 -> FStar_Pervasives_Native.None
  
let is_op : Prims.string -> Prims.bool =
  fun op  -> (mk_op op) <> FStar_Pervasives_Native.None 
let is_machine_int : Prims.string -> Prims.bool =
  fun m  -> (mk_width m) <> FStar_Pervasives_Native.None 
type env =
  {
  names: name Prims.list ;
  names_t: Prims.string Prims.list ;
  module_name: Prims.string Prims.list }
and name = {
  pretty: Prims.string ;
  mut: Prims.bool }
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
        let uu___131_2879 = env  in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___131_2879.names_t);
          module_name = (uu___131_2879.module_name)
        }
  
let extend_t : env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___132_2888 = env  in
      {
        names = (uu___132_2888.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___132_2888.module_name)
      }
  
let find_name : env -> Prims.string -> name =
  fun env  ->
    fun x  ->
      let uu____2897 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____2897 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let is_mutable : env -> Prims.string -> Prims.bool =
  fun env  -> fun x  -> let uu____2911 = find_name env x  in uu____2911.mut 
let find : env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____2928 ->
          let uu____2929 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____2929
  
let find_t : env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____2946 ->
          let uu____2947 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____2947
  
let add_binders :
  'Auu____2956 'Auu____2957 .
    env ->
      ((Prims.string,'Auu____2957) FStar_Pervasives_Native.tuple2,'Auu____2956)
        FStar_Pervasives_Native.tuple2 Prims.list -> env
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____3000  ->
             match uu____3000 with
             | ((name,uu____3010),uu____3011) -> extend env1 name false) env
        binders
  
let rec translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____3140  ->
    match uu____3140 with
    | FStar_Extraction_ML_Syntax.MLLib modules1 ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3200 = m  in
               match uu____3200 with
               | ((prefix1,final),uu____3221,uu____3222) ->
                   FStar_String.concat "."
                     (FStar_List.append prefix1 [final])
                in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____3254 = translate_module m  in
                FStar_Pervasives_Native.Some uu____3254)
             with
             | e ->
                 ((let uu____3263 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3263);
                  FStar_Pervasives_Native.None)) modules1

and translate_module :
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
    (FStar_Extraction_ML_Syntax.mlsig,FStar_Extraction_ML_Syntax.mlmodule)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,FStar_Extraction_ML_Syntax.mllib)
    FStar_Pervasives_Native.tuple3 -> file
  =
  fun uu____3264  ->
    match uu____3264 with
    | (module_name,modul,uu____3285) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.filter_map (translate_decl (empty module_name1))
                decls
          | uu____3328 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and translate_flags :
  FStar_Extraction_ML_Syntax.c_flag Prims.list -> flag Prims.list =
  fun flags  ->
    FStar_List.choose
      (fun uu___127_3343  ->
         match uu___127_3343 with
         | FStar_Extraction_ML_Syntax.Private  ->
             FStar_Pervasives_Native.Some Private
         | FStar_Extraction_ML_Syntax.NoExtract  ->
             FStar_Pervasives_Native.Some NoExtract
         | FStar_Extraction_ML_Syntax.Attribute "c_inline" ->
             FStar_Pervasives_Native.Some CInline
         | FStar_Extraction_ML_Syntax.Attribute "substitute" ->
             FStar_Pervasives_Native.Some Substitute
         | FStar_Extraction_ML_Syntax.Attribute a ->
             (FStar_Util.print1_warning "Warning: unrecognized attribute %s"
                a;
              FStar_Pervasives_Native.None)
         | uu____3348 -> FStar_Pervasives_Native.None) flags

and translate_decl :
  env ->
    FStar_Extraction_ML_Syntax.mlmodule1 ->
      decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____3356);
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3359;
                          FStar_Extraction_ML_Syntax.mllb_def =
                            {
                              FStar_Extraction_ML_Syntax.expr =
                                FStar_Extraction_ML_Syntax.MLE_Fun
                                (args,body);
                              FStar_Extraction_ML_Syntax.mlty = uu____3362;
                              FStar_Extraction_ML_Syntax.loc = uu____3363;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____3364;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___128_3385  ->
                 match uu___128_3385 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____3386 -> false) flags
             in
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env  in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun uu____3399  ->
                   match uu____3399 with
                   | (name1,uu____3405) -> extend_t env2 name1) env1 tvars
             in
          let rec find_return_type i uu___129_3412 =
            match uu___129_3412 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3413,uu____3414,t)
                when i > (Prims.parse_int "0") ->
                find_return_type (i - (Prims.parse_int "1")) t
            | t -> t  in
          let t =
            let uu____3418 = find_return_type (FStar_List.length args) t0  in
            translate_type env2 uu____3418  in
          let binders = translate_binders env2 args  in
          let env3 = add_binders env2 args  in
          let name1 = ((env3.module_name), name)  in
          let flags1 = translate_flags flags  in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
               let uu____3443 =
                 let uu____3444 =
                   let uu____3459 = translate_type env3 t0  in
                   (FStar_Pervasives_Native.None, name1, uu____3459)  in
                 DExternal uu____3444  in
               FStar_Pervasives_Native.Some uu____3443
             else FStar_Pervasives_Native.None)
          else
            (try
               let body1 = translate_expr env3 body  in
               FStar_Pervasives_Native.Some
                 (DFunction
                    (FStar_Pervasives_Native.None, flags1,
                      (FStar_List.length tvars), t, name1, binders, body1))
             with
             | e ->
                 let msg = FStar_Util.print_exn e  in
                 (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n"
                    (FStar_Pervasives_Native.snd name1) msg;
                  (let msg1 =
                     Prims.strcat "This function was not extracted:\n" msg
                      in
                   FStar_Pervasives_Native.Some
                     (DFunction
                        (FStar_Pervasives_Native.None, flags1,
                          (FStar_List.length tvars), t, name1, binders,
                          (EAbortS msg1))))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____3519);
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3522;
                          FStar_Extraction_ML_Syntax.mllb_def =
                            {
                              FStar_Extraction_ML_Syntax.expr =
                                FStar_Extraction_ML_Syntax.MLE_Coerce
                                ({
                                   FStar_Extraction_ML_Syntax.expr =
                                     FStar_Extraction_ML_Syntax.MLE_Fun
                                     (args,body);
                                   FStar_Extraction_ML_Syntax.mlty =
                                     uu____3525;
                                   FStar_Extraction_ML_Syntax.loc =
                                     uu____3526;_},uu____3527,uu____3528);
                              FStar_Extraction_ML_Syntax.mlty = uu____3529;
                              FStar_Extraction_ML_Syntax.loc = uu____3530;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____3531;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___128_3552  ->
                 match uu___128_3552 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____3553 -> false) flags
             in
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env  in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun uu____3566  ->
                   match uu____3566 with
                   | (name1,uu____3572) -> extend_t env2 name1) env1 tvars
             in
          let rec find_return_type i uu___129_3579 =
            match uu___129_3579 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3580,uu____3581,t)
                when i > (Prims.parse_int "0") ->
                find_return_type (i - (Prims.parse_int "1")) t
            | t -> t  in
          let t =
            let uu____3585 = find_return_type (FStar_List.length args) t0  in
            translate_type env2 uu____3585  in
          let binders = translate_binders env2 args  in
          let env3 = add_binders env2 args  in
          let name1 = ((env3.module_name), name)  in
          let flags1 = translate_flags flags  in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
               let uu____3610 =
                 let uu____3611 =
                   let uu____3626 = translate_type env3 t0  in
                   (FStar_Pervasives_Native.None, name1, uu____3626)  in
                 DExternal uu____3611  in
               FStar_Pervasives_Native.Some uu____3610
             else FStar_Pervasives_Native.None)
          else
            (try
               let body1 = translate_expr env3 body  in
               FStar_Pervasives_Native.Some
                 (DFunction
                    (FStar_Pervasives_Native.None, flags1,
                      (FStar_List.length tvars), t, name1, binders, body1))
             with
             | e ->
                 let msg = FStar_Util.print_exn e  in
                 (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n"
                    (FStar_Pervasives_Native.snd name1) msg;
                  (let msg1 =
                     Prims.strcat "This function was not extracted:\n" msg
                      in
                   FStar_Pervasives_Native.Some
                     (DFunction
                        (FStar_Pervasives_Native.None, flags1,
                          (FStar_List.length tvars), t, name1, binders,
                          (EAbortS msg1))))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (flavor,flags,{
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (name,uu____3686);
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some ([],t);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3688;
                          FStar_Extraction_ML_Syntax.mllb_def = expr;
                          FStar_Extraction_ML_Syntax.print_typ = uu____3690;_}::[])
          ->
          let flags1 = translate_flags flags  in
          let t1 = translate_type env t  in
          let name1 = ((env.module_name), name)  in
          (try
             let expr1 = translate_expr env expr  in
             FStar_Pervasives_Native.Some
               (DGlobal (flags1, name1, t1, expr1))
           with
           | e ->
               ((let uu____3738 = FStar_Util.print_exn e  in
                 FStar_Util.print2
                   "Warning: not translating definition for %s (%s)\n"
                   (FStar_Pervasives_Native.snd name1) uu____3738);
                FStar_Pervasives_Native.Some
                  (DGlobal (flags1, name1, t1, EAny))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (uu____3749,uu____3750,{
                                   FStar_Extraction_ML_Syntax.mllb_name =
                                     (name,uu____3752);
                                   FStar_Extraction_ML_Syntax.mllb_tysc = ts;
                                   FStar_Extraction_ML_Syntax.mllb_add_unit =
                                     uu____3754;
                                   FStar_Extraction_ML_Syntax.mllb_def =
                                     uu____3755;
                                   FStar_Extraction_ML_Syntax.print_typ =
                                     uu____3756;_}::uu____3757)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           (match ts with
            | FStar_Pervasives_Native.Some (idents,t) ->
                let uu____3772 =
                  let uu____3773 =
                    FStar_List.map FStar_Pervasives_Native.fst idents  in
                  FStar_String.concat ", " uu____3773  in
                let uu____3780 =
                  FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                  uu____3772 uu____3780
            | FStar_Pervasives_Native.None  -> ());
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Let uu____3783 ->
          failwith "impossible"
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3786 ->
          FStar_Pervasives_Native.None
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((assumed,name,_mangled_name,args,uu____3791,FStar_Pervasives_Native.Some
            (FStar_Extraction_ML_Syntax.MLTD_Abbrev t))::[])
          ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____3850  ->
                   match uu____3850 with
                   | (name2,uu____3856) -> extend_t env1 name2) env args
             in
          if assumed
          then FStar_Pervasives_Native.None
          else
            (let uu____3860 =
               let uu____3861 =
                 let uu____3874 = translate_type env1 t  in
                 (name1, (FStar_List.length args), uu____3874)  in
               DTypeAlias uu____3861  in
             FStar_Pervasives_Native.Some uu____3860)
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____3881,name,_mangled_name,args,uu____3885,FStar_Pervasives_Native.Some
            (FStar_Extraction_ML_Syntax.MLTD_Record fields))::[])
          ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____3950  ->
                   match uu____3950 with
                   | (name2,uu____3956) -> extend_t env1 name2) env args
             in
          let uu____3957 =
            let uu____3958 =
              let uu____3981 =
                FStar_List.map
                  (fun uu____4008  ->
                     match uu____4008 with
                     | (f,t) ->
                         let uu____4023 =
                           let uu____4028 = translate_type env1 t  in
                           (uu____4028, false)  in
                         (f, uu____4023)) fields
                 in
              (name1, (FStar_List.length args), uu____3981)  in
            DTypeFlat uu____3958  in
          FStar_Pervasives_Native.Some uu____3957
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____4049,name,_mangled_name,args,uu____4053,FStar_Pervasives_Native.Some
            (FStar_Extraction_ML_Syntax.MLTD_DType branches))::[])
          ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____4124  ->
                   match uu____4124 with
                   | (name2,uu____4130) -> extend_t env1 name2) env args
             in
          let uu____4131 =
            let uu____4132 =
              let uu____4161 =
                FStar_List.map
                  (fun uu____4206  ->
                     match uu____4206 with
                     | (cons1,ts) ->
                         let uu____4245 =
                           FStar_List.map
                             (fun uu____4272  ->
                                match uu____4272 with
                                | (name2,t) ->
                                    let uu____4287 =
                                      let uu____4292 = translate_type env1 t
                                         in
                                      (uu____4292, false)  in
                                    (name2, uu____4287)) ts
                            in
                         (cons1, uu____4245)) branches
                 in
              (name1, (FStar_List.length args), uu____4161)  in
            DTypeVariant uu____4132  in
          FStar_Pervasives_Native.Some uu____4131
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____4329,name,_mangled_name,uu____4332,uu____4333,uu____4334)::uu____4335)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Ty [] ->
          (FStar_Util.print_string
             "Impossible!! Empty block of mutually recursive type declarations";
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Top uu____4380 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____4383 ->
          failwith "todo: translate_decl [MLM_Exn]"

and translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var (name,uu____4399) ->
          let uu____4400 = find_t env name  in TBound uu____4400
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4402,t2) ->
          let uu____4404 =
            let uu____4409 = translate_type env t1  in
            let uu____4410 = translate_type env t2  in
            (uu____4409, uu____4410)  in
          TArrow uu____4404
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4414 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4414 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4418 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4418 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4430 = FStar_Util.must (mk_width m)  in TInt uu____4430
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4442 = FStar_Util.must (mk_width m)  in TInt uu____4442
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4447 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4447 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4452 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4452 = "FStar.Buffer.buffer" ->
          let uu____4453 = translate_type env arg  in TBuf uu____4453
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4454::[],p) when
          let uu____4458 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4458 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4496 = FStar_List.map (translate_type env) args  in
          TTuple uu____4496
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4505 =
              let uu____4518 = FStar_List.map (translate_type env) args  in
              (lid, uu____4518)  in
            TApp uu____4505
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4527 = FStar_List.map (translate_type env) ts  in
          TTuple uu____4527

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
    fun uu____4543  ->
      match uu____4543 with
      | ((name,uu____4549),typ) ->
          let uu____4555 = translate_type env typ  in
          { name; typ = uu____4555; mut = false }

and translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____4560) ->
          let uu____4561 = find env name  in EBound uu____4561
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4566 =
            let uu____4571 = FStar_Util.must (mk_op op)  in
            let uu____4572 = FStar_Util.must (mk_width m)  in
            (uu____4571, uu____4572)  in
          EOp uu____4566
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4576 =
            let uu____4581 = FStar_Util.must (mk_bool_op op)  in
            (uu____4581, Bool)  in
          EOp uu____4576
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags,{
                           FStar_Extraction_ML_Syntax.mllb_name =
                             (name,uu____4586);
                           FStar_Extraction_ML_Syntax.mllb_tysc =
                             FStar_Pervasives_Native.Some ([],typ);
                           FStar_Extraction_ML_Syntax.mllb_add_unit =
                             add_unit;
                           FStar_Extraction_ML_Syntax.mllb_def = body;
                           FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let is_mut =
            FStar_Util.for_some
              (fun uu___130_4612  ->
                 match uu___130_4612 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____4613 -> false) flags
             in
          let uu____4614 =
            if is_mut
            then
              let uu____4623 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____4628 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4628 = "FStar.ST.stackref" -> t
                | uu____4629 ->
                    let uu____4630 =
                      let uu____4631 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ
                         in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____4631
                       in
                    failwith uu____4630
                 in
              let uu____4634 =
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
                      (uu____4635,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____4637;
                    FStar_Extraction_ML_Syntax.loc = uu____4638;_} -> body1
                | uu____4641 ->
                    failwith "unexpected: bad desugaring of Mutable"
                 in
              (uu____4623, uu____4634)
            else (typ, body)  in
          (match uu____4614 with
           | (typ1,body1) ->
               let binder =
                 let uu____4646 = translate_type env typ1  in
                 { name; typ = uu____4646; mut = is_mut }  in
               let body2 = translate_expr env body1  in
               let env1 = extend env name is_mut  in
               let continuation1 = translate_expr env1 continuation  in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4672 =
            let uu____4683 = translate_expr env expr  in
            let uu____4684 = translate_branches env branches  in
            (uu____4683, uu____4684)  in
          EMatch uu____4672
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4698;
             FStar_Extraction_ML_Syntax.loc = uu____4699;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____4701);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4702;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4703;_}::[])
          when
          (let uu____4708 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4708 = "FStar.HyperStack.ST.op_Bang") && (is_mutable env v1)
          -> let uu____4709 = find env v1  in EBound uu____4709
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4711;
             FStar_Extraction_ML_Syntax.loc = uu____4712;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____4714);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4715;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4716;_}::e1::[])
          when
          (let uu____4722 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4722 = "FStar.HyperStack.ST.op_Colon_Equals") &&
            (is_mutable env v1)
          ->
          let uu____4723 =
            let uu____4728 =
              let uu____4729 = find env v1  in EBound uu____4729  in
            let uu____4730 = translate_expr env e1  in
            (uu____4728, uu____4730)  in
          EAssign uu____4723
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4732;
             FStar_Extraction_ML_Syntax.loc = uu____4733;_},e1::e2::[])
          when
          (let uu____4740 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4740 = "FStar.Buffer.index") ||
            (let uu____4742 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4742 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____4743 =
            let uu____4748 = translate_expr env e1  in
            let uu____4749 = translate_expr env e2  in
            (uu____4748, uu____4749)  in
          EBufRead uu____4743
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4751;
             FStar_Extraction_ML_Syntax.loc = uu____4752;_},e1::e2::[])
          when
          let uu____4757 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4757 = "FStar.Buffer.create" ->
          let uu____4758 =
            let uu____4765 = translate_expr env e1  in
            let uu____4766 = translate_expr env e2  in
            (Stack, uu____4765, uu____4766)  in
          EBufCreate uu____4758
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4768;
             FStar_Extraction_ML_Syntax.loc = uu____4769;_},_e0::e1::e2::[])
          when
          let uu____4775 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4775 = "FStar.Buffer.rcreate" ->
          let uu____4776 =
            let uu____4783 = translate_expr env e1  in
            let uu____4784 = translate_expr env e2  in
            (Eternal, uu____4783, uu____4784)  in
          EBufCreate uu____4776
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4786;
             FStar_Extraction_ML_Syntax.loc = uu____4787;_},e2::[])
          when
          let uu____4791 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4791 = "FStar.Buffer.createL" ->
          let rec list_elements1 acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements1 (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____4829 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!"
             in
          let list_elements2 = list_elements1 []  in
          let uu____4837 =
            let uu____4844 =
              let uu____4847 = list_elements2 e2  in
              FStar_List.map (translate_expr env) uu____4847  in
            (Stack, uu____4844)  in
          EBufCreateL uu____4837
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4853;
             FStar_Extraction_ML_Syntax.loc = uu____4854;_},e1::e2::_e3::[])
          when
          let uu____4860 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4860 = "FStar.Buffer.sub" ->
          let uu____4861 =
            let uu____4866 = translate_expr env e1  in
            let uu____4867 = translate_expr env e2  in
            (uu____4866, uu____4867)  in
          EBufSub uu____4861
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4869;
             FStar_Extraction_ML_Syntax.loc = uu____4870;_},e1::e2::[])
          when
          let uu____4875 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4875 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4877;
             FStar_Extraction_ML_Syntax.loc = uu____4878;_},e1::e2::[])
          when
          let uu____4883 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4883 = "FStar.Buffer.offset" ->
          let uu____4884 =
            let uu____4889 = translate_expr env e1  in
            let uu____4890 = translate_expr env e2  in
            (uu____4889, uu____4890)  in
          EBufSub uu____4884
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4892;
             FStar_Extraction_ML_Syntax.loc = uu____4893;_},e1::e2::e3::[])
          when
          (let uu____4901 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4901 = "FStar.Buffer.upd") ||
            (let uu____4903 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4903 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____4904 =
            let uu____4911 = translate_expr env e1  in
            let uu____4912 = translate_expr env e2  in
            let uu____4913 = translate_expr env e3  in
            (uu____4911, uu____4912, uu____4913)  in
          EBufWrite uu____4904
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4915;
             FStar_Extraction_ML_Syntax.loc = uu____4916;_},uu____4917::[])
          when
          let uu____4920 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4920 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4922;
             FStar_Extraction_ML_Syntax.loc = uu____4923;_},uu____4924::[])
          when
          let uu____4927 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4927 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4929;
             FStar_Extraction_ML_Syntax.loc = uu____4930;_},e1::e2::e3::e4::e5::[])
          when
          let uu____4938 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4938 = "FStar.Buffer.blit" ->
          let uu____4939 =
            let uu____4950 = translate_expr env e1  in
            let uu____4951 = translate_expr env e2  in
            let uu____4952 = translate_expr env e3  in
            let uu____4953 = translate_expr env e4  in
            let uu____4954 = translate_expr env e5  in
            (uu____4950, uu____4951, uu____4952, uu____4953, uu____4954)  in
          EBufBlit uu____4939
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4956;
             FStar_Extraction_ML_Syntax.loc = uu____4957;_},e1::e2::e3::[])
          when
          let uu____4963 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4963 = "FStar.Buffer.fill" ->
          let uu____4964 =
            let uu____4971 = translate_expr env e1  in
            let uu____4972 = translate_expr env e2  in
            let uu____4973 = translate_expr env e3  in
            (uu____4971, uu____4972, uu____4973)  in
          EBufFill uu____4964
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4975;
             FStar_Extraction_ML_Syntax.loc = uu____4976;_},uu____4977::[])
          when
          let uu____4980 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4980 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4982;
             FStar_Extraction_ML_Syntax.loc = uu____4983;_},e1::[])
          when
          let uu____4987 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4987 = "Obj.repr" ->
          let uu____4988 =
            let uu____4993 = translate_expr env e1  in (uu____4993, TAny)  in
          ECast uu____4988
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____4996;
             FStar_Extraction_ML_Syntax.loc = uu____4997;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5005 = FStar_Util.must (mk_width m)  in
          let uu____5006 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____5005 uu____5006 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5008;
             FStar_Extraction_ML_Syntax.loc = uu____5009;_},args)
          when is_bool_op op ->
          let uu____5017 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____5017 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5019;
             FStar_Extraction_ML_Syntax.loc = uu____5020;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5022;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5023;_}::[])
          when is_machine_int m ->
          let uu____5038 =
            let uu____5043 = FStar_Util.must (mk_width m)  in (uu____5043, c)
             in
          EConstant uu____5038
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5045;
             FStar_Extraction_ML_Syntax.loc = uu____5046;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5048;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5049;_}::[])
          when is_machine_int m ->
          let uu____5064 =
            let uu____5069 = FStar_Util.must (mk_width m)  in (uu____5069, c)
             in
          EConstant uu____5064
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5070;
             FStar_Extraction_ML_Syntax.loc = uu____5071;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5073;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5074;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5080 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5082;
             FStar_Extraction_ML_Syntax.loc = uu____5083;_},arg::[])
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
            let uu____5090 =
              let uu____5095 = translate_expr env arg  in
              (uu____5095, (TInt UInt64))  in
            ECast uu____5090
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5097 =
                 let uu____5102 = translate_expr env arg  in
                 (uu____5102, (TInt UInt32))  in
               ECast uu____5097)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5104 =
                   let uu____5109 = translate_expr env arg  in
                   (uu____5109, (TInt UInt16))  in
                 ECast uu____5104)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5111 =
                     let uu____5116 = translate_expr env arg  in
                     (uu____5116, (TInt UInt8))  in
                   ECast uu____5111)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5118 =
                       let uu____5123 = translate_expr env arg  in
                       (uu____5123, (TInt Int64))  in
                     ECast uu____5118)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5125 =
                         let uu____5130 = translate_expr env arg  in
                         (uu____5130, (TInt Int32))  in
                       ECast uu____5125)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5132 =
                           let uu____5137 = translate_expr env arg  in
                           (uu____5137, (TInt Int16))  in
                         ECast uu____5132)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5139 =
                             let uu____5144 = translate_expr env arg  in
                             (uu____5144, (TInt Int8))  in
                           ECast uu____5139)
                        else
                          (let uu____5146 =
                             let uu____5153 =
                               let uu____5156 = translate_expr env arg  in
                               [uu____5156]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5153)
                              in
                           EApp uu____5146)
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name (path,function_name);
             FStar_Extraction_ML_Syntax.mlty = uu____5163;
             FStar_Extraction_ML_Syntax.loc = uu____5164;_},args)
          ->
          let uu____5174 =
            let uu____5181 = FStar_List.map (translate_expr env) args  in
            ((EQualified (path, function_name)), uu____5181)  in
          EApp uu____5174
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Var (name,uu____5189);
             FStar_Extraction_ML_Syntax.mlty = uu____5190;
             FStar_Extraction_ML_Syntax.loc = uu____5191;_},args)
          ->
          let uu____5197 =
            let uu____5204 =
              let uu____5205 = find env name  in EBound uu____5205  in
            let uu____5206 = FStar_List.map (translate_expr env) args  in
            (uu____5204, uu____5206)  in
          EApp uu____5197
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5214 =
            let uu____5219 = translate_expr env e1  in
            let uu____5220 = translate_type env t_to  in
            (uu____5219, uu____5220)  in
          ECast uu____5214
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5221,fields) ->
          let uu____5239 =
            let uu____5250 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5251 =
              FStar_List.map
                (fun uu____5270  ->
                   match uu____5270 with
                   | (field,expr) ->
                       let uu____5281 = translate_expr env expr  in
                       (field, uu____5281)) fields
               in
            (uu____5250, uu____5251)  in
          EFlat uu____5239
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5290 =
            let uu____5297 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____5298 = translate_expr env e1  in
            (uu____5297, uu____5298, (FStar_Pervasives_Native.snd path))  in
          EField uu____5290
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5301 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5315) ->
          let uu____5320 =
            let uu____5321 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5321
             in
          failwith uu____5320
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5327 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____5327
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5333 = FStar_List.map (translate_expr env) es  in
          ETuple uu____5333
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5336,cons1),es) ->
          let uu____5353 =
            let uu____5362 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5363 = FStar_List.map (translate_expr env) es  in
            (uu____5362, cons1, uu____5363)  in
          ECons uu____5353
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____5386 =
            let uu____5395 = translate_expr env1 body  in
            let uu____5396 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____5395, uu____5396)  in
          EFun uu____5386
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5406 =
            let uu____5413 = translate_expr env e1  in
            let uu____5414 = translate_expr env e2  in
            let uu____5415 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____5413, uu____5414, uu____5415)  in
          EIfThenElse uu____5406
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5417 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5424 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____5439 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____5454 =
              let uu____5467 = FStar_List.map (translate_type env) ts  in
              (lid, uu____5467)  in
            TApp uu____5454
          else TQualified lid
      | uu____5473 -> failwith "invalid argument: assert_lid"

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
    fun uu____5499  ->
      match uu____5499 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____5525 = translate_pat env pat  in
            (match uu____5525 with
             | (env1,pat1) ->
                 let uu____5536 = translate_expr env1 expr  in
                 (pat1, uu____5536))
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
      | FStar_Extraction_ML_Syntax.MLP_Var (name,uu____5550) ->
          let env1 = extend env name false  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_" false  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5553,cons1),ps) ->
          let uu____5570 =
            FStar_List.fold_left
              (fun uu____5590  ->
                 fun p1  ->
                   match uu____5590 with
                   | (env1,acc) ->
                       let uu____5610 = translate_pat env1 p1  in
                       (match uu____5610 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____5570 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____5639,ps) ->
          let uu____5657 =
            FStar_List.fold_left
              (fun uu____5691  ->
                 fun uu____5692  ->
                   match (uu____5691, uu____5692) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____5761 = translate_pat env1 p1  in
                       (match uu____5761 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____5657 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____5823 =
            FStar_List.fold_left
              (fun uu____5843  ->
                 fun p1  ->
                   match uu____5843 with
                   | (env1,acc) ->
                       let uu____5863 = translate_pat env1 p1  in
                       (match uu____5863 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____5823 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____5890 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____5895 ->
          failwith "todo: translate_pat [MLP_Branch]"

and translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____5905) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____5920 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____5921 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____5922 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____5923 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int
        (uu____5926,FStar_Pervasives_Native.None ) ->
        failwith "todo: translate_expr [MLC_Int]"

and mk_op_app :
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr
  =
  fun env  ->
    fun w  ->
      fun op  ->
        fun args  ->
          let uu____5943 =
            let uu____5950 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____5950)  in
          EApp uu____5943
