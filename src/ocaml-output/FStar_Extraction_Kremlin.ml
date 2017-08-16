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
  | NoExtract 
  | CInline 
  | Substitute 
  | GCType 
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
let uu___is_DGlobal : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DGlobal _0 -> true | uu____520 -> false
  
let __proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,typ,expr)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let uu___is_DFunction : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____608 -> false
  
let __proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr) FStar_Pervasives_Native.tuple7
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let uu___is_DTypeAlias : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____712 -> false
  
let __proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      Prims.int,typ) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let uu___is_DTypeFlat : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____784 -> false
  
let __proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      Prims.int,(Prims.string,(typ,Prims.bool) FStar_Pervasives_Native.tuple2)
                  FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let uu___is_DExternal : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____878 -> false
  
let __proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,(Prims.string Prims.list,Prims.string)
                                         FStar_Pervasives_Native.tuple2,
      typ) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let uu___is_DTypeVariant : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____966 -> false
  
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
    match projectee with | StdCall  -> true | uu____1075 -> false
  
let uu___is_CDecl : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1080 -> false
  
let uu___is_FastCall : cc -> Prims.bool =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1085 -> false
  
let uu___is_Private : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1090 -> false
  
let uu___is_NoExtract : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | NoExtract  -> true | uu____1095 -> false
  
let uu___is_CInline : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1100 -> false
  
let uu___is_Substitute : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1105 -> false
  
let uu___is_GCType : flag -> Prims.bool =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1110 -> false
  
let uu___is_Eternal : lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1115 -> false
  
let uu___is_Stack : lifetime -> Prims.bool =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1120 -> false
  
let uu___is_EBound : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1126 -> false
  
let __proj__EBound__item___0 : expr -> Prims.int =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let uu___is_EQualified : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1146 -> false
  
let __proj__EQualified__item___0 :
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EQualified _0 -> _0 
let uu___is_EConstant : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1182 -> false
  
let __proj__EConstant__item___0 :
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let uu___is_EUnit : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1207 -> false
  
let uu___is_EApp : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1219 -> false
  
let __proj__EApp__item___0 :
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let uu___is_ETypApp : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1257 -> false
  
let __proj__ETypApp__item___0 :
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let uu___is_ELet : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1295 -> false
  
let __proj__ELet__item___0 :
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let uu___is_EIfThenElse : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1333 -> false
  
let __proj__EIfThenElse__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let uu___is_ESequence : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1367 -> false
  
let __proj__ESequence__item___0 : expr -> expr Prims.list =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let uu___is_EAssign : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1391 -> false
  
let __proj__EAssign__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let uu___is_EBufCreate : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____1423 -> false
  
let __proj__EBufCreate__item___0 :
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let uu___is_EBufRead : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____1459 -> false
  
let __proj__EBufRead__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let uu___is_EBufWrite : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____1491 -> false
  
let __proj__EBufWrite__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let uu___is_EBufSub : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____1527 -> false
  
let __proj__EBufSub__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let uu___is_EBufBlit : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____1563 -> false
  
let __proj__EBufBlit__item___0 :
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5 =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let uu___is_EMatch : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____1617 -> false
  
let __proj__EMatch__item___0 :
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let uu___is_EOp : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1665 -> false
  
let __proj__EOp__item___0 : expr -> (op,width) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EOp _0 -> _0 
let uu___is_ECast : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1695 -> false
  
let __proj__ECast__item___0 :
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let uu___is_EPushFrame : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1720 -> false
  
let uu___is_EPopFrame : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1725 -> false
  
let uu___is_EBool : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1731 -> false
  
let __proj__EBool__item___0 : expr -> Prims.bool =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let uu___is_EAny : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1744 -> false
  
let uu___is_EAbort : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1749 -> false
  
let uu___is_EReturn : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1755 -> false
  
let __proj__EReturn__item___0 : expr -> expr =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let uu___is_EFlat : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1779 -> false
  
let __proj__EFlat__item___0 :
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | EFlat _0 -> _0 
let uu___is_EField : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____1829 -> false
  
let __proj__EField__item___0 :
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EField _0 -> _0 
let uu___is_EWhile : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____1865 -> false
  
let __proj__EWhile__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let uu___is_EBufCreateL : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____1897 -> false
  
let __proj__EBufCreateL__item___0 :
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let uu___is_ETuple : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____1931 -> false
  
let __proj__ETuple__item___0 : expr -> expr Prims.list =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let uu___is_ECons : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____1959 -> false
  
let __proj__ECons__item___0 :
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let uu___is_EBufFill : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2003 -> false
  
let __proj__EBufFill__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let uu___is_EString : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2035 -> false
  
let __proj__EString__item___0 : expr -> Prims.string =
  fun projectee  -> match projectee with | EString _0 -> _0 
let uu___is_EFun : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2057 -> false
  
let __proj__EFun__item___0 :
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3 =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let uu___is_EAbortS : expr -> Prims.bool =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2095 -> false
  
let __proj__EAbortS__item___0 : expr -> Prims.string =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let uu___is_Add : op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____2108 -> false 
let uu___is_AddW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2113 -> false
  
let uu___is_Sub : op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____2118 -> false 
let uu___is_SubW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2123 -> false
  
let uu___is_Div : op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____2128 -> false 
let uu___is_DivW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2133 -> false
  
let uu___is_Mult : op -> Prims.bool =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2138 -> false
  
let uu___is_MultW : op -> Prims.bool =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2143 -> false
  
let uu___is_Mod : op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____2148 -> false 
let uu___is_BOr : op -> Prims.bool =
  fun projectee  -> match projectee with | BOr  -> true | uu____2153 -> false 
let uu___is_BAnd : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2158 -> false
  
let uu___is_BXor : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2163 -> false
  
let uu___is_BShiftL : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2168 -> false
  
let uu___is_BShiftR : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2173 -> false
  
let uu___is_BNot : op -> Prims.bool =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2178 -> false
  
let uu___is_Eq : op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____2183 -> false 
let uu___is_Neq : op -> Prims.bool =
  fun projectee  -> match projectee with | Neq  -> true | uu____2188 -> false 
let uu___is_Lt : op -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____2193 -> false 
let uu___is_Lte : op -> Prims.bool =
  fun projectee  -> match projectee with | Lte  -> true | uu____2198 -> false 
let uu___is_Gt : op -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____2203 -> false 
let uu___is_Gte : op -> Prims.bool =
  fun projectee  -> match projectee with | Gte  -> true | uu____2208 -> false 
let uu___is_And : op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____2213 -> false 
let uu___is_Or : op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____2218 -> false 
let uu___is_Xor : op -> Prims.bool =
  fun projectee  -> match projectee with | Xor  -> true | uu____2223 -> false 
let uu___is_Not : op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____2228 -> false 
let uu___is_PUnit : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2233 -> false
  
let uu___is_PBool : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2239 -> false
  
let __proj__PBool__item___0 : pattern -> Prims.bool =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let uu___is_PVar : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2253 -> false
  
let __proj__PVar__item___0 : pattern -> binder =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let uu___is_PCons : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2273 -> false
  
let __proj__PCons__item___0 :
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PCons _0 -> _0 
let uu___is_PTuple : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2307 -> false
  
let __proj__PTuple__item___0 : pattern -> pattern Prims.list =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let uu___is_PRecord : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2333 -> false
  
let __proj__PRecord__item___0 :
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list
  = fun projectee  -> match projectee with | PRecord _0 -> _0 
let uu___is_UInt8 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____2364 -> false
  
let uu___is_UInt16 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2369 -> false
  
let uu___is_UInt32 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2374 -> false
  
let uu___is_UInt64 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2379 -> false
  
let uu___is_Int8 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2384 -> false
  
let uu___is_Int16 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2389 -> false
  
let uu___is_Int32 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2394 -> false
  
let uu___is_Int64 : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2399 -> false
  
let uu___is_Bool : width -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2404 -> false
  
let uu___is_CInt : width -> Prims.bool =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____2409 -> false
  
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
    match projectee with | TInt _0 -> true | uu____2436 -> false
  
let __proj__TInt__item___0 : typ -> width =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let uu___is_TBuf : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2450 -> false
  
let __proj__TBuf__item___0 : typ -> typ =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let uu___is_TUnit : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2463 -> false
  
let uu___is_TQualified : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2475 -> false
  
let __proj__TQualified__item___0 :
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TQualified _0 -> _0 
let uu___is_TBool : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2506 -> false
  
let uu___is_TAny : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2511 -> false
  
let uu___is_TArrow : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2521 -> false
  
let __proj__TArrow__item___0 :
  typ -> (typ,typ) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let uu___is_TBound : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2547 -> false
  
let __proj__TBound__item___0 : typ -> Prims.int =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let uu___is_TApp : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2573 -> false
  
let __proj__TApp__item___0 :
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TApp _0 -> _0 
let uu___is_TTuple : typ -> Prims.bool =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____2625 -> false
  
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
let current_version : version = (Prims.parse_int "24") 
type file = (Prims.string,program) FStar_Pervasives_Native.tuple2
type binary_format = (version,file Prims.list) FStar_Pervasives_Native.tuple2
let fst3 :
  'Auu____2706 'Auu____2707 'Auu____2708 .
    ('Auu____2708,'Auu____2707,'Auu____2706) FStar_Pervasives_Native.tuple3
      -> 'Auu____2708
  = fun uu____2718  -> match uu____2718 with | (x,uu____2726,uu____2727) -> x 
let snd3 :
  'Auu____2736 'Auu____2737 'Auu____2738 .
    ('Auu____2738,'Auu____2737,'Auu____2736) FStar_Pervasives_Native.tuple3
      -> 'Auu____2737
  = fun uu____2748  -> match uu____2748 with | (uu____2755,x,uu____2757) -> x 
let thd3 :
  'Auu____2766 'Auu____2767 'Auu____2768 .
    ('Auu____2768,'Auu____2767,'Auu____2766) FStar_Pervasives_Native.tuple3
      -> 'Auu____2766
  = fun uu____2778  -> match uu____2778 with | (uu____2785,uu____2786,x) -> x 
let mk_width : Prims.string -> width FStar_Pervasives_Native.option =
  fun uu___123_2793  ->
    match uu___123_2793 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____2796 -> FStar_Pervasives_Native.None
  
let mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___124_2802  ->
    match uu___124_2802 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____2805 -> FStar_Pervasives_Native.None
  
let is_bool_op : Prims.string -> Prims.bool =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let mk_op : Prims.string -> op FStar_Pervasives_Native.option =
  fun uu___125_2817  ->
    match uu___125_2817 with
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
    | uu____2820 -> FStar_Pervasives_Native.None
  
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
        let uu___130_2942 = env  in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___130_2942.names_t);
          module_name = (uu___130_2942.module_name)
        }
  
let extend_t : env -> Prims.string -> env =
  fun env  ->
    fun x  ->
      let uu___131_2951 = env  in
      {
        names = (uu___131_2951.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___131_2951.module_name)
      }
  
let find_name : env -> Prims.string -> name =
  fun env  ->
    fun x  ->
      let uu____2960 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____2960 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let is_mutable : env -> Prims.string -> Prims.bool =
  fun env  -> fun x  -> let uu____2974 = find_name env x  in uu____2974.mut 
let find : env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____2991 ->
          let uu____2992 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____2992
  
let find_t : env -> Prims.string -> Prims.int =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____3009 ->
          let uu____3010 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____3010
  
let add_binders :
  'Auu____3019 'Auu____3020 .
    env ->
      ((Prims.string,'Auu____3020) FStar_Pervasives_Native.tuple2,'Auu____3019)
        FStar_Pervasives_Native.tuple2 Prims.list -> env
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____3063  ->
             match uu____3063 with
             | ((name,uu____3073),uu____3074) -> extend env1 name false) env
        binders
  
let rec translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list =
  fun uu____3203  ->
    match uu____3203 with
    | FStar_Extraction_ML_Syntax.MLLib modules1 ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3263 = m  in
               match uu____3263 with
               | ((prefix1,final),uu____3284,uu____3285) ->
                   FStar_String.concat "."
                     (FStar_List.append prefix1 [final])
                in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____3317 = translate_module m  in
                FStar_Pervasives_Native.Some uu____3317)
             with
             | e ->
                 ((let uu____3326 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3326);
                  FStar_Pervasives_Native.None)) modules1

and translate_module :
  ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
    (FStar_Extraction_ML_Syntax.mlsig,FStar_Extraction_ML_Syntax.mlmodule)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,FStar_Extraction_ML_Syntax.mllib)
    FStar_Pervasives_Native.tuple3 -> file
  =
  fun uu____3327  ->
    match uu____3327 with
    | (module_name,modul,uu____3348) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.filter_map (translate_decl (empty module_name1))
                decls
          | uu____3391 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list =
  fun flags  ->
    FStar_List.choose
      (fun uu___126_3406  ->
         match uu___126_3406 with
         | FStar_Extraction_ML_Syntax.Private  ->
             FStar_Pervasives_Native.Some Private
         | FStar_Extraction_ML_Syntax.NoExtract  ->
             FStar_Pervasives_Native.Some NoExtract
         | FStar_Extraction_ML_Syntax.CInline  ->
             FStar_Pervasives_Native.Some CInline
         | FStar_Extraction_ML_Syntax.Substitute  ->
             FStar_Pervasives_Native.Some Substitute
         | FStar_Extraction_ML_Syntax.GCType  ->
             FStar_Pervasives_Native.Some GCType
         | uu____3409 -> FStar_Pervasives_Native.None) flags

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
                            (name,uu____3417);
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3420;
                          FStar_Extraction_ML_Syntax.mllb_def =
                            {
                              FStar_Extraction_ML_Syntax.expr =
                                FStar_Extraction_ML_Syntax.MLE_Fun
                                (args,body);
                              FStar_Extraction_ML_Syntax.mlty = uu____3423;
                              FStar_Extraction_ML_Syntax.loc = uu____3424;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____3425;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___127_3446  ->
                 match uu___127_3446 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____3447 -> false) flags
             in
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env  in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun uu____3460  ->
                   match uu____3460 with
                   | (name1,uu____3466) -> extend_t env2 name1) env1 tvars
             in
          let rec find_return_type i uu___128_3473 =
            match uu___128_3473 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3474,uu____3475,t)
                when i > (Prims.parse_int "0") ->
                find_return_type (i - (Prims.parse_int "1")) t
            | t -> t  in
          let t =
            let uu____3479 = find_return_type (FStar_List.length args) t0  in
            translate_type env2 uu____3479  in
          let binders = translate_binders env2 args  in
          let env3 = add_binders env2 args  in
          let name1 = ((env3.module_name), name)  in
          let flags1 = translate_flags flags  in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
               let uu____3504 =
                 let uu____3505 =
                   let uu____3520 = translate_type env3 t0  in
                   (FStar_Pervasives_Native.None, name1, uu____3520)  in
                 DExternal uu____3505  in
               FStar_Pervasives_Native.Some uu____3504
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
                            (name,uu____3580);
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some (tvars,t0);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3583;
                          FStar_Extraction_ML_Syntax.mllb_def =
                            {
                              FStar_Extraction_ML_Syntax.expr =
                                FStar_Extraction_ML_Syntax.MLE_Coerce
                                ({
                                   FStar_Extraction_ML_Syntax.expr =
                                     FStar_Extraction_ML_Syntax.MLE_Fun
                                     (args,body);
                                   FStar_Extraction_ML_Syntax.mlty =
                                     uu____3586;
                                   FStar_Extraction_ML_Syntax.loc =
                                     uu____3587;_},uu____3588,uu____3589);
                              FStar_Extraction_ML_Syntax.mlty = uu____3590;
                              FStar_Extraction_ML_Syntax.loc = uu____3591;_};
                          FStar_Extraction_ML_Syntax.print_typ = uu____3592;_}::[])
          ->
          let assumed =
            FStar_Util.for_some
              (fun uu___127_3613  ->
                 match uu___127_3613 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____3614 -> false) flags
             in
          let env1 =
            if flavor = FStar_Extraction_ML_Syntax.Rec
            then extend env name false
            else env  in
          let env2 =
            FStar_List.fold_left
              (fun env2  ->
                 fun uu____3627  ->
                   match uu____3627 with
                   | (name1,uu____3633) -> extend_t env2 name1) env1 tvars
             in
          let rec find_return_type i uu___128_3640 =
            match uu___128_3640 with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3641,uu____3642,t)
                when i > (Prims.parse_int "0") ->
                find_return_type (i - (Prims.parse_int "1")) t
            | t -> t  in
          let t =
            let uu____3646 = find_return_type (FStar_List.length args) t0  in
            translate_type env2 uu____3646  in
          let binders = translate_binders env2 args  in
          let env3 = add_binders env2 args  in
          let name1 = ((env3.module_name), name)  in
          let flags1 = translate_flags flags  in
          if assumed
          then
            (if (FStar_List.length tvars) = (Prims.parse_int "0")
             then
               let uu____3671 =
                 let uu____3672 =
                   let uu____3687 = translate_type env3 t0  in
                   (FStar_Pervasives_Native.None, name1, uu____3687)  in
                 DExternal uu____3672  in
               FStar_Pervasives_Native.Some uu____3671
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
                            (name,uu____3747);
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            FStar_Pervasives_Native.Some ([],t);
                          FStar_Extraction_ML_Syntax.mllb_add_unit =
                            uu____3749;
                          FStar_Extraction_ML_Syntax.mllb_def = expr;
                          FStar_Extraction_ML_Syntax.print_typ = uu____3751;_}::[])
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
               ((let uu____3799 = FStar_Util.print_exn e  in
                 FStar_Util.print2
                   "Warning: not translating definition for %s (%s)\n"
                   (FStar_Pervasives_Native.snd name1) uu____3799);
                FStar_Pervasives_Native.Some
                  (DGlobal (flags1, name1, t1, EAny))))
      | FStar_Extraction_ML_Syntax.MLM_Let
          (uu____3810,uu____3811,{
                                   FStar_Extraction_ML_Syntax.mllb_name =
                                     (name,uu____3813);
                                   FStar_Extraction_ML_Syntax.mllb_tysc = ts;
                                   FStar_Extraction_ML_Syntax.mllb_add_unit =
                                     uu____3815;
                                   FStar_Extraction_ML_Syntax.mllb_def =
                                     uu____3816;
                                   FStar_Extraction_ML_Syntax.print_typ =
                                     uu____3817;_}::uu____3818)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           (match ts with
            | FStar_Pervasives_Native.Some (idents,t) ->
                let uu____3833 =
                  let uu____3834 =
                    FStar_List.map FStar_Pervasives_Native.fst idents  in
                  FStar_String.concat ", " uu____3834  in
                let uu____3841 =
                  FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                  uu____3833 uu____3841
            | FStar_Pervasives_Native.None  -> ());
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Let uu____3844 ->
          failwith "impossible"
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3847 ->
          FStar_Pervasives_Native.None
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((assumed,name,_mangled_name,args,uu____3852,FStar_Pervasives_Native.Some
            (FStar_Extraction_ML_Syntax.MLTD_Abbrev t))::[])
          ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____3911  ->
                   match uu____3911 with
                   | (name2,uu____3917) -> extend_t env1 name2) env args
             in
          if assumed
          then FStar_Pervasives_Native.None
          else
            (let uu____3921 =
               let uu____3922 =
                 let uu____3935 = translate_type env1 t  in
                 (name1, (FStar_List.length args), uu____3935)  in
               DTypeAlias uu____3922  in
             FStar_Pervasives_Native.Some uu____3921)
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____3942,name,_mangled_name,args,uu____3946,FStar_Pervasives_Native.Some
            (FStar_Extraction_ML_Syntax.MLTD_Record fields))::[])
          ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____4011  ->
                   match uu____4011 with
                   | (name2,uu____4017) -> extend_t env1 name2) env args
             in
          let uu____4018 =
            let uu____4019 =
              let uu____4042 =
                FStar_List.map
                  (fun uu____4069  ->
                     match uu____4069 with
                     | (f,t) ->
                         let uu____4084 =
                           let uu____4089 = translate_type env1 t  in
                           (uu____4089, false)  in
                         (f, uu____4084)) fields
                 in
              (name1, (FStar_List.length args), uu____4042)  in
            DTypeFlat uu____4019  in
          FStar_Pervasives_Native.Some uu____4018
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____4110,name,_mangled_name,args,attrs,FStar_Pervasives_Native.Some
            (FStar_Extraction_ML_Syntax.MLTD_DType branches))::[])
          ->
          let name1 = ((env.module_name), name)  in
          let flags = translate_flags attrs  in
          let env1 =
            FStar_List.fold_left
              (fun env1  ->
                 fun uu____4188  ->
                   match uu____4188 with
                   | (name2,uu____4194) -> extend_t env1 name2) env args
             in
          let uu____4195 =
            let uu____4196 =
              let uu____4229 =
                FStar_List.map
                  (fun uu____4274  ->
                     match uu____4274 with
                     | (cons1,ts) ->
                         let uu____4313 =
                           FStar_List.map
                             (fun uu____4340  ->
                                match uu____4340 with
                                | (name2,t) ->
                                    let uu____4355 =
                                      let uu____4360 = translate_type env1 t
                                         in
                                      (uu____4360, false)  in
                                    (name2, uu____4355)) ts
                            in
                         (cons1, uu____4313)) branches
                 in
              (name1, flags, (FStar_List.length args), uu____4229)  in
            DTypeVariant uu____4196  in
          FStar_Pervasives_Native.Some uu____4195
      | FStar_Extraction_ML_Syntax.MLM_Ty
          ((uu____4399,name,_mangled_name,uu____4402,uu____4403,uu____4404)::uu____4405)
          ->
          (FStar_Util.print1
             "Warning: not translating definition for %s (and possibly others)\n"
             name;
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Ty [] ->
          (FStar_Util.print_string
             "Impossible!! Empty block of mutually recursive type declarations";
           FStar_Pervasives_Native.None)
      | FStar_Extraction_ML_Syntax.MLM_Top uu____4450 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn uu____4453 ->
          failwith "todo: translate_decl [MLM_Exn]"

and translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var (name,uu____4469) ->
          let uu____4470 = find_t env name  in TBound uu____4470
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4472,t2) ->
          let uu____4474 =
            let uu____4479 = translate_type env t1  in
            let uu____4480 = translate_type env t2  in
            (uu____4479, uu____4480)  in
          TArrow uu____4474
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4484 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4484 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4488 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4488 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4500 = FStar_Util.must (mk_width m)  in TInt uu____4500
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4512 = FStar_Util.must (mk_width m)  in TInt uu____4512
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4517 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4517 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4522 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4522 = "FStar.Buffer.buffer" ->
          let uu____4523 = translate_type env arg  in TBuf uu____4523
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4524::[],p) when
          let uu____4528 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4528 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4566 = FStar_List.map (translate_type env) args  in
          TTuple uu____4566
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4575 =
              let uu____4588 = FStar_List.map (translate_type env) args  in
              (lid, uu____4588)  in
            TApp uu____4575
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4597 = FStar_List.map (translate_type env) ts  in
          TTuple uu____4597

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
    fun uu____4613  ->
      match uu____4613 with
      | ((name,uu____4619),typ) ->
          let uu____4625 = translate_type env typ  in
          { name; typ = uu____4625; mut = false }

and translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var (name,uu____4630) ->
          let uu____4631 = find env name  in EBound uu____4631
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4636 =
            let uu____4641 = FStar_Util.must (mk_op op)  in
            let uu____4642 = FStar_Util.must (mk_width m)  in
            (uu____4641, uu____4642)  in
          EOp uu____4636
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4646 =
            let uu____4651 = FStar_Util.must (mk_bool_op op)  in
            (uu____4651, Bool)  in
          EOp uu____4646
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,flags,{
                           FStar_Extraction_ML_Syntax.mllb_name =
                             (name,uu____4656);
                           FStar_Extraction_ML_Syntax.mllb_tysc =
                             FStar_Pervasives_Native.Some ([],typ);
                           FStar_Extraction_ML_Syntax.mllb_add_unit =
                             add_unit;
                           FStar_Extraction_ML_Syntax.mllb_def = body;
                           FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let is_mut =
            FStar_Util.for_some
              (fun uu___129_4682  ->
                 match uu___129_4682 with
                 | FStar_Extraction_ML_Syntax.Mutable  -> true
                 | uu____4683 -> false) flags
             in
          let uu____4684 =
            if is_mut
            then
              let uu____4693 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[],p) when
                    let uu____4698 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4698 = "FStar.ST.stackref" -> t
                | uu____4699 ->
                    let uu____4700 =
                      let uu____4701 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ
                         in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____4701
                       in
                    failwith uu____4700
                 in
              let uu____4704 =
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
                      (uu____4705,body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____4707;
                    FStar_Extraction_ML_Syntax.loc = uu____4708;_} -> body1
                | uu____4711 ->
                    failwith "unexpected: bad desugaring of Mutable"
                 in
              (uu____4693, uu____4704)
            else (typ, body)  in
          (match uu____4684 with
           | (typ1,body1) ->
               let binder =
                 let uu____4716 = translate_type env typ1  in
                 { name; typ = uu____4716; mut = is_mut }  in
               let body2 = translate_expr env body1  in
               let env1 = extend env name is_mut  in
               let continuation1 = translate_expr env1 continuation  in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4742 =
            let uu____4753 = translate_expr env expr  in
            let uu____4754 = translate_branches env branches  in
            (uu____4753, uu____4754)  in
          EMatch uu____4742
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4768;
             FStar_Extraction_ML_Syntax.loc = uu____4769;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____4771);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4772;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4773;_}::[])
          when
          (let uu____4778 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4778 = "FStar.HyperStack.ST.op_Bang") && (is_mutable env v1)
          -> let uu____4779 = find env v1  in EBound uu____4779
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4781;
             FStar_Extraction_ML_Syntax.loc = uu____4782;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Var
                                                                (v1,uu____4784);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____4785;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____4786;_}::e1::[])
          when
          (let uu____4792 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4792 = "FStar.HyperStack.ST.op_Colon_Equals") &&
            (is_mutable env v1)
          ->
          let uu____4793 =
            let uu____4798 =
              let uu____4799 = find env v1  in EBound uu____4799  in
            let uu____4800 = translate_expr env e1  in
            (uu____4798, uu____4800)  in
          EAssign uu____4793
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4802;
             FStar_Extraction_ML_Syntax.loc = uu____4803;_},e1::e2::[])
          when
          (let uu____4810 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4810 = "FStar.Buffer.index") ||
            (let uu____4812 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4812 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____4813 =
            let uu____4818 = translate_expr env e1  in
            let uu____4819 = translate_expr env e2  in
            (uu____4818, uu____4819)  in
          EBufRead uu____4813
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4821;
             FStar_Extraction_ML_Syntax.loc = uu____4822;_},e1::e2::[])
          when
          let uu____4827 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4827 = "FStar.Buffer.create" ->
          let uu____4828 =
            let uu____4835 = translate_expr env e1  in
            let uu____4836 = translate_expr env e2  in
            (Stack, uu____4835, uu____4836)  in
          EBufCreate uu____4828
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4838;
             FStar_Extraction_ML_Syntax.loc = uu____4839;_},_e0::e1::e2::[])
          when
          let uu____4845 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4845 = "FStar.Buffer.rcreate" ->
          let uu____4846 =
            let uu____4853 = translate_expr env e1  in
            let uu____4854 = translate_expr env e2  in
            (Eternal, uu____4853, uu____4854)  in
          EBufCreate uu____4846
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4856;
             FStar_Extraction_ML_Syntax.loc = uu____4857;_},e2::[])
          when
          let uu____4861 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4861 = "FStar.Buffer.createL" ->
          let rec list_elements1 acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements1 (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____4899 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!"
             in
          let list_elements2 = list_elements1 []  in
          let uu____4907 =
            let uu____4914 =
              let uu____4917 = list_elements2 e2  in
              FStar_List.map (translate_expr env) uu____4917  in
            (Stack, uu____4914)  in
          EBufCreateL uu____4907
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4923;
             FStar_Extraction_ML_Syntax.loc = uu____4924;_},e1::e2::_e3::[])
          when
          let uu____4930 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4930 = "FStar.Buffer.sub" ->
          let uu____4931 =
            let uu____4936 = translate_expr env e1  in
            let uu____4937 = translate_expr env e2  in
            (uu____4936, uu____4937)  in
          EBufSub uu____4931
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4939;
             FStar_Extraction_ML_Syntax.loc = uu____4940;_},e1::e2::[])
          when
          let uu____4945 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4945 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4947;
             FStar_Extraction_ML_Syntax.loc = uu____4948;_},e1::e2::[])
          when
          let uu____4953 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4953 = "FStar.Buffer.offset" ->
          let uu____4954 =
            let uu____4959 = translate_expr env e1  in
            let uu____4960 = translate_expr env e2  in
            (uu____4959, uu____4960)  in
          EBufSub uu____4954
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4962;
             FStar_Extraction_ML_Syntax.loc = uu____4963;_},e1::e2::e3::[])
          when
          (let uu____4971 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4971 = "FStar.Buffer.upd") ||
            (let uu____4973 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4973 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____4974 =
            let uu____4981 = translate_expr env e1  in
            let uu____4982 = translate_expr env e2  in
            let uu____4983 = translate_expr env e3  in
            (uu____4981, uu____4982, uu____4983)  in
          EBufWrite uu____4974
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4985;
             FStar_Extraction_ML_Syntax.loc = uu____4986;_},uu____4987::[])
          when
          let uu____4990 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4990 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4992;
             FStar_Extraction_ML_Syntax.loc = uu____4993;_},uu____4994::[])
          when
          let uu____4997 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4997 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4999;
             FStar_Extraction_ML_Syntax.loc = uu____5000;_},e1::e2::e3::e4::e5::[])
          when
          let uu____5008 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5008 = "FStar.Buffer.blit" ->
          let uu____5009 =
            let uu____5020 = translate_expr env e1  in
            let uu____5021 = translate_expr env e2  in
            let uu____5022 = translate_expr env e3  in
            let uu____5023 = translate_expr env e4  in
            let uu____5024 = translate_expr env e5  in
            (uu____5020, uu____5021, uu____5022, uu____5023, uu____5024)  in
          EBufBlit uu____5009
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5026;
             FStar_Extraction_ML_Syntax.loc = uu____5027;_},e1::e2::e3::[])
          when
          let uu____5033 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5033 = "FStar.Buffer.fill" ->
          let uu____5034 =
            let uu____5041 = translate_expr env e1  in
            let uu____5042 = translate_expr env e2  in
            let uu____5043 = translate_expr env e3  in
            (uu____5041, uu____5042, uu____5043)  in
          EBufFill uu____5034
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5045;
             FStar_Extraction_ML_Syntax.loc = uu____5046;_},uu____5047::[])
          when
          let uu____5050 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5050 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5052;
             FStar_Extraction_ML_Syntax.loc = uu____5053;_},e1::[])
          when
          let uu____5057 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5057 = "Obj.repr" ->
          let uu____5058 =
            let uu____5063 = translate_expr env e1  in (uu____5063, TAny)  in
          ECast uu____5058
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5066;
             FStar_Extraction_ML_Syntax.loc = uu____5067;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5075 = FStar_Util.must (mk_width m)  in
          let uu____5076 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____5075 uu____5076 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5078;
             FStar_Extraction_ML_Syntax.loc = uu____5079;_},args)
          when is_bool_op op ->
          let uu____5087 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____5087 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5089;
             FStar_Extraction_ML_Syntax.loc = uu____5090;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5092;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5093;_}::[])
          when is_machine_int m ->
          let uu____5108 =
            let uu____5113 = FStar_Util.must (mk_width m)  in (uu____5113, c)
             in
          EConstant uu____5108
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5115;
             FStar_Extraction_ML_Syntax.loc = uu____5116;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5118;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5119;_}::[])
          when is_machine_int m ->
          let uu____5134 =
            let uu____5139 = FStar_Util.must (mk_width m)  in (uu____5139, c)
             in
          EConstant uu____5134
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5140;
             FStar_Extraction_ML_Syntax.loc = uu____5141;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5143;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5144;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5150 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5152;
             FStar_Extraction_ML_Syntax.loc = uu____5153;_},arg::[])
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
            let uu____5160 =
              let uu____5165 = translate_expr env arg  in
              (uu____5165, (TInt UInt64))  in
            ECast uu____5160
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5167 =
                 let uu____5172 = translate_expr env arg  in
                 (uu____5172, (TInt UInt32))  in
               ECast uu____5167)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5174 =
                   let uu____5179 = translate_expr env arg  in
                   (uu____5179, (TInt UInt16))  in
                 ECast uu____5174)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5181 =
                     let uu____5186 = translate_expr env arg  in
                     (uu____5186, (TInt UInt8))  in
                   ECast uu____5181)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5188 =
                       let uu____5193 = translate_expr env arg  in
                       (uu____5193, (TInt Int64))  in
                     ECast uu____5188)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5195 =
                         let uu____5200 = translate_expr env arg  in
                         (uu____5200, (TInt Int32))  in
                       ECast uu____5195)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5202 =
                           let uu____5207 = translate_expr env arg  in
                           (uu____5207, (TInt Int16))  in
                         ECast uu____5202)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5209 =
                             let uu____5214 = translate_expr env arg  in
                             (uu____5214, (TInt Int8))  in
                           ECast uu____5209)
                        else
                          (let uu____5216 =
                             let uu____5223 =
                               let uu____5226 = translate_expr env arg  in
                               [uu____5226]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5223)
                              in
                           EApp uu____5216)
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name (path,function_name);
             FStar_Extraction_ML_Syntax.mlty = uu____5233;
             FStar_Extraction_ML_Syntax.loc = uu____5234;_},args)
          ->
          let uu____5244 =
            let uu____5251 = FStar_List.map (translate_expr env) args  in
            ((EQualified (path, function_name)), uu____5251)  in
          EApp uu____5244
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Var (name,uu____5259);
             FStar_Extraction_ML_Syntax.mlty = uu____5260;
             FStar_Extraction_ML_Syntax.loc = uu____5261;_},args)
          ->
          let uu____5267 =
            let uu____5274 =
              let uu____5275 = find env name  in EBound uu____5275  in
            let uu____5276 = FStar_List.map (translate_expr env) args  in
            (uu____5274, uu____5276)  in
          EApp uu____5267
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5287 =
            let uu____5294 = translate_expr env head1  in
            let uu____5295 = FStar_List.map (translate_type env) ty_args  in
            (uu____5294, uu____5295)  in
          ETypApp uu____5287
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5303 =
            let uu____5308 = translate_expr env e1  in
            let uu____5309 = translate_type env t_to  in
            (uu____5308, uu____5309)  in
          ECast uu____5303
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5310,fields) ->
          let uu____5328 =
            let uu____5339 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5340 =
              FStar_List.map
                (fun uu____5359  ->
                   match uu____5359 with
                   | (field,expr) ->
                       let uu____5370 = translate_expr env expr  in
                       (field, uu____5370)) fields
               in
            (uu____5339, uu____5340)  in
          EFlat uu____5328
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5379 =
            let uu____5386 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____5387 = translate_expr env e1  in
            (uu____5386, uu____5387, (FStar_Pervasives_Native.snd path))  in
          EField uu____5379
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5390 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5404) ->
          let uu____5409 =
            let uu____5410 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5410
             in
          failwith uu____5409
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5416 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____5416
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5422 = FStar_List.map (translate_expr env) es  in
          ETuple uu____5422
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5425,cons1),es) ->
          let uu____5442 =
            let uu____5451 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5452 = FStar_List.map (translate_expr env) es  in
            (uu____5451, cons1, uu____5452)  in
          ECons uu____5442
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____5475 =
            let uu____5484 = translate_expr env1 body  in
            let uu____5485 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____5484, uu____5485)  in
          EFun uu____5475
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5495 =
            let uu____5502 = translate_expr env e1  in
            let uu____5503 = translate_expr env e2  in
            let uu____5504 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____5502, uu____5503, uu____5504)  in
          EIfThenElse uu____5495
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5506 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5513 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____5528 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____5543 =
              let uu____5556 = FStar_List.map (translate_type env) ts  in
              (lid, uu____5556)  in
            TApp uu____5543
          else TQualified lid
      | uu____5562 -> failwith "invalid argument: assert_lid"

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
    fun uu____5588  ->
      match uu____5588 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____5614 = translate_pat env pat  in
            (match uu____5614 with
             | (env1,pat1) ->
                 let uu____5625 = translate_expr env1 expr  in
                 (pat1, uu____5625))
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
      | FStar_Extraction_ML_Syntax.MLP_Var (name,uu____5639) ->
          let env1 = extend env name false  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_" false  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5642,cons1),ps) ->
          let uu____5659 =
            FStar_List.fold_left
              (fun uu____5679  ->
                 fun p1  ->
                   match uu____5679 with
                   | (env1,acc) ->
                       let uu____5699 = translate_pat env1 p1  in
                       (match uu____5699 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____5659 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____5728,ps) ->
          let uu____5746 =
            FStar_List.fold_left
              (fun uu____5780  ->
                 fun uu____5781  ->
                   match (uu____5780, uu____5781) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____5850 = translate_pat env1 p1  in
                       (match uu____5850 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____5746 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____5912 =
            FStar_List.fold_left
              (fun uu____5932  ->
                 fun p1  ->
                   match uu____5932 with
                   | (env1,acc) ->
                       let uu____5952 = translate_pat env1 p1  in
                       (match uu____5952 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____5912 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____5979 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____5984 ->
          failwith "todo: translate_pat [MLP_Branch]"

and translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____5994) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6009 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Char uu____6010 ->
        failwith "todo: translate_expr [MLC_Char]"
    | FStar_Extraction_ML_Syntax.MLC_String uu____6011 ->
        failwith "todo: translate_expr [MLC_String]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6012 ->
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
          let uu____6032 =
            let uu____6039 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____6039)  in
          EApp uu____6032
