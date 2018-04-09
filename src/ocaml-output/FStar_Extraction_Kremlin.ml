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
    match projectee with | DGlobal _0 -> true | uu____559 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list,(Prims.string Prims.list,Prims.string)
                       FStar_Pervasives_Native.tuple2,Prims.int,typ,expr)
      FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____651 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option,flag Prims.list,Prims.int,typ,
      (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list,expr) FStar_Pervasives_Native.tuple7)
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____757 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list,Prims.int,typ) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____843 -> false
  
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
    match projectee with | DExternal _0 -> true | uu____951 -> false
  
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
    match projectee with | DTypeVariant _0 -> true | uu____1049 -> false
  
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
    match projectee with | StdCall  -> true | uu____1156 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1160 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1164 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1168 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1172 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1176 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1180 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1184 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1189 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1200 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1205 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1217 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1229 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1240 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1244 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1248 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1253 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1271 -> false
  
let (__proj__EQualified__item___0 :
  expr ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1305 -> false
  
let (__proj__EConstant__item___0 :
  expr -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____1328 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____1339 -> false
  
let (__proj__EApp__item___0 :
  expr -> (expr,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____1375 -> false
  
let (__proj__ETypApp__item___0 :
  expr -> (expr,typ Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____1411 -> false
  
let (__proj__ELet__item___0 :
  expr -> (binder,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____1447 -> false
  
let (__proj__EIfThenElse__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____1479 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____1501 -> false
  
let (__proj__EAssign__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____1531 -> false
  
let (__proj__EBufCreate__item___0 :
  expr -> (lifetime,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____1565 -> false
  
let (__proj__EBufRead__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____1595 -> false
  
let (__proj__EBufWrite__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____1629 -> false
  
let (__proj__EBufSub__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____1663 -> false
  
let (__proj__EBufBlit__item___0 :
  expr -> (expr,expr,expr,expr,expr) FStar_Pervasives_Native.tuple5) =
  fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____1715 -> false
  
let (__proj__EMatch__item___0 :
  expr ->
    (expr,(pattern,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____1761 -> false
  
let (__proj__EOp__item___0 :
  expr -> (op,width) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____1789 -> false
  
let (__proj__ECast__item___0 :
  expr -> (expr,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____1812 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____1816 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____1821 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____1832 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____1836 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____1841 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____1863 -> false
  
let (__proj__EFlat__item___0 :
  expr ->
    (typ,(Prims.string,expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____1911 -> false
  
let (__proj__EField__item___0 :
  expr -> (typ,expr,Prims.string) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____1945 -> false
  
let (__proj__EWhile__item___0 :
  expr -> (expr,expr) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____1975 -> false
  
let (__proj__EBufCreateL__item___0 :
  expr -> (lifetime,expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2007 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2033 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ,Prims.string,expr Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2075 -> false
  
let (__proj__EBufFill__item___0 :
  expr -> (expr,expr,expr) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____2105 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____2125 -> false
  
let (__proj__EFun__item___0 :
  expr -> (binder Prims.list,expr,typ) FStar_Pervasives_Native.tuple3) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____2161 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____2173 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____2184 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____2188 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____2192 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____2196 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____2200 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____2204 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____2208 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____2212 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____2216 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____2220 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____2224 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____2228 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____2232 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____2236 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____2240 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____2244 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____2248 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____2252 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____2256 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____2260 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____2264 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____2268 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____2272 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____2276 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____2280 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____2284 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____2289 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____2301 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____2319 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string,pattern Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____2351 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____2375 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string,pattern) FStar_Pervasives_Native.tuple2 Prims.list)
  = fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____2409 -> false
  
let (__proj__PConstant__item___0 :
  pattern -> (width,Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____2432 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____2436 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____2440 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____2444 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____2448 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____2452 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____2456 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____2460 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____2464 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____2468 -> false
  
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
    match projectee with | TInt _0 -> true | uu____2483 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____2495 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____2506 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____2517 -> false
  
let (__proj__TQualified__item___0 :
  typ ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____2546 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____2550 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____2559 -> false
  
let (__proj__TArrow__item___0 :
  typ -> (typ,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____2583 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____2607 -> false
  
let (__proj__TApp__item___0 :
  typ ->
    ((Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____2657 -> false
  
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
  'Auu____2733 'Auu____2734 'Auu____2735 .
    ('Auu____2733,'Auu____2734,'Auu____2735) FStar_Pervasives_Native.tuple3
      -> 'Auu____2733
  = fun uu____2745  -> match uu____2745 with | (x,uu____2753,uu____2754) -> x 
let snd3 :
  'Auu____2759 'Auu____2760 'Auu____2761 .
    ('Auu____2759,'Auu____2760,'Auu____2761) FStar_Pervasives_Native.tuple3
      -> 'Auu____2760
  = fun uu____2771  -> match uu____2771 with | (uu____2778,x,uu____2780) -> x 
let thd3 :
  'Auu____2785 'Auu____2786 'Auu____2787 .
    ('Auu____2785,'Auu____2786,'Auu____2787) FStar_Pervasives_Native.tuple3
      -> 'Auu____2787
  = fun uu____2797  -> match uu____2797 with | (uu____2804,uu____2805,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___35_2811  ->
    match uu___35_2811 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____2814 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___36_2819  ->
    match uu___36_2819 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____2822 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___37_2832  ->
    match uu___37_2832 with
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
    | uu____2835 -> FStar_Pervasives_Native.None
  
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
      let uu___42_2933 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___42_2933.names_t);
        module_name = (uu___42_2933.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___43_2940 = env  in
      {
        names = (uu___43_2940.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___43_2940.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____2947 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____2947 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name.pretty = x) env.names
      with
      | uu____2967 ->
          let uu____2968 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____2968
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try FStar_List.index (fun name  -> name = x) env.names_t
      with
      | uu____2983 ->
          let uu____2984 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____2984
  
let add_binders :
  'Auu____2988 .
    env ->
      (Prims.string,'Auu____2988) FStar_Pervasives_Native.tuple2 Prims.list
        -> env
  =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____3018  ->
             match uu____3018 with | (name,uu____3024) -> extend env1 name)
        env binders
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____3165  ->
    match uu____3165 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____3213 = m  in
               match uu____3213 with
               | (path,uu____3227,uu____3228) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____3250 = translate_module m  in
                FStar_Pervasives_Native.Some uu____3250)
             with
             | e ->
                 ((let uu____3259 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3259);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath,(FStar_Extraction_ML_Syntax.mlsig,
                                       FStar_Extraction_ML_Syntax.mlmodule)
                                       FStar_Pervasives_Native.tuple2
                                       FStar_Pervasives_Native.option,
    FStar_Extraction_ML_Syntax.mllib) FStar_Pervasives_Native.tuple3 -> 
    file)
  =
  fun uu____3260  ->
    match uu____3260 with
    | (module_name,modul,uu____3275) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____3306 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags1  ->
    FStar_List.choose
      (fun uu___38_3321  ->
         match uu___38_3321 with
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
         | uu____3328 -> FStar_Pervasives_Native.None) flags1

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3339 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3341 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____3345) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3367;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____3370;
                FStar_Extraction_ML_Syntax.loc = uu____3371;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3373;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___39_3395  ->
                      match uu___39_3395 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____3396 -> false) meta
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
               let rec find_return_type eff i uu___40_3417 =
                 match uu___40_3417 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3422,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (eff, t)  in
               let uu____3426 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____3426 with
               | (eff,t) ->
                   let t1 = translate_type env2 t  in
                   let binders = translate_binders env2 args  in
                   let env3 = add_binders env2 args  in
                   let name1 = ((env3.module_name), name)  in
                   let meta1 =
                     match (eff, t1) with
                     | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____3458) ->
                         let uu____3459 = translate_flags meta  in
                         MustDisappear :: uu____3459
                     | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                         let uu____3462 = translate_flags meta  in
                         MustDisappear :: uu____3462
                     | uu____3465 -> translate_flags meta  in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____3474 =
                          let uu____3475 =
                            let uu____3494 = translate_type env3 t0  in
                            (FStar_Pervasives_Native.None, meta1, name1,
                              uu____3494)
                             in
                          DExternal uu____3475  in
                        FStar_Pervasives_Native.Some uu____3474
                      else
                        ((let uu____3507 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1
                             in
                          FStar_Util.print1_warning
                            "No writing anything for %s (polymorphic assume)\n"
                            uu____3507);
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
                          ((let uu____3540 =
                              let uu____3545 =
                                let uu____3546 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1
                                   in
                                FStar_Util.format2
                                  "Writing a stub for %s (%s)\n" uu____3546
                                  msg
                                 in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____3545)
                               in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____3540);
                           (let msg1 =
                              Prims.strcat
                                "This function was not extracted:\n" msg
                               in
                            FStar_Pervasives_Native.Some
                              (DFunction
                                 (FStar_Pervasives_Native.None, meta1,
                                   (FStar_List.length tvars), t1, name1,
                                   binders, (EAbortS msg1)))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3563;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Coerce
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____3566;
                     FStar_Extraction_ML_Syntax.loc = uu____3567;_},uu____3568,uu____3569);
                FStar_Extraction_ML_Syntax.mlty = uu____3570;
                FStar_Extraction_ML_Syntax.loc = uu____3571;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3573;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let assumed =
                 FStar_Util.for_some
                   (fun uu___39_3595  ->
                      match uu___39_3595 with
                      | FStar_Extraction_ML_Syntax.Assumed  -> true
                      | uu____3596 -> false) meta
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
               let rec find_return_type eff i uu___40_3617 =
                 match uu___40_3617 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3622,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (eff, t)  in
               let uu____3626 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____3626 with
               | (eff,t) ->
                   let t1 = translate_type env2 t  in
                   let binders = translate_binders env2 args  in
                   let env3 = add_binders env2 args  in
                   let name1 = ((env3.module_name), name)  in
                   let meta1 =
                     match (eff, t1) with
                     | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____3658) ->
                         let uu____3659 = translate_flags meta  in
                         MustDisappear :: uu____3659
                     | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                         let uu____3662 = translate_flags meta  in
                         MustDisappear :: uu____3662
                     | uu____3665 -> translate_flags meta  in
                   if assumed
                   then
                     (if (FStar_List.length tvars) = (Prims.parse_int "0")
                      then
                        let uu____3674 =
                          let uu____3675 =
                            let uu____3694 = translate_type env3 t0  in
                            (FStar_Pervasives_Native.None, meta1, name1,
                              uu____3694)
                             in
                          DExternal uu____3675  in
                        FStar_Pervasives_Native.Some uu____3674
                      else
                        ((let uu____3707 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath name1
                             in
                          FStar_Util.print1_warning
                            "No writing anything for %s (polymorphic assume)\n"
                            uu____3707);
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
                          ((let uu____3740 =
                              let uu____3745 =
                                let uu____3746 =
                                  FStar_Extraction_ML_Syntax.string_of_mlpath
                                    name1
                                   in
                                FStar_Util.format2
                                  "Writing a stub for %s (%s)\n" uu____3746
                                  msg
                                 in
                              (FStar_Errors.Warning_FunctionNotExtacted,
                                uu____3745)
                               in
                            FStar_Errors.log_issue FStar_Range.dummyRange
                              uu____3740);
                           (let msg1 =
                              Prims.strcat
                                "This function was not extracted:\n" msg
                               in
                            FStar_Pervasives_Native.Some
                              (DFunction
                                 (FStar_Pervasives_Native.None, meta1,
                                   (FStar_List.length tvars), t1, name1,
                                   binders, (EAbortS msg1)))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3763;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3766;_} ->
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
                 let expr1 = translate_expr env1 expr  in
                 FStar_Pervasives_Native.Some
                   (DGlobal
                      (meta1, name1, (FStar_List.length tvars), t1, expr1))
               with
               | e ->
                   ((let uu____3816 =
                       let uu____3821 =
                         let uu____3822 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____3823 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Not translating definition for %s (%s)\n"
                           uu____3822 uu____3823
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____3821)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____3816);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3834;
            FStar_Extraction_ML_Syntax.mllb_def = uu____3835;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____3836;
            FStar_Extraction_ML_Syntax.print_typ = uu____3837;_} ->
            ((let uu____3841 =
                let uu____3846 =
                  FStar_Util.format1 "Not translating definition for %s\n"
                    name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____3846)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____3841);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____3854 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____3854
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
            (let uu____3892 =
               let uu____3893 =
                 let uu____3910 = translate_flags flags1  in
                 let uu____3913 = translate_type env1 t  in
                 (name1, uu____3910, (FStar_List.length args), uu____3913)
                  in
               DTypeAlias uu____3893  in
             FStar_Pervasives_Native.Some uu____3892)
      | (uu____3922,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args
             in
          let uu____3954 =
            let uu____3955 =
              let uu____3982 = translate_flags flags1  in
              let uu____3985 =
                FStar_List.map
                  (fun uu____4012  ->
                     match uu____4012 with
                     | (f,t) ->
                         let uu____4027 =
                           let uu____4032 = translate_type env1 t  in
                           (uu____4032, false)  in
                         (f, uu____4027)) fields
                 in
              (name1, uu____3982, (FStar_List.length args), uu____3985)  in
            DTypeFlat uu____3955  in
          FStar_Pervasives_Native.Some uu____3954
      | (uu____4055,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
          let name1 = ((env.module_name), name)  in
          let flags2 = translate_flags flags1  in
          let env1 = FStar_List.fold_left extend_t env args  in
          let uu____4092 =
            let uu____4093 =
              let uu____4126 =
                FStar_List.map
                  (fun uu____4171  ->
                     match uu____4171 with
                     | (cons1,ts) ->
                         let uu____4210 =
                           FStar_List.map
                             (fun uu____4237  ->
                                match uu____4237 with
                                | (name2,t) ->
                                    let uu____4252 =
                                      let uu____4257 = translate_type env1 t
                                         in
                                      (uu____4257, false)  in
                                    (name2, uu____4252)) ts
                            in
                         (cons1, uu____4210)) branches
                 in
              (name1, flags2, (FStar_List.length args), uu____4126)  in
            DTypeVariant uu____4093  in
          FStar_Pervasives_Native.Some uu____4092
      | (uu____4296,name,_mangled_name,uu____4299,uu____4300,uu____4301) ->
          ((let uu____4311 =
              let uu____4316 =
                FStar_Util.format1 "Not translating type definition for %s\n"
                  name
                 in
              (FStar_Errors.Warning_DefinitionNotTranslated, uu____4316)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____4311);
           FStar_Pervasives_Native.None)

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4320 = find_t env name  in TBound uu____4320
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4322,t2) ->
          let uu____4324 =
            let uu____4329 = translate_type env t1  in
            let uu____4330 = translate_type env t2  in
            (uu____4329, uu____4330)  in
          TArrow uu____4324
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4334 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4334 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4338 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4338 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4350 = FStar_Util.must (mk_width m)  in TInt uu____4350
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4362 = FStar_Util.must (mk_width m)  in TInt uu____4362
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4367 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4367 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____4368::arg::uu____4370::[],p) when
          (((let uu____4376 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4376 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____4378 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4378 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____4380 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4380 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____4382 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4382 = "FStar.HyperStack.ST.s_mref")
          -> let uu____4383 = translate_type env arg  in TBuf uu____4383
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____4385::[],p) when
          ((((((((((let uu____4391 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4391 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____4393 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4393 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____4395 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4395 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____4397 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4397 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____4399 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4399 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____4401 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4401 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____4403 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4403 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____4405 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4405 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____4407 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4407 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____4409 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4409 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____4411 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4411 = "FStar.HyperStack.ST.mmmref")
          -> let uu____4412 = translate_type env arg  in TBuf uu____4412
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          ((((((((((let uu____4419 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4419 = "FStar.Buffer.buffer") ||
                     (let uu____4421 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4421 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____4423 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4423 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____4425 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4425 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____4427 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4427 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____4429 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4429 = "FStar.HyperStack.mmref"))
                ||
                (let uu____4431 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4431 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____4433 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4433 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____4435 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4435 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____4437 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4437 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____4439 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4439 = "FStar.HyperStack.ST.mmref")
          -> let uu____4440 = translate_type env arg  in TBuf uu____4440
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4441::arg::[],p) when
          (let uu____4448 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4448 = "FStar.HyperStack.s_ref") ||
            (let uu____4450 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4450 = "FStar.HyperStack.ST.s_ref")
          -> let uu____4451 = translate_type env arg  in TBuf uu____4451
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4452::[],p) when
          let uu____4456 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4456 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4494 = FStar_List.map (translate_type env) args  in
          TTuple uu____4494
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4503 =
              let uu____4516 = FStar_List.map (translate_type env) args  in
              (lid, uu____4516)  in
            TApp uu____4503
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4525 = FStar_List.map (translate_type env) ts  in
          TTuple uu____4525

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
    fun uu____4541  ->
      match uu____4541 with
      | (name,typ) ->
          let uu____4548 = translate_type env typ  in
          { name; typ = uu____4548 }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____4553 = find env name  in EBound uu____4553
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4558 =
            let uu____4563 = FStar_Util.must (mk_op op)  in
            let uu____4564 = FStar_Util.must (mk_width m)  in
            (uu____4563, uu____4564)  in
          EOp uu____4558
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4568 =
            let uu____4573 = FStar_Util.must (mk_bool_op op)  in
            (uu____4573, Bool)  in
          EOp uu____4568
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
            let uu____4600 = translate_type env typ  in
            { name; typ = uu____4600 }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4626 =
            let uu____4637 = translate_expr env expr  in
            let uu____4638 = translate_branches env branches  in
            (uu____4637, uu____4638)  in
          EMatch uu____4626
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4652;
                  FStar_Extraction_ML_Syntax.loc = uu____4653;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____4655;
             FStar_Extraction_ML_Syntax.loc = uu____4656;_},arg::[])
          when
          let uu____4662 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4662 = "FStar.Dyn.undyn" ->
          let uu____4663 =
            let uu____4668 = translate_expr env arg  in
            let uu____4669 = translate_type env t  in
            (uu____4668, uu____4669)  in
          ECast uu____4663
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4671;
                  FStar_Extraction_ML_Syntax.loc = uu____4672;_},uu____4673);
             FStar_Extraction_ML_Syntax.mlty = uu____4674;
             FStar_Extraction_ML_Syntax.loc = uu____4675;_},uu____4676)
          when
          let uu____4685 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4685 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4687;
                  FStar_Extraction_ML_Syntax.loc = uu____4688;_},uu____4689);
             FStar_Extraction_ML_Syntax.mlty = uu____4690;
             FStar_Extraction_ML_Syntax.loc = uu____4691;_},arg::[])
          when
          ((let uu____4701 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____4701 = "FStar.HyperStack.All.failwith") ||
             (let uu____4703 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4703 = "FStar.Error.unexpected"))
            ||
            (let uu____4705 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4705 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____4707;
               FStar_Extraction_ML_Syntax.loc = uu____4708;_} -> EAbortS msg
           | uu____4709 ->
               let print7 =
                 let uu____4711 =
                   let uu____4712 =
                     let uu____4713 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____4713
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____4712  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____4711
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
                  FStar_Extraction_ML_Syntax.mlty = uu____4719;
                  FStar_Extraction_ML_Syntax.loc = uu____4720;_},uu____4721);
             FStar_Extraction_ML_Syntax.mlty = uu____4722;
             FStar_Extraction_ML_Syntax.loc = uu____4723;_},e1::e2::[])
          when
          (let uu____4734 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4734 = "FStar.Buffer.index") ||
            (let uu____4736 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4736 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____4737 =
            let uu____4742 = translate_expr env e1  in
            let uu____4743 = translate_expr env e2  in
            (uu____4742, uu____4743)  in
          EBufRead uu____4737
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4745;
                  FStar_Extraction_ML_Syntax.loc = uu____4746;_},uu____4747);
             FStar_Extraction_ML_Syntax.mlty = uu____4748;
             FStar_Extraction_ML_Syntax.loc = uu____4749;_},e1::[])
          when
          let uu____4757 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4757 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____4758 =
            let uu____4763 = translate_expr env e1  in
            (uu____4763, (EConstant (UInt32, "0")))  in
          EBufRead uu____4758
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
          let uu____4778 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4778 = "FStar.Buffer.create" ->
          let uu____4779 =
            let uu____4786 = translate_expr env e1  in
            let uu____4787 = translate_expr env e2  in
            (Stack, uu____4786, uu____4787)  in
          EBufCreate uu____4779
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4789;
                  FStar_Extraction_ML_Syntax.loc = uu____4790;_},uu____4791);
             FStar_Extraction_ML_Syntax.mlty = uu____4792;
             FStar_Extraction_ML_Syntax.loc = uu____4793;_},init1::[])
          when
          let uu____4801 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4801 = "FStar.HyperStack.ST.salloc" ->
          let uu____4802 =
            let uu____4809 = translate_expr env init1  in
            (Stack, uu____4809, (EConstant (UInt32, "1")))  in
          EBufCreate uu____4802
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
             FStar_Extraction_ML_Syntax.loc = uu____4815;_},e2::[])
          when
          let uu____4823 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4823 = "FStar.Buffer.createL" ->
          let rec list_elements acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____4861 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a list literal!"
             in
          let list_elements1 = list_elements []  in
          let uu____4869 =
            let uu____4876 =
              let uu____4879 = list_elements1 e2  in
              FStar_List.map (translate_expr env) uu____4879  in
            (Stack, uu____4876)  in
          EBufCreateL uu____4869
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4885;
                  FStar_Extraction_ML_Syntax.loc = uu____4886;_},uu____4887);
             FStar_Extraction_ML_Syntax.mlty = uu____4888;
             FStar_Extraction_ML_Syntax.loc = uu____4889;_},_rid::init1::[])
          when
          let uu____4898 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4898 = "FStar.HyperStack.ST.ralloc" ->
          let uu____4899 =
            let uu____4906 = translate_expr env init1  in
            (Eternal, uu____4906, (EConstant (UInt32, "1")))  in
          EBufCreate uu____4899
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4908;
                  FStar_Extraction_ML_Syntax.loc = uu____4909;_},uu____4910);
             FStar_Extraction_ML_Syntax.mlty = uu____4911;
             FStar_Extraction_ML_Syntax.loc = uu____4912;_},_e0::e1::e2::[])
          when
          let uu____4922 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4922 = "FStar.Buffer.rcreate" ->
          let uu____4923 =
            let uu____4930 = translate_expr env e1  in
            let uu____4931 = translate_expr env e2  in
            (Eternal, uu____4930, uu____4931)  in
          EBufCreate uu____4923
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4933;
                  FStar_Extraction_ML_Syntax.loc = uu____4934;_},uu____4935);
             FStar_Extraction_ML_Syntax.mlty = uu____4936;
             FStar_Extraction_ML_Syntax.loc = uu____4937;_},_rid::init1::[])
          when
          let uu____4946 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4946 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____4947 =
            let uu____4954 = translate_expr env init1  in
            (ManuallyManaged, uu____4954, (EConstant (UInt32, "1")))  in
          EBufCreate uu____4947
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4956;
                  FStar_Extraction_ML_Syntax.loc = uu____4957;_},uu____4958);
             FStar_Extraction_ML_Syntax.mlty = uu____4959;
             FStar_Extraction_ML_Syntax.loc = uu____4960;_},_e0::e1::e2::[])
          when
          let uu____4970 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4970 = "FStar.Buffer.rcreate_mm" ->
          let uu____4971 =
            let uu____4978 = translate_expr env e1  in
            let uu____4979 = translate_expr env e2  in
            (ManuallyManaged, uu____4978, uu____4979)  in
          EBufCreate uu____4971
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4981;
                  FStar_Extraction_ML_Syntax.loc = uu____4982;_},uu____4983);
             FStar_Extraction_ML_Syntax.mlty = uu____4984;
             FStar_Extraction_ML_Syntax.loc = uu____4985;_},e2::[])
          when
          let uu____4993 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4993 = "FStar.HyperStack.ST.rfree" ->
          let uu____4994 = translate_expr env e2  in EBufFree uu____4994
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4996;
                  FStar_Extraction_ML_Syntax.loc = uu____4997;_},uu____4998);
             FStar_Extraction_ML_Syntax.mlty = uu____4999;
             FStar_Extraction_ML_Syntax.loc = uu____5000;_},e2::[])
          when
          let uu____5008 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5008 = "FStar.Buffer.rfree" ->
          let uu____5009 = translate_expr env e2  in EBufFree uu____5009
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5011;
                  FStar_Extraction_ML_Syntax.loc = uu____5012;_},uu____5013);
             FStar_Extraction_ML_Syntax.mlty = uu____5014;
             FStar_Extraction_ML_Syntax.loc = uu____5015;_},e1::e2::_e3::[])
          when
          let uu____5025 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5025 = "FStar.Buffer.sub" ->
          let uu____5026 =
            let uu____5031 = translate_expr env e1  in
            let uu____5032 = translate_expr env e2  in
            (uu____5031, uu____5032)  in
          EBufSub uu____5026
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5034;
                  FStar_Extraction_ML_Syntax.loc = uu____5035;_},uu____5036);
             FStar_Extraction_ML_Syntax.mlty = uu____5037;
             FStar_Extraction_ML_Syntax.loc = uu____5038;_},e1::e2::[])
          when
          let uu____5047 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5047 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5049;
                  FStar_Extraction_ML_Syntax.loc = uu____5050;_},uu____5051);
             FStar_Extraction_ML_Syntax.mlty = uu____5052;
             FStar_Extraction_ML_Syntax.loc = uu____5053;_},e1::e2::[])
          when
          let uu____5062 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5062 = "FStar.Buffer.offset" ->
          let uu____5063 =
            let uu____5068 = translate_expr env e1  in
            let uu____5069 = translate_expr env e2  in
            (uu____5068, uu____5069)  in
          EBufSub uu____5063
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5071;
                  FStar_Extraction_ML_Syntax.loc = uu____5072;_},uu____5073);
             FStar_Extraction_ML_Syntax.mlty = uu____5074;
             FStar_Extraction_ML_Syntax.loc = uu____5075;_},e1::e2::e3::[])
          when
          (let uu____5087 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5087 = "FStar.Buffer.upd") ||
            (let uu____5089 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5089 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____5090 =
            let uu____5097 = translate_expr env e1  in
            let uu____5098 = translate_expr env e2  in
            let uu____5099 = translate_expr env e3  in
            (uu____5097, uu____5098, uu____5099)  in
          EBufWrite uu____5090
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5101;
                  FStar_Extraction_ML_Syntax.loc = uu____5102;_},uu____5103);
             FStar_Extraction_ML_Syntax.mlty = uu____5104;
             FStar_Extraction_ML_Syntax.loc = uu____5105;_},e1::e2::[])
          when
          let uu____5114 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5114 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5115 =
            let uu____5122 = translate_expr env e1  in
            let uu____5123 = translate_expr env e2  in
            (uu____5122, (EConstant (UInt32, "0")), uu____5123)  in
          EBufWrite uu____5115
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5125;
             FStar_Extraction_ML_Syntax.loc = uu____5126;_},uu____5127::[])
          when
          let uu____5130 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5130 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5132;
             FStar_Extraction_ML_Syntax.loc = uu____5133;_},uu____5134::[])
          when
          let uu____5137 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5137 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5139;
                  FStar_Extraction_ML_Syntax.loc = uu____5140;_},uu____5141);
             FStar_Extraction_ML_Syntax.mlty = uu____5142;
             FStar_Extraction_ML_Syntax.loc = uu____5143;_},e1::e2::e3::e4::e5::[])
          when
          let uu____5155 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5155 = "FStar.Buffer.blit" ->
          let uu____5156 =
            let uu____5167 = translate_expr env e1  in
            let uu____5168 = translate_expr env e2  in
            let uu____5169 = translate_expr env e3  in
            let uu____5170 = translate_expr env e4  in
            let uu____5171 = translate_expr env e5  in
            (uu____5167, uu____5168, uu____5169, uu____5170, uu____5171)  in
          EBufBlit uu____5156
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5173;
                  FStar_Extraction_ML_Syntax.loc = uu____5174;_},uu____5175);
             FStar_Extraction_ML_Syntax.mlty = uu____5176;
             FStar_Extraction_ML_Syntax.loc = uu____5177;_},e1::e2::e3::[])
          when
          let uu____5187 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5187 = "FStar.Buffer.fill" ->
          let uu____5188 =
            let uu____5195 = translate_expr env e1  in
            let uu____5196 = translate_expr env e2  in
            let uu____5197 = translate_expr env e3  in
            (uu____5195, uu____5196, uu____5197)  in
          EBufFill uu____5188
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5199;
             FStar_Extraction_ML_Syntax.loc = uu____5200;_},uu____5201::[])
          when
          let uu____5204 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5204 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5206;
             FStar_Extraction_ML_Syntax.loc = uu____5207;_},e1::[])
          when
          let uu____5211 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5211 = "Obj.repr" ->
          let uu____5212 =
            let uu____5217 = translate_expr env e1  in (uu____5217, TAny)  in
          ECast uu____5212
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5220;
             FStar_Extraction_ML_Syntax.loc = uu____5221;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5229 = FStar_Util.must (mk_width m)  in
          let uu____5230 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____5229 uu____5230 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5232;
             FStar_Extraction_ML_Syntax.loc = uu____5233;_},args)
          when is_bool_op op ->
          let uu____5241 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____5241 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5243;
             FStar_Extraction_ML_Syntax.loc = uu____5244;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5246;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5247;_}::[])
          when is_machine_int m ->
          let uu____5262 =
            let uu____5267 = FStar_Util.must (mk_width m)  in (uu____5267, c)
             in
          EConstant uu____5262
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5269;
             FStar_Extraction_ML_Syntax.loc = uu____5270;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5272;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5273;_}::[])
          when is_machine_int m ->
          let uu____5288 =
            let uu____5293 = FStar_Util.must (mk_width m)  in (uu____5293, c)
             in
          EConstant uu____5288
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5294;
             FStar_Extraction_ML_Syntax.loc = uu____5295;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5297;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5298;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5304 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5305;
             FStar_Extraction_ML_Syntax.loc = uu____5306;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5308;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5309;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5315 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5317;
             FStar_Extraction_ML_Syntax.loc = uu____5318;_},arg::[])
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
            let uu____5325 =
              let uu____5330 = translate_expr env arg  in
              (uu____5330, (TInt UInt64))  in
            ECast uu____5325
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5332 =
                 let uu____5337 = translate_expr env arg  in
                 (uu____5337, (TInt UInt32))  in
               ECast uu____5332)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5339 =
                   let uu____5344 = translate_expr env arg  in
                   (uu____5344, (TInt UInt16))  in
                 ECast uu____5339)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5346 =
                     let uu____5351 = translate_expr env arg  in
                     (uu____5351, (TInt UInt8))  in
                   ECast uu____5346)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5353 =
                       let uu____5358 = translate_expr env arg  in
                       (uu____5358, (TInt Int64))  in
                     ECast uu____5353)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5360 =
                         let uu____5365 = translate_expr env arg  in
                         (uu____5365, (TInt Int32))  in
                       ECast uu____5360)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5367 =
                           let uu____5372 = translate_expr env arg  in
                           (uu____5372, (TInt Int16))  in
                         ECast uu____5367)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5374 =
                             let uu____5379 = translate_expr env arg  in
                             (uu____5379, (TInt Int8))  in
                           ECast uu____5374)
                        else
                          (let uu____5381 =
                             let uu____5388 =
                               let uu____5391 = translate_expr env arg  in
                               [uu____5391]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5388)
                              in
                           EApp uu____5381)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5402 =
            let uu____5409 = translate_expr env head1  in
            let uu____5410 = FStar_List.map (translate_expr env) args  in
            (uu____5409, uu____5410)  in
          EApp uu____5402
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5421 =
            let uu____5428 = translate_expr env head1  in
            let uu____5429 = FStar_List.map (translate_type env) ty_args  in
            (uu____5428, uu____5429)  in
          ETypApp uu____5421
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5437 =
            let uu____5442 = translate_expr env e1  in
            let uu____5443 = translate_type env t_to  in
            (uu____5442, uu____5443)  in
          ECast uu____5437
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5444,fields) ->
          let uu____5462 =
            let uu____5473 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5474 =
              FStar_List.map
                (fun uu____5493  ->
                   match uu____5493 with
                   | (field,expr) ->
                       let uu____5504 = translate_expr env expr  in
                       (field, uu____5504)) fields
               in
            (uu____5473, uu____5474)  in
          EFlat uu____5462
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5513 =
            let uu____5520 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____5521 = translate_expr env e1  in
            (uu____5520, uu____5521, (FStar_Pervasives_Native.snd path))  in
          EField uu____5513
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5524 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5536) ->
          let uu____5541 =
            let uu____5542 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5542
             in
          failwith uu____5541
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5548 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____5548
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5554 = FStar_List.map (translate_expr env) es  in
          ETuple uu____5554
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5557,cons1),es) ->
          let uu____5574 =
            let uu____5583 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5584 = FStar_List.map (translate_expr env) es  in
            (uu____5583, cons1, uu____5584)  in
          ECons uu____5574
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____5607 =
            let uu____5616 = translate_expr env1 body  in
            let uu____5617 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____5616, uu____5617)  in
          EFun uu____5607
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5627 =
            let uu____5634 = translate_expr env e1  in
            let uu____5635 = translate_expr env e2  in
            let uu____5636 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____5634, uu____5635, uu____5636)  in
          EIfThenElse uu____5627
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5638 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5645 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____5660 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____5675 =
              let uu____5688 = FStar_List.map (translate_type env) ts  in
              (lid, uu____5688)  in
            TApp uu____5675
          else TQualified lid
      | uu____5694 -> failwith "invalid argument: assert_lid"

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
    fun uu____5720  ->
      match uu____5720 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____5746 = translate_pat env pat  in
            (match uu____5746 with
             | (env1,pat1) ->
                 let uu____5757 = translate_expr env1 expr  in
                 (pat1, uu____5757))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___41_5763  ->
    match uu___41_5763 with
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
          let uu____5827 =
            let uu____5828 =
              let uu____5833 = translate_width sw  in (uu____5833, s)  in
            PConstant uu____5828  in
          (env, uu____5827)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in (env1, (PVar { name; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5837,cons1),ps) ->
          let uu____5854 =
            FStar_List.fold_left
              (fun uu____5874  ->
                 fun p1  ->
                   match uu____5874 with
                   | (env1,acc) ->
                       let uu____5894 = translate_pat env1 p1  in
                       (match uu____5894 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____5854 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____5923,ps) ->
          let uu____5941 =
            FStar_List.fold_left
              (fun uu____5975  ->
                 fun uu____5976  ->
                   match (uu____5975, uu____5976) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____6045 = translate_pat env1 p1  in
                       (match uu____6045 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____5941 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____6107 =
            FStar_List.fold_left
              (fun uu____6127  ->
                 fun p1  ->
                   match uu____6127 with
                   | (env1,acc) ->
                       let uu____6147 = translate_pat env1 p1  in
                       (match uu____6147 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6107 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6174 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6179 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____6190 =
            let uu____6191 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____6191
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____6190
          then
            let uu____6203 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____6203
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6215) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6230 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6231 ->
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
          let uu____6251 =
            let uu____6258 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____6258)  in
          EApp uu____6251
