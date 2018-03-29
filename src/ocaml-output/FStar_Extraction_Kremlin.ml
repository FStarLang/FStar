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
            let assumed =
              FStar_Util.for_some
                (fun uu___39_3392  ->
                   match uu___39_3392 with
                   | FStar_Extraction_ML_Syntax.Assumed  -> true
                   | uu____3393 -> false) meta
               in
            let env1 =
              if flavor = FStar_Extraction_ML_Syntax.Rec
              then extend env name
              else env  in
            let env2 =
              FStar_List.fold_left
                (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars
               in
            let rec find_return_type eff i uu___40_3414 =
              match uu___40_3414 with
              | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3419,eff1,t) when
                  i > (Prims.parse_int "0") ->
                  find_return_type eff1 (i - (Prims.parse_int "1")) t
              | t -> (eff, t)  in
            let uu____3423 =
              find_return_type FStar_Extraction_ML_Syntax.E_PURE
                (FStar_List.length args) t0
               in
            (match uu____3423 with
             | (eff,t) ->
                 let t1 = translate_type env2 t  in
                 let binders = translate_binders env2 args  in
                 let env3 = add_binders env2 args  in
                 let name1 = ((env3.module_name), name)  in
                 let meta1 =
                   match (eff, t1) with
                   | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____3455) ->
                       let uu____3456 = translate_flags meta  in
                       MustDisappear :: uu____3456
                   | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                       let uu____3459 = translate_flags meta  in
                       MustDisappear :: uu____3459
                   | uu____3462 -> translate_flags meta  in
                 if assumed
                 then
                   (if (FStar_List.length tvars) = (Prims.parse_int "0")
                    then
                      let uu____3471 =
                        let uu____3472 =
                          let uu____3491 = translate_type env3 t0  in
                          (FStar_Pervasives_Native.None, meta1, name1,
                            uu____3491)
                           in
                        DExternal uu____3472  in
                      FStar_Pervasives_Native.Some uu____3471
                    else
                      ((let uu____3504 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath name1
                           in
                        FStar_Util.print1_warning
                          "No writing anything for %s (polymorphic assume)\n"
                          uu____3504);
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
                        ((let uu____3537 =
                            let uu____3542 =
                              let uu____3543 =
                                FStar_Extraction_ML_Syntax.string_of_mlpath
                                  name1
                                 in
                              FStar_Util.format2
                                "Writing a stub for %s (%s)\n" uu____3543 msg
                               in
                            (FStar_Errors.Warning_FunctionNotExtacted,
                              uu____3542)
                             in
                          FStar_Errors.log_issue FStar_Range.dummyRange
                            uu____3537);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3560;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Coerce
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____3563;
                     FStar_Extraction_ML_Syntax.loc = uu____3564;_},uu____3565,uu____3566);
                FStar_Extraction_ML_Syntax.mlty = uu____3567;
                FStar_Extraction_ML_Syntax.loc = uu____3568;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3570;_} ->
            let assumed =
              FStar_Util.for_some
                (fun uu___39_3589  ->
                   match uu___39_3589 with
                   | FStar_Extraction_ML_Syntax.Assumed  -> true
                   | uu____3590 -> false) meta
               in
            let env1 =
              if flavor = FStar_Extraction_ML_Syntax.Rec
              then extend env name
              else env  in
            let env2 =
              FStar_List.fold_left
                (fun env2  -> fun name1  -> extend_t env2 name1) env1 tvars
               in
            let rec find_return_type eff i uu___40_3611 =
              match uu___40_3611 with
              | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3616,eff1,t) when
                  i > (Prims.parse_int "0") ->
                  find_return_type eff1 (i - (Prims.parse_int "1")) t
              | t -> (eff, t)  in
            let uu____3620 =
              find_return_type FStar_Extraction_ML_Syntax.E_PURE
                (FStar_List.length args) t0
               in
            (match uu____3620 with
             | (eff,t) ->
                 let t1 = translate_type env2 t  in
                 let binders = translate_binders env2 args  in
                 let env3 = add_binders env2 args  in
                 let name1 = ((env3.module_name), name)  in
                 let meta1 =
                   match (eff, t1) with
                   | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____3652) ->
                       let uu____3653 = translate_flags meta  in
                       MustDisappear :: uu____3653
                   | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                       let uu____3656 = translate_flags meta  in
                       MustDisappear :: uu____3656
                   | uu____3659 -> translate_flags meta  in
                 if assumed
                 then
                   (if (FStar_List.length tvars) = (Prims.parse_int "0")
                    then
                      let uu____3668 =
                        let uu____3669 =
                          let uu____3688 = translate_type env3 t0  in
                          (FStar_Pervasives_Native.None, meta1, name1,
                            uu____3688)
                           in
                        DExternal uu____3669  in
                      FStar_Pervasives_Native.Some uu____3668
                    else
                      ((let uu____3701 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath name1
                           in
                        FStar_Util.print1_warning
                          "No writing anything for %s (polymorphic assume)\n"
                          uu____3701);
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
                        ((let uu____3734 =
                            let uu____3739 =
                              let uu____3740 =
                                FStar_Extraction_ML_Syntax.string_of_mlpath
                                  name1
                                 in
                              FStar_Util.format2
                                "Writing a stub for %s (%s)\n" uu____3740 msg
                               in
                            (FStar_Errors.Warning_FunctionNotExtacted,
                              uu____3739)
                             in
                          FStar_Errors.log_issue FStar_Range.dummyRange
                            uu____3734);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3757;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3760;_} ->
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
                 ((let uu____3807 =
                     let uu____3812 =
                       let uu____3813 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       let uu____3814 = FStar_Util.print_exn e  in
                       FStar_Util.format2
                         "Not translating definition for %s (%s)\n"
                         uu____3813 uu____3814
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____3812)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____3807);
                  FStar_Pervasives_Native.Some
                    (DGlobal
                       (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3825;
            FStar_Extraction_ML_Syntax.mllb_def = uu____3826;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____3827;
            FStar_Extraction_ML_Syntax.print_typ = uu____3828;_} ->
            ((let uu____3832 =
                let uu____3837 =
                  FStar_Util.format1 "Not translating definition for %s\n"
                    name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____3837)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____3832);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____3845 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____3845
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
            (let uu____3883 =
               let uu____3884 =
                 let uu____3901 = translate_flags flags1  in
                 let uu____3904 = translate_type env1 t  in
                 (name1, uu____3901, (FStar_List.length args), uu____3904)
                  in
               DTypeAlias uu____3884  in
             FStar_Pervasives_Native.Some uu____3883)
      | (uu____3913,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
          let name1 = ((env.module_name), name)  in
          let env1 =
            FStar_List.fold_left
              (fun env1  -> fun name2  -> extend_t env1 name2) env args
             in
          let uu____3945 =
            let uu____3946 =
              let uu____3973 = translate_flags flags1  in
              let uu____3976 =
                FStar_List.map
                  (fun uu____4003  ->
                     match uu____4003 with
                     | (f,t) ->
                         let uu____4018 =
                           let uu____4023 = translate_type env1 t  in
                           (uu____4023, false)  in
                         (f, uu____4018)) fields
                 in
              (name1, uu____3973, (FStar_List.length args), uu____3976)  in
            DTypeFlat uu____3946  in
          FStar_Pervasives_Native.Some uu____3945
      | (uu____4046,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
         (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
          let name1 = ((env.module_name), name)  in
          let flags2 = translate_flags flags1  in
          let env1 = FStar_List.fold_left extend_t env args  in
          let uu____4083 =
            let uu____4084 =
              let uu____4117 =
                FStar_List.map
                  (fun uu____4162  ->
                     match uu____4162 with
                     | (cons1,ts) ->
                         let uu____4201 =
                           FStar_List.map
                             (fun uu____4228  ->
                                match uu____4228 with
                                | (name2,t) ->
                                    let uu____4243 =
                                      let uu____4248 = translate_type env1 t
                                         in
                                      (uu____4248, false)  in
                                    (name2, uu____4243)) ts
                            in
                         (cons1, uu____4201)) branches
                 in
              (name1, flags2, (FStar_List.length args), uu____4117)  in
            DTypeVariant uu____4084  in
          FStar_Pervasives_Native.Some uu____4083
      | (uu____4287,name,_mangled_name,uu____4290,uu____4291,uu____4292) ->
          ((let uu____4302 =
              let uu____4307 =
                FStar_Util.format1 "Not translating type definition for %s\n"
                  name
                 in
              (FStar_Errors.Warning_DefinitionNotTranslated, uu____4307)  in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____4302);
           FStar_Pervasives_Native.None)

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4311 = find_t env name  in TBound uu____4311
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____4313,t2) ->
          let uu____4315 =
            let uu____4320 = translate_type env t1  in
            let uu____4321 = translate_type env t2  in
            (uu____4320, uu____4321)  in
          TArrow uu____4315
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4325 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4325 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____4329 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4329 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____4341 = FStar_Util.must (mk_width m)  in TInt uu____4341
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____4353 = FStar_Util.must (mk_width m)  in TInt uu____4353
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____4358 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4358 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____4359::arg::uu____4361::[],p) when
          (((let uu____4367 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4367 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____4369 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4369 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____4371 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4371 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____4373 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4373 = "FStar.HyperStack.ST.s_mref")
          -> let uu____4374 = translate_type env arg  in TBuf uu____4374
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____4376::[],p) when
          ((((((((((let uu____4382 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4382 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____4384 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4384 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____4386 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4386 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____4388 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4388 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____4390 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4390 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____4392 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4392 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____4394 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4394 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____4396 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4396 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____4398 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4398 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____4400 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4400 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____4402 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4402 = "FStar.HyperStack.ST.mmmref")
          -> let uu____4403 = translate_type env arg  in TBuf uu____4403
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          ((((((((((let uu____4410 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4410 = "FStar.Buffer.buffer") ||
                     (let uu____4412 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____4412 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____4414 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____4414 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____4416 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____4416 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____4418 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____4418 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____4420 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____4420 = "FStar.HyperStack.mmref"))
                ||
                (let uu____4422 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____4422 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____4424 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____4424 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____4426 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____4426 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____4428 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4428 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____4430 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4430 = "FStar.HyperStack.ST.mmref")
          -> let uu____4431 = translate_type env arg  in TBuf uu____4431
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4432::arg::[],p) when
          (let uu____4439 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4439 = "FStar.HyperStack.s_ref") ||
            (let uu____4441 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4441 = "FStar.HyperStack.ST.s_ref")
          -> let uu____4442 = translate_type env arg  in TBuf uu____4442
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4443::[],p) when
          let uu____4447 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4447 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4485 = FStar_List.map (translate_type env) args  in
          TTuple uu____4485
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4494 =
              let uu____4507 = FStar_List.map (translate_type env) args  in
              (lid, uu____4507)  in
            TApp uu____4494
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4516 = FStar_List.map (translate_type env) ts  in
          TTuple uu____4516

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
    fun uu____4532  ->
      match uu____4532 with
      | (name,typ) ->
          let uu____4539 = translate_type env typ  in
          { name; typ = uu____4539 }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____4544 = find env name  in EBound uu____4544
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4549 =
            let uu____4554 = FStar_Util.must (mk_op op)  in
            let uu____4555 = FStar_Util.must (mk_width m)  in
            (uu____4554, uu____4555)  in
          EOp uu____4549
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____4559 =
            let uu____4564 = FStar_Util.must (mk_bool_op op)  in
            (uu____4564, Bool)  in
          EOp uu____4559
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
            let uu____4591 = translate_type env typ  in
            { name; typ = uu____4591 }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____4617 =
            let uu____4628 = translate_expr env expr  in
            let uu____4629 = translate_branches env branches  in
            (uu____4628, uu____4629)  in
          EMatch uu____4617
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4643;
                  FStar_Extraction_ML_Syntax.loc = uu____4644;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____4646;
             FStar_Extraction_ML_Syntax.loc = uu____4647;_},arg::[])
          when
          let uu____4653 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4653 = "FStar.Dyn.undyn" ->
          let uu____4654 =
            let uu____4659 = translate_expr env arg  in
            let uu____4660 = translate_type env t  in
            (uu____4659, uu____4660)  in
          ECast uu____4654
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4662;
                  FStar_Extraction_ML_Syntax.loc = uu____4663;_},uu____4664);
             FStar_Extraction_ML_Syntax.mlty = uu____4665;
             FStar_Extraction_ML_Syntax.loc = uu____4666;_},uu____4667)
          when
          let uu____4676 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4676 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4678;
                  FStar_Extraction_ML_Syntax.loc = uu____4679;_},uu____4680);
             FStar_Extraction_ML_Syntax.mlty = uu____4681;
             FStar_Extraction_ML_Syntax.loc = uu____4682;_},arg::[])
          when
          ((let uu____4692 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____4692 = "FStar.HyperStack.All.failwith") ||
             (let uu____4694 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____4694 = "FStar.Error.unexpected"))
            ||
            (let uu____4696 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4696 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____4698;
               FStar_Extraction_ML_Syntax.loc = uu____4699;_} -> EAbortS msg
           | uu____4700 ->
               let print7 =
                 let uu____4702 =
                   let uu____4703 =
                     let uu____4704 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____4704
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____4703  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____4702
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
                  FStar_Extraction_ML_Syntax.mlty = uu____4710;
                  FStar_Extraction_ML_Syntax.loc = uu____4711;_},uu____4712);
             FStar_Extraction_ML_Syntax.mlty = uu____4713;
             FStar_Extraction_ML_Syntax.loc = uu____4714;_},e1::e2::[])
          when
          (let uu____4725 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____4725 = "FStar.Buffer.index") ||
            (let uu____4727 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____4727 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____4728 =
            let uu____4733 = translate_expr env e1  in
            let uu____4734 = translate_expr env e2  in
            (uu____4733, uu____4734)  in
          EBufRead uu____4728
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4736;
                  FStar_Extraction_ML_Syntax.loc = uu____4737;_},uu____4738);
             FStar_Extraction_ML_Syntax.mlty = uu____4739;
             FStar_Extraction_ML_Syntax.loc = uu____4740;_},e1::[])
          when
          let uu____4748 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4748 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____4749 =
            let uu____4754 = translate_expr env e1  in
            (uu____4754, (EConstant (UInt32, "0")))  in
          EBufRead uu____4749
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4756;
                  FStar_Extraction_ML_Syntax.loc = uu____4757;_},uu____4758);
             FStar_Extraction_ML_Syntax.mlty = uu____4759;
             FStar_Extraction_ML_Syntax.loc = uu____4760;_},e1::e2::[])
          when
          let uu____4769 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4769 = "FStar.Buffer.create" ->
          let uu____4770 =
            let uu____4777 = translate_expr env e1  in
            let uu____4778 = translate_expr env e2  in
            (Stack, uu____4777, uu____4778)  in
          EBufCreate uu____4770
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4780;
                  FStar_Extraction_ML_Syntax.loc = uu____4781;_},uu____4782);
             FStar_Extraction_ML_Syntax.mlty = uu____4783;
             FStar_Extraction_ML_Syntax.loc = uu____4784;_},init1::[])
          when
          let uu____4792 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4792 = "FStar.HyperStack.ST.salloc" ->
          let uu____4793 =
            let uu____4800 = translate_expr env init1  in
            (Stack, uu____4800, (EConstant (UInt32, "1")))  in
          EBufCreate uu____4793
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4802;
                  FStar_Extraction_ML_Syntax.loc = uu____4803;_},uu____4804);
             FStar_Extraction_ML_Syntax.mlty = uu____4805;
             FStar_Extraction_ML_Syntax.loc = uu____4806;_},e2::[])
          when
          let uu____4814 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4814 = "FStar.Buffer.createL" ->
          let rec list_elements acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[],"Cons"),hd1::tl1::[]) ->
                list_elements (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[],"Nil"),[]) ->
                FStar_List.rev acc
            | uu____4852 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a list literal!"
             in
          let list_elements1 = list_elements []  in
          let uu____4860 =
            let uu____4867 =
              let uu____4870 = list_elements1 e2  in
              FStar_List.map (translate_expr env) uu____4870  in
            (Stack, uu____4867)  in
          EBufCreateL uu____4860
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4876;
                  FStar_Extraction_ML_Syntax.loc = uu____4877;_},uu____4878);
             FStar_Extraction_ML_Syntax.mlty = uu____4879;
             FStar_Extraction_ML_Syntax.loc = uu____4880;_},_rid::init1::[])
          when
          let uu____4889 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4889 = "FStar.HyperStack.ST.ralloc" ->
          let uu____4890 =
            let uu____4897 = translate_expr env init1  in
            (Eternal, uu____4897, (EConstant (UInt32, "1")))  in
          EBufCreate uu____4890
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4899;
                  FStar_Extraction_ML_Syntax.loc = uu____4900;_},uu____4901);
             FStar_Extraction_ML_Syntax.mlty = uu____4902;
             FStar_Extraction_ML_Syntax.loc = uu____4903;_},_e0::e1::e2::[])
          when
          let uu____4913 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4913 = "FStar.Buffer.rcreate" ->
          let uu____4914 =
            let uu____4921 = translate_expr env e1  in
            let uu____4922 = translate_expr env e2  in
            (Eternal, uu____4921, uu____4922)  in
          EBufCreate uu____4914
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4924;
                  FStar_Extraction_ML_Syntax.loc = uu____4925;_},uu____4926);
             FStar_Extraction_ML_Syntax.mlty = uu____4927;
             FStar_Extraction_ML_Syntax.loc = uu____4928;_},_rid::init1::[])
          when
          let uu____4937 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4937 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____4938 =
            let uu____4945 = translate_expr env init1  in
            (ManuallyManaged, uu____4945, (EConstant (UInt32, "1")))  in
          EBufCreate uu____4938
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4947;
                  FStar_Extraction_ML_Syntax.loc = uu____4948;_},uu____4949);
             FStar_Extraction_ML_Syntax.mlty = uu____4950;
             FStar_Extraction_ML_Syntax.loc = uu____4951;_},_e0::e1::e2::[])
          when
          let uu____4961 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4961 = "FStar.Buffer.rcreate_mm" ->
          let uu____4962 =
            let uu____4969 = translate_expr env e1  in
            let uu____4970 = translate_expr env e2  in
            (ManuallyManaged, uu____4969, uu____4970)  in
          EBufCreate uu____4962
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4972;
                  FStar_Extraction_ML_Syntax.loc = uu____4973;_},uu____4974);
             FStar_Extraction_ML_Syntax.mlty = uu____4975;
             FStar_Extraction_ML_Syntax.loc = uu____4976;_},e2::[])
          when
          let uu____4984 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4984 = "FStar.HyperStack.ST.rfree" ->
          let uu____4985 = translate_expr env e2  in EBufFree uu____4985
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4987;
                  FStar_Extraction_ML_Syntax.loc = uu____4988;_},uu____4989);
             FStar_Extraction_ML_Syntax.mlty = uu____4990;
             FStar_Extraction_ML_Syntax.loc = uu____4991;_},e2::[])
          when
          let uu____4999 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____4999 = "FStar.Buffer.rfree" ->
          let uu____5000 = translate_expr env e2  in EBufFree uu____5000
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5002;
                  FStar_Extraction_ML_Syntax.loc = uu____5003;_},uu____5004);
             FStar_Extraction_ML_Syntax.mlty = uu____5005;
             FStar_Extraction_ML_Syntax.loc = uu____5006;_},e1::e2::_e3::[])
          when
          let uu____5016 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5016 = "FStar.Buffer.sub" ->
          let uu____5017 =
            let uu____5022 = translate_expr env e1  in
            let uu____5023 = translate_expr env e2  in
            (uu____5022, uu____5023)  in
          EBufSub uu____5017
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5025;
                  FStar_Extraction_ML_Syntax.loc = uu____5026;_},uu____5027);
             FStar_Extraction_ML_Syntax.mlty = uu____5028;
             FStar_Extraction_ML_Syntax.loc = uu____5029;_},e1::e2::[])
          when
          let uu____5038 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5038 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5040;
                  FStar_Extraction_ML_Syntax.loc = uu____5041;_},uu____5042);
             FStar_Extraction_ML_Syntax.mlty = uu____5043;
             FStar_Extraction_ML_Syntax.loc = uu____5044;_},e1::e2::[])
          when
          let uu____5053 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5053 = "FStar.Buffer.offset" ->
          let uu____5054 =
            let uu____5059 = translate_expr env e1  in
            let uu____5060 = translate_expr env e2  in
            (uu____5059, uu____5060)  in
          EBufSub uu____5054
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5062;
                  FStar_Extraction_ML_Syntax.loc = uu____5063;_},uu____5064);
             FStar_Extraction_ML_Syntax.mlty = uu____5065;
             FStar_Extraction_ML_Syntax.loc = uu____5066;_},e1::e2::e3::[])
          when
          (let uu____5078 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____5078 = "FStar.Buffer.upd") ||
            (let uu____5080 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____5080 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____5081 =
            let uu____5088 = translate_expr env e1  in
            let uu____5089 = translate_expr env e2  in
            let uu____5090 = translate_expr env e3  in
            (uu____5088, uu____5089, uu____5090)  in
          EBufWrite uu____5081
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5092;
                  FStar_Extraction_ML_Syntax.loc = uu____5093;_},uu____5094);
             FStar_Extraction_ML_Syntax.mlty = uu____5095;
             FStar_Extraction_ML_Syntax.loc = uu____5096;_},e1::e2::[])
          when
          let uu____5105 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5105 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5106 =
            let uu____5113 = translate_expr env e1  in
            let uu____5114 = translate_expr env e2  in
            (uu____5113, (EConstant (UInt32, "0")), uu____5114)  in
          EBufWrite uu____5106
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5116;
             FStar_Extraction_ML_Syntax.loc = uu____5117;_},uu____5118::[])
          when
          let uu____5121 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5121 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5123;
             FStar_Extraction_ML_Syntax.loc = uu____5124;_},uu____5125::[])
          when
          let uu____5128 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5128 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5130;
                  FStar_Extraction_ML_Syntax.loc = uu____5131;_},uu____5132);
             FStar_Extraction_ML_Syntax.mlty = uu____5133;
             FStar_Extraction_ML_Syntax.loc = uu____5134;_},e1::e2::e3::e4::e5::[])
          when
          let uu____5146 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5146 = "FStar.Buffer.blit" ->
          let uu____5147 =
            let uu____5158 = translate_expr env e1  in
            let uu____5159 = translate_expr env e2  in
            let uu____5160 = translate_expr env e3  in
            let uu____5161 = translate_expr env e4  in
            let uu____5162 = translate_expr env e5  in
            (uu____5158, uu____5159, uu____5160, uu____5161, uu____5162)  in
          EBufBlit uu____5147
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5164;
                  FStar_Extraction_ML_Syntax.loc = uu____5165;_},uu____5166);
             FStar_Extraction_ML_Syntax.mlty = uu____5167;
             FStar_Extraction_ML_Syntax.loc = uu____5168;_},e1::e2::e3::[])
          when
          let uu____5178 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5178 = "FStar.Buffer.fill" ->
          let uu____5179 =
            let uu____5186 = translate_expr env e1  in
            let uu____5187 = translate_expr env e2  in
            let uu____5188 = translate_expr env e3  in
            (uu____5186, uu____5187, uu____5188)  in
          EBufFill uu____5179
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5190;
             FStar_Extraction_ML_Syntax.loc = uu____5191;_},uu____5192::[])
          when
          let uu____5195 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5195 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5197;
             FStar_Extraction_ML_Syntax.loc = uu____5198;_},e1::[])
          when
          let uu____5202 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____5202 = "Obj.repr" ->
          let uu____5203 =
            let uu____5208 = translate_expr env e1  in (uu____5208, TAny)  in
          ECast uu____5203
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5211;
             FStar_Extraction_ML_Syntax.loc = uu____5212;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5220 = FStar_Util.must (mk_width m)  in
          let uu____5221 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____5220 uu____5221 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____5223;
             FStar_Extraction_ML_Syntax.loc = uu____5224;_},args)
          when is_bool_op op ->
          let uu____5232 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____5232 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5234;
             FStar_Extraction_ML_Syntax.loc = uu____5235;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5237;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5238;_}::[])
          when is_machine_int m ->
          let uu____5253 =
            let uu____5258 = FStar_Util.must (mk_width m)  in (uu____5258, c)
             in
          EConstant uu____5253
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5260;
             FStar_Extraction_ML_Syntax.loc = uu____5261;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5263;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5264;_}::[])
          when is_machine_int m ->
          let uu____5279 =
            let uu____5284 = FStar_Util.must (mk_width m)  in (uu____5284, c)
             in
          EConstant uu____5279
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5285;
             FStar_Extraction_ML_Syntax.loc = uu____5286;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5288;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5289;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5295 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5296;
             FStar_Extraction_ML_Syntax.loc = uu____5297;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____5299;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____5300;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5306 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____5308;
             FStar_Extraction_ML_Syntax.loc = uu____5309;_},arg::[])
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
            let uu____5316 =
              let uu____5321 = translate_expr env arg  in
              (uu____5321, (TInt UInt64))  in
            ECast uu____5316
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5323 =
                 let uu____5328 = translate_expr env arg  in
                 (uu____5328, (TInt UInt32))  in
               ECast uu____5323)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5330 =
                   let uu____5335 = translate_expr env arg  in
                   (uu____5335, (TInt UInt16))  in
                 ECast uu____5330)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5337 =
                     let uu____5342 = translate_expr env arg  in
                     (uu____5342, (TInt UInt8))  in
                   ECast uu____5337)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5344 =
                       let uu____5349 = translate_expr env arg  in
                       (uu____5349, (TInt Int64))  in
                     ECast uu____5344)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5351 =
                         let uu____5356 = translate_expr env arg  in
                         (uu____5356, (TInt Int32))  in
                       ECast uu____5351)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5358 =
                           let uu____5363 = translate_expr env arg  in
                           (uu____5363, (TInt Int16))  in
                         ECast uu____5358)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5365 =
                             let uu____5370 = translate_expr env arg  in
                             (uu____5370, (TInt Int8))  in
                           ECast uu____5365)
                        else
                          (let uu____5372 =
                             let uu____5379 =
                               let uu____5382 = translate_expr env arg  in
                               [uu____5382]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5379)
                              in
                           EApp uu____5372)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____5393 =
            let uu____5400 = translate_expr env head1  in
            let uu____5401 = FStar_List.map (translate_expr env) args  in
            (uu____5400, uu____5401)  in
          EApp uu____5393
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____5412 =
            let uu____5419 = translate_expr env head1  in
            let uu____5420 = FStar_List.map (translate_type env) ty_args  in
            (uu____5419, uu____5420)  in
          ETypApp uu____5412
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____5428 =
            let uu____5433 = translate_expr env e1  in
            let uu____5434 = translate_type env t_to  in
            (uu____5433, uu____5434)  in
          ECast uu____5428
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5435,fields) ->
          let uu____5453 =
            let uu____5464 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5465 =
              FStar_List.map
                (fun uu____5484  ->
                   match uu____5484 with
                   | (field,expr) ->
                       let uu____5495 = translate_expr env expr  in
                       (field, uu____5495)) fields
               in
            (uu____5464, uu____5465)  in
          EFlat uu____5453
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____5504 =
            let uu____5511 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____5512 = translate_expr env e1  in
            (uu____5511, uu____5512, (FStar_Pervasives_Native.snd path))  in
          EField uu____5504
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5515 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____5527) ->
          let uu____5532 =
            let uu____5533 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5533
             in
          failwith uu____5532
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5539 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____5539
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5545 = FStar_List.map (translate_expr env) es  in
          ETuple uu____5545
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5548,cons1),es) ->
          let uu____5565 =
            let uu____5574 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____5575 = FStar_List.map (translate_expr env) es  in
            (uu____5574, cons1, uu____5575)  in
          ECons uu____5565
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____5598 =
            let uu____5607 = translate_expr env1 body  in
            let uu____5608 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____5607, uu____5608)  in
          EFun uu____5598
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____5618 =
            let uu____5625 = translate_expr env e1  in
            let uu____5626 = translate_expr env e2  in
            let uu____5627 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____5625, uu____5626, uu____5627)  in
          EIfThenElse uu____5618
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5629 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5636 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____5651 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____5666 =
              let uu____5679 = FStar_List.map (translate_type env) ts  in
              (lid, uu____5679)  in
            TApp uu____5666
          else TQualified lid
      | uu____5685 -> failwith "invalid argument: assert_lid"

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
    fun uu____5711  ->
      match uu____5711 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____5737 = translate_pat env pat  in
            (match uu____5737 with
             | (env1,pat1) ->
                 let uu____5748 = translate_expr env1 expr  in
                 (pat1, uu____5748))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness,FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___41_5754  ->
    match uu___41_5754 with
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
          let uu____5818 =
            let uu____5819 =
              let uu____5824 = translate_width sw  in (uu____5824, s)  in
            PConstant uu____5819  in
          (env, uu____5818)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in (env1, (PVar { name; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5828,cons1),ps) ->
          let uu____5845 =
            FStar_List.fold_left
              (fun uu____5865  ->
                 fun p1  ->
                   match uu____5865 with
                   | (env1,acc) ->
                       let uu____5885 = translate_pat env1 p1  in
                       (match uu____5885 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____5845 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____5914,ps) ->
          let uu____5932 =
            FStar_List.fold_left
              (fun uu____5966  ->
                 fun uu____5967  ->
                   match (uu____5966, uu____5967) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____6036 = translate_pat env1 p1  in
                       (match uu____6036 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____5932 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____6098 =
            FStar_List.fold_left
              (fun uu____6118  ->
                 fun p1  ->
                   match uu____6118 with
                   | (env1,acc) ->
                       let uu____6138 = translate_pat env1 p1  in
                       (match uu____6138 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____6098 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6165 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6170 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____6181 =
            let uu____6182 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____6182
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____6181
          then
            let uu____6194 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____6194
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____6206) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6221 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6222 ->
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
          let uu____6242 =
            let uu____6249 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____6249)  in
          EApp uu____6242
