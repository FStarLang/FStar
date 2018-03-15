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
  | PCons of (Prims.string, pattern Prims.list)
  FStar_Pervasives_Native.tuple2 
  | PTuple of pattern Prims.list 
  | PRecord of (Prims.string, pattern) FStar_Pervasives_Native.tuple2
  Prims.list 
  | PConstant of (width, Prims.string) FStar_Pervasives_Native.tuple2 
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
  | TQualified of (Prims.string Prims.list, Prims.string)
  FStar_Pervasives_Native.tuple2 
  | TBool 
  | TAny 
  | TArrow of (typ, typ) FStar_Pervasives_Native.tuple2 
  | TBound of Prims.int 
  | TApp of
  ((Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
  typ Prims.list) FStar_Pervasives_Native.tuple2 
  | TTuple of typ Prims.list [@@deriving show]
let (uu___is_DGlobal : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DGlobal _0 -> true | uu____563 -> false
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list,
      (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
      Prims.int, typ, expr) FStar_Pervasives_Native.tuple5)
  = fun projectee -> match projectee with | DGlobal _0 -> _0
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DFunction _0 -> true | uu____655 -> false
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option, flag Prims.list, Prims.int, typ,
      (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
      binder Prims.list, expr) FStar_Pervasives_Native.tuple7)
  = fun projectee -> match projectee with | DFunction _0 -> _0
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeAlias _0 -> true | uu____761 -> false
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
      flag Prims.list, Prims.int, typ) FStar_Pervasives_Native.tuple4)
  = fun projectee -> match projectee with | DTypeAlias _0 -> _0
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeFlat _0 -> true | uu____847 -> false
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
    match projectee with | DExternal _0 -> true | uu____955 -> false
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option, flag Prims.list,
      (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
      typ) FStar_Pervasives_Native.tuple4)
  = fun projectee -> match projectee with | DExternal _0 -> _0
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeVariant _0 -> true | uu____1053 -> false
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
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee ->
    match projectee with | StdCall -> true | uu____1160 -> false
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee -> match projectee with | CDecl -> true | uu____1164 -> false
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee ->
    match projectee with | FastCall -> true | uu____1168 -> false
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Private -> true | uu____1172 -> false
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | WipeBody -> true | uu____1176 -> false
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | CInline -> true | uu____1180 -> false
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Substitute -> true | uu____1184 -> false
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | GCType -> true | uu____1188 -> false
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Comment _0 -> true | uu____1193 -> false
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Comment _0 -> _0
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | MustDisappear -> true | uu____1204 -> false
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Const _0 -> true | uu____1209 -> false
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Const _0 -> _0
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Prologue _0 -> true | uu____1221 -> false
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Prologue _0 -> _0
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Epilogue _0 -> true | uu____1233 -> false
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Epilogue _0 -> _0
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee ->
    match projectee with | Eternal -> true | uu____1244 -> false
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee -> match projectee with | Stack -> true | uu____1248 -> false
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee ->
    match projectee with | ManuallyManaged -> true | uu____1252 -> false
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBound _0 -> true | uu____1257 -> false
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee -> match projectee with | EBound _0 -> _0
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EQualified _0 -> true | uu____1275 -> false
let (__proj__EQualified__item___0 :
  expr ->
    (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | EQualified _0 -> _0
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EConstant _0 -> true | uu____1309 -> false
let (__proj__EConstant__item___0 :
  expr -> (width, Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | EConstant _0 -> _0
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee -> match projectee with | EUnit -> true | uu____1332 -> false
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EApp _0 -> true | uu____1343 -> false
let (__proj__EApp__item___0 :
  expr -> (expr, expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | EApp _0 -> _0
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ETypApp _0 -> true | uu____1379 -> false
let (__proj__ETypApp__item___0 :
  expr -> (expr, typ Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | ETypApp _0 -> _0
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ELet _0 -> true | uu____1415 -> false
let (__proj__ELet__item___0 :
  expr -> (binder, expr, expr) FStar_Pervasives_Native.tuple3) =
  fun projectee -> match projectee with | ELet _0 -> _0
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EIfThenElse _0 -> true | uu____1451 -> false
let (__proj__EIfThenElse__item___0 :
  expr -> (expr, expr, expr) FStar_Pervasives_Native.tuple3) =
  fun projectee -> match projectee with | EIfThenElse _0 -> _0
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ESequence _0 -> true | uu____1483 -> false
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee -> match projectee with | ESequence _0 -> _0
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EAssign _0 -> true | uu____1505 -> false
let (__proj__EAssign__item___0 :
  expr -> (expr, expr) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | EAssign _0 -> _0
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufCreate _0 -> true | uu____1535 -> false
let (__proj__EBufCreate__item___0 :
  expr -> (lifetime, expr, expr) FStar_Pervasives_Native.tuple3) =
  fun projectee -> match projectee with | EBufCreate _0 -> _0
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufRead _0 -> true | uu____1569 -> false
let (__proj__EBufRead__item___0 :
  expr -> (expr, expr) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | EBufRead _0 -> _0
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufWrite _0 -> true | uu____1599 -> false
let (__proj__EBufWrite__item___0 :
  expr -> (expr, expr, expr) FStar_Pervasives_Native.tuple3) =
  fun projectee -> match projectee with | EBufWrite _0 -> _0
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufSub _0 -> true | uu____1633 -> false
let (__proj__EBufSub__item___0 :
  expr -> (expr, expr) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | EBufSub _0 -> _0
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufBlit _0 -> true | uu____1667 -> false
let (__proj__EBufBlit__item___0 :
  expr -> (expr, expr, expr, expr, expr) FStar_Pervasives_Native.tuple5) =
  fun projectee -> match projectee with | EBufBlit _0 -> _0
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EMatch _0 -> true | uu____1719 -> false
let (__proj__EMatch__item___0 :
  expr ->
    (expr, (pattern, expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | EMatch _0 -> _0
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EOp _0 -> true | uu____1765 -> false
let (__proj__EOp__item___0 :
  expr -> (op, width) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | EOp _0 -> _0
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ECast _0 -> true | uu____1793 -> false
let (__proj__ECast__item___0 :
  expr -> (expr, typ) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | ECast _0 -> _0
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EPushFrame -> true | uu____1816 -> false
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EPopFrame -> true | uu____1820 -> false
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBool _0 -> true | uu____1825 -> false
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee -> match projectee with | EBool _0 -> _0
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee -> match projectee with | EAny -> true | uu____1836 -> false
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EAbort -> true | uu____1840 -> false
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EReturn _0 -> true | uu____1845 -> false
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee -> match projectee with | EReturn _0 -> _0
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EFlat _0 -> true | uu____1867 -> false
let (__proj__EFlat__item___0 :
  expr ->
    (typ, (Prims.string, expr) FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | EFlat _0 -> _0
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EField _0 -> true | uu____1915 -> false
let (__proj__EField__item___0 :
  expr -> (typ, expr, Prims.string) FStar_Pervasives_Native.tuple3) =
  fun projectee -> match projectee with | EField _0 -> _0
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EWhile _0 -> true | uu____1949 -> false
let (__proj__EWhile__item___0 :
  expr -> (expr, expr) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | EWhile _0 -> _0
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufCreateL _0 -> true | uu____1979 -> false
let (__proj__EBufCreateL__item___0 :
  expr -> (lifetime, expr Prims.list) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | EBufCreateL _0 -> _0
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ETuple _0 -> true | uu____2011 -> false
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee -> match projectee with | ETuple _0 -> _0
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ECons _0 -> true | uu____2037 -> false
let (__proj__ECons__item___0 :
  expr -> (typ, Prims.string, expr Prims.list) FStar_Pervasives_Native.tuple3)
  = fun projectee -> match projectee with | ECons _0 -> _0
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufFill _0 -> true | uu____2079 -> false
let (__proj__EBufFill__item___0 :
  expr -> (expr, expr, expr) FStar_Pervasives_Native.tuple3) =
  fun projectee -> match projectee with | EBufFill _0 -> _0
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EString _0 -> true | uu____2109 -> false
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee -> match projectee with | EString _0 -> _0
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EFun _0 -> true | uu____2129 -> false
let (__proj__EFun__item___0 :
  expr -> (binder Prims.list, expr, typ) FStar_Pervasives_Native.tuple3) =
  fun projectee -> match projectee with | EFun _0 -> _0
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EAbortS _0 -> true | uu____2165 -> false
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee -> match projectee with | EAbortS _0 -> _0
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufFree _0 -> true | uu____2177 -> false
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee -> match projectee with | EBufFree _0 -> _0
let (uu___is_Add : op -> Prims.bool) =
  fun projectee -> match projectee with | Add -> true | uu____2188 -> false
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee -> match projectee with | AddW -> true | uu____2192 -> false
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee -> match projectee with | Sub -> true | uu____2196 -> false
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee -> match projectee with | SubW -> true | uu____2200 -> false
let (uu___is_Div : op -> Prims.bool) =
  fun projectee -> match projectee with | Div -> true | uu____2204 -> false
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee -> match projectee with | DivW -> true | uu____2208 -> false
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee -> match projectee with | Mult -> true | uu____2212 -> false
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee -> match projectee with | MultW -> true | uu____2216 -> false
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee -> match projectee with | Mod -> true | uu____2220 -> false
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee -> match projectee with | BOr -> true | uu____2224 -> false
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee -> match projectee with | BAnd -> true | uu____2228 -> false
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee -> match projectee with | BXor -> true | uu____2232 -> false
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee ->
    match projectee with | BShiftL -> true | uu____2236 -> false
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee ->
    match projectee with | BShiftR -> true | uu____2240 -> false
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee -> match projectee with | BNot -> true | uu____2244 -> false
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee -> match projectee with | Eq -> true | uu____2248 -> false
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee -> match projectee with | Neq -> true | uu____2252 -> false
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee -> match projectee with | Lt -> true | uu____2256 -> false
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee -> match projectee with | Lte -> true | uu____2260 -> false
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee -> match projectee with | Gt -> true | uu____2264 -> false
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee -> match projectee with | Gte -> true | uu____2268 -> false
let (uu___is_And : op -> Prims.bool) =
  fun projectee -> match projectee with | And -> true | uu____2272 -> false
let (uu___is_Or : op -> Prims.bool) =
  fun projectee -> match projectee with | Or -> true | uu____2276 -> false
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee -> match projectee with | Xor -> true | uu____2280 -> false
let (uu___is_Not : op -> Prims.bool) =
  fun projectee -> match projectee with | Not -> true | uu____2284 -> false
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PUnit -> true | uu____2288 -> false
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PBool _0 -> true | uu____2293 -> false
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PBool _0 -> _0
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PVar _0 -> true | uu____2305 -> false
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee -> match projectee with | PVar _0 -> _0
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PCons _0 -> true | uu____2323 -> false
let (__proj__PCons__item___0 :
  pattern ->
    (Prims.string, pattern Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | PCons _0 -> _0
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PTuple _0 -> true | uu____2355 -> false
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee -> match projectee with | PTuple _0 -> _0
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PRecord _0 -> true | uu____2379 -> false
let (__proj__PRecord__item___0 :
  pattern ->
    (Prims.string, pattern) FStar_Pervasives_Native.tuple2 Prims.list)
  = fun projectee -> match projectee with | PRecord _0 -> _0
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PConstant _0 -> true | uu____2413 -> false
let (__proj__PConstant__item___0 :
  pattern -> (width, Prims.string) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | PConstant _0 -> _0
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee -> match projectee with | UInt8 -> true | uu____2436 -> false
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee ->
    match projectee with | UInt16 -> true | uu____2440 -> false
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee ->
    match projectee with | UInt32 -> true | uu____2444 -> false
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee ->
    match projectee with | UInt64 -> true | uu____2448 -> false
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int8 -> true | uu____2452 -> false
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int16 -> true | uu____2456 -> false
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int32 -> true | uu____2460 -> false
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int64 -> true | uu____2464 -> false
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee -> match projectee with | Bool -> true | uu____2468 -> false
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee -> match projectee with | CInt -> true | uu____2472 -> false
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
    match projectee with | TInt _0 -> true | uu____2495 -> false
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee -> match projectee with | TInt _0 -> _0
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TBuf _0 -> true | uu____2507 -> false
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee -> match projectee with | TBuf _0 -> _0
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee -> match projectee with | TUnit -> true | uu____2518 -> false
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TQualified _0 -> true | uu____2529 -> false
let (__proj__TQualified__item___0 :
  typ ->
    (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | TQualified _0 -> _0
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee -> match projectee with | TBool -> true | uu____2558 -> false
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee -> match projectee with | TAny -> true | uu____2562 -> false
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TArrow _0 -> true | uu____2571 -> false
let (__proj__TArrow__item___0 :
  typ -> (typ, typ) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | TArrow _0 -> _0
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TBound _0 -> true | uu____2595 -> false
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee -> match projectee with | TBound _0 -> _0
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TApp _0 -> true | uu____2619 -> false
let (__proj__TApp__item___0 :
  typ ->
    ((Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2,
      typ Prims.list) FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | TApp _0 -> _0
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TTuple _0 -> true | uu____2669 -> false
let (__proj__TTuple__item___0 : typ -> typ Prims.list) =
  fun projectee -> match projectee with | TTuple _0 -> _0
type program = decl Prims.list[@@deriving show]
type ident = Prims.string[@@deriving show]
type fields_t =
  (Prims.string, (typ, Prims.bool) FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
type branches_t =
  (Prims.string,
    (Prims.string, (typ, Prims.bool) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2 Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
type fsdoc = Prims.string[@@deriving show]
type branch = (pattern, expr) FStar_Pervasives_Native.tuple2[@@deriving show]
type branches = (pattern, expr) FStar_Pervasives_Native.tuple2 Prims.list
[@@deriving show]
type constant = (width, Prims.string) FStar_Pervasives_Native.tuple2[@@deriving
                                                                    show]
type var = Prims.int[@@deriving show]
type lident =
  (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2
[@@deriving show]
type version = Prims.int[@@deriving show]
let (current_version : version) = (Prims.parse_int "27")
type file = (Prims.string, program) FStar_Pervasives_Native.tuple2[@@deriving
                                                                    show]
type binary_format =
  (version, file Prims.list) FStar_Pervasives_Native.tuple2[@@deriving show]
let fst3 :
  'Auu____2745 'Auu____2746 'Auu____2747 .
    ('Auu____2745, 'Auu____2746, 'Auu____2747) FStar_Pervasives_Native.tuple3
      -> 'Auu____2745
  =
  fun uu____2757 -> match uu____2757 with | (x, uu____2765, uu____2766) -> x
let snd3 :
  'Auu____2771 'Auu____2772 'Auu____2773 .
    ('Auu____2771, 'Auu____2772, 'Auu____2773) FStar_Pervasives_Native.tuple3
      -> 'Auu____2772
  =
  fun uu____2783 -> match uu____2783 with | (uu____2790, x, uu____2792) -> x
let thd3 :
  'Auu____2797 'Auu____2798 'Auu____2799 .
    ('Auu____2797, 'Auu____2798, 'Auu____2799) FStar_Pervasives_Native.tuple3
      -> 'Auu____2799
  =
  fun uu____2809 -> match uu____2809 with | (uu____2816, uu____2817, x) -> x
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___34_2823 ->
    match uu___34_2823 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____2826 -> FStar_Pervasives_Native.None
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___35_2831 ->
    match uu___35_2831 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____2834 -> FStar_Pervasives_Native.None
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op -> (mk_bool_op op) <> FStar_Pervasives_Native.None
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___36_2844 ->
    match uu___36_2844 with
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
    | uu____2847 -> FStar_Pervasives_Native.None
let (is_op : Prims.string -> Prims.bool) =
  fun op -> (mk_op op) <> FStar_Pervasives_Native.None
let (is_machine_int : Prims.string -> Prims.bool) =
  fun m -> (mk_width m) <> FStar_Pervasives_Native.None
type env =
  {
  names: name Prims.list ;
  names_t: Prims.string Prims.list ;
  module_name: Prims.string Prims.list }[@@deriving show]
and name = {
  pretty: Prims.string ;
  mut: Prims.bool }[@@deriving show]
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
    match projectee with
    | { pretty = __fname__pretty; mut = __fname__mut;_} -> __fname__pretty
let (__proj__Mkname__item__mut : name -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { pretty = __fname__pretty; mut = __fname__mut;_} -> __fname__mut
let (empty : Prims.string Prims.list -> env) =
  fun module_name -> { names = []; names_t = []; module_name }
let (extend : env -> Prims.string -> Prims.bool -> env) =
  fun env ->
    fun x ->
      fun is_mut ->
        let uu___42_2958 = env in
        {
          names = ({ pretty = x; mut = is_mut } :: (env.names));
          names_t = (uu___42_2958.names_t);
          module_name = (uu___42_2958.module_name)
        }
let (extend_t : env -> Prims.string -> env) =
  fun env ->
    fun x ->
      let uu___43_2965 = env in
      {
        names = (uu___43_2965.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___43_2965.module_name)
      }
let (find_name : env -> Prims.string -> name) =
  fun env ->
    fun x ->
      let uu____2972 =
        FStar_List.tryFind (fun name -> name.pretty = x) env.names in
      match uu____2972 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None ->
          failwith "internal error: name not found"
let (is_mutable : env -> Prims.string -> Prims.bool) =
  fun env -> fun x -> let uu____2984 = find_name env x in uu____2984.mut
let (find : env -> Prims.string -> Prims.int) =
  fun env ->
    fun x ->
      try FStar_List.index (fun name -> name.pretty = x) env.names
      with
      | uu____2999 ->
          let uu____3000 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____3000
let (find_t : env -> Prims.string -> Prims.int) =
  fun env ->
    fun x ->
      try FStar_List.index (fun name -> name = x) env.names_t
      with
      | uu____3015 ->
          let uu____3016 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____3016
let add_binders :
  'Auu____3020 .
    env ->
      (Prims.string, 'Auu____3020) FStar_Pervasives_Native.tuple2 Prims.list
        -> env
  =
  fun env ->
    fun binders ->
      FStar_List.fold_left
        (fun env1 ->
           fun uu____3050 ->
             match uu____3050 with
             | (name, uu____3056) -> extend env1 name false) env binders
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____3197 ->
    match uu____3197 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m ->
             let m_name =
               let uu____3245 = m in
               match uu____3245 with
               | (path, uu____3259, uu____3260) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path in
             try
               FStar_Util.print1 "Attempting to translate module %s\n" m_name;
               (let uu____3282 = translate_module m in
                FStar_Pervasives_Native.Some uu____3282)
             with
             | e ->
                 ((let uu____3291 = FStar_Util.print_exn e in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____3291);
                  FStar_Pervasives_Native.None)) modules
and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath,
    (FStar_Extraction_ML_Syntax.mlsig, FStar_Extraction_ML_Syntax.mlmodule)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
    FStar_Extraction_ML_Syntax.mllib) FStar_Pervasives_Native.tuple3 -> 
    file)
  =
  fun uu____3292 ->
    match uu____3292 with
    | (module_name, modul, uu____3307) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name] in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature, decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____3338 ->
              failwith "Unexpected standalone interface or nested modules" in
        ((FStar_String.concat "_" module_name1), program)
and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags1 ->
    FStar_List.choose
      (fun uu___37_3353 ->
         match uu___37_3353 with
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
         | uu____3360 -> FStar_Pervasives_Native.None) flags1
and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env ->
    fun d ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor, lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____3371 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____3373 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m, uu____3377) ->
          (FStar_Util.print1_warning
             "Skipping the translation of exception: %s\n" m;
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3399;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args, body);
                FStar_Extraction_ML_Syntax.mlty = uu____3402;
                FStar_Extraction_ML_Syntax.loc = uu____3403;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3405;_} ->
            let assumed =
              FStar_Util.for_some
                (fun uu___38_3424 ->
                   match uu___38_3424 with
                   | FStar_Extraction_ML_Syntax.Assumed -> true
                   | uu____3425 -> false) meta in
            let env1 =
              if flavor = FStar_Extraction_ML_Syntax.Rec
              then extend env name false
              else env in
            let env2 =
              FStar_List.fold_left
                (fun env2 -> fun name1 -> extend_t env2 name1) env1 tvars in
            let rec find_return_type eff i uu___39_3446 =
              match uu___39_3446 with
              | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3451, eff1, t)
                  when i > (Prims.parse_int "0") ->
                  find_return_type eff1 (i - (Prims.parse_int "1")) t
              | t -> (eff, t) in
            let uu____3455 =
              find_return_type FStar_Extraction_ML_Syntax.E_PURE
                (FStar_List.length args) t0 in
            (match uu____3455 with
             | (eff, t) ->
                 let t1 = translate_type env2 t in
                 let binders = translate_binders env2 args in
                 let env3 = add_binders env2 args in
                 let name1 = ((env3.module_name), name) in
                 let meta1 =
                   match (eff, t1) with
                   | (FStar_Extraction_ML_Syntax.E_GHOST, uu____3487) ->
                       let uu____3488 = translate_flags meta in MustDisappear
                         :: uu____3488
                   | (FStar_Extraction_ML_Syntax.E_PURE, TUnit) ->
                       let uu____3491 = translate_flags meta in MustDisappear
                         :: uu____3491
                   | uu____3494 -> translate_flags meta in
                 if assumed
                 then
                   (if (FStar_List.length tvars) = (Prims.parse_int "0")
                    then
                      let uu____3503 =
                        let uu____3504 =
                          let uu____3523 = translate_type env3 t0 in
                          (FStar_Pervasives_Native.None, meta1, name1,
                            uu____3523) in
                        DExternal uu____3504 in
                      FStar_Pervasives_Native.Some uu____3503
                    else
                      ((let uu____3536 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath name1 in
                        FStar_Util.print1_warning
                          "No writing anything for %s (polymorphic assume)\n"
                          uu____3536);
                       FStar_Pervasives_Native.None))
                 else
                   (try
                      let body1 = translate_expr env3 body in
                      FStar_Pervasives_Native.Some
                        (DFunction
                           (FStar_Pervasives_Native.None, meta1,
                             (FStar_List.length tvars), t1, name1, binders,
                             body1))
                    with
                    | e ->
                        let msg = FStar_Util.print_exn e in
                        ((let uu____3569 =
                            let uu____3574 =
                              let uu____3575 =
                                FStar_Extraction_ML_Syntax.string_of_mlpath
                                  name1 in
                              FStar_Util.format2
                                "Writing a stub for %s (%s)\n" uu____3575 msg in
                            (FStar_Errors.Warning_FunctionNotExtacted,
                              uu____3574) in
                          FStar_Errors.log_issue FStar_Range.dummyRange
                            uu____3569);
                         (let msg1 =
                            Prims.strcat "This function was not extracted:\n"
                              msg in
                          FStar_Pervasives_Native.Some
                            (DFunction
                               (FStar_Pervasives_Native.None, meta1,
                                 (FStar_List.length tvars), t1, name1,
                                 binders, (EAbortS msg1)))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3592;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Coerce
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (args, body);
                     FStar_Extraction_ML_Syntax.mlty = uu____3595;
                     FStar_Extraction_ML_Syntax.loc = uu____3596;_},
                   uu____3597, uu____3598);
                FStar_Extraction_ML_Syntax.mlty = uu____3599;
                FStar_Extraction_ML_Syntax.loc = uu____3600;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3602;_} ->
            let assumed =
              FStar_Util.for_some
                (fun uu___38_3621 ->
                   match uu___38_3621 with
                   | FStar_Extraction_ML_Syntax.Assumed -> true
                   | uu____3622 -> false) meta in
            let env1 =
              if flavor = FStar_Extraction_ML_Syntax.Rec
              then extend env name false
              else env in
            let env2 =
              FStar_List.fold_left
                (fun env2 -> fun name1 -> extend_t env2 name1) env1 tvars in
            let rec find_return_type eff i uu___39_3643 =
              match uu___39_3643 with
              | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3648, eff1, t)
                  when i > (Prims.parse_int "0") ->
                  find_return_type eff1 (i - (Prims.parse_int "1")) t
              | t -> (eff, t) in
            let uu____3652 =
              find_return_type FStar_Extraction_ML_Syntax.E_PURE
                (FStar_List.length args) t0 in
            (match uu____3652 with
             | (eff, t) ->
                 let t1 = translate_type env2 t in
                 let binders = translate_binders env2 args in
                 let env3 = add_binders env2 args in
                 let name1 = ((env3.module_name), name) in
                 let meta1 =
                   match (eff, t1) with
                   | (FStar_Extraction_ML_Syntax.E_GHOST, uu____3684) ->
                       let uu____3685 = translate_flags meta in MustDisappear
                         :: uu____3685
                   | (FStar_Extraction_ML_Syntax.E_PURE, TUnit) ->
                       let uu____3688 = translate_flags meta in MustDisappear
                         :: uu____3688
                   | uu____3691 -> translate_flags meta in
                 if assumed
                 then
                   (if (FStar_List.length tvars) = (Prims.parse_int "0")
                    then
                      let uu____3700 =
                        let uu____3701 =
                          let uu____3720 = translate_type env3 t0 in
                          (FStar_Pervasives_Native.None, meta1, name1,
                            uu____3720) in
                        DExternal uu____3701 in
                      FStar_Pervasives_Native.Some uu____3700
                    else
                      ((let uu____3733 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath name1 in
                        FStar_Util.print1_warning
                          "No writing anything for %s (polymorphic assume)\n"
                          uu____3733);
                       FStar_Pervasives_Native.None))
                 else
                   (try
                      let body1 = translate_expr env3 body in
                      FStar_Pervasives_Native.Some
                        (DFunction
                           (FStar_Pervasives_Native.None, meta1,
                             (FStar_List.length tvars), t1, name1, binders,
                             body1))
                    with
                    | e ->
                        let msg = FStar_Util.print_exn e in
                        ((let uu____3766 =
                            let uu____3771 =
                              let uu____3772 =
                                FStar_Extraction_ML_Syntax.string_of_mlpath
                                  name1 in
                              FStar_Util.format2
                                "Writing a stub for %s (%s)\n" uu____3772 msg in
                            (FStar_Errors.Warning_FunctionNotExtacted,
                              uu____3771) in
                          FStar_Errors.log_issue FStar_Range.dummyRange
                            uu____3766);
                         (let msg1 =
                            Prims.strcat "This function was not extracted:\n"
                              msg in
                          FStar_Pervasives_Native.Some
                            (DFunction
                               (FStar_Pervasives_Native.None, meta1,
                                 (FStar_List.length tvars), t1, name1,
                                 binders, (EAbortS msg1)))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3789;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____3792;_} ->
            let meta1 = translate_flags meta in
            let env1 =
              FStar_List.fold_left
                (fun env1 -> fun name1 -> extend_t env1 name1) env tvars in
            let t1 = translate_type env1 t in
            let name1 = ((env1.module_name), name) in
            (try
               let expr1 = translate_expr env1 expr in
               FStar_Pervasives_Native.Some
                 (DGlobal
                    (meta1, name1, (FStar_List.length tvars), t1, expr1))
             with
             | e ->
                 ((let uu____3839 =
                     let uu____3844 =
                       let uu____3845 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1 in
                       let uu____3846 = FStar_Util.print_exn e in
                       FStar_Util.format2
                         "Not translating definition for %s (%s)\n"
                         uu____3845 uu____3846 in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____3844) in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____3839);
                  FStar_Pervasives_Native.Some
                    (DGlobal
                       (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3857;
            FStar_Extraction_ML_Syntax.mllb_def = uu____3858;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____3859;
            FStar_Extraction_ML_Syntax.print_typ = uu____3860;_} ->
            ((let uu____3864 =
                let uu____3869 =
                  FStar_Util.format1 "Not translating definition for %s\n"
                    name in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____3869) in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____3864);
             (match ts with
              | FStar_Pervasives_Native.Some (idents, t) ->
                  let uu____3877 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____3877
              | FStar_Pervasives_Native.None -> ());
             FStar_Pervasives_Native.None)
and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env ->
    fun ty ->
      match ty with
      | (assumed, name, _mangled_name, args, flags1,
         FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev
         t)) ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1 -> fun name2 -> extend_t env1 name2) env args in
          if assumed
          then
            let name2 = FStar_Extraction_ML_Syntax.string_of_mlpath name1 in
            (FStar_Util.print1_warning
               "Not translating type definition (assumed) for %s\n" name2;
             FStar_Pervasives_Native.None)
          else
            (let uu____3915 =
               let uu____3916 =
                 let uu____3933 = translate_flags flags1 in
                 let uu____3936 = translate_type env1 t in
                 (name1, uu____3933, (FStar_List.length args), uu____3936) in
               DTypeAlias uu____3916 in
             FStar_Pervasives_Native.Some uu____3915)
      | (uu____3945, name, _mangled_name, args, flags1,
         FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_Record
         fields)) ->
          let name1 = ((env.module_name), name) in
          let env1 =
            FStar_List.fold_left
              (fun env1 -> fun name2 -> extend_t env1 name2) env args in
          let uu____3977 =
            let uu____3978 =
              let uu____4005 = translate_flags flags1 in
              let uu____4008 =
                FStar_List.map
                  (fun uu____4035 ->
                     match uu____4035 with
                     | (f, t) ->
                         let uu____4050 =
                           let uu____4055 = translate_type env1 t in
                           (uu____4055, false) in
                         (f, uu____4050)) fields in
              (name1, uu____4005, (FStar_List.length args), uu____4008) in
            DTypeFlat uu____3978 in
          FStar_Pervasives_Native.Some uu____3977
      | (uu____4078, name, _mangled_name, args, flags1,
         FStar_Pervasives_Native.Some (FStar_Extraction_ML_Syntax.MLTD_DType
         branches)) ->
          let name1 = ((env.module_name), name) in
          let flags2 = translate_flags flags1 in
          let env1 = FStar_List.fold_left extend_t env args in
          let uu____4115 =
            let uu____4116 =
              let uu____4149 =
                FStar_List.map
                  (fun uu____4194 ->
                     match uu____4194 with
                     | (cons1, ts) ->
                         let uu____4233 =
                           FStar_List.map
                             (fun uu____4260 ->
                                match uu____4260 with
                                | (name2, t) ->
                                    let uu____4275 =
                                      let uu____4280 = translate_type env1 t in
                                      (uu____4280, false) in
                                    (name2, uu____4275)) ts in
                         (cons1, uu____4233)) branches in
              (name1, flags2, (FStar_List.length args), uu____4149) in
            DTypeVariant uu____4116 in
          FStar_Pervasives_Native.Some uu____4115
      | (uu____4319, name, _mangled_name, uu____4322, uu____4323, uu____4324)
          ->
          ((let uu____4334 =
              let uu____4339 =
                FStar_Util.format1 "Not translating type definition for %s\n"
                  name in
              (FStar_Errors.Warning_DefinitionNotTranslated, uu____4339) in
            FStar_Errors.log_issue FStar_Range.dummyRange uu____4334);
           FStar_Pervasives_Native.None)
and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____4343 = find_t env name in TBound uu____4343
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____4345, t2) ->
          let uu____4347 =
            let uu____4352 = translate_type env t1 in
            let uu____4353 = translate_type env t2 in
            (uu____4352, uu____4353) in
          TArrow uu____4347
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu____4357 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4357 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu____4361 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4361 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], ("FStar"::m::[], "t"))
          when is_machine_int m ->
          let uu____4373 = FStar_Util.must (mk_width m) in TInt uu____4373
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], ("FStar"::m::[], "t'"))
          when is_machine_int m ->
          let uu____4385 = FStar_Util.must (mk_width m) in TInt uu____4385
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu____4390 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4390 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____4391::arg::uu____4393::[], p) when
          (((let uu____4399 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4399 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____4401 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____4401 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____4403 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____4403 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____4405 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4405 = "FStar.HyperStack.ST.s_mref")
          -> let uu____4406 = translate_type env arg in TBuf uu____4406
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____4408::[], p) when
          ((((((((((let uu____4414 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4414 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____4416 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p in
                      uu____4416 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____4418 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p in
                     uu____4418 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____4420 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4420 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____4422 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p in
                   uu____4422 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____4424 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p in
                  uu____4424 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____4426 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____4426 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____4428 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu____4428 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____4430 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____4430 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____4432 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____4432 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____4434 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4434 = "FStar.HyperStack.ST.mmmref")
          -> let uu____4435 = translate_type env arg in TBuf uu____4435
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          ((((((((((let uu____4442 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4442 = "FStar.Buffer.buffer") ||
                     (let uu____4444 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p in
                      uu____4444 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____4446 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p in
                     uu____4446 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____4448 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4448 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____4450 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p in
                   uu____4450 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____4452 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p in
                  uu____4452 = "FStar.HyperStack.mmref"))
                ||
                (let uu____4454 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____4454 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____4456 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu____4456 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____4458 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____4458 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____4460 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____4460 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____4462 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4462 = "FStar.HyperStack.ST.mmref")
          -> let uu____4463 = translate_type env arg in TBuf uu____4463
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4464::arg::[], p) when
          (let uu____4471 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4471 = "FStar.HyperStack.s_ref") ||
            (let uu____4473 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4473 = "FStar.HyperStack.ST.s_ref")
          -> let uu____4474 = translate_type env arg in TBuf uu____4474
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4475::[], p) when
          let uu____4479 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4479 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, (ns, t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____4517 = FStar_List.map (translate_type env) args in
          TTuple uu____4517
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____4526 =
              let uu____4539 = FStar_List.map (translate_type env) args in
              (lid, uu____4539) in
            TApp uu____4526
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____4548 = FStar_List.map (translate_type env) ts in
          TTuple uu____4548
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
    fun uu____4564 ->
      match uu____4564 with
      | (name, typ) ->
          let uu____4571 = translate_type env typ in
          { name; typ = uu____4571; mut = false }
and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env ->
    fun e ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____4576 = find env name in EBound uu____4576
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], op) when
          (is_machine_int m) && (is_op op) ->
          let uu____4581 =
            let uu____4586 = FStar_Util.must (mk_op op) in
            let uu____4587 = FStar_Util.must (mk_width m) in
            (uu____4586, uu____4587) in
          EOp uu____4581
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[], op) when
          is_bool_op op ->
          let uu____4591 =
            let uu____4596 = FStar_Util.must (mk_bool_op op) in
            (uu____4596, Bool) in
          EOp uu____4591
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
          let is_mut =
            FStar_Util.for_some
              (fun uu___40_4624 ->
                 match uu___40_4624 with
                 | FStar_Extraction_ML_Syntax.Mutable -> true
                 | uu____4625 -> false) flags1 in
          let uu____4626 =
            if is_mut
            then
              let uu____4635 =
                match typ with
                | FStar_Extraction_ML_Syntax.MLTY_Named (t::[], p) when
                    let uu____4640 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4640 = "FStar.ST.stackref" -> t
                | uu____4641 ->
                    let uu____4642 =
                      let uu____4643 =
                        FStar_Extraction_ML_Code.string_of_mlty ([], "") typ in
                      FStar_Util.format1
                        "unexpected: bad desugaring of Mutable (typ is %s)"
                        uu____4643 in
                    failwith uu____4642 in
              let uu____4646 =
                match body with
                | {
                    FStar_Extraction_ML_Syntax.expr =
                      FStar_Extraction_ML_Syntax.MLE_App
                      (uu____4647, body1::[]);
                    FStar_Extraction_ML_Syntax.mlty = uu____4649;
                    FStar_Extraction_ML_Syntax.loc = uu____4650;_} -> body1
                | uu____4653 ->
                    failwith "unexpected: bad desugaring of Mutable" in
              (uu____4635, uu____4646)
            else (typ, body) in
          (match uu____4626 with
           | (typ1, body1) ->
               let binder =
                 let uu____4658 = translate_type env typ1 in
                 { name; typ = uu____4658; mut = is_mut } in
               let body2 = translate_expr env body1 in
               let env1 = extend env name is_mut in
               let continuation1 = translate_expr env1 continuation in
               ELet (binder, body2, continuation1))
      | FStar_Extraction_ML_Syntax.MLE_Match (expr, branches) ->
          let uu____4684 =
            let uu____4695 = translate_expr env expr in
            let uu____4696 = translate_branches env branches in
            (uu____4695, uu____4696) in
          EMatch uu____4684
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4710;
                  FStar_Extraction_ML_Syntax.loc = uu____4711;_},
                t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____4713;
             FStar_Extraction_ML_Syntax.loc = uu____4714;_},
           arg::[])
          when
          let uu____4720 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4720 = "FStar.Dyn.undyn" ->
          let uu____4721 =
            let uu____4726 = translate_expr env arg in
            let uu____4727 = translate_type env t in (uu____4726, uu____4727) in
          ECast uu____4721
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4729;
                  FStar_Extraction_ML_Syntax.loc = uu____4730;_},
                uu____4731);
             FStar_Extraction_ML_Syntax.mlty = uu____4732;
             FStar_Extraction_ML_Syntax.loc = uu____4733;_},
           uu____4734)
          when
          let uu____4743 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4743 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4745;
                  FStar_Extraction_ML_Syntax.loc = uu____4746;_},
                uu____4747);
             FStar_Extraction_ML_Syntax.mlty = uu____4748;
             FStar_Extraction_ML_Syntax.loc = uu____4749;_},
           arg::[])
          when
          ((let uu____4759 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____4759 = "FStar.HyperStack.All.failwith") ||
             (let uu____4761 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____4761 = "FStar.Error.unexpected"))
            ||
            (let uu____4763 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4763 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____4765;
               FStar_Extraction_ML_Syntax.loc = uu____4766;_} -> EAbortS msg
           | uu____4767 ->
               let print7 =
                 let uu____4769 =
                   let uu____4770 =
                     let uu____4771 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____4771 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____4770 in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____4769 in
               let print8 =
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top
                   (FStar_Extraction_ML_Syntax.MLE_App (print7, [arg])) in
               let t = translate_expr env print8 in ESequence [t; EAbort])
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4777;
             FStar_Extraction_ML_Syntax.loc = uu____4778;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Var v1;
             FStar_Extraction_ML_Syntax.mlty = uu____4780;
             FStar_Extraction_ML_Syntax.loc = uu____4781;_}::[])
          when
          (let uu____4786 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4786 = "FStar.HyperStack.ST.op_Bang") && (is_mutable env v1)
          -> let uu____4787 = find env v1 in EBound uu____4787
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____4789;
             FStar_Extraction_ML_Syntax.loc = uu____4790;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Var v1;
             FStar_Extraction_ML_Syntax.mlty = uu____4792;
             FStar_Extraction_ML_Syntax.loc = uu____4793;_}::e1::[])
          when
          (let uu____4799 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4799 = "FStar.HyperStack.ST.op_Colon_Equals") &&
            (is_mutable env v1)
          ->
          let uu____4800 =
            let uu____4805 =
              let uu____4806 = find env v1 in EBound uu____4806 in
            let uu____4807 = translate_expr env e1 in
            (uu____4805, uu____4807) in
          EAssign uu____4800
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4809;
                  FStar_Extraction_ML_Syntax.loc = uu____4810;_},
                uu____4811);
             FStar_Extraction_ML_Syntax.mlty = uu____4812;
             FStar_Extraction_ML_Syntax.loc = uu____4813;_},
           e1::e2::[])
          when
          (let uu____4824 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____4824 = "FStar.Buffer.index") ||
            (let uu____4826 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4826 = "FStar.Buffer.op_Array_Access")
          ->
          let uu____4827 =
            let uu____4832 = translate_expr env e1 in
            let uu____4833 = translate_expr env e2 in
            (uu____4832, uu____4833) in
          EBufRead uu____4827
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4835;
                  FStar_Extraction_ML_Syntax.loc = uu____4836;_},
                uu____4837);
             FStar_Extraction_ML_Syntax.mlty = uu____4838;
             FStar_Extraction_ML_Syntax.loc = uu____4839;_},
           e1::[])
          when
          let uu____4847 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4847 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____4848 =
            let uu____4853 = translate_expr env e1 in
            (uu____4853, (EConstant (UInt32, "0"))) in
          EBufRead uu____4848
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4855;
                  FStar_Extraction_ML_Syntax.loc = uu____4856;_},
                uu____4857);
             FStar_Extraction_ML_Syntax.mlty = uu____4858;
             FStar_Extraction_ML_Syntax.loc = uu____4859;_},
           e1::e2::[])
          when
          let uu____4868 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4868 = "FStar.Buffer.create" ->
          let uu____4869 =
            let uu____4876 = translate_expr env e1 in
            let uu____4877 = translate_expr env e2 in
            (Stack, uu____4876, uu____4877) in
          EBufCreate uu____4869
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4879;
                  FStar_Extraction_ML_Syntax.loc = uu____4880;_},
                uu____4881);
             FStar_Extraction_ML_Syntax.mlty = uu____4882;
             FStar_Extraction_ML_Syntax.loc = uu____4883;_},
           init1::[])
          when
          let uu____4891 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4891 = "FStar.HyperStack.ST.salloc" ->
          let uu____4892 =
            let uu____4899 = translate_expr env init1 in
            (Eternal, uu____4899, (EConstant (UInt32, "1"))) in
          EBufCreate uu____4892
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4901;
                  FStar_Extraction_ML_Syntax.loc = uu____4902;_},
                uu____4903);
             FStar_Extraction_ML_Syntax.mlty = uu____4904;
             FStar_Extraction_ML_Syntax.loc = uu____4905;_},
           _rid::init1::[])
          when
          let uu____4914 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4914 = "FStar.HyperStack.ST.ralloc" ->
          let uu____4915 =
            let uu____4922 = translate_expr env init1 in
            (Eternal, uu____4922, (EConstant (UInt32, "1"))) in
          EBufCreate uu____4915
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4924;
                  FStar_Extraction_ML_Syntax.loc = uu____4925;_},
                uu____4926);
             FStar_Extraction_ML_Syntax.mlty = uu____4927;
             FStar_Extraction_ML_Syntax.loc = uu____4928;_},
           _e0::e1::e2::[])
          when
          let uu____4938 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4938 = "FStar.Buffer.rcreate" ->
          let uu____4939 =
            let uu____4946 = translate_expr env e1 in
            let uu____4947 = translate_expr env e2 in
            (Eternal, uu____4946, uu____4947) in
          EBufCreate uu____4939
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4949;
                  FStar_Extraction_ML_Syntax.loc = uu____4950;_},
                uu____4951);
             FStar_Extraction_ML_Syntax.mlty = uu____4952;
             FStar_Extraction_ML_Syntax.loc = uu____4953;_},
           _e0::e1::e2::[])
          when
          let uu____4963 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4963 = "FStar.Buffer.rcreate_mm" ->
          let uu____4964 =
            let uu____4971 = translate_expr env e1 in
            let uu____4972 = translate_expr env e2 in
            (ManuallyManaged, uu____4971, uu____4972) in
          EBufCreate uu____4964
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____4974;
                  FStar_Extraction_ML_Syntax.loc = uu____4975;_},
                uu____4976);
             FStar_Extraction_ML_Syntax.mlty = uu____4977;
             FStar_Extraction_ML_Syntax.loc = uu____4978;_},
           e2::[])
          when
          let uu____4986 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4986 = "FStar.Buffer.createL" ->
          let rec list_elements acc e21 =
            match e21.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_CTor
                (("Prims"::[], "Cons"), hd1::tl1::[]) ->
                list_elements (hd1 :: acc) tl1
            | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[], "Nil"), [])
                -> FStar_List.rev acc
            | uu____5024 ->
                failwith
                  "Argument of FStar.Buffer.createL is not a string literal!" in
          let list_elements1 = list_elements [] in
          let uu____5032 =
            let uu____5039 =
              let uu____5042 = list_elements1 e2 in
              FStar_List.map (translate_expr env) uu____5042 in
            (Stack, uu____5039) in
          EBufCreateL uu____5032
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5048;
                  FStar_Extraction_ML_Syntax.loc = uu____5049;_},
                uu____5050);
             FStar_Extraction_ML_Syntax.mlty = uu____5051;
             FStar_Extraction_ML_Syntax.loc = uu____5052;_},
           e2::[])
          when
          let uu____5060 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5060 = "FStar.Buffer.rfree" ->
          let uu____5061 = translate_expr env e2 in EBufFree uu____5061
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5063;
                  FStar_Extraction_ML_Syntax.loc = uu____5064;_},
                uu____5065);
             FStar_Extraction_ML_Syntax.mlty = uu____5066;
             FStar_Extraction_ML_Syntax.loc = uu____5067;_},
           e1::e2::_e3::[])
          when
          let uu____5077 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5077 = "FStar.Buffer.sub" ->
          let uu____5078 =
            let uu____5083 = translate_expr env e1 in
            let uu____5084 = translate_expr env e2 in
            (uu____5083, uu____5084) in
          EBufSub uu____5078
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5086;
                  FStar_Extraction_ML_Syntax.loc = uu____5087;_},
                uu____5088);
             FStar_Extraction_ML_Syntax.mlty = uu____5089;
             FStar_Extraction_ML_Syntax.loc = uu____5090;_},
           e1::e2::[])
          when
          let uu____5099 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5099 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5101;
                  FStar_Extraction_ML_Syntax.loc = uu____5102;_},
                uu____5103);
             FStar_Extraction_ML_Syntax.mlty = uu____5104;
             FStar_Extraction_ML_Syntax.loc = uu____5105;_},
           e1::e2::[])
          when
          let uu____5114 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5114 = "FStar.Buffer.offset" ->
          let uu____5115 =
            let uu____5120 = translate_expr env e1 in
            let uu____5121 = translate_expr env e2 in
            (uu____5120, uu____5121) in
          EBufSub uu____5115
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5123;
                  FStar_Extraction_ML_Syntax.loc = uu____5124;_},
                uu____5125);
             FStar_Extraction_ML_Syntax.mlty = uu____5126;
             FStar_Extraction_ML_Syntax.loc = uu____5127;_},
           e1::e2::e3::[])
          when
          (let uu____5139 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5139 = "FStar.Buffer.upd") ||
            (let uu____5141 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5141 = "FStar.Buffer.op_Array_Assignment")
          ->
          let uu____5142 =
            let uu____5149 = translate_expr env e1 in
            let uu____5150 = translate_expr env e2 in
            let uu____5151 = translate_expr env e3 in
            (uu____5149, uu____5150, uu____5151) in
          EBufWrite uu____5142
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5153;
                  FStar_Extraction_ML_Syntax.loc = uu____5154;_},
                uu____5155);
             FStar_Extraction_ML_Syntax.mlty = uu____5156;
             FStar_Extraction_ML_Syntax.loc = uu____5157;_},
           e1::e2::[])
          when
          let uu____5166 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5166 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5167 =
            let uu____5174 = translate_expr env e1 in
            let uu____5175 = translate_expr env e2 in
            (uu____5174, (EConstant (UInt32, "0")), uu____5175) in
          EBufWrite uu____5167
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5177;
             FStar_Extraction_ML_Syntax.loc = uu____5178;_},
           uu____5179::[])
          when
          let uu____5182 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5182 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5184;
             FStar_Extraction_ML_Syntax.loc = uu____5185;_},
           uu____5186::[])
          when
          let uu____5189 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5189 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5191;
                  FStar_Extraction_ML_Syntax.loc = uu____5192;_},
                uu____5193);
             FStar_Extraction_ML_Syntax.mlty = uu____5194;
             FStar_Extraction_ML_Syntax.loc = uu____5195;_},
           e1::e2::e3::e4::e5::[])
          when
          let uu____5207 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5207 = "FStar.Buffer.blit" ->
          let uu____5208 =
            let uu____5219 = translate_expr env e1 in
            let uu____5220 = translate_expr env e2 in
            let uu____5221 = translate_expr env e3 in
            let uu____5222 = translate_expr env e4 in
            let uu____5223 = translate_expr env e5 in
            (uu____5219, uu____5220, uu____5221, uu____5222, uu____5223) in
          EBufBlit uu____5208
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5225;
                  FStar_Extraction_ML_Syntax.loc = uu____5226;_},
                uu____5227);
             FStar_Extraction_ML_Syntax.mlty = uu____5228;
             FStar_Extraction_ML_Syntax.loc = uu____5229;_},
           e1::e2::e3::[])
          when
          let uu____5239 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5239 = "FStar.Buffer.fill" ->
          let uu____5240 =
            let uu____5247 = translate_expr env e1 in
            let uu____5248 = translate_expr env e2 in
            let uu____5249 = translate_expr env e3 in
            (uu____5247, uu____5248, uu____5249) in
          EBufFill uu____5240
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5251;
             FStar_Extraction_ML_Syntax.loc = uu____5252;_},
           uu____5253::[])
          when
          let uu____5256 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5256 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5258;
             FStar_Extraction_ML_Syntax.loc = uu____5259;_},
           e1::[])
          when
          let uu____5263 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5263 = "Obj.repr" ->
          let uu____5264 =
            let uu____5269 = translate_expr env e1 in (uu____5269, TAny) in
          ECast uu____5264
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], op);
             FStar_Extraction_ML_Syntax.mlty = uu____5272;
             FStar_Extraction_ML_Syntax.loc = uu____5273;_},
           args)
          when (is_machine_int m) && (is_op op) ->
          let uu____5281 = FStar_Util.must (mk_width m) in
          let uu____5282 = FStar_Util.must (mk_op op) in
          mk_op_app env uu____5281 uu____5282 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[], op);
             FStar_Extraction_ML_Syntax.mlty = uu____5284;
             FStar_Extraction_ML_Syntax.loc = uu____5285;_},
           args)
          when is_bool_op op ->
          let uu____5293 = FStar_Util.must (mk_bool_op op) in
          mk_op_app env Bool uu____5293 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[], "int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5295;
             FStar_Extraction_ML_Syntax.loc = uu____5296;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_Int
               (c, FStar_Pervasives_Native.None));
             FStar_Extraction_ML_Syntax.mlty = uu____5298;
             FStar_Extraction_ML_Syntax.loc = uu____5299;_}::[])
          when is_machine_int m ->
          let uu____5314 =
            let uu____5319 = FStar_Util.must (mk_width m) in (uu____5319, c) in
          EConstant uu____5314
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[], "uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____5321;
             FStar_Extraction_ML_Syntax.loc = uu____5322;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_Int
               (c, FStar_Pervasives_Native.None));
             FStar_Extraction_ML_Syntax.mlty = uu____5324;
             FStar_Extraction_ML_Syntax.loc = uu____5325;_}::[])
          when is_machine_int m ->
          let uu____5340 =
            let uu____5345 = FStar_Util.must (mk_width m) in (uu____5345, c) in
          EConstant uu____5340
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[], "string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5346;
             FStar_Extraction_ML_Syntax.loc = uu____5347;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu____5349;
             FStar_Extraction_ML_Syntax.loc = uu____5350;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5356 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[], "of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____5357;
             FStar_Extraction_ML_Syntax.loc = uu____5358;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu____5360;
             FStar_Extraction_ML_Syntax.loc = uu____5361;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____5367 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[], c);
             FStar_Extraction_ML_Syntax.mlty = uu____5369;
             FStar_Extraction_ML_Syntax.loc = uu____5370;_},
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
            let uu____5377 =
              let uu____5382 = translate_expr env arg in
              (uu____5382, (TInt UInt64)) in
            ECast uu____5377
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____5384 =
                 let uu____5389 = translate_expr env arg in
                 (uu____5389, (TInt UInt32)) in
               ECast uu____5384)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____5391 =
                   let uu____5396 = translate_expr env arg in
                   (uu____5396, (TInt UInt16)) in
                 ECast uu____5391)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____5398 =
                     let uu____5403 = translate_expr env arg in
                     (uu____5403, (TInt UInt8)) in
                   ECast uu____5398)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____5405 =
                       let uu____5410 = translate_expr env arg in
                       (uu____5410, (TInt Int64)) in
                     ECast uu____5405)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____5412 =
                         let uu____5417 = translate_expr env arg in
                         (uu____5417, (TInt Int32)) in
                       ECast uu____5412)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____5419 =
                           let uu____5424 = translate_expr env arg in
                           (uu____5424, (TInt Int16)) in
                         ECast uu____5419)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____5426 =
                             let uu____5431 = translate_expr env arg in
                             (uu____5431, (TInt Int8)) in
                           ECast uu____5426)
                        else
                          (let uu____5433 =
                             let uu____5440 =
                               let uu____5443 = translate_expr env arg in
                               [uu____5443] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____5440) in
                           EApp uu____5433)
      | FStar_Extraction_ML_Syntax.MLE_App (head1, args) ->
          let uu____5454 =
            let uu____5461 = translate_expr env head1 in
            let uu____5462 = FStar_List.map (translate_expr env) args in
            (uu____5461, uu____5462) in
          EApp uu____5454
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1, ty_args) ->
          let uu____5473 =
            let uu____5480 = translate_expr env head1 in
            let uu____5481 = FStar_List.map (translate_type env) ty_args in
            (uu____5480, uu____5481) in
          ETypApp uu____5473
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t_from, t_to) ->
          let uu____5489 =
            let uu____5494 = translate_expr env e1 in
            let uu____5495 = translate_type env t_to in
            (uu____5494, uu____5495) in
          ECast uu____5489
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____5496, fields) ->
          let uu____5514 =
            let uu____5525 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5526 =
              FStar_List.map
                (fun uu____5545 ->
                   match uu____5545 with
                   | (field, expr) ->
                       let uu____5556 = translate_expr env expr in
                       (field, uu____5556)) fields in
            (uu____5525, uu____5526) in
          EFlat uu____5514
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1, path) ->
          let uu____5565 =
            let uu____5572 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____5573 = translate_expr env e1 in
            (uu____5572, uu____5573, (FStar_Pervasives_Native.snd path)) in
          EField uu____5565
      | FStar_Extraction_ML_Syntax.MLE_Let uu____5576 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1, uu____5588) ->
          let uu____5593 =
            let uu____5594 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1 in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____5594 in
          failwith uu____5593
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____5600 = FStar_List.map (translate_expr env) seqs in
          ESequence uu____5600
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____5606 = FStar_List.map (translate_expr env) es in
          ETuple uu____5606
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____5609, cons1), es) ->
          let uu____5626 =
            let uu____5635 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty in
            let uu____5636 = FStar_List.map (translate_expr env) es in
            (uu____5635, cons1, uu____5636) in
          ECons uu____5626
      | FStar_Extraction_ML_Syntax.MLE_Fun (args, body) ->
          let binders = translate_binders env args in
          let env1 = add_binders env args in
          let uu____5659 =
            let uu____5668 = translate_expr env1 body in
            let uu____5669 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty in
            (binders, uu____5668, uu____5669) in
          EFun uu____5659
      | FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) ->
          let uu____5679 =
            let uu____5686 = translate_expr env e1 in
            let uu____5687 = translate_expr env e2 in
            let uu____5688 =
              match e3 with
              | FStar_Pervasives_Native.None -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31 in
            (uu____5686, uu____5687, uu____5688) in
          EIfThenElse uu____5679
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____5690 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____5697 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____5712 ->
          failwith "todo: translate_expr [MLE_Coerce]"
and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____5727 =
              let uu____5740 = FStar_List.map (translate_type env) ts in
              (lid, uu____5740) in
            TApp uu____5727
          else TQualified lid
      | uu____5746 -> failwith "invalid argument: assert_lid"
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
    fun uu____5772 ->
      match uu____5772 with
      | (pat, guard, expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____5798 = translate_pat env pat in
            (match uu____5798 with
             | (env1, pat1) ->
                 let uu____5809 = translate_expr env1 expr in
                 (pat1, uu____5809))
          else failwith "todo: translate_branch"
and (translate_width :
  (FStar_Const.signedness, FStar_Const.width) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option -> width)
  =
  fun uu___41_5815 ->
    match uu___41_5815 with
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
          let uu____5879 =
            let uu____5880 =
              let uu____5885 = translate_width sw in (uu____5885, s) in
            PConstant uu____5880 in
          (env, uu____5879)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name false in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild ->
          let env1 = extend env "_" false in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____5889, cons1), ps) ->
          let uu____5906 =
            FStar_List.fold_left
              (fun uu____5926 ->
                 fun p1 ->
                   match uu____5926 with
                   | (env1, acc) ->
                       let uu____5946 = translate_pat env1 p1 in
                       (match uu____5946 with
                        | (env2, p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____5906 with
           | (env1, ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____5975, ps) ->
          let uu____5993 =
            FStar_List.fold_left
              (fun uu____6027 ->
                 fun uu____6028 ->
                   match (uu____6027, uu____6028) with
                   | ((env1, acc), (field, p1)) ->
                       let uu____6097 = translate_pat env1 p1 in
                       (match uu____6097 with
                        | (env2, p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps in
          (match uu____5993 with
           | (env1, ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____6159 =
            FStar_List.fold_left
              (fun uu____6179 ->
                 fun p1 ->
                   match uu____6179 with
                   | (env1, acc) ->
                       let uu____6199 = translate_pat env1 p1 in
                       (match uu____6199 with
                        | (env2, p2) -> (env2, (p2 :: acc)))) (env, []) ps in
          (match uu____6159 with
           | (env1, ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____6226 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____6231 ->
          failwith "todo: translate_pat [MLP_Branch]"
and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____6242 =
            let uu____6243 = FStar_String.list_of_string s in
            FStar_All.pipe_right uu____6243
              (FStar_Util.for_some
                 (fun c1 ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0")))) in
          if uu____6242
          then
            let uu____6255 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s in
            failwith uu____6255
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1 in
        let s = FStar_Util.string_of_int i in
        let c2 = EConstant (UInt32, s) in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int") in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s, FStar_Pervasives_Native.Some uu____6267) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____6282 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____6283 ->
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
          let uu____6303 =
            let uu____6310 = FStar_List.map (translate_expr env) args in
            ((EOp (op, w)), uu____6310) in
          EApp uu____6303