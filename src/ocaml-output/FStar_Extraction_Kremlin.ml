open Prims
type decl =
  | DGlobal of (flag Prims.list * (Prims.string Prims.list * Prims.string) *
  Prims.int * typ * expr) 
  | DFunction of (cc FStar_Pervasives_Native.option * flag Prims.list *
  Prims.int * typ * (Prims.string Prims.list * Prims.string) * binder
  Prims.list * expr) 
  | DTypeAlias of ((Prims.string Prims.list * Prims.string) * flag Prims.list
  * Prims.int * typ) 
  | DTypeFlat of ((Prims.string Prims.list * Prims.string) * flag Prims.list
  * Prims.int * (Prims.string * (typ * Prims.bool)) Prims.list) 
  | DUnusedRetainedForBackwardsCompat of (cc FStar_Pervasives_Native.option *
  flag Prims.list * (Prims.string Prims.list * Prims.string) * typ) 
  | DTypeVariant of ((Prims.string Prims.list * Prims.string) * flag
  Prims.list * Prims.int * (Prims.string * (Prims.string * (typ *
  Prims.bool)) Prims.list) Prims.list) 
  | DTypeAbstractStruct of (Prims.string Prims.list * Prims.string) 
  | DExternal of (cc FStar_Pervasives_Native.option * flag Prims.list *
  (Prims.string Prims.list * Prims.string) * typ * Prims.string Prims.list) 
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
  | IfDef 
  | Macro 
  | Deprecated of Prims.string 
and lifetime =
  | Eternal 
  | Stack 
  | ManuallyManaged 
and expr =
  | EBound of Prims.int 
  | EQualified of (Prims.string Prims.list * Prims.string) 
  | EConstant of (width * Prims.string) 
  | EUnit 
  | EApp of (expr * expr Prims.list) 
  | ETypApp of (expr * typ Prims.list) 
  | ELet of (binder * expr * expr) 
  | EIfThenElse of (expr * expr * expr) 
  | ESequence of expr Prims.list 
  | EAssign of (expr * expr) 
  | EBufCreate of (lifetime * expr * expr) 
  | EBufRead of (expr * expr) 
  | EBufWrite of (expr * expr * expr) 
  | EBufSub of (expr * expr) 
  | EBufBlit of (expr * expr * expr * expr * expr) 
  | EMatch of (expr * (pattern * expr) Prims.list) 
  | EOp of (op * width) 
  | ECast of (expr * typ) 
  | EPushFrame 
  | EPopFrame 
  | EBool of Prims.bool 
  | EAny 
  | EAbort 
  | EReturn of expr 
  | EFlat of (typ * (Prims.string * expr) Prims.list) 
  | EField of (typ * expr * Prims.string) 
  | EWhile of (expr * expr) 
  | EBufCreateL of (lifetime * expr Prims.list) 
  | ETuple of expr Prims.list 
  | ECons of (typ * Prims.string * expr Prims.list) 
  | EBufFill of (expr * expr * expr) 
  | EString of Prims.string 
  | EFun of (binder Prims.list * expr * typ) 
  | EAbortS of Prims.string 
  | EBufFree of expr 
  | EBufCreateNoInit of (lifetime * expr) 
  | EAbortT of (Prims.string * typ) 
  | EComment of (Prims.string * expr * Prims.string) 
  | EStandaloneComment of Prims.string 
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
  | PCons of (Prims.string * pattern Prims.list) 
  | PTuple of pattern Prims.list 
  | PRecord of (Prims.string * pattern) Prims.list 
  | PConstant of (width * Prims.string) 
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
  | TQualified of (Prims.string Prims.list * Prims.string) 
  | TBool 
  | TAny 
  | TArrow of (typ * typ) 
  | TBound of Prims.int 
  | TApp of ((Prims.string Prims.list * Prims.string) * typ Prims.list) 
  | TTuple of typ Prims.list 
  | TConstBuf of typ 
let (uu___is_DGlobal : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DGlobal _0 -> true | uu____709 -> false
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee -> match projectee with | DGlobal _0 -> _0
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DFunction _0 -> true | uu____802 -> false
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee -> match projectee with | DFunction _0 -> _0
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeAlias _0 -> true | uu____909 -> false
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee -> match projectee with | DTypeAlias _0 -> _0
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeFlat _0 -> true | uu____996 -> false
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee -> match projectee with | DTypeFlat _0 -> _0
let (uu___is_DUnusedRetainedForBackwardsCompat : decl -> Prims.bool) =
  fun projectee ->
    match projectee with
    | DUnusedRetainedForBackwardsCompat _0 -> true
    | uu____1105 -> false
let (__proj__DUnusedRetainedForBackwardsCompat__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  =
  fun projectee ->
    match projectee with | DUnusedRetainedForBackwardsCompat _0 -> _0
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DTypeVariant _0 -> true | uu____1204 -> false
let (__proj__DTypeVariant__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (Prims.string * (typ * Prims.bool)) Prims.list)
      Prims.list))
  = fun projectee -> match projectee with | DTypeVariant _0 -> _0
let (uu___is_DTypeAbstractStruct : decl -> Prims.bool) =
  fun projectee ->
    match projectee with
    | DTypeAbstractStruct _0 -> true
    | uu____1319 -> false
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee -> match projectee with | DTypeAbstractStruct _0 -> _0
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee ->
    match projectee with | DExternal _0 -> true | uu____1372 -> false
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ * Prims.string Prims.list))
  = fun projectee -> match projectee with | DExternal _0 -> _0
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee ->
    match projectee with | StdCall -> true | uu____1450 -> false
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee -> match projectee with | CDecl -> true | uu____1456 -> false
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee ->
    match projectee with | FastCall -> true | uu____1462 -> false
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Private -> true | uu____1468 -> false
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | WipeBody -> true | uu____1474 -> false
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | CInline -> true | uu____1480 -> false
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Substitute -> true | uu____1486 -> false
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | GCType -> true | uu____1492 -> false
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Comment _0 -> true | uu____1499 -> false
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Comment _0 -> _0
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | MustDisappear -> true | uu____1511 -> false
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Const _0 -> true | uu____1518 -> false
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Const _0 -> _0
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Prologue _0 -> true | uu____1531 -> false
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Prologue _0 -> _0
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Epilogue _0 -> true | uu____1544 -> false
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Epilogue _0 -> _0
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Abstract -> true | uu____1556 -> false
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee -> match projectee with | IfDef -> true | uu____1562 -> false
let (uu___is_Macro : flag -> Prims.bool) =
  fun projectee -> match projectee with | Macro -> true | uu____1568 -> false
let (uu___is_Deprecated : flag -> Prims.bool) =
  fun projectee ->
    match projectee with | Deprecated _0 -> true | uu____1575 -> false
let (__proj__Deprecated__item___0 : flag -> Prims.string) =
  fun projectee -> match projectee with | Deprecated _0 -> _0
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee ->
    match projectee with | Eternal -> true | uu____1587 -> false
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee -> match projectee with | Stack -> true | uu____1593 -> false
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee ->
    match projectee with | ManuallyManaged -> true | uu____1599 -> false
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBound _0 -> true | uu____1606 -> false
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee -> match projectee with | EBound _0 -> _0
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EQualified _0 -> true | uu____1625 -> false
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee -> match projectee with | EQualified _0 -> _0
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EConstant _0 -> true | uu____1660 -> false
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee -> match projectee with | EConstant _0 -> _0
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee -> match projectee with | EUnit -> true | uu____1684 -> false
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EApp _0 -> true | uu____1697 -> false
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee -> match projectee with | EApp _0 -> _0
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ETypApp _0 -> true | uu____1734 -> false
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee -> match projectee with | ETypApp _0 -> _0
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ELet _0 -> true | uu____1771 -> false
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee -> match projectee with | ELet _0 -> _0
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EIfThenElse _0 -> true | uu____1808 -> false
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee -> match projectee with | EIfThenElse _0 -> _0
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ESequence _0 -> true | uu____1841 -> false
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee -> match projectee with | ESequence _0 -> _0
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EAssign _0 -> true | uu____1864 -> false
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee -> match projectee with | EAssign _0 -> _0
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufCreate _0 -> true | uu____1895 -> false
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee -> match projectee with | EBufCreate _0 -> _0
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufRead _0 -> true | uu____1930 -> false
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee -> match projectee with | EBufRead _0 -> _0
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufWrite _0 -> true | uu____1961 -> false
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee -> match projectee with | EBufWrite _0 -> _0
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufSub _0 -> true | uu____1996 -> false
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee -> match projectee with | EBufSub _0 -> _0
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufBlit _0 -> true | uu____2031 -> false
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee -> match projectee with | EBufBlit _0 -> _0
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EMatch _0 -> true | uu____2084 -> false
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee -> match projectee with | EMatch _0 -> _0
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EOp _0 -> true | uu____2131 -> false
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee -> match projectee with | EOp _0 -> _0
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ECast _0 -> true | uu____2160 -> false
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee -> match projectee with | ECast _0 -> _0
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EPushFrame -> true | uu____2184 -> false
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EPopFrame -> true | uu____2190 -> false
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBool _0 -> true | uu____2197 -> false
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee -> match projectee with | EBool _0 -> _0
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee -> match projectee with | EAny -> true | uu____2209 -> false
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EAbort -> true | uu____2215 -> false
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EReturn _0 -> true | uu____2222 -> false
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee -> match projectee with | EReturn _0 -> _0
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EFlat _0 -> true | uu____2245 -> false
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee -> match projectee with | EFlat _0 -> _0
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EField _0 -> true | uu____2294 -> false
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee -> match projectee with | EField _0 -> _0
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EWhile _0 -> true | uu____2329 -> false
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee -> match projectee with | EWhile _0 -> _0
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufCreateL _0 -> true | uu____2360 -> false
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee -> match projectee with | EBufCreateL _0 -> _0
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ETuple _0 -> true | uu____2393 -> false
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee -> match projectee with | ETuple _0 -> _0
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | ECons _0 -> true | uu____2420 -> false
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee -> match projectee with | ECons _0 -> _0
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufFill _0 -> true | uu____2463 -> false
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee -> match projectee with | EBufFill _0 -> _0
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EString _0 -> true | uu____2494 -> false
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee -> match projectee with | EString _0 -> _0
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EFun _0 -> true | uu____2515 -> false
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee -> match projectee with | EFun _0 -> _0
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EAbortS _0 -> true | uu____2552 -> false
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee -> match projectee with | EAbortS _0 -> _0
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufFree _0 -> true | uu____2565 -> false
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee -> match projectee with | EBufFree _0 -> _0
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____2582 -> false
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee -> match projectee with | EBufCreateNoInit _0 -> _0
let (uu___is_EAbortT : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EAbortT _0 -> true | uu____2611 -> false
let (__proj__EAbortT__item___0 : expr -> (Prims.string * typ)) =
  fun projectee -> match projectee with | EAbortT _0 -> _0
let (uu___is_EComment : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | EComment _0 -> true | uu____2642 -> false
let (__proj__EComment__item___0 :
  expr -> (Prims.string * expr * Prims.string)) =
  fun projectee -> match projectee with | EComment _0 -> _0
let (uu___is_EStandaloneComment : expr -> Prims.bool) =
  fun projectee ->
    match projectee with
    | EStandaloneComment _0 -> true
    | uu____2673 -> false
let (__proj__EStandaloneComment__item___0 : expr -> Prims.string) =
  fun projectee -> match projectee with | EStandaloneComment _0 -> _0
let (uu___is_Add : op -> Prims.bool) =
  fun projectee -> match projectee with | Add -> true | uu____2685 -> false
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee -> match projectee with | AddW -> true | uu____2691 -> false
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee -> match projectee with | Sub -> true | uu____2697 -> false
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee -> match projectee with | SubW -> true | uu____2703 -> false
let (uu___is_Div : op -> Prims.bool) =
  fun projectee -> match projectee with | Div -> true | uu____2709 -> false
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee -> match projectee with | DivW -> true | uu____2715 -> false
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee -> match projectee with | Mult -> true | uu____2721 -> false
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee -> match projectee with | MultW -> true | uu____2727 -> false
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee -> match projectee with | Mod -> true | uu____2733 -> false
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee -> match projectee with | BOr -> true | uu____2739 -> false
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee -> match projectee with | BAnd -> true | uu____2745 -> false
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee -> match projectee with | BXor -> true | uu____2751 -> false
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee ->
    match projectee with | BShiftL -> true | uu____2757 -> false
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee ->
    match projectee with | BShiftR -> true | uu____2763 -> false
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee -> match projectee with | BNot -> true | uu____2769 -> false
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee -> match projectee with | Eq -> true | uu____2775 -> false
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee -> match projectee with | Neq -> true | uu____2781 -> false
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee -> match projectee with | Lt -> true | uu____2787 -> false
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee -> match projectee with | Lte -> true | uu____2793 -> false
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee -> match projectee with | Gt -> true | uu____2799 -> false
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee -> match projectee with | Gte -> true | uu____2805 -> false
let (uu___is_And : op -> Prims.bool) =
  fun projectee -> match projectee with | And -> true | uu____2811 -> false
let (uu___is_Or : op -> Prims.bool) =
  fun projectee -> match projectee with | Or -> true | uu____2817 -> false
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee -> match projectee with | Xor -> true | uu____2823 -> false
let (uu___is_Not : op -> Prims.bool) =
  fun projectee -> match projectee with | Not -> true | uu____2829 -> false
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PUnit -> true | uu____2835 -> false
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PBool _0 -> true | uu____2842 -> false
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PBool _0 -> _0
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PVar _0 -> true | uu____2855 -> false
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee -> match projectee with | PVar _0 -> _0
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PCons _0 -> true | uu____2874 -> false
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee -> match projectee with | PCons _0 -> _0
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PTuple _0 -> true | uu____2907 -> false
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee -> match projectee with | PTuple _0 -> _0
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PRecord _0 -> true | uu____2932 -> false
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee -> match projectee with | PRecord _0 -> _0
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PConstant _0 -> true | uu____2967 -> false
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee -> match projectee with | PConstant _0 -> _0
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee -> match projectee with | UInt8 -> true | uu____2991 -> false
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee ->
    match projectee with | UInt16 -> true | uu____2997 -> false
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee ->
    match projectee with | UInt32 -> true | uu____3003 -> false
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee ->
    match projectee with | UInt64 -> true | uu____3009 -> false
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int8 -> true | uu____3015 -> false
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int16 -> true | uu____3021 -> false
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int32 -> true | uu____3027 -> false
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int64 -> true | uu____3033 -> false
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee -> match projectee with | Bool -> true | uu____3039 -> false
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee -> match projectee with | CInt -> true | uu____3045 -> false
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee -> match projectee with | { name; typ = typ1; mut;_} -> name
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee -> match projectee with | { name; typ = typ1; mut;_} -> typ1
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee -> match projectee with | { name; typ = typ1; mut;_} -> mut
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TInt _0 -> true | uu____3076 -> false
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee -> match projectee with | TInt _0 -> _0
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TBuf _0 -> true | uu____3089 -> false
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee -> match projectee with | TBuf _0 -> _0
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee -> match projectee with | TUnit -> true | uu____3101 -> false
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TQualified _0 -> true | uu____3114 -> false
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee -> match projectee with | TQualified _0 -> _0
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee -> match projectee with | TBool -> true | uu____3144 -> false
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee -> match projectee with | TAny -> true | uu____3150 -> false
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TArrow _0 -> true | uu____3161 -> false
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee -> match projectee with | TArrow _0 -> _0
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TBound _0 -> true | uu____3186 -> false
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee -> match projectee with | TBound _0 -> _0
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TApp _0 -> true | uu____3211 -> false
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee -> match projectee with | TApp _0 -> _0
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TTuple _0 -> true | uu____3262 -> false
let (__proj__TTuple__item___0 : typ -> typ Prims.list) =
  fun projectee -> match projectee with | TTuple _0 -> _0
let (uu___is_TConstBuf : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | TConstBuf _0 -> true | uu____3281 -> false
let (__proj__TConstBuf__item___0 : typ -> typ) =
  fun projectee -> match projectee with | TConstBuf _0 -> _0
type program = decl Prims.list
type ident = Prims.string
type fields_t = (Prims.string * (typ * Prims.bool)) Prims.list
type branches_t =
  (Prims.string * (Prims.string * (typ * Prims.bool)) Prims.list) Prims.list
type fsdoc = Prims.string
type branch = (pattern * expr)
type branches = (pattern * expr) Prims.list
type constant = (width * Prims.string)
type var = Prims.int
type lident = (Prims.string Prims.list * Prims.string)
type version = Prims.int
let (current_version : version) = (Prims.of_int (28))
type file = (Prims.string * program)
type binary_format = (version * file Prims.list)
let fst3 :
  'uuuuuu3354 'uuuuuu3355 'uuuuuu3356 .
    ('uuuuuu3354 * 'uuuuuu3355 * 'uuuuuu3356) -> 'uuuuuu3354
  =
  fun uu____3367 -> match uu____3367 with | (x, uu____3375, uu____3376) -> x
let snd3 :
  'uuuuuu3385 'uuuuuu3386 'uuuuuu3387 .
    ('uuuuuu3385 * 'uuuuuu3386 * 'uuuuuu3387) -> 'uuuuuu3386
  =
  fun uu____3398 -> match uu____3398 with | (uu____3405, x, uu____3407) -> x
let thd3 :
  'uuuuuu3416 'uuuuuu3417 'uuuuuu3418 .
    ('uuuuuu3416 * 'uuuuuu3417 * 'uuuuuu3418) -> 'uuuuuu3418
  =
  fun uu____3429 -> match uu____3429 with | (uu____3436, uu____3437, x) -> x
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___0_3445 ->
    match uu___0_3445 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____3448 -> FStar_Pervasives_Native.None
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___1_3455 ->
    match uu___1_3455 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____3458 -> FStar_Pervasives_Native.None
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op1 -> (mk_bool_op op1) <> FStar_Pervasives_Native.None
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___2_3472 ->
    match uu___2_3472 with
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
    | uu____3475 -> FStar_Pervasives_Native.None
let (is_op : Prims.string -> Prims.bool) =
  fun op1 -> (mk_op op1) <> FStar_Pervasives_Native.None
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
    match projectee with | { names; names_t; module_name;_} -> names
let (__proj__Mkenv__item__names_t : env -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with | { names; names_t; module_name;_} -> names_t
let (__proj__Mkenv__item__module_name : env -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with | { names; names_t; module_name;_} -> module_name
let (__proj__Mkname__item__pretty : name -> Prims.string) =
  fun projectee -> match projectee with | { pretty;_} -> pretty
let (empty : Prims.string Prims.list -> env) =
  fun module_name -> { names = []; names_t = []; module_name }
let (extend : env -> Prims.string -> env) =
  fun env1 ->
    fun x ->
      let uu___168_3595 = env1 in
      {
        names = ({ pretty = x } :: (env1.names));
        names_t = (uu___168_3595.names_t);
        module_name = (uu___168_3595.module_name)
      }
let (extend_t : env -> Prims.string -> env) =
  fun env1 ->
    fun x ->
      let uu___172_3606 = env1 in
      {
        names = (uu___172_3606.names);
        names_t = (x :: (env1.names_t));
        module_name = (uu___172_3606.module_name)
      }
let (find_name : env -> Prims.string -> name) =
  fun env1 ->
    fun x ->
      let uu____3617 =
        FStar_List.tryFind (fun name1 -> name1.pretty = x) env1.names in
      match uu____3617 with
      | FStar_Pervasives_Native.Some name1 -> name1
      | FStar_Pervasives_Native.None ->
          failwith "internal error: name not found"
let (find : env -> Prims.string -> Prims.int) =
  fun env1 ->
    fun x ->
      try
        (fun uu___183_3634 ->
           match () with
           | () ->
               FStar_List.index (fun name1 -> name1.pretty = x) env1.names)
          ()
      with
      | uu___182_3639 ->
          let uu____3640 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____3640
let (find_t : env -> Prims.string -> Prims.int) =
  fun env1 ->
    fun x ->
      try
        (fun uu___192_3652 ->
           match () with
           | () -> FStar_List.index (fun name1 -> name1 = x) env1.names_t) ()
      with
      | uu___191_3657 ->
          let uu____3658 =
            FStar_Util.format1 "Internal error: name not found %s\n" x in
          failwith uu____3658
let add_binders :
  'uuuuuu3665 . env -> (Prims.string * 'uuuuuu3665) Prims.list -> env =
  fun env1 ->
    fun binders ->
      FStar_List.fold_left
        (fun env2 ->
           fun uu____3697 ->
             match uu____3697 with | (name1, uu____3703) -> extend env2 name1)
        env1 binders
let (list_elements :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr Prims.list)
  =
  fun e2 ->
    let rec list_elements acc e21 =
      match e21.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_CTor
          (("Prims"::[], "Cons"), hd::tl::[]) -> list_elements (hd :: acc) tl
      | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[], "Nil"), []) ->
          FStar_List.rev acc
      | uu____3740 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!" in
    list_elements [] e2
let rec (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun m ->
    let uu____3962 = m in
    match uu____3962 with
    | (module_name, modul, uu____3977) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name] in
        let program1 =
          match modul with
          | FStar_Pervasives_Native.Some (_signature, decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____4004 ->
              failwith "Unexpected standalone interface or nested modules" in
        ((FStar_String.concat "_" module_name1), program1)
and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags ->
    FStar_List.choose
      (fun uu___3_4015 ->
         match uu___3_4015 with
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
         | FStar_Extraction_ML_Syntax.CIfDef ->
             FStar_Pervasives_Native.Some IfDef
         | FStar_Extraction_ML_Syntax.CMacro ->
             FStar_Pervasives_Native.Some Macro
         | FStar_Extraction_ML_Syntax.Deprecated s ->
             FStar_Pervasives_Native.Some (Deprecated s)
         | uu____4023 -> FStar_Pervasives_Native.None) flags
and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags ->
    let uu____4027 =
      FStar_List.choose
        (fun uu___4_4032 ->
           match uu___4_4032 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____4036 -> FStar_Pervasives_Native.None) flags in
    match uu____4027 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____4039 -> FStar_Pervasives_Native.None
and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env1 ->
    fun d ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor, lbs) ->
          FStar_List.choose (translate_let env1 flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____4052 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env1) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____4054 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m, uu____4058) ->
          (FStar_Util.print1_warning
             "Not extracting exception %s to KreMLin (exceptions unsupported)\n"
             m;
           [])
and (translate_let :
  env ->
    FStar_Extraction_ML_Syntax.mlletflavor ->
      FStar_Extraction_ML_Syntax.mllb -> decl FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun flavor ->
      fun lb ->
        match lb with
        | { FStar_Extraction_ML_Syntax.mllb_name = name1;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4080;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4083;_} when
            FStar_Util.for_some
              (fun uu___5_4085 ->
                 match uu___5_4085 with
                 | FStar_Extraction_ML_Syntax.Assumed -> true
                 | uu____4086 -> false) meta
            ->
            let name2 = ((env1.module_name), name1) in
            let arg_names =
              match e.FStar_Extraction_ML_Syntax.expr with
              | FStar_Extraction_ML_Syntax.MLE_Fun (args, uu____4102) ->
                  FStar_List.map FStar_Pervasives_Native.fst args
              | uu____4119 -> [] in
            if (FStar_List.length tvars) = Prims.int_zero
            then
              let uu____4122 =
                let uu____4123 =
                  let uu____4146 = translate_cc meta in
                  let uu____4149 = translate_flags meta in
                  let uu____4152 = translate_type env1 t0 in
                  (uu____4146, uu____4149, name2, uu____4152, arg_names) in
                DExternal uu____4123 in
              FStar_Pervasives_Native.Some uu____4122
            else
              ((let uu____4167 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name2 in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____4167);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name1;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4171;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args, body);
                FStar_Extraction_ML_Syntax.mlty = uu____4174;
                FStar_Extraction_ML_Syntax.loc = uu____4175;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4177;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let env2 =
                 if flavor = FStar_Extraction_ML_Syntax.Rec
                 then extend env1 name1
                 else env1 in
               let env3 =
                 FStar_List.fold_left
                   (fun env3 -> fun name2 -> extend_t env3 name2) env2 tvars in
               let rec find_return_type eff i uu___6_4221 =
                 match uu___6_4221 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____4228, eff1, t)
                     when i > Prims.int_zero ->
                     find_return_type eff1 (i - Prims.int_one) t
                 | t -> (i, eff, t) in
               let name2 = ((env3.module_name), name1) in
               let uu____4241 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0 in
               match uu____4241 with
               | (i, eff, t) ->
                   (if i > Prims.int_zero
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction" in
                       let uu____4259 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name2 in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____4259 msg)
                    else ();
                    (let t1 = translate_type env3 t in
                     let binders = translate_binders env3 args in
                     let env4 = add_binders env3 args in
                     let cc1 = translate_cc meta in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST, uu____4274) ->
                           let uu____4275 = translate_flags meta in
                           MustDisappear :: uu____4275
                       | (FStar_Extraction_ML_Syntax.E_PURE, TUnit) ->
                           let uu____4278 = translate_flags meta in
                           MustDisappear :: uu____4278
                       | uu____4281 -> translate_flags meta in
                     try
                       (fun uu___366_4290 ->
                          match () with
                          | () ->
                              let body1 = translate_expr env4 body in
                              FStar_Pervasives_Native.Some
                                (DFunction
                                   (cc1, meta1, (FStar_List.length tvars),
                                     t1, name2, binders, body1))) ()
                     with
                     | e ->
                         let msg = FStar_Util.print_exn e in
                         ((let uu____4317 =
                             let uu____4322 =
                               let uu____4323 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name2 in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____4323 msg in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____4322) in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____4317);
                          (let msg1 =
                             Prims.op_Hat
                               "This function was not extracted:\n" msg in
                           FStar_Pervasives_Native.Some
                             (DFunction
                                (cc1, meta1, (FStar_List.length tvars), t1,
                                  name2, binders, (EAbortS msg1))))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name1;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars, t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4340;
            FStar_Extraction_ML_Syntax.mllb_def = expr1;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____4343;_} ->
            if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract meta
            then FStar_Pervasives_Native.None
            else
              (let meta1 = translate_flags meta in
               let env2 =
                 FStar_List.fold_left
                   (fun env2 -> fun name2 -> extend_t env2 name2) env1 tvars in
               let t1 = translate_type env2 t in
               let name2 = ((env2.module_name), name1) in
               try
                 (fun uu___393_4369 ->
                    match () with
                    | () ->
                        let expr2 = translate_expr env2 expr1 in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name2, (FStar_List.length tvars), t1,
                               expr2))) ()
               with
               | e ->
                   ((let uu____4389 =
                       let uu____4394 =
                         let uu____4395 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name2 in
                         let uu____4396 = FStar_Util.print_exn e in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____4395
                           uu____4396 in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____4394) in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____4389);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name2, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name1;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____4407;
            FStar_Extraction_ML_Syntax.mllb_def = uu____4408;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____4409;
            FStar_Extraction_ML_Syntax.print_typ = uu____4410;_} ->
            ((let uu____4414 =
                let uu____4419 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name1 in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____4419) in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____4414);
             (match ts with
              | FStar_Pervasives_Native.Some (idents, t) ->
                  let uu____4423 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____4423
              | FStar_Pervasives_Native.None -> ());
             FStar_Pervasives_Native.None)
and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun ty ->
      let uu____4430 = ty in
      match uu____4430 with
      | (uu____4433, uu____4434, uu____4435, uu____4436, flags, uu____4438)
          ->
          if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract flags
          then FStar_Pervasives_Native.None
          else
            (match ty with
             | (assumed, name1, _mangled_name, args, flags1,
                FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Abbrev t)) ->
                 let name2 = ((env1.module_name), name1) in
                 let env2 =
                   FStar_List.fold_left
                     (fun env2 -> fun name3 -> extend_t env2 name3) env1 args in
                 if
                   assumed &&
                     (FStar_List.mem FStar_Extraction_ML_Syntax.CAbstract
                        flags1)
                 then
                   FStar_Pervasives_Native.Some (DTypeAbstractStruct name2)
                 else
                   if assumed
                   then
                     (let name3 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath name2 in
                      FStar_Util.print1_warning
                        "Not extracting type definition %s to KreMLin (assumed type)\n"
                        name3;
                      FStar_Pervasives_Native.None)
                   else
                     (let uu____4486 =
                        let uu____4487 =
                          let uu____4504 = translate_flags flags1 in
                          let uu____4507 = translate_type env2 t in
                          (name2, uu____4504, (FStar_List.length args),
                            uu____4507) in
                        DTypeAlias uu____4487 in
                      FStar_Pervasives_Native.Some uu____4486)
             | (uu____4516, name1, _mangled_name, args, flags1,
                FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name2 = ((env1.module_name), name1) in
                 let env2 =
                   FStar_List.fold_left
                     (fun env2 -> fun name3 -> extend_t env2 name3) env1 args in
                 let uu____4548 =
                   let uu____4549 =
                     let uu____4576 = translate_flags flags1 in
                     let uu____4579 =
                       FStar_List.map
                         (fun uu____4606 ->
                            match uu____4606 with
                            | (f, t) ->
                                let uu____4621 =
                                  let uu____4626 = translate_type env2 t in
                                  (uu____4626, false) in
                                (f, uu____4621)) fields in
                     (name2, uu____4576, (FStar_List.length args),
                       uu____4579) in
                   DTypeFlat uu____4549 in
                 FStar_Pervasives_Native.Some uu____4548
             | (uu____4649, name1, _mangled_name, args, flags1,
                FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches1)) ->
                 let name2 = ((env1.module_name), name1) in
                 let flags2 = translate_flags flags1 in
                 let env2 = FStar_List.fold_left extend_t env1 args in
                 let uu____4686 =
                   let uu____4687 =
                     let uu____4720 =
                       FStar_List.map
                         (fun uu____4765 ->
                            match uu____4765 with
                            | (cons, ts) ->
                                let uu____4804 =
                                  FStar_List.map
                                    (fun uu____4831 ->
                                       match uu____4831 with
                                       | (name3, t) ->
                                           let uu____4846 =
                                             let uu____4851 =
                                               translate_type env2 t in
                                             (uu____4851, false) in
                                           (name3, uu____4846)) ts in
                                (cons, uu____4804)) branches1 in
                     (name2, flags2, (FStar_List.length args), uu____4720) in
                   DTypeVariant uu____4687 in
                 FStar_Pervasives_Native.Some uu____4686
             | (uu____4890, name1, _mangled_name, uu____4893, uu____4894,
                uu____4895) ->
                 ((let uu____4905 =
                     let uu____4910 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name1 in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____4910) in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____4905);
                  FStar_Pervasives_Native.None))
and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env1 ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name1 ->
          let uu____4914 = find_t env1 name1 in TBound uu____4914
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____4916, t2) ->
          let uu____4918 =
            let uu____4923 = translate_type env1 t1 in
            let uu____4924 = translate_type env1 t2 in
            (uu____4923, uu____4924) in
          TArrow uu____4918
      | FStar_Extraction_ML_Syntax.MLTY_Erased -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu____4928 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4928 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when
          let uu____4932 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4932 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], ("FStar"::m::[], "t"))
          when is_machine_int m ->
          let uu____4938 = FStar_Util.must (mk_width m) in TInt uu____4938
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], ("FStar"::m::[], "t'"))
          when is_machine_int m ->
          let uu____4944 = FStar_Util.must (mk_width m) in TInt uu____4944
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu____4949 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____4949 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____4950::arg::uu____4952::[], p) when
          (((let uu____4958 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4958 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____4960 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____4960 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____4962 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____4962 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____4964 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4964 = "FStar.HyperStack.ST.s_mref")
          -> let uu____4965 = translate_type env1 arg in TBuf uu____4965
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____4967::[], p) when
          ((((((((((let uu____4973 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4973 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____4975 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p in
                      uu____4975 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____4977 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p in
                     uu____4977 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____4979 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____4979 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____4981 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p in
                   uu____4981 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____4983 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p in
                  uu____4983 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____4985 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____4985 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____4987 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu____4987 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____4989 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____4989 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____4991 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____4991 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____4993 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____4993 = "FStar.HyperStack.ST.mmmref")
          -> let uu____4994 = translate_type env1 arg in TBuf uu____4994
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____4996::uu____4997::[], p) when
          let uu____5001 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5001 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____5002 = translate_type env1 arg in TBuf uu____5002
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          let uu____5007 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5007 = "LowStar.ConstBuffer.const_buffer" ->
          let uu____5008 = translate_type env1 arg in TConstBuf uu____5008
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
          (((((((((((((let uu____5015 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p in
                       uu____5015 = "FStar.Buffer.buffer") ||
                        (let uu____5017 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p in
                         uu____5017 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____5019 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p in
                        uu____5019 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____5021 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p in
                       uu____5021 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____5023 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p in
                      uu____5023 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____5025 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p in
                     uu____5025 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____5027 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p in
                    uu____5027 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____5029 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p in
                   uu____5029 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____5031 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p in
                  uu____5031 = "FStar.HyperStack.mmref"))
                ||
                (let uu____5033 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____5033 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____5035 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu____5035 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____5037 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____5037 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____5039 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____5039 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____5041 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5041 = "FStar.HyperStack.ST.mmref")
          -> let uu____5042 = translate_type env1 arg in TBuf uu____5042
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____5043::arg::[], p) when
          (let uu____5050 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5050 = "FStar.HyperStack.s_ref") ||
            (let uu____5052 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5052 = "FStar.HyperStack.ST.s_ref")
          -> let uu____5053 = translate_type env1 arg in TBuf uu____5053
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____5054::[], p) when
          let uu____5058 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5058 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, (ns, t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____5084 = FStar_List.map (translate_type env1) args in
          TTuple uu____5084
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, lid) ->
          if (FStar_List.length args) > Prims.int_zero
          then
            let uu____5093 =
              let uu____5106 = FStar_List.map (translate_type env1) args in
              (lid, uu____5106) in
            TApp uu____5093
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____5121 = FStar_List.map (translate_type env1) ts in
          TTuple uu____5121
and (translate_binders :
  env ->
    (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
      Prims.list -> binder Prims.list)
  = fun env1 -> fun args -> FStar_List.map (translate_binder env1) args
and (translate_binder :
  env ->
    (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) ->
      binder)
  =
  fun env1 ->
    fun uu____5137 ->
      match uu____5137 with
      | (name1, typ1) ->
          let uu____5144 = translate_type env1 typ1 in
          { name = name1; typ = uu____5144; mut = false }
and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env1 ->
    fun e ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name1 ->
          let uu____5149 = find env1 name1 in EBound uu____5149
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], op1) when
          (is_machine_int m) && (is_op op1) ->
          let uu____5154 =
            let uu____5159 = FStar_Util.must (mk_op op1) in
            let uu____5160 = FStar_Util.must (mk_width m) in
            (uu____5159, uu____5160) in
          EOp uu____5154
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[], op1) when
          is_bool_op op1 ->
          let uu____5164 =
            let uu____5169 = FStar_Util.must (mk_bool_op op1) in
            (uu____5169, Bool) in
          EOp uu____5164
      | FStar_Extraction_ML_Syntax.MLE_Name n -> EQualified n
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,
            { FStar_Extraction_ML_Syntax.mllb_name = name1;
              FStar_Extraction_ML_Syntax.mllb_tysc =
                FStar_Pervasives_Native.Some ([], typ1);
              FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit;
              FStar_Extraction_ML_Syntax.mllb_def = body;
              FStar_Extraction_ML_Syntax.mllb_meta = flags;
              FStar_Extraction_ML_Syntax.print_typ = print;_}::[]),
           continuation)
          ->
          let binder1 =
            let uu____5188 = translate_type env1 typ1 in
            { name = name1; typ = uu____5188; mut = false } in
          let body1 = translate_expr env1 body in
          let env2 = extend env1 name1 in
          let continuation1 = translate_expr env2 continuation in
          ELet (binder1, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr1, branches1) ->
          let uu____5214 =
            let uu____5225 = translate_expr env1 expr1 in
            let uu____5226 = translate_branches env1 branches1 in
            (uu____5225, uu____5226) in
          EMatch uu____5214
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5240;
                  FStar_Extraction_ML_Syntax.loc = uu____5241;_},
                t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____5243;
             FStar_Extraction_ML_Syntax.loc = uu____5244;_},
           arg::[])
          when
          let uu____5250 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5250 = "FStar.Dyn.undyn" ->
          let uu____5251 =
            let uu____5256 = translate_expr env1 arg in
            let uu____5257 = translate_type env1 t in
            (uu____5256, uu____5257) in
          ECast uu____5251
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5259;
                  FStar_Extraction_ML_Syntax.loc = uu____5260;_},
                uu____5261);
             FStar_Extraction_ML_Syntax.mlty = uu____5262;
             FStar_Extraction_ML_Syntax.loc = uu____5263;_},
           uu____5264)
          when
          let uu____5273 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5273 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5275;
                  FStar_Extraction_ML_Syntax.loc = uu____5276;_},
                t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____5278;
             FStar_Extraction_ML_Syntax.loc = uu____5279;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s);
             FStar_Extraction_ML_Syntax.mlty = uu____5281;
             FStar_Extraction_ML_Syntax.loc = uu____5282;_}::[])
          when
          let uu____5287 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5287 = "LowStar.Failure.failwith" ->
          let uu____5288 =
            let uu____5293 = translate_type env1 t in (s, uu____5293) in
          EAbortT uu____5288
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5295;
                  FStar_Extraction_ML_Syntax.loc = uu____5296;_},
                uu____5297);
             FStar_Extraction_ML_Syntax.mlty = uu____5298;
             FStar_Extraction_ML_Syntax.loc = uu____5299;_},
           arg::[])
          when
          ((let uu____5309 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____5309 = "FStar.HyperStack.All.failwith") ||
             (let uu____5311 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____5311 = "FStar.Error.unexpected"))
            ||
            (let uu____5313 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5313 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____5315;
               FStar_Extraction_ML_Syntax.loc = uu____5316;_} -> EAbortS msg
           | uu____5317 ->
               let print_nm = (["FStar"; "HyperStack"; "IO"], "print_string") in
               let print =
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top
                   (FStar_Extraction_ML_Syntax.MLE_Name print_nm) in
               let print1 =
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top
                   (FStar_Extraction_ML_Syntax.MLE_App (print, [arg])) in
               let t = translate_expr env1 print1 in ESequence [t; EAbort])
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5333;
                  FStar_Extraction_ML_Syntax.loc = uu____5334;_},
                uu____5335);
             FStar_Extraction_ML_Syntax.mlty = uu____5336;
             FStar_Extraction_ML_Syntax.loc = uu____5337;_},
           e1::[])
          when
          (let uu____5347 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5347 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____5349 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5349 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env1 e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5351;
                  FStar_Extraction_ML_Syntax.loc = uu____5352;_},
                uu____5353);
             FStar_Extraction_ML_Syntax.mlty = uu____5354;
             FStar_Extraction_ML_Syntax.loc = uu____5355;_},
           e1::e2::[])
          when
          ((((let uu____5366 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____5366 = "FStar.Buffer.index") ||
               (let uu____5368 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu____5368 = "FStar.Buffer.op_Array_Access"))
              ||
              (let uu____5370 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____5370 = "LowStar.Monotonic.Buffer.index"))
             ||
             (let uu____5372 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____5372 = "LowStar.UninitializedBuffer.uindex"))
            ||
            (let uu____5374 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5374 = "LowStar.ConstBuffer.index")
          ->
          let uu____5375 =
            let uu____5380 = translate_expr env1 e1 in
            let uu____5381 = translate_expr env1 e2 in
            (uu____5380, uu____5381) in
          EBufRead uu____5375
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5383;
                  FStar_Extraction_ML_Syntax.loc = uu____5384;_},
                uu____5385);
             FStar_Extraction_ML_Syntax.mlty = uu____5386;
             FStar_Extraction_ML_Syntax.loc = uu____5387;_},
           e1::[])
          when
          let uu____5395 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5395 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____5396 =
            let uu____5401 = translate_expr env1 e1 in
            (uu____5401, (EConstant (UInt32, "0"))) in
          EBufRead uu____5396
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5403;
                  FStar_Extraction_ML_Syntax.loc = uu____5404;_},
                uu____5405);
             FStar_Extraction_ML_Syntax.mlty = uu____5406;
             FStar_Extraction_ML_Syntax.loc = uu____5407;_},
           e1::e2::[])
          when
          ((let uu____5418 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____5418 = "FStar.Buffer.create") ||
             (let uu____5420 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____5420 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____5422 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5422 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____5423 =
            let uu____5430 = translate_expr env1 e1 in
            let uu____5431 = translate_expr env1 e2 in
            (Stack, uu____5430, uu____5431) in
          EBufCreate uu____5423
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5433;
                  FStar_Extraction_ML_Syntax.loc = uu____5434;_},
                uu____5435);
             FStar_Extraction_ML_Syntax.mlty = uu____5436;
             FStar_Extraction_ML_Syntax.loc = uu____5437;_},
           elen::[])
          when
          let uu____5445 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5445 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____5446 =
            let uu____5451 = translate_expr env1 elen in (Stack, uu____5451) in
          EBufCreateNoInit uu____5446
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5453;
                  FStar_Extraction_ML_Syntax.loc = uu____5454;_},
                uu____5455);
             FStar_Extraction_ML_Syntax.mlty = uu____5456;
             FStar_Extraction_ML_Syntax.loc = uu____5457;_},
           init::[])
          when
          let uu____5465 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5465 = "FStar.HyperStack.ST.salloc" ->
          let uu____5466 =
            let uu____5473 = translate_expr env1 init in
            (Stack, uu____5473, (EConstant (UInt32, "1"))) in
          EBufCreate uu____5466
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5475;
                  FStar_Extraction_ML_Syntax.loc = uu____5476;_},
                uu____5477);
             FStar_Extraction_ML_Syntax.mlty = uu____5478;
             FStar_Extraction_ML_Syntax.loc = uu____5479;_},
           e2::[])
          when
          ((let uu____5489 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____5489 = "FStar.Buffer.createL") ||
             (let uu____5491 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____5491 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____5493 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5493 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____5494 =
            let uu____5501 =
              let uu____5504 = list_elements e2 in
              FStar_List.map (translate_expr env1) uu____5504 in
            (Stack, uu____5501) in
          EBufCreateL uu____5494
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5510;
                  FStar_Extraction_ML_Syntax.loc = uu____5511;_},
                uu____5512);
             FStar_Extraction_ML_Syntax.mlty = uu____5513;
             FStar_Extraction_ML_Syntax.loc = uu____5514;_},
           _erid::e2::[])
          when
          (let uu____5525 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5525 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____5527 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5527 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____5528 =
            let uu____5535 =
              let uu____5538 = list_elements e2 in
              FStar_List.map (translate_expr env1) uu____5538 in
            (Eternal, uu____5535) in
          EBufCreateL uu____5528
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5544;
                  FStar_Extraction_ML_Syntax.loc = uu____5545;_},
                uu____5546);
             FStar_Extraction_ML_Syntax.mlty = uu____5547;
             FStar_Extraction_ML_Syntax.loc = uu____5548;_},
           _rid::init::[])
          when
          (let uu____5559 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5559 = "FStar.HyperStack.ST.ralloc") ||
            (let uu____5561 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5561 = "FStar.HyperStack.ST.ralloc_drgn")
          ->
          let uu____5562 =
            let uu____5569 = translate_expr env1 init in
            (Eternal, uu____5569, (EConstant (UInt32, "1"))) in
          EBufCreate uu____5562
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5571;
                  FStar_Extraction_ML_Syntax.loc = uu____5572;_},
                uu____5573);
             FStar_Extraction_ML_Syntax.mlty = uu____5574;
             FStar_Extraction_ML_Syntax.loc = uu____5575;_},
           _e0::e1::e2::[])
          when
          ((let uu____5587 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____5587 = "FStar.Buffer.rcreate") ||
             (let uu____5589 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____5589 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____5591 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5591 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____5592 =
            let uu____5599 = translate_expr env1 e1 in
            let uu____5600 = translate_expr env1 e2 in
            (Eternal, uu____5599, uu____5600) in
          EBufCreate uu____5592
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5602;
                  FStar_Extraction_ML_Syntax.loc = uu____5603;_},
                uu____5604);
             FStar_Extraction_ML_Syntax.mlty = uu____5605;
             FStar_Extraction_ML_Syntax.loc = uu____5606;_},
           uu____5607)
          when
          (((((let uu____5618 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____5618 = "LowStar.Monotonic.Buffer.mgcmalloc_and_blit") ||
                (let uu____5620 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p in
                 uu____5620 = "LowStar.Monotonic.Buffer.mmalloc_and_blit"))
               ||
               (let uu____5622 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p in
                uu____5622 = "LowStar.Monotonic.Buffer.malloca_and_blit"))
              ||
              (let uu____5624 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____5624 = "LowStar.ImmutableBuffer.igcmalloc_and_blit"))
             ||
             (let uu____5626 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____5626 = "LowStar.ImmutableBuffer.imalloc_and_blit"))
            ||
            (let uu____5628 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5628 = "LowStar.ImmutableBuffer.ialloca_and_blit")
          ->
          EAbortS
            "alloc_and_blit family of functions are not yet supported downstream"
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5630;
                  FStar_Extraction_ML_Syntax.loc = uu____5631;_},
                uu____5632);
             FStar_Extraction_ML_Syntax.mlty = uu____5633;
             FStar_Extraction_ML_Syntax.loc = uu____5634;_},
           _erid::elen::[])
          when
          let uu____5643 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5643 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____5644 =
            let uu____5649 = translate_expr env1 elen in
            (Eternal, uu____5649) in
          EBufCreateNoInit uu____5644
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5651;
                  FStar_Extraction_ML_Syntax.loc = uu____5652;_},
                uu____5653);
             FStar_Extraction_ML_Syntax.mlty = uu____5654;
             FStar_Extraction_ML_Syntax.loc = uu____5655;_},
           _rid::init::[])
          when
          (let uu____5666 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5666 = "FStar.HyperStack.ST.ralloc_mm") ||
            (let uu____5668 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5668 = "FStar.HyperStack.ST.ralloc_drgn_mm")
          ->
          let uu____5669 =
            let uu____5676 = translate_expr env1 init in
            (ManuallyManaged, uu____5676, (EConstant (UInt32, "1"))) in
          EBufCreate uu____5669
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5678;
                  FStar_Extraction_ML_Syntax.loc = uu____5679;_},
                uu____5680);
             FStar_Extraction_ML_Syntax.mlty = uu____5681;
             FStar_Extraction_ML_Syntax.loc = uu____5682;_},
           _e0::e1::e2::[])
          when
          (((let uu____5694 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5694 = "FStar.Buffer.rcreate_mm") ||
              (let uu____5696 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____5696 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____5698 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____5698 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____5700 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5700 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____5701 =
            let uu____5708 = translate_expr env1 e1 in
            let uu____5709 = translate_expr env1 e2 in
            (ManuallyManaged, uu____5708, uu____5709) in
          EBufCreate uu____5701
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5711;
                  FStar_Extraction_ML_Syntax.loc = uu____5712;_},
                uu____5713);
             FStar_Extraction_ML_Syntax.mlty = uu____5714;
             FStar_Extraction_ML_Syntax.loc = uu____5715;_},
           _erid::elen::[])
          when
          let uu____5724 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5724 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____5725 =
            let uu____5730 = translate_expr env1 elen in
            (ManuallyManaged, uu____5730) in
          EBufCreateNoInit uu____5725
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5732;
                  FStar_Extraction_ML_Syntax.loc = uu____5733;_},
                uu____5734);
             FStar_Extraction_ML_Syntax.mlty = uu____5735;
             FStar_Extraction_ML_Syntax.loc = uu____5736;_},
           e2::[])
          when
          let uu____5744 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5744 = "FStar.HyperStack.ST.rfree" ->
          let uu____5745 = translate_expr env1 e2 in EBufFree uu____5745
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5747;
                  FStar_Extraction_ML_Syntax.loc = uu____5748;_},
                uu____5749);
             FStar_Extraction_ML_Syntax.mlty = uu____5750;
             FStar_Extraction_ML_Syntax.loc = uu____5751;_},
           e2::[])
          when
          (let uu____5761 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5761 = "FStar.Buffer.rfree") ||
            (let uu____5763 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5763 = "LowStar.Monotonic.Buffer.free")
          -> let uu____5764 = translate_expr env1 e2 in EBufFree uu____5764
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5766;
                  FStar_Extraction_ML_Syntax.loc = uu____5767;_},
                uu____5768);
             FStar_Extraction_ML_Syntax.mlty = uu____5769;
             FStar_Extraction_ML_Syntax.loc = uu____5770;_},
           e1::e2::_e3::[])
          when
          let uu____5780 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5780 = "FStar.Buffer.sub" ->
          let uu____5781 =
            let uu____5786 = translate_expr env1 e1 in
            let uu____5787 = translate_expr env1 e2 in
            (uu____5786, uu____5787) in
          EBufSub uu____5781
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5789;
                  FStar_Extraction_ML_Syntax.loc = uu____5790;_},
                uu____5791);
             FStar_Extraction_ML_Syntax.mlty = uu____5792;
             FStar_Extraction_ML_Syntax.loc = uu____5793;_},
           e1::e2::_e3::[])
          when
          (let uu____5805 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____5805 = "LowStar.Monotonic.Buffer.msub") ||
            (let uu____5807 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5807 = "LowStar.ConstBuffer.sub")
          ->
          let uu____5808 =
            let uu____5813 = translate_expr env1 e1 in
            let uu____5814 = translate_expr env1 e2 in
            (uu____5813, uu____5814) in
          EBufSub uu____5808
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5816;
                  FStar_Extraction_ML_Syntax.loc = uu____5817;_},
                uu____5818);
             FStar_Extraction_ML_Syntax.mlty = uu____5819;
             FStar_Extraction_ML_Syntax.loc = uu____5820;_},
           e1::e2::[])
          when
          let uu____5829 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5829 = "FStar.Buffer.join" -> translate_expr env1 e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5831;
                  FStar_Extraction_ML_Syntax.loc = uu____5832;_},
                uu____5833);
             FStar_Extraction_ML_Syntax.mlty = uu____5834;
             FStar_Extraction_ML_Syntax.loc = uu____5835;_},
           e1::e2::[])
          when
          let uu____5844 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5844 = "FStar.Buffer.offset" ->
          let uu____5845 =
            let uu____5850 = translate_expr env1 e1 in
            let uu____5851 = translate_expr env1 e2 in
            (uu____5850, uu____5851) in
          EBufSub uu____5845
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5853;
                  FStar_Extraction_ML_Syntax.loc = uu____5854;_},
                uu____5855);
             FStar_Extraction_ML_Syntax.mlty = uu____5856;
             FStar_Extraction_ML_Syntax.loc = uu____5857;_},
           e1::e2::[])
          when
          let uu____5866 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5866 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____5867 =
            let uu____5872 = translate_expr env1 e1 in
            let uu____5873 = translate_expr env1 e2 in
            (uu____5872, uu____5873) in
          EBufSub uu____5867
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5875;
                  FStar_Extraction_ML_Syntax.loc = uu____5876;_},
                uu____5877);
             FStar_Extraction_ML_Syntax.mlty = uu____5878;
             FStar_Extraction_ML_Syntax.loc = uu____5879;_},
           e1::e2::e3::[])
          when
          (((let uu____5891 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5891 = "FStar.Buffer.upd") ||
              (let uu____5893 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____5893 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____5895 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____5895 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____5897 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5897 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____5898 =
            let uu____5905 = translate_expr env1 e1 in
            let uu____5906 = translate_expr env1 e2 in
            let uu____5907 = translate_expr env1 e3 in
            (uu____5905, uu____5906, uu____5907) in
          EBufWrite uu____5898
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5909;
                  FStar_Extraction_ML_Syntax.loc = uu____5910;_},
                uu____5911);
             FStar_Extraction_ML_Syntax.mlty = uu____5912;
             FStar_Extraction_ML_Syntax.loc = uu____5913;_},
           e1::e2::[])
          when
          let uu____5922 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5922 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____5923 =
            let uu____5930 = translate_expr env1 e1 in
            let uu____5931 = translate_expr env1 e2 in
            (uu____5930, (EConstant (UInt32, "0")), uu____5931) in
          EBufWrite uu____5923
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5933;
             FStar_Extraction_ML_Syntax.loc = uu____5934;_},
           uu____5935::[])
          when
          let uu____5938 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5938 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____5940;
             FStar_Extraction_ML_Syntax.loc = uu____5941;_},
           uu____5942::[])
          when
          let uu____5945 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____5945 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5947;
                  FStar_Extraction_ML_Syntax.loc = uu____5948;_},
                uu____5949);
             FStar_Extraction_ML_Syntax.mlty = uu____5950;
             FStar_Extraction_ML_Syntax.loc = uu____5951;_},
           e1::e2::e3::e4::e5::[])
          when
          ((let uu____5965 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____5965 = "FStar.Buffer.blit") ||
             (let uu____5967 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____5967 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____5969 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____5969 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____5970 =
            let uu____5981 = translate_expr env1 e1 in
            let uu____5982 = translate_expr env1 e2 in
            let uu____5983 = translate_expr env1 e3 in
            let uu____5984 = translate_expr env1 e4 in
            let uu____5985 = translate_expr env1 e5 in
            (uu____5981, uu____5982, uu____5983, uu____5984, uu____5985) in
          EBufBlit uu____5970
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____5987;
                  FStar_Extraction_ML_Syntax.loc = uu____5988;_},
                uu____5989);
             FStar_Extraction_ML_Syntax.mlty = uu____5990;
             FStar_Extraction_ML_Syntax.loc = uu____5991;_},
           e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____6002 =
            let uu____6009 = translate_expr env1 e1 in
            let uu____6010 = translate_expr env1 e2 in
            let uu____6011 = translate_expr env1 e3 in
            (uu____6009, uu____6010, uu____6011) in
          EBufFill uu____6002
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____6013;
             FStar_Extraction_ML_Syntax.loc = uu____6014;_},
           uu____6015::[])
          when
          let uu____6018 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6018 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6020;
                  FStar_Extraction_ML_Syntax.loc = uu____6021;_},
                uu____6022);
             FStar_Extraction_ML_Syntax.mlty = uu____6023;
             FStar_Extraction_ML_Syntax.loc = uu____6024;_},
           _rid::[])
          when
          (let uu____6034 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____6034 = "FStar.HyperStack.ST.free_drgn") ||
            (let uu____6036 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6036 = "FStar.HyperStack.ST.new_drgn")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6038;
                  FStar_Extraction_ML_Syntax.loc = uu____6039;_},
                uu____6040);
             FStar_Extraction_ML_Syntax.mlty = uu____6041;
             FStar_Extraction_ML_Syntax.loc = uu____6042;_},
           _ebuf::_eseq::[])
          when
          (((let uu____6053 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6053 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____6055 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
               uu____6055 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____6057 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____6057 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____6059 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6059 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6061;
                  FStar_Extraction_ML_Syntax.loc = uu____6062;_},
                uu____6063);
             FStar_Extraction_ML_Syntax.mlty = uu____6064;
             FStar_Extraction_ML_Syntax.loc = uu____6065;_},
           e1::[])
          when
          (let uu____6075 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
           uu____6075 = "LowStar.ConstBuffer.of_buffer") ||
            (let uu____6077 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6077 = "LowStar.ConstBuffer.of_ibuffer")
          -> translate_expr env1 e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6079;
                  FStar_Extraction_ML_Syntax.loc = uu____6080;_},
                t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6082;
             FStar_Extraction_ML_Syntax.loc = uu____6083;_},
           _eqal::e1::[])
          when
          let uu____6090 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6090 = "LowStar.ConstBuffer.of_qbuf" ->
          let uu____6091 =
            let uu____6096 = translate_expr env1 e1 in
            let uu____6097 =
              let uu____6098 = translate_type env1 t in TConstBuf uu____6098 in
            (uu____6096, uu____6097) in
          ECast uu____6091
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6100;
                  FStar_Extraction_ML_Syntax.loc = uu____6101;_},
                t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6103;
             FStar_Extraction_ML_Syntax.loc = uu____6104;_},
           e1::[])
          when
          ((let uu____6112 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
            uu____6112 = "LowStar.ConstBuffer.cast") ||
             (let uu____6114 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
              uu____6114 = "LowStar.ConstBuffer.to_buffer"))
            ||
            (let uu____6116 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
             uu____6116 = "LowStar.ConstBuffer.to_ibuffer")
          ->
          let uu____6117 =
            let uu____6122 = translate_expr env1 e1 in
            let uu____6123 =
              let uu____6124 = translate_type env1 t in TBuf uu____6124 in
            (uu____6122, uu____6123) in
          ECast uu____6117
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____6126;
             FStar_Extraction_ML_Syntax.loc = uu____6127;_},
           e1::[])
          when
          let uu____6131 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6131 = "Obj.repr" ->
          let uu____6132 =
            let uu____6137 = translate_expr env1 e1 in (uu____6137, TAny) in
          ECast uu____6132
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], op1);
             FStar_Extraction_ML_Syntax.mlty = uu____6140;
             FStar_Extraction_ML_Syntax.loc = uu____6141;_},
           args)
          when (is_machine_int m) && (is_op op1) ->
          let uu____6149 = FStar_Util.must (mk_width m) in
          let uu____6150 = FStar_Util.must (mk_op op1) in
          mk_op_app env1 uu____6149 uu____6150 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[], op1);
             FStar_Extraction_ML_Syntax.mlty = uu____6152;
             FStar_Extraction_ML_Syntax.loc = uu____6153;_},
           args)
          when is_bool_op op1 ->
          let uu____6161 = FStar_Util.must (mk_bool_op op1) in
          mk_op_app env1 Bool uu____6161 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[], "int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____6163;
             FStar_Extraction_ML_Syntax.loc = uu____6164;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_Int
               (c, FStar_Pervasives_Native.None));
             FStar_Extraction_ML_Syntax.mlty = uu____6166;
             FStar_Extraction_ML_Syntax.loc = uu____6167;_}::[])
          when is_machine_int m ->
          let uu____6182 =
            let uu____6187 = FStar_Util.must (mk_width m) in (uu____6187, c) in
          EConstant uu____6182
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[], "uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____6189;
             FStar_Extraction_ML_Syntax.loc = uu____6190;_},
           {
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_Int
               (c, FStar_Pervasives_Native.None));
             FStar_Extraction_ML_Syntax.mlty = uu____6192;
             FStar_Extraction_ML_Syntax.loc = uu____6193;_}::[])
          when is_machine_int m ->
          let uu____6208 =
            let uu____6213 = FStar_Util.must (mk_width m) in (uu____6213, c) in
          EConstant uu____6208
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[], "string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____6214;
             FStar_Extraction_ML_Syntax.loc = uu____6215;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu____6217;
             FStar_Extraction_ML_Syntax.loc = uu____6218;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____6224 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[], "of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____6225;
             FStar_Extraction_ML_Syntax.loc = uu____6226;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu____6228;
             FStar_Extraction_ML_Syntax.loc = uu____6229;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____6235 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[], "of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____6236;
             FStar_Extraction_ML_Syntax.loc = uu____6237;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu____6239;
             FStar_Extraction_ML_Syntax.loc = uu____6240;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____6246 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6248;
                  FStar_Extraction_ML_Syntax.loc = uu____6249;_},
                uu____6250);
             FStar_Extraction_ML_Syntax.mlty = uu____6251;
             FStar_Extraction_ML_Syntax.loc = uu____6252;_},
           { FStar_Extraction_ML_Syntax.expr = ebefore;
             FStar_Extraction_ML_Syntax.mlty = uu____6254;
             FStar_Extraction_ML_Syntax.loc = uu____6255;_}::e1::{
                                                                   FStar_Extraction_ML_Syntax.expr
                                                                    = eafter;
                                                                   FStar_Extraction_ML_Syntax.mlty
                                                                    =
                                                                    uu____6258;
                                                                   FStar_Extraction_ML_Syntax.loc
                                                                    =
                                                                    uu____6259;_}::[])
          when
          let uu____6266 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6266 = "LowStar.Comment.comment_gen" ->
          (match (ebefore, eafter) with
           | (FStar_Extraction_ML_Syntax.MLE_Const
              (FStar_Extraction_ML_Syntax.MLC_String sbefore),
              FStar_Extraction_ML_Syntax.MLE_Const
              (FStar_Extraction_ML_Syntax.MLC_String safter)) ->
               (if FStar_Util.contains sbefore "*/"
                then failwith "Before Comment contains end-of-comment marker"
                else ();
                if FStar_Util.contains safter "*/"
                then failwith "After Comment contains end-of-comment marker"
                else ();
                (let uu____6273 =
                   let uu____6280 = translate_expr env1 e1 in
                   (sbefore, uu____6280, safter) in
                 EComment uu____6273))
           | uu____6281 ->
               failwith "Cannot extract comment applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____6287;
             FStar_Extraction_ML_Syntax.loc = uu____6288;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu____6290;
             FStar_Extraction_ML_Syntax.loc = uu____6291;_}::[])
          when
          let uu____6294 = FStar_Extraction_ML_Syntax.string_of_mlpath p in
          uu____6294 = "LowStar.Comment.comment" ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               (if FStar_Util.contains s "*/"
                then
                  failwith
                    "Standalone Comment contains end-of-comment marker"
                else ();
                EStandaloneComment s)
           | uu____6298 ->
               failwith "Cannot extract comment applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[], "buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____6299;
             FStar_Extraction_ML_Syntax.loc = uu____6300;_},
           { FStar_Extraction_ML_Syntax.expr = e1;
             FStar_Extraction_ML_Syntax.mlty = uu____6302;
             FStar_Extraction_ML_Syntax.loc = uu____6303;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____6309 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[], c);
             FStar_Extraction_ML_Syntax.mlty = uu____6311;
             FStar_Extraction_ML_Syntax.loc = uu____6312;_},
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
            let uu____6319 =
              let uu____6324 = translate_expr env1 arg in
              (uu____6324, (TInt UInt64)) in
            ECast uu____6319
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____6326 =
                 let uu____6331 = translate_expr env1 arg in
                 (uu____6331, (TInt UInt32)) in
               ECast uu____6326)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____6333 =
                   let uu____6338 = translate_expr env1 arg in
                   (uu____6338, (TInt UInt16)) in
                 ECast uu____6333)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____6340 =
                     let uu____6345 = translate_expr env1 arg in
                     (uu____6345, (TInt UInt8)) in
                   ECast uu____6340)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____6347 =
                       let uu____6352 = translate_expr env1 arg in
                       (uu____6352, (TInt Int64)) in
                     ECast uu____6347)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____6354 =
                         let uu____6359 = translate_expr env1 arg in
                         (uu____6359, (TInt Int32)) in
                       ECast uu____6354)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____6361 =
                           let uu____6366 = translate_expr env1 arg in
                           (uu____6366, (TInt Int16)) in
                         ECast uu____6361)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____6368 =
                             let uu____6373 = translate_expr env1 arg in
                             (uu____6373, (TInt Int8)) in
                           ECast uu____6368)
                        else
                          (let uu____6375 =
                             let uu____6382 =
                               let uu____6385 = translate_expr env1 arg in
                               [uu____6385] in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____6382) in
                           EApp uu____6375)
      | FStar_Extraction_ML_Syntax.MLE_App (head, args) ->
          let uu____6396 =
            let uu____6403 = translate_expr env1 head in
            let uu____6404 = FStar_List.map (translate_expr env1) args in
            (uu____6403, uu____6404) in
          EApp uu____6396
      | FStar_Extraction_ML_Syntax.MLE_TApp (head, ty_args) ->
          let uu____6415 =
            let uu____6422 = translate_expr env1 head in
            let uu____6423 = FStar_List.map (translate_type env1) ty_args in
            (uu____6422, uu____6423) in
          ETypApp uu____6415
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t_from, t_to) ->
          let uu____6431 =
            let uu____6436 = translate_expr env1 e1 in
            let uu____6437 = translate_type env1 t_to in
            (uu____6436, uu____6437) in
          ECast uu____6431
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____6438, fields) ->
          let uu____6456 =
            let uu____6467 =
              assert_lid env1 e.FStar_Extraction_ML_Syntax.mlty in
            let uu____6468 =
              FStar_List.map
                (fun uu____6487 ->
                   match uu____6487 with
                   | (field, expr1) ->
                       let uu____6498 = translate_expr env1 expr1 in
                       (field, uu____6498)) fields in
            (uu____6467, uu____6468) in
          EFlat uu____6456
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1, path) ->
          let uu____6507 =
            let uu____6514 =
              assert_lid env1 e1.FStar_Extraction_ML_Syntax.mlty in
            let uu____6515 = translate_expr env1 e1 in
            (uu____6514, uu____6515, (FStar_Pervasives_Native.snd path)) in
          EField uu____6507
      | FStar_Extraction_ML_Syntax.MLE_Let uu____6518 ->
          let uu____6529 =
            let uu____6530 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") e in
            FStar_Util.format1 "todo: translate_expr [MLE_Let] (expr is: %s)"
              uu____6530 in
          failwith uu____6529
      | FStar_Extraction_ML_Syntax.MLE_App (head, uu____6534) ->
          let uu____6539 =
            let uu____6540 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____6540 in
          failwith uu____6539
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____6546 = FStar_List.map (translate_expr env1) seqs in
          ESequence uu____6546
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____6552 = FStar_List.map (translate_expr env1) es in
          ETuple uu____6552
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____6555, cons), es) ->
          let uu____6566 =
            let uu____6575 =
              assert_lid env1 e.FStar_Extraction_ML_Syntax.mlty in
            let uu____6576 = FStar_List.map (translate_expr env1) es in
            (uu____6575, cons, uu____6576) in
          ECons uu____6566
      | FStar_Extraction_ML_Syntax.MLE_Fun (args, body) ->
          let binders = translate_binders env1 args in
          let env2 = add_binders env1 args in
          let uu____6599 =
            let uu____6608 = translate_expr env2 body in
            let uu____6609 =
              translate_type env2 body.FStar_Extraction_ML_Syntax.mlty in
            (binders, uu____6608, uu____6609) in
          EFun uu____6599
      | FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3) ->
          let uu____6619 =
            let uu____6626 = translate_expr env1 e1 in
            let uu____6627 = translate_expr env1 e2 in
            let uu____6628 =
              match e3 with
              | FStar_Pervasives_Native.None -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env1 e31 in
            (uu____6626, uu____6627, uu____6628) in
          EIfThenElse uu____6619
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____6630 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____6637 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____6652 ->
          failwith "todo: translate_expr [MLE_Coerce]"
and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env1 ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) ->
          if (FStar_List.length ts) > Prims.int_zero
          then
            let uu____6667 =
              let uu____6680 = FStar_List.map (translate_type env1) ts in
              (lid, uu____6680) in
            TApp uu____6667
          else TQualified lid
      | uu____6692 ->
          let uu____6693 =
            let uu____6694 =
              FStar_Extraction_ML_Code.string_of_mlty ([], "") t in
            FStar_Util.format1
              "invalid argument: expected MLTY_Named, got %s" uu____6694 in
          failwith uu____6693
and (translate_branches :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr
      FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr)
      Prims.list -> (pattern * expr) Prims.list)
  =
  fun env1 ->
    fun branches1 -> FStar_List.map (translate_branch env1) branches1
and (translate_branch :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr
      FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr) ->
      (pattern * expr))
  =
  fun env1 ->
    fun uu____6722 ->
      match uu____6722 with
      | (pat, guard, expr1) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____6748 = translate_pat env1 pat in
            (match uu____6748 with
             | (env2, pat1) ->
                 let uu____6759 = translate_expr env2 expr1 in
                 (pat1, uu____6759))
          else failwith "todo: translate_branch"
and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___7_6765 ->
    match uu___7_6765 with
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
  env -> FStar_Extraction_ML_Syntax.mlpattern -> (env * pattern)) =
  fun env1 ->
    fun p ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Unit) -> (env1, PUnit)
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Bool b) -> (env1, (PBool b))
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Int (s, sw)) ->
          let uu____6829 =
            let uu____6830 =
              let uu____6835 = translate_width sw in (uu____6835, s) in
            PConstant uu____6830 in
          (env1, uu____6829)
      | FStar_Extraction_ML_Syntax.MLP_Var name1 ->
          let env2 = extend env1 name1 in
          (env2, (PVar { name = name1; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild ->
          let env2 = extend env1 "_" in
          (env2, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____6839, cons), ps) ->
          let uu____6850 =
            FStar_List.fold_left
              (fun uu____6870 ->
                 fun p1 ->
                   match uu____6870 with
                   | (env2, acc) ->
                       let uu____6890 = translate_pat env2 p1 in
                       (match uu____6890 with
                        | (env3, p2) -> (env3, (p2 :: acc)))) (env1, []) ps in
          (match uu____6850 with
           | (env2, ps1) -> (env2, (PCons (cons, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____6919, ps) ->
          let uu____6937 =
            FStar_List.fold_left
              (fun uu____6971 ->
                 fun uu____6972 ->
                   match (uu____6971, uu____6972) with
                   | ((env2, acc), (field, p1)) ->
                       let uu____7041 = translate_pat env2 p1 in
                       (match uu____7041 with
                        | (env3, p2) -> (env3, ((field, p2) :: acc))))
              (env1, []) ps in
          (match uu____6937 with
           | (env2, ps1) -> (env2, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____7103 =
            FStar_List.fold_left
              (fun uu____7123 ->
                 fun p1 ->
                   match uu____7123 with
                   | (env2, acc) ->
                       let uu____7143 = translate_pat env2 p1 in
                       (match uu____7143 with
                        | (env3, p2) -> (env3, (p2 :: acc)))) (env1, []) ps in
          (match uu____7103 with
           | (env2, ps1) -> (env2, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____7170 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____7175 ->
          failwith "todo: translate_pat [MLP_Branch]"
and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____7186 =
            let uu____7187 = FStar_String.list_of_string s in
            FStar_All.pipe_right uu____7187
              (FStar_Util.for_some
                 (fun c1 -> c1 = (FStar_Char.char_of_int Prims.int_zero))) in
          if uu____7186
          then
            let uu____7194 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s in
            failwith uu____7194
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1 in
        let s = FStar_Util.string_of_int i in
        let c2 = EConstant (UInt32, s) in
        let char_of_int = EQualified (["FStar"; "Char"], "char_of_int") in
        EApp (char_of_int, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s, FStar_Pervasives_Native.Some uu____7206) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____7221 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____7222 ->
        failwith "todo: translate_expr [MLC_Bytes]"
    | FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.None) ->
        EConstant (CInt, s)
and (mk_op_app :
  env -> width -> op -> FStar_Extraction_ML_Syntax.mlexpr Prims.list -> expr)
  =
  fun env1 ->
    fun w ->
      fun op1 ->
        fun args ->
          let uu____7242 =
            let uu____7249 = FStar_List.map (translate_expr env1) args in
            ((EOp (op1, w)), uu____7249) in
          EApp uu____7242
let (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____7260 ->
    match uu____7260 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m ->
             let m_name =
               let uu____7308 = m in
               match uu____7308 with
               | (path, uu____7322, uu____7323) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path in
             try
               (fun uu___1671_7341 ->
                  match () with
                  | () ->
                      ((let uu____7345 =
                          let uu____7346 = FStar_Options.silent () in
                          Prims.op_Negation uu____7346 in
                        if uu____7345
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____7348 = translate_module m in
                        FStar_Pervasives_Native.Some uu____7348))) ()
             with
             | uu___1670_7351 ->
                 ((let uu____7355 = FStar_Util.print_exn uu___1670_7351 in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____7355);
                  FStar_Pervasives_Native.None)) modules