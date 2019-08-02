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
let (uu___is_DGlobal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DGlobal _0 -> true | uu____738 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____849 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____974 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____1081 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DUnusedRetainedForBackwardsCompat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DUnusedRetainedForBackwardsCompat _0 -> true
    | uu____1213 -> false
  
let (__proj__DUnusedRetainedForBackwardsCompat__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  =
  fun projectee  ->
    match projectee with | DUnusedRetainedForBackwardsCompat _0 -> _0
  
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____1330 -> false
  
let (__proj__DTypeVariant__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (Prims.string * (typ * Prims.bool)) Prims.list)
      Prims.list))
  = fun projectee  -> match projectee with | DTypeVariant _0 -> _0 
let (uu___is_DTypeAbstractStruct : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DTypeAbstractStruct _0 -> true
    | uu____1471 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____1539 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ * Prims.string Prims.list))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1632 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1643 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1654 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1665 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1676 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1687 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1698 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1709 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1722 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1743 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1756 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1779 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1802 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____1823 -> false
  
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | IfDef  -> true | uu____1834 -> false
  
let (uu___is_Macro : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Macro  -> true | uu____1845 -> false
  
let (uu___is_Deprecated : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Deprecated _0 -> true | uu____1858 -> false
  
let (__proj__Deprecated__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Deprecated _0 -> _0 
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1879 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1890 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1901 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1914 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1944 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1992 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____2025 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____2043 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____2086 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____2129 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____2172 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____2211 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____2240 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____2277 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____2318 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____2355 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____2396 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____2437 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____2496 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____2549 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____2584 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____2614 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____2625 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____2638 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____2659 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____2670 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____2682 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____2712 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____2771 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____2815 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____2852 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2891 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2925 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2977 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____3015 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____3045 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____3089 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____3111 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____3134 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____3164 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____3175 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____3186 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____3197 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____3208 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____3219 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____3230 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____3241 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____3252 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____3263 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____3274 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____3285 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____3296 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____3307 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____3318 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____3329 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____3340 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____3351 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____3362 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____3373 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____3384 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____3395 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____3406 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____3417 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____3428 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____3439 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____3452 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____3474 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____3500 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____3542 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____3574 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____3619 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____3652 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____3663 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____3674 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____3685 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____3696 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____3707 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____3718 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____3729 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____3740 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____3751 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____3800 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____3819 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____3837 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____3857 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____3899 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____3910 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____3926 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____3958 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____3994 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____4057 -> false
  
let (__proj__TTuple__item___0 : typ -> typ Prims.list) =
  fun projectee  -> match projectee with | TTuple _0 -> _0 
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
let (current_version : version) = (Prims.of_int (27)) 
type file = (Prims.string * program)
type binary_format = (version * file Prims.list)
let fst3 :
  'Auu____4158 'Auu____4159 'Auu____4160 .
    ('Auu____4158 * 'Auu____4159 * 'Auu____4160) -> 'Auu____4158
  = fun uu____4171  -> match uu____4171 with | (x,uu____4179,uu____4180) -> x 
let snd3 :
  'Auu____4190 'Auu____4191 'Auu____4192 .
    ('Auu____4190 * 'Auu____4191 * 'Auu____4192) -> 'Auu____4191
  = fun uu____4203  -> match uu____4203 with | (uu____4210,x,uu____4212) -> x 
let thd3 :
  'Auu____4222 'Auu____4223 'Auu____4224 .
    ('Auu____4222 * 'Auu____4223 * 'Auu____4224) -> 'Auu____4224
  = fun uu____4235  -> match uu____4235 with | (uu____4242,uu____4243,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___0_4253  ->
    match uu___0_4253 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____4265 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___1_4275  ->
    match uu___1_4275 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____4284 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___2_4305  ->
    match uu___2_4305 with
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
    | uu____4350 -> FStar_Pervasives_Native.None
  
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
      let uu___164_4506 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___164_4506.names_t);
        module_name = (uu___164_4506.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___168_4520 = env  in
      {
        names = (uu___168_4520.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___168_4520.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____4535 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____4535 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___179_4559  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___178_4566 ->
          let uu____4568 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4568
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___188_4588  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___187_4597 ->
          let uu____4599 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4599
  
let add_binders :
  'Auu____4610 . env -> (Prims.string * 'Auu____4610) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____4645  ->
             match uu____4645 with | (name,uu____4652) -> extend env1 name)
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
      | uu____4704 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____4923  ->
    match uu____4923 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____4972 = m  in
               match uu____4972 with
               | (path,uu____4987,uu____4988) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___230_5006  ->
                  match () with
                  | () ->
                      ((let uu____5010 =
                          let uu____5012 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____5012  in
                        if uu____5010
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____5018 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____5018))) ()
             with
             | e ->
                 ((let uu____5027 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____5027);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____5030  ->
    match uu____5030 with
    | (module_name,modul,uu____5045) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____5080 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___3_5094  ->
         match uu___3_5094 with
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
         | FStar_Extraction_ML_Syntax.CIfDef  ->
             FStar_Pervasives_Native.Some IfDef
         | FStar_Extraction_ML_Syntax.CMacro  ->
             FStar_Pervasives_Native.Some Macro
         | FStar_Extraction_ML_Syntax.Deprecated s ->
             FStar_Pervasives_Native.Some (Deprecated s)
         | uu____5107 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____5111 =
      FStar_List.choose
        (fun uu___4_5118  ->
           match uu___4_5118 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____5125 -> FStar_Pervasives_Native.None) flags
       in
    match uu____5111 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____5138 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____5152 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____5154 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____5159) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5186;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5189;_} when
            FStar_Util.for_some
              (fun uu___5_5194  ->
                 match uu___5_5194 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____5197 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            let arg_names =
              match e.FStar_Extraction_ML_Syntax.expr with
              | FStar_Extraction_ML_Syntax.MLE_Fun (args,uu____5220) ->
                  FStar_List.map FStar_Pervasives_Native.fst args
              | uu____5242 -> []  in
            if (FStar_List.length tvars) = Prims.int_zero
            then
              let uu____5250 =
                let uu____5251 =
                  let uu____5277 = translate_cc meta  in
                  let uu____5280 = translate_flags meta  in
                  let uu____5283 = translate_type env t0  in
                  (uu____5277, uu____5280, name1, uu____5283, arg_names)  in
                DExternal uu____5251  in
              FStar_Pervasives_Native.Some uu____5250
            else
              ((let uu____5302 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____5302);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5308;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____5311;
                FStar_Extraction_ML_Syntax.loc = uu____5312;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5314;_} ->
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
               let rec find_return_type eff i uu___6_5371 =
                 match uu___6_5371 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5380,eff1,t)
                     when i > Prims.int_zero ->
                     find_return_type eff1 (i - Prims.int_one) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____5400 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____5400 with
               | (i,eff,t) ->
                   (if i > Prims.int_zero
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____5426 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____5426 msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5444) ->
                           let uu____5445 = translate_flags meta  in
                           MustDisappear :: uu____5445
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____5448 = translate_flags meta  in
                           MustDisappear :: uu____5448
                       | uu____5451 -> translate_flags meta  in
                     try
                       (fun uu___378_5460  ->
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
                         ((let uu____5492 =
                             let uu____5498 =
                               let uu____5500 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____5500 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____5498)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____5492);
                          (let msg1 =
                             Prims.op_Hat
                               "This function was not extracted:\n" msg
                              in
                           FStar_Pervasives_Native.Some
                             (DFunction
                                (cc, meta1, (FStar_List.length tvars), t1,
                                  name1, binders, (EAbortS msg1))))))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5526;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5529;_} ->
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
                 (fun uu___405_5566  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____5590 =
                       let uu____5596 =
                         let uu____5598 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____5600 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____5598
                           uu____5600
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____5596)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____5590);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5618;
            FStar_Extraction_ML_Syntax.mllb_def = uu____5619;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____5620;
            FStar_Extraction_ML_Syntax.print_typ = uu____5621;_} ->
            ((let uu____5628 =
                let uu____5634 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____5634)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____5628);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____5641 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____5641
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____5655 = ty  in
      match uu____5655 with
      | (uu____5658,uu____5659,uu____5660,uu____5661,flags,uu____5663) ->
          if FStar_List.mem FStar_Extraction_ML_Syntax.NoExtract flags
          then FStar_Pervasives_Native.None
          else
            (match ty with
             | (assumed,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
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
                        flags1)
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
                     (let uu____5737 =
                        let uu____5738 =
                          let uu____5758 = translate_flags flags1  in
                          let uu____5761 = translate_type env1 t  in
                          (name1, uu____5758, (FStar_List.length args),
                            uu____5761)
                           in
                        DTypeAlias uu____5738  in
                      FStar_Pervasives_Native.Some uu____5737)
             | (uu____5774,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____5819 =
                   let uu____5820 =
                     let uu____5852 = translate_flags flags1  in
                     let uu____5855 =
                       FStar_List.map
                         (fun uu____5887  ->
                            match uu____5887 with
                            | (f,t) ->
                                let uu____5907 =
                                  let uu____5913 = translate_type env1 t  in
                                  (uu____5913, false)  in
                                (f, uu____5907)) fields
                        in
                     (name1, uu____5852, (FStar_List.length args),
                       uu____5855)
                      in
                   DTypeFlat uu____5820  in
                 FStar_Pervasives_Native.Some uu____5819
             | (uu____5946,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____5996 =
                   let uu____5997 =
                     let uu____6036 =
                       FStar_List.map
                         (fun uu____6089  ->
                            match uu____6089 with
                            | (cons1,ts) ->
                                let uu____6137 =
                                  FStar_List.map
                                    (fun uu____6169  ->
                                       match uu____6169 with
                                       | (name2,t) ->
                                           let uu____6189 =
                                             let uu____6195 =
                                               translate_type env1 t  in
                                             (uu____6195, false)  in
                                           (name2, uu____6189)) ts
                                   in
                                (cons1, uu____6137)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____6036)
                      in
                   DTypeVariant uu____5997  in
                 FStar_Pervasives_Native.Some uu____5996
             | (uu____6248,name,_mangled_name,uu____6251,uu____6252,uu____6253)
                 ->
                 ((let uu____6269 =
                     let uu____6275 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____6275)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____6269);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____6283 = find_t env name  in TBound uu____6283
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____6286,t2) ->
          let uu____6288 =
            let uu____6293 = translate_type env t1  in
            let uu____6294 = translate_type env t2  in
            (uu____6293, uu____6294)  in
          TArrow uu____6288
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6298 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6298 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6305 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6305 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____6322 = FStar_Util.must (mk_width m)  in TInt uu____6322
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____6336 = FStar_Util.must (mk_width m)  in TInt uu____6336
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6341 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6341 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____6345::arg::uu____6347::[],p) when
          (((let uu____6353 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6353 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____6358 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6358 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____6363 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6363 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____6368 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6368 = "FStar.HyperStack.ST.s_mref")
          -> let uu____6372 = translate_type env arg  in TBuf uu____6372
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____6374::[],p) when
          ((((((((((let uu____6380 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6380 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____6385 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6385 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____6390 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6390 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____6395 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6395 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____6400 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6400 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____6405 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6405 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____6410 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6410 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____6415 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6415 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____6420 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6420 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____6425 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6425 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____6430 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6430 = "FStar.HyperStack.ST.mmmref")
          -> let uu____6434 = translate_type env arg  in TBuf uu____6434
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____6436::uu____6437::[],p) when
          let uu____6441 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6441 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____6445 = translate_type env arg  in TBuf uu____6445
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6450 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6450 = "LowStar.ConstBuffer.const_buffer" ->
          let uu____6454 = translate_type env arg  in TBuf uu____6454
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____6461 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6461 = "FStar.Buffer.buffer") ||
                        (let uu____6466 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____6466 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____6471 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____6471 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____6476 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6476 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____6481 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6481 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____6486 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6486 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____6491 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6491 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____6496 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6496 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____6501 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6501 = "FStar.HyperStack.mmref"))
                ||
                (let uu____6506 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6506 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____6511 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6511 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____6516 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6516 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____6521 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6521 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____6526 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6526 = "FStar.HyperStack.ST.mmref")
          -> let uu____6530 = translate_type env arg  in TBuf uu____6530
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6531::arg::[],p) when
          (let uu____6538 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6538 = "FStar.HyperStack.s_ref") ||
            (let uu____6543 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6543 = "FStar.HyperStack.ST.s_ref")
          -> let uu____6547 = translate_type env arg  in TBuf uu____6547
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6548::[],p) when
          let uu____6552 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6552 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____6604 = FStar_List.map (translate_type env) args  in
          TTuple uu____6604
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > Prims.int_zero
          then
            let uu____6615 =
              let uu____6630 = FStar_List.map (translate_type env) args  in
              (lid, uu____6630)  in
            TApp uu____6615
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____6648 = FStar_List.map (translate_type env) ts  in
          TTuple uu____6648

and (translate_binders :
  env ->
    (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
      Prims.list -> binder Prims.list)
  = fun env  -> fun args  -> FStar_List.map (translate_binder env) args

and (translate_binder :
  env ->
    (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) ->
      binder)
  =
  fun env  ->
    fun uu____6666  ->
      match uu____6666 with
      | (name,typ) ->
          let uu____6676 = translate_type env typ  in
          { name; typ = uu____6676; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____6683 = find env name  in EBound uu____6683
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____6697 =
            let uu____6702 = FStar_Util.must (mk_op op)  in
            let uu____6703 = FStar_Util.must (mk_width m)  in
            (uu____6702, uu____6703)  in
          EOp uu____6697
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____6713 =
            let uu____6718 = FStar_Util.must (mk_bool_op op)  in
            (uu____6718, Bool)  in
          EOp uu____6713
      | FStar_Extraction_ML_Syntax.MLE_Name n1 -> EQualified n1
      | FStar_Extraction_ML_Syntax.MLE_Let
          ((flavor,{ FStar_Extraction_ML_Syntax.mllb_name = name;
                     FStar_Extraction_ML_Syntax.mllb_tysc =
                       FStar_Pervasives_Native.Some ([],typ);
                     FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit;
                     FStar_Extraction_ML_Syntax.mllb_def = body;
                     FStar_Extraction_ML_Syntax.mllb_meta = flags;
                     FStar_Extraction_ML_Syntax.print_typ = print7;_}::[]),continuation)
          ->
          let binder =
            let uu____6741 = translate_type env typ  in
            { name; typ = uu____6741; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____6768 =
            let uu____6779 = translate_expr env expr  in
            let uu____6780 = translate_branches env branches  in
            (uu____6779, uu____6780)  in
          EMatch uu____6768
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6794;
                  FStar_Extraction_ML_Syntax.loc = uu____6795;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6797;
             FStar_Extraction_ML_Syntax.loc = uu____6798;_},arg::[])
          when
          let uu____6804 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6804 = "FStar.Dyn.undyn" ->
          let uu____6808 =
            let uu____6813 = translate_expr env arg  in
            let uu____6814 = translate_type env t  in
            (uu____6813, uu____6814)  in
          ECast uu____6808
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6816;
                  FStar_Extraction_ML_Syntax.loc = uu____6817;_},uu____6818);
             FStar_Extraction_ML_Syntax.mlty = uu____6819;
             FStar_Extraction_ML_Syntax.loc = uu____6820;_},uu____6821)
          when
          let uu____6830 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6830 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6835;
                  FStar_Extraction_ML_Syntax.loc = uu____6836;_},uu____6837);
             FStar_Extraction_ML_Syntax.mlty = uu____6838;
             FStar_Extraction_ML_Syntax.loc = uu____6839;_},arg::[])
          when
          ((let uu____6849 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6849 = "FStar.HyperStack.All.failwith") ||
             (let uu____6854 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6854 = "FStar.Error.unexpected"))
            ||
            (let uu____6859 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6859 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____6864;
               FStar_Extraction_ML_Syntax.loc = uu____6865;_} -> EAbortS msg
           | uu____6867 ->
               let print7 =
                 let uu____6869 =
                   let uu____6870 =
                     let uu____6871 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____6871
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____6870  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____6869
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
                  FStar_Extraction_ML_Syntax.mlty = uu____6878;
                  FStar_Extraction_ML_Syntax.loc = uu____6879;_},uu____6880);
             FStar_Extraction_ML_Syntax.mlty = uu____6881;
             FStar_Extraction_ML_Syntax.loc = uu____6882;_},e1::[])
          when
          (let uu____6892 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6892 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____6897 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6897 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6902;
                  FStar_Extraction_ML_Syntax.loc = uu____6903;_},uu____6904);
             FStar_Extraction_ML_Syntax.mlty = uu____6905;
             FStar_Extraction_ML_Syntax.loc = uu____6906;_},e1::e2::[])
          when
          ((((let uu____6917 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6917 = "FStar.Buffer.index") ||
               (let uu____6922 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6922 = "FStar.Buffer.op_Array_Access"))
              ||
              (let uu____6927 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6927 = "LowStar.Monotonic.Buffer.index"))
             ||
             (let uu____6932 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6932 = "LowStar.UninitializedBuffer.uindex"))
            ||
            (let uu____6937 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6937 = "LowStar.ConstBuffer.index")
          ->
          let uu____6941 =
            let uu____6946 = translate_expr env e1  in
            let uu____6947 = translate_expr env e2  in
            (uu____6946, uu____6947)  in
          EBufRead uu____6941
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6949;
                  FStar_Extraction_ML_Syntax.loc = uu____6950;_},uu____6951);
             FStar_Extraction_ML_Syntax.mlty = uu____6952;
             FStar_Extraction_ML_Syntax.loc = uu____6953;_},e1::[])
          when
          let uu____6961 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6961 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____6965 =
            let uu____6970 = translate_expr env e1  in
            (uu____6970, (EConstant (UInt32, "0")))  in
          EBufRead uu____6965
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6974;
                  FStar_Extraction_ML_Syntax.loc = uu____6975;_},uu____6976);
             FStar_Extraction_ML_Syntax.mlty = uu____6977;
             FStar_Extraction_ML_Syntax.loc = uu____6978;_},e1::e2::[])
          when
          ((let uu____6989 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6989 = "FStar.Buffer.create") ||
             (let uu____6994 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6994 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____6999 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6999 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____7003 =
            let uu____7010 = translate_expr env e1  in
            let uu____7011 = translate_expr env e2  in
            (Stack, uu____7010, uu____7011)  in
          EBufCreate uu____7003
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7013;
                  FStar_Extraction_ML_Syntax.loc = uu____7014;_},uu____7015);
             FStar_Extraction_ML_Syntax.mlty = uu____7016;
             FStar_Extraction_ML_Syntax.loc = uu____7017;_},elen::[])
          when
          let uu____7025 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7025 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____7029 =
            let uu____7034 = translate_expr env elen  in (Stack, uu____7034)
             in
          EBufCreateNoInit uu____7029
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7036;
                  FStar_Extraction_ML_Syntax.loc = uu____7037;_},uu____7038);
             FStar_Extraction_ML_Syntax.mlty = uu____7039;
             FStar_Extraction_ML_Syntax.loc = uu____7040;_},init1::[])
          when
          let uu____7048 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7048 = "FStar.HyperStack.ST.salloc" ->
          let uu____7052 =
            let uu____7059 = translate_expr env init1  in
            (Stack, uu____7059, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7052
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7063;
                  FStar_Extraction_ML_Syntax.loc = uu____7064;_},uu____7065);
             FStar_Extraction_ML_Syntax.mlty = uu____7066;
             FStar_Extraction_ML_Syntax.loc = uu____7067;_},e2::[])
          when
          ((let uu____7077 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7077 = "FStar.Buffer.createL") ||
             (let uu____7082 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7082 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____7087 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7087 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____7091 =
            let uu____7098 =
              let uu____7101 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7101  in
            (Stack, uu____7098)  in
          EBufCreateL uu____7091
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7107;
                  FStar_Extraction_ML_Syntax.loc = uu____7108;_},uu____7109);
             FStar_Extraction_ML_Syntax.mlty = uu____7110;
             FStar_Extraction_ML_Syntax.loc = uu____7111;_},_erid::e2::[])
          when
          (let uu____7122 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7122 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____7127 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7127 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____7131 =
            let uu____7138 =
              let uu____7141 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7141  in
            (Eternal, uu____7138)  in
          EBufCreateL uu____7131
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7147;
                  FStar_Extraction_ML_Syntax.loc = uu____7148;_},uu____7149);
             FStar_Extraction_ML_Syntax.mlty = uu____7150;
             FStar_Extraction_ML_Syntax.loc = uu____7151;_},_rid::init1::[])
          when
          let uu____7160 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7160 = "FStar.HyperStack.ST.ralloc" ->
          let uu____7164 =
            let uu____7171 = translate_expr env init1  in
            (Eternal, uu____7171, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7164
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7175;
                  FStar_Extraction_ML_Syntax.loc = uu____7176;_},uu____7177);
             FStar_Extraction_ML_Syntax.mlty = uu____7178;
             FStar_Extraction_ML_Syntax.loc = uu____7179;_},_e0::e1::e2::[])
          when
          ((let uu____7191 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7191 = "FStar.Buffer.rcreate") ||
             (let uu____7196 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7196 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____7201 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7201 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____7205 =
            let uu____7212 = translate_expr env e1  in
            let uu____7213 = translate_expr env e2  in
            (Eternal, uu____7212, uu____7213)  in
          EBufCreate uu____7205
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7215;
                  FStar_Extraction_ML_Syntax.loc = uu____7216;_},uu____7217);
             FStar_Extraction_ML_Syntax.mlty = uu____7218;
             FStar_Extraction_ML_Syntax.loc = uu____7219;_},uu____7220)
          when
          (((((let uu____7231 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7231 = "LowStar.Monotonic.Buffer.mgcmalloc_and_blit") ||
                (let uu____7236 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____7236 = "LowStar.Monotonic.Buffer.mmalloc_and_blit"))
               ||
               (let uu____7241 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____7241 = "LowStar.Monotonic.Buffer.malloca_and_blit"))
              ||
              (let uu____7246 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7246 = "LowStar.ImmutableBuffer.igcmalloc_and_blit"))
             ||
             (let uu____7251 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7251 = "LowStar.ImmutableBuffer.imalloc_and_blit"))
            ||
            (let uu____7256 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7256 = "LowStar.ImmutableBuffer.ialloca_and_blit")
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
          (let uu____7468 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7468 = "LowStar.Monotonic.Buffer.msub") ||
            (let uu____7473 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7473 = "LowStar.ConstBuffer.sub")
          ->
          let uu____7477 =
            let uu____7482 = translate_expr env e1  in
            let uu____7483 = translate_expr env e2  in
            (uu____7482, uu____7483)  in
          EBufSub uu____7477
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7485;
                  FStar_Extraction_ML_Syntax.loc = uu____7486;_},uu____7487);
             FStar_Extraction_ML_Syntax.mlty = uu____7488;
             FStar_Extraction_ML_Syntax.loc = uu____7489;_},e1::e2::[])
          when
          let uu____7498 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7498 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7503;
                  FStar_Extraction_ML_Syntax.loc = uu____7504;_},uu____7505);
             FStar_Extraction_ML_Syntax.mlty = uu____7506;
             FStar_Extraction_ML_Syntax.loc = uu____7507;_},e1::e2::[])
          when
          let uu____7516 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7516 = "FStar.Buffer.offset" ->
          let uu____7520 =
            let uu____7525 = translate_expr env e1  in
            let uu____7526 = translate_expr env e2  in
            (uu____7525, uu____7526)  in
          EBufSub uu____7520
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7528;
                  FStar_Extraction_ML_Syntax.loc = uu____7529;_},uu____7530);
             FStar_Extraction_ML_Syntax.mlty = uu____7531;
             FStar_Extraction_ML_Syntax.loc = uu____7532;_},e1::e2::[])
          when
          let uu____7541 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7541 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____7545 =
            let uu____7550 = translate_expr env e1  in
            let uu____7551 = translate_expr env e2  in
            (uu____7550, uu____7551)  in
          EBufSub uu____7545
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7553;
                  FStar_Extraction_ML_Syntax.loc = uu____7554;_},uu____7555);
             FStar_Extraction_ML_Syntax.mlty = uu____7556;
             FStar_Extraction_ML_Syntax.loc = uu____7557;_},e1::e2::e3::[])
          when
          (((let uu____7569 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7569 = "FStar.Buffer.upd") ||
              (let uu____7574 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7574 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____7579 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7579 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____7584 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7584 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____7588 =
            let uu____7595 = translate_expr env e1  in
            let uu____7596 = translate_expr env e2  in
            let uu____7597 = translate_expr env e3  in
            (uu____7595, uu____7596, uu____7597)  in
          EBufWrite uu____7588
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7599;
                  FStar_Extraction_ML_Syntax.loc = uu____7600;_},uu____7601);
             FStar_Extraction_ML_Syntax.mlty = uu____7602;
             FStar_Extraction_ML_Syntax.loc = uu____7603;_},e1::e2::[])
          when
          let uu____7612 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7612 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____7616 =
            let uu____7623 = translate_expr env e1  in
            let uu____7624 = translate_expr env e2  in
            (uu____7623, (EConstant (UInt32, "0")), uu____7624)  in
          EBufWrite uu____7616
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7628;
             FStar_Extraction_ML_Syntax.loc = uu____7629;_},uu____7630::[])
          when
          let uu____7633 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7633 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7638;
             FStar_Extraction_ML_Syntax.loc = uu____7639;_},uu____7640::[])
          when
          let uu____7643 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7643 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7648;
                  FStar_Extraction_ML_Syntax.loc = uu____7649;_},uu____7650);
             FStar_Extraction_ML_Syntax.mlty = uu____7651;
             FStar_Extraction_ML_Syntax.loc = uu____7652;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____7666 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7666 = "FStar.Buffer.blit") ||
             (let uu____7671 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7671 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____7676 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7676 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____7680 =
            let uu____7691 = translate_expr env e1  in
            let uu____7692 = translate_expr env e2  in
            let uu____7693 = translate_expr env e3  in
            let uu____7694 = translate_expr env e4  in
            let uu____7695 = translate_expr env e5  in
            (uu____7691, uu____7692, uu____7693, uu____7694, uu____7695)  in
          EBufBlit uu____7680
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7697;
                  FStar_Extraction_ML_Syntax.loc = uu____7698;_},uu____7699);
             FStar_Extraction_ML_Syntax.mlty = uu____7700;
             FStar_Extraction_ML_Syntax.loc = uu____7701;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____7717 =
            let uu____7724 = translate_expr env e1  in
            let uu____7725 = translate_expr env e2  in
            let uu____7726 = translate_expr env e3  in
            (uu____7724, uu____7725, uu____7726)  in
          EBufFill uu____7717
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7728;
             FStar_Extraction_ML_Syntax.loc = uu____7729;_},uu____7730::[])
          when
          let uu____7733 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7733 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7738;
                  FStar_Extraction_ML_Syntax.loc = uu____7739;_},uu____7740);
             FStar_Extraction_ML_Syntax.mlty = uu____7741;
             FStar_Extraction_ML_Syntax.loc = uu____7742;_},_ebuf::_eseq::[])
          when
          (((let uu____7753 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7753 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____7758 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7758 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____7763 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7763 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____7768 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7768 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7773;
                  FStar_Extraction_ML_Syntax.loc = uu____7774;_},uu____7775);
             FStar_Extraction_ML_Syntax.mlty = uu____7776;
             FStar_Extraction_ML_Syntax.loc = uu____7777;_},e1::[])
          when
          ((((let uu____7787 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7787 = "LowStar.ConstBuffer.of_buffer") ||
               (let uu____7792 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____7792 = "LowStar.ConstBuffer.of_ibuffer"))
              ||
              (let uu____7797 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7797 = "LowStar.ConstBuffer.cast"))
             ||
             (let uu____7802 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7802 = "LowStar.ConstBuffer.to_buffer"))
            ||
            (let uu____7807 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7807 = "LowStar.ConstBuffer.to_ibuffer")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7812;
             FStar_Extraction_ML_Syntax.loc = uu____7813;_},e1::[])
          when
          let uu____7817 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7817 = "Obj.repr" ->
          let uu____7821 =
            let uu____7826 = translate_expr env e1  in (uu____7826, TAny)  in
          ECast uu____7821
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7829;
             FStar_Extraction_ML_Syntax.loc = uu____7830;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____7846 = FStar_Util.must (mk_width m)  in
          let uu____7847 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____7846 uu____7847 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7849;
             FStar_Extraction_ML_Syntax.loc = uu____7850;_},args)
          when is_bool_op op ->
          let uu____7864 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____7864 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7866;
             FStar_Extraction_ML_Syntax.loc = uu____7867;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7869;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7870;_}::[])
          when is_machine_int m ->
          let uu____7895 =
            let uu____7901 = FStar_Util.must (mk_width m)  in (uu____7901, c)
             in
          EConstant uu____7895
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7904;
             FStar_Extraction_ML_Syntax.loc = uu____7905;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7907;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7908;_}::[])
          when is_machine_int m ->
          let uu____7933 =
            let uu____7939 = FStar_Util.must (mk_width m)  in (uu____7939, c)
             in
          EConstant uu____7933
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7941;
             FStar_Extraction_ML_Syntax.loc = uu____7942;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7944;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7945;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7958 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7960;
             FStar_Extraction_ML_Syntax.loc = uu____7961;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7963;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7964;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7981 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7983;
             FStar_Extraction_ML_Syntax.loc = uu____7984;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7986;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7987;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8002 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[],"buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8004;
             FStar_Extraction_ML_Syntax.loc = uu____8005;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8007;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8008;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____8023 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____8026;
             FStar_Extraction_ML_Syntax.loc = uu____8027;_},arg::[])
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
            let uu____8055 =
              let uu____8060 = translate_expr env arg  in
              (uu____8060, (TInt UInt64))  in
            ECast uu____8055
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____8065 =
                 let uu____8070 = translate_expr env arg  in
                 (uu____8070, (TInt UInt32))  in
               ECast uu____8065)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____8075 =
                   let uu____8080 = translate_expr env arg  in
                   (uu____8080, (TInt UInt16))  in
                 ECast uu____8075)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____8085 =
                     let uu____8090 = translate_expr env arg  in
                     (uu____8090, (TInt UInt8))  in
                   ECast uu____8085)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____8095 =
                       let uu____8100 = translate_expr env arg  in
                       (uu____8100, (TInt Int64))  in
                     ECast uu____8095)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____8105 =
                         let uu____8110 = translate_expr env arg  in
                         (uu____8110, (TInt Int32))  in
                       ECast uu____8105)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____8115 =
                           let uu____8120 = translate_expr env arg  in
                           (uu____8120, (TInt Int16))  in
                         ECast uu____8115)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____8125 =
                             let uu____8130 = translate_expr env arg  in
                             (uu____8130, (TInt Int8))  in
                           ECast uu____8125)
                        else
                          (let uu____8133 =
                             let uu____8140 =
                               let uu____8143 = translate_expr env arg  in
                               [uu____8143]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____8140)
                              in
                           EApp uu____8133)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____8163 =
            let uu____8170 = translate_expr env head1  in
            let uu____8171 = FStar_List.map (translate_expr env) args  in
            (uu____8170, uu____8171)  in
          EApp uu____8163
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____8182 =
            let uu____8189 = translate_expr env head1  in
            let uu____8190 = FStar_List.map (translate_type env) ty_args  in
            (uu____8189, uu____8190)  in
          ETypApp uu____8182
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____8198 =
            let uu____8203 = translate_expr env e1  in
            let uu____8204 = translate_type env t_to  in
            (uu____8203, uu____8204)  in
          ECast uu____8198
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____8205,fields) ->
          let uu____8227 =
            let uu____8239 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8240 =
              FStar_List.map
                (fun uu____8262  ->
                   match uu____8262 with
                   | (field,expr) ->
                       let uu____8277 = translate_expr env expr  in
                       (field, uu____8277)) fields
               in
            (uu____8239, uu____8240)  in
          EFlat uu____8227
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____8288 =
            let uu____8296 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____8297 = translate_expr env e1  in
            (uu____8296, uu____8297, (FStar_Pervasives_Native.snd path))  in
          EField uu____8288
      | FStar_Extraction_ML_Syntax.MLE_Let uu____8303 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____8316) ->
          let uu____8321 =
            let uu____8323 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____8323
             in
          failwith uu____8321
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____8335 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____8335
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____8341 = FStar_List.map (translate_expr env) es  in
          ETuple uu____8341
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____8344,cons1),es) ->
          let uu____8359 =
            let uu____8369 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8370 = FStar_List.map (translate_expr env) es  in
            (uu____8369, cons1, uu____8370)  in
          ECons uu____8359
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____8396 =
            let uu____8405 = translate_expr env1 body  in
            let uu____8406 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____8405, uu____8406)  in
          EFun uu____8396
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____8416 =
            let uu____8423 = translate_expr env e1  in
            let uu____8424 = translate_expr env e2  in
            let uu____8425 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____8423, uu____8424, uu____8425)  in
          EIfThenElse uu____8416
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____8427 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____8435 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____8451 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > Prims.int_zero
          then
            let uu____8469 =
              let uu____8484 = FStar_List.map (translate_type env) ts  in
              (lid, uu____8484)  in
            TApp uu____8469
          else TQualified lid
      | uu____8499 ->
          let uu____8500 =
            let uu____8502 =
              FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
            FStar_Util.format1
              "invalid argument: expected MLTY_Named, got %s" uu____8502
             in
          failwith uu____8500

and (translate_branches :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr
      FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr)
      Prims.list -> (pattern * expr) Prims.list)
  =
  fun env  -> fun branches  -> FStar_List.map (translate_branch env) branches

and (translate_branch :
  env ->
    (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr
      FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr) ->
      (pattern * expr))
  =
  fun env  ->
    fun uu____8536  ->
      match uu____8536 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____8563 = translate_pat env pat  in
            (match uu____8563 with
             | (env1,pat1) ->
                 let uu____8574 = translate_expr env1 expr  in
                 (pat1, uu____8574))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___7_8582  ->
    match uu___7_8582 with
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
  env -> FStar_Extraction_ML_Syntax.mlpattern -> (env * pattern)) =
  fun env  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Unit ) -> (env, PUnit)
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Bool b) -> (env, (PBool b))
      | FStar_Extraction_ML_Syntax.MLP_Const
          (FStar_Extraction_ML_Syntax.MLC_Int (s,sw)) ->
          let uu____8649 =
            let uu____8650 =
              let uu____8656 = translate_width sw  in (uu____8656, s)  in
            PConstant uu____8650  in
          (env, uu____8649)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____8666,cons1),ps) ->
          let uu____8681 =
            FStar_List.fold_left
              (fun uu____8701  ->
                 fun p1  ->
                   match uu____8701 with
                   | (env1,acc) ->
                       let uu____8721 = translate_pat env1 p1  in
                       (match uu____8721 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8681 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____8751,ps) ->
          let uu____8773 =
            FStar_List.fold_left
              (fun uu____8810  ->
                 fun uu____8811  ->
                   match (uu____8810, uu____8811) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____8891 = translate_pat env1 p1  in
                       (match uu____8891 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____8773 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____8962 =
            FStar_List.fold_left
              (fun uu____8982  ->
                 fun p1  ->
                   match uu____8982 with
                   | (env1,acc) ->
                       let uu____9002 = translate_pat env1 p1  in
                       (match uu____9002 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8962 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____9029 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____9035 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____9049 =
            let uu____9051 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____9051
              (FStar_Util.for_some
                 (fun c1  -> c1 = (FStar_Char.char_of_int Prims.int_zero)))
             in
          if uu____9049
          then
            let uu____9066 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____9066
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____9093) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____9111 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____9113 ->
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
          let uu____9137 =
            let uu____9144 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____9144)  in
          EApp uu____9137
