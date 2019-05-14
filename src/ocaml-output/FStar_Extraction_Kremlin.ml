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
    match projectee with | DGlobal _0 -> true | uu____753 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____867 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____1001 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____1108 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DUnusedRetainedForBackwardsCompat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DUnusedRetainedForBackwardsCompat _0 -> true
    | uu____1240 -> false
  
let (__proj__DUnusedRetainedForBackwardsCompat__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  =
  fun projectee  ->
    match projectee with | DUnusedRetainedForBackwardsCompat _0 -> _0
  
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____1357 -> false
  
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
    | uu____1498 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____1566 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ * Prims.string Prims.list))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1659 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1670 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1681 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1692 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1703 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1714 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1725 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1736 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1749 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1770 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1783 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1806 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1829 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____1850 -> false
  
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | IfDef  -> true | uu____1861 -> false
  
let (uu___is_Macro : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Macro  -> true | uu____1872 -> false
  
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1883 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1894 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1905 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1918 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1948 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1996 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____2029 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____2047 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____2090 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____2136 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____2188 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____2227 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____2256 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____2293 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____2334 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____2371 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____2412 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____2453 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____2512 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____2565 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____2600 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____2630 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____2641 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____2654 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____2675 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____2686 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____2698 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____2728 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____2787 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____2831 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____2868 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2907 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2941 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2993 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____3031 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____3064 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____3117 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____3139 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____3162 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____3192 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____3203 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____3214 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____3225 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____3236 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____3247 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____3258 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____3269 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____3280 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____3291 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____3302 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____3313 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____3324 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____3335 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____3346 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____3357 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____3368 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____3379 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____3390 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____3401 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____3412 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____3423 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____3434 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____3445 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____3456 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____3467 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____3480 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____3505 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____3546 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____3588 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____3620 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____3665 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____3698 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____3709 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____3720 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____3731 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____3742 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____3753 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____3764 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____3775 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____3786 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____3797 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____3864 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____3883 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____3901 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____3921 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____3963 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____3974 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____3990 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____4022 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____4058 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____4121 -> false
  
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
let (current_version : version) = (Prims.parse_int "27") 
type file = (Prims.string * program)
type binary_format = (version * file Prims.list)
let fst3 :
  'Auu____4222 'Auu____4223 'Auu____4224 .
    ('Auu____4222 * 'Auu____4223 * 'Auu____4224) -> 'Auu____4222
  = fun uu____4235  -> match uu____4235 with | (x,uu____4243,uu____4244) -> x 
let snd3 :
  'Auu____4254 'Auu____4255 'Auu____4256 .
    ('Auu____4254 * 'Auu____4255 * 'Auu____4256) -> 'Auu____4255
  = fun uu____4267  -> match uu____4267 with | (uu____4274,x,uu____4276) -> x 
let thd3 :
  'Auu____4286 'Auu____4287 'Auu____4288 .
    ('Auu____4286 * 'Auu____4287 * 'Auu____4288) -> 'Auu____4288
  = fun uu____4299  -> match uu____4299 with | (uu____4306,uu____4307,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___0_4317  ->
    match uu___0_4317 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____4329 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___1_4339  ->
    match uu___1_4339 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____4348 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___2_4369  ->
    match uu___2_4369 with
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
    | uu____4414 -> FStar_Pervasives_Native.None
  
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
      let uu___163_4633 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___163_4633.names_t);
        module_name = (uu___163_4633.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___167_4669 = env  in
      {
        names = (uu___167_4669.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___167_4669.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____4697 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____4697 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___178_4735  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___177_4744 ->
          let uu____4746 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4746
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___187_4772  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___186_4781 ->
          let uu____4783 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4783
  
let add_binders :
  'Auu____4794 . env -> (Prims.string * 'Auu____4794) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____4841  ->
             match uu____4841 with | (name,uu____4854) -> extend env1 name)
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
      | uu____4963 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____5259  ->
    match uu____5259 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____5312 = m  in
               match uu____5312 with
               | (path,uu____5328,uu____5329) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___229_5349  ->
                  match () with
                  | () ->
                      ((let uu____5353 =
                          let uu____5355 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____5355  in
                        if uu____5353
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____5361 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____5361))) ()
             with
             | e ->
                 ((let uu____5370 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____5370);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____5373  ->
    match uu____5373 with
    | (module_name,modul,uu____5389) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____5426 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___3_5440  ->
         match uu___3_5440 with
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
         | uu____5451 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____5455 =
      FStar_List.choose
        (fun uu___4_5462  ->
           match uu___4_5462 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____5469 -> FStar_Pervasives_Native.None) flags
       in
    match uu____5455 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____5482 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____5517 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____5519 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____5527) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5563;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5566;_} when
            FStar_Util.for_some
              (fun uu___5_5574  ->
                 match uu___5_5574 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____5577 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            let arg_names =
              match e.FStar_Extraction_ML_Syntax.expr with
              | FStar_Extraction_ML_Syntax.MLE_Fun (args,uu____5600) ->
                  FStar_List.map FStar_Pervasives_Native.fst args
              | uu____5628 -> []  in
            if (FStar_List.length tvars) = (Prims.parse_int "0")
            then
              let uu____5636 =
                let uu____5637 =
                  let uu____5663 = translate_cc meta  in
                  let uu____5666 = translate_flags meta  in
                  let uu____5669 = translate_type env t0  in
                  (uu____5663, uu____5666, name1, uu____5669, arg_names)  in
                DExternal uu____5637  in
              FStar_Pervasives_Native.Some uu____5636
            else
              ((let uu____5688 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____5688);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5694;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____5697;
                FStar_Extraction_ML_Syntax.loc = uu____5698;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5700;_} ->
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
               let rec find_return_type eff i uu___6_5784 =
                 match uu___6_5784 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5793,eff1,t)
                     when i > (Prims.parse_int "0") ->
                     find_return_type eff1 (i - (Prims.parse_int "1")) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____5813 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____5813 with
               | (i,eff,t) ->
                   (if i > (Prims.parse_int "0")
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____5839 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____5839 msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5866) ->
                           let uu____5867 = translate_flags meta  in
                           MustDisappear :: uu____5867
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____5870 = translate_flags meta  in
                           MustDisappear :: uu____5870
                       | uu____5873 -> translate_flags meta  in
                     try
                       (fun uu___375_5882  ->
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
                         ((let uu____5917 =
                             let uu____5923 =
                               let uu____5925 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____5925 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____5923)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____5917);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5954;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5957;_} ->
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
                 (fun uu___402_6009  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____6033 =
                       let uu____6039 =
                         let uu____6041 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____6043 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____6041
                           uu____6043
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____6039)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____6033);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____6061;
            FStar_Extraction_ML_Syntax.mllb_def = uu____6062;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____6063;
            FStar_Extraction_ML_Syntax.print_typ = uu____6064;_} ->
            ((let uu____6074 =
                let uu____6080 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____6080)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____6074);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____6087 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____6087
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____6104 = ty  in
      match uu____6104 with
      | (uu____6107,uu____6108,uu____6109,uu____6110,flags,uu____6112) ->
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
                     (let uu____6198 =
                        let uu____6199 =
                          let uu____6219 = translate_flags flags1  in
                          let uu____6222 = translate_type env1 t  in
                          (name1, uu____6219, (FStar_List.length args),
                            uu____6222)
                           in
                        DTypeAlias uu____6199  in
                      FStar_Pervasives_Native.Some uu____6198)
             | (uu____6235,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____6292 =
                   let uu____6293 =
                     let uu____6325 = translate_flags flags1  in
                     let uu____6328 =
                       FStar_List.map
                         (fun uu____6360  ->
                            match uu____6360 with
                            | (f,t) ->
                                let uu____6380 =
                                  let uu____6386 = translate_type env1 t  in
                                  (uu____6386, false)  in
                                (f, uu____6380)) fields
                        in
                     (name1, uu____6325, (FStar_List.length args),
                       uu____6328)
                      in
                   DTypeFlat uu____6293  in
                 FStar_Pervasives_Native.Some uu____6292
             | (uu____6419,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____6478 =
                   let uu____6479 =
                     let uu____6518 =
                       FStar_List.map
                         (fun uu____6571  ->
                            match uu____6571 with
                            | (cons1,ts) ->
                                let uu____6619 =
                                  FStar_List.map
                                    (fun uu____6651  ->
                                       match uu____6651 with
                                       | (name2,t) ->
                                           let uu____6671 =
                                             let uu____6677 =
                                               translate_type env1 t  in
                                             (uu____6677, false)  in
                                           (name2, uu____6671)) ts
                                   in
                                (cons1, uu____6619)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____6518)
                      in
                   DTypeVariant uu____6479  in
                 FStar_Pervasives_Native.Some uu____6478
             | (uu____6730,name,_mangled_name,uu____6733,uu____6734,uu____6735)
                 ->
                 ((let uu____6751 =
                     let uu____6757 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____6757)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____6751);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____6768 = find_t env name  in TBound uu____6768
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____6771,t2) ->
          let uu____6773 =
            let uu____6778 = translate_type env t1  in
            let uu____6779 = translate_type env t2  in
            (uu____6778, uu____6779)  in
          TArrow uu____6773
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6783 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6783 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6790 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6790 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____6807 = FStar_Util.must (mk_width m)  in TInt uu____6807
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____6821 = FStar_Util.must (mk_width m)  in TInt uu____6821
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6826 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6826 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____6830::arg::uu____6832::[],p) when
          (((let uu____6838 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6838 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____6843 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6843 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____6848 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6848 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____6853 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6853 = "FStar.HyperStack.ST.s_mref")
          -> let uu____6857 = translate_type env arg  in TBuf uu____6857
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____6859::[],p) when
          ((((((((((let uu____6865 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6865 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____6870 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6870 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____6875 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6875 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____6880 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6880 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____6885 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6885 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____6890 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6890 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____6895 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6895 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____6900 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6900 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____6905 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6905 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____6910 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6910 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____6915 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6915 = "FStar.HyperStack.ST.mmmref")
          -> let uu____6919 = translate_type env arg  in TBuf uu____6919
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____6921::uu____6922::[],p) when
          let uu____6926 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6926 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____6930 = translate_type env arg  in TBuf uu____6930
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____6937 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6937 = "FStar.Buffer.buffer") ||
                        (let uu____6942 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____6942 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____6947 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____6947 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____6952 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6952 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____6957 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6957 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____6962 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6962 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____6967 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6967 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____6972 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6972 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____6977 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6977 = "FStar.HyperStack.mmref"))
                ||
                (let uu____6982 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6982 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____6987 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6987 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____6992 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6992 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____6997 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6997 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____7002 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7002 = "FStar.HyperStack.ST.mmref")
          -> let uu____7006 = translate_type env arg  in TBuf uu____7006
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____7007::arg::[],p) when
          (let uu____7014 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7014 = "FStar.HyperStack.s_ref") ||
            (let uu____7019 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7019 = "FStar.HyperStack.ST.s_ref")
          -> let uu____7023 = translate_type env arg  in TBuf uu____7023
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____7024::[],p) when
          let uu____7028 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7028 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____7080 = FStar_List.map (translate_type env) args  in
          TTuple uu____7080
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > (Prims.parse_int "0")
          then
            let uu____7091 =
              let uu____7106 = FStar_List.map (translate_type env) args  in
              (lid, uu____7106)  in
            TApp uu____7091
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____7124 = FStar_List.map (translate_type env) ts  in
          TTuple uu____7124

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
    fun uu____7148  ->
      match uu____7148 with
      | (name,typ) ->
          let uu____7164 = translate_type env typ  in
          { name; typ = uu____7164; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____7180 = find env name  in EBound uu____7180
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____7194 =
            let uu____7199 = FStar_Util.must (mk_op op)  in
            let uu____7200 = FStar_Util.must (mk_width m)  in
            (uu____7199, uu____7200)  in
          EOp uu____7194
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____7210 =
            let uu____7215 = FStar_Util.must (mk_bool_op op)  in
            (uu____7215, Bool)  in
          EOp uu____7210
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
            let uu____7277 = translate_type env typ  in
            { name; typ = uu____7277; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____7331 =
            let uu____7342 = translate_expr env expr  in
            let uu____7343 = translate_branches env branches  in
            (uu____7342, uu____7343)  in
          EMatch uu____7331
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7357;
                  FStar_Extraction_ML_Syntax.loc = uu____7358;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____7360;
             FStar_Extraction_ML_Syntax.loc = uu____7361;_},arg::[])
          when
          let uu____7385 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7385 = "FStar.Dyn.undyn" ->
          let uu____7389 =
            let uu____7394 = translate_expr env arg  in
            let uu____7395 = translate_type env t  in
            (uu____7394, uu____7395)  in
          ECast uu____7389
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7397;
                  FStar_Extraction_ML_Syntax.loc = uu____7398;_},uu____7399);
             FStar_Extraction_ML_Syntax.mlty = uu____7400;
             FStar_Extraction_ML_Syntax.loc = uu____7401;_},uu____7402)
          when
          let uu____7423 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7423 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7428;
                  FStar_Extraction_ML_Syntax.loc = uu____7429;_},uu____7430);
             FStar_Extraction_ML_Syntax.mlty = uu____7431;
             FStar_Extraction_ML_Syntax.loc = uu____7432;_},arg::[])
          when
          ((let uu____7460 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7460 = "FStar.HyperStack.All.failwith") ||
             (let uu____7465 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7465 = "FStar.Error.unexpected"))
            ||
            (let uu____7470 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7470 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____7475;
               FStar_Extraction_ML_Syntax.loc = uu____7476;_} -> EAbortS msg
           | uu____7478 ->
               let print7 =
                 let uu____7489 =
                   let uu____7490 =
                     let uu____7491 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____7491
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____7490  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____7489
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
                  FStar_Extraction_ML_Syntax.mlty = uu____7524;
                  FStar_Extraction_ML_Syntax.loc = uu____7525;_},uu____7526);
             FStar_Extraction_ML_Syntax.mlty = uu____7527;
             FStar_Extraction_ML_Syntax.loc = uu____7528;_},e1::[])
          when
          (let uu____7556 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7556 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____7561 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7561 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7566;
                  FStar_Extraction_ML_Syntax.loc = uu____7567;_},uu____7568);
             FStar_Extraction_ML_Syntax.mlty = uu____7569;
             FStar_Extraction_ML_Syntax.loc = uu____7570;_},e1::e2::[])
          when
          (((let uu____7605 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7605 = "FStar.Buffer.index") ||
              (let uu____7610 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7610 = "FStar.Buffer.op_Array_Access"))
             ||
             (let uu____7615 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7615 = "LowStar.Monotonic.Buffer.index"))
            ||
            (let uu____7620 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7620 = "LowStar.UninitializedBuffer.uindex")
          ->
          let uu____7624 =
            let uu____7629 = translate_expr env e1  in
            let uu____7630 = translate_expr env e2  in
            (uu____7629, uu____7630)  in
          EBufRead uu____7624
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7632;
                  FStar_Extraction_ML_Syntax.loc = uu____7633;_},uu____7634);
             FStar_Extraction_ML_Syntax.mlty = uu____7635;
             FStar_Extraction_ML_Syntax.loc = uu____7636;_},e1::[])
          when
          let uu____7662 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7662 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____7666 =
            let uu____7671 = translate_expr env e1  in
            (uu____7671, (EConstant (UInt32, "0")))  in
          EBufRead uu____7666
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7675;
                  FStar_Extraction_ML_Syntax.loc = uu____7676;_},uu____7677);
             FStar_Extraction_ML_Syntax.mlty = uu____7678;
             FStar_Extraction_ML_Syntax.loc = uu____7679;_},e1::e2::[])
          when
          ((let uu____7714 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7714 = "FStar.Buffer.create") ||
             (let uu____7719 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7719 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____7724 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7724 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____7728 =
            let uu____7735 = translate_expr env e1  in
            let uu____7736 = translate_expr env e2  in
            (Stack, uu____7735, uu____7736)  in
          EBufCreate uu____7728
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
             FStar_Extraction_ML_Syntax.loc = uu____7742;_},elen::[])
          when
          let uu____7768 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7768 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____7772 =
            let uu____7777 = translate_expr env elen  in (Stack, uu____7777)
             in
          EBufCreateNoInit uu____7772
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7779;
                  FStar_Extraction_ML_Syntax.loc = uu____7780;_},uu____7781);
             FStar_Extraction_ML_Syntax.mlty = uu____7782;
             FStar_Extraction_ML_Syntax.loc = uu____7783;_},init1::[])
          when
          let uu____7809 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7809 = "FStar.HyperStack.ST.salloc" ->
          let uu____7813 =
            let uu____7820 = translate_expr env init1  in
            (Stack, uu____7820, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7813
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7824;
                  FStar_Extraction_ML_Syntax.loc = uu____7825;_},uu____7826);
             FStar_Extraction_ML_Syntax.mlty = uu____7827;
             FStar_Extraction_ML_Syntax.loc = uu____7828;_},e2::[])
          when
          ((let uu____7856 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7856 = "FStar.Buffer.createL") ||
             (let uu____7861 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7861 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____7866 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7866 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____7870 =
            let uu____7877 =
              let uu____7880 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7880  in
            (Stack, uu____7877)  in
          EBufCreateL uu____7870
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7892;
                  FStar_Extraction_ML_Syntax.loc = uu____7893;_},uu____7894);
             FStar_Extraction_ML_Syntax.mlty = uu____7895;
             FStar_Extraction_ML_Syntax.loc = uu____7896;_},_erid::e2::[])
          when
          (let uu____7931 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7931 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____7936 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7936 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____7940 =
            let uu____7947 =
              let uu____7950 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7950  in
            (Eternal, uu____7947)  in
          EBufCreateL uu____7940
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7962;
                  FStar_Extraction_ML_Syntax.loc = uu____7963;_},uu____7964);
             FStar_Extraction_ML_Syntax.mlty = uu____7965;
             FStar_Extraction_ML_Syntax.loc = uu____7966;_},_rid::init1::[])
          when
          let uu____7999 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7999 = "FStar.HyperStack.ST.ralloc" ->
          let uu____8003 =
            let uu____8010 = translate_expr env init1  in
            (Eternal, uu____8010, (EConstant (UInt32, "1")))  in
          EBufCreate uu____8003
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8014;
                  FStar_Extraction_ML_Syntax.loc = uu____8015;_},uu____8016);
             FStar_Extraction_ML_Syntax.mlty = uu____8017;
             FStar_Extraction_ML_Syntax.loc = uu____8018;_},_e0::e1::e2::[])
          when
          ((let uu____8060 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____8060 = "FStar.Buffer.rcreate") ||
             (let uu____8065 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____8065 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____8070 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____8070 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____8074 =
            let uu____8081 = translate_expr env e1  in
            let uu____8082 = translate_expr env e2  in
            (Eternal, uu____8081, uu____8082)  in
          EBufCreate uu____8074
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8084;
                  FStar_Extraction_ML_Syntax.loc = uu____8085;_},uu____8086);
             FStar_Extraction_ML_Syntax.mlty = uu____8087;
             FStar_Extraction_ML_Syntax.loc = uu____8088;_},_erid::elen::[])
          when
          let uu____8121 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8121 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____8125 =
            let uu____8130 = translate_expr env elen  in
            (Eternal, uu____8130)  in
          EBufCreateNoInit uu____8125
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8132;
                  FStar_Extraction_ML_Syntax.loc = uu____8133;_},uu____8134);
             FStar_Extraction_ML_Syntax.mlty = uu____8135;
             FStar_Extraction_ML_Syntax.loc = uu____8136;_},_rid::init1::[])
          when
          let uu____8169 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8169 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____8173 =
            let uu____8180 = translate_expr env init1  in
            (ManuallyManaged, uu____8180, (EConstant (UInt32, "1")))  in
          EBufCreate uu____8173
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8184;
                  FStar_Extraction_ML_Syntax.loc = uu____8185;_},uu____8186);
             FStar_Extraction_ML_Syntax.mlty = uu____8187;
             FStar_Extraction_ML_Syntax.loc = uu____8188;_},_e0::e1::e2::[])
          when
          (((let uu____8230 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____8230 = "FStar.Buffer.rcreate_mm") ||
              (let uu____8235 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____8235 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____8240 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____8240 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____8245 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____8245 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____8249 =
            let uu____8256 = translate_expr env e1  in
            let uu____8257 = translate_expr env e2  in
            (ManuallyManaged, uu____8256, uu____8257)  in
          EBufCreate uu____8249
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8259;
                  FStar_Extraction_ML_Syntax.loc = uu____8260;_},uu____8261);
             FStar_Extraction_ML_Syntax.mlty = uu____8262;
             FStar_Extraction_ML_Syntax.loc = uu____8263;_},_erid::elen::[])
          when
          let uu____8296 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8296 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____8300 =
            let uu____8305 = translate_expr env elen  in
            (ManuallyManaged, uu____8305)  in
          EBufCreateNoInit uu____8300
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8307;
                  FStar_Extraction_ML_Syntax.loc = uu____8308;_},uu____8309);
             FStar_Extraction_ML_Syntax.mlty = uu____8310;
             FStar_Extraction_ML_Syntax.loc = uu____8311;_},e2::[])
          when
          let uu____8337 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8337 = "FStar.HyperStack.ST.rfree" ->
          let uu____8341 = translate_expr env e2  in EBufFree uu____8341
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8343;
                  FStar_Extraction_ML_Syntax.loc = uu____8344;_},uu____8345);
             FStar_Extraction_ML_Syntax.mlty = uu____8346;
             FStar_Extraction_ML_Syntax.loc = uu____8347;_},e2::[])
          when
          (let uu____8375 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____8375 = "FStar.Buffer.rfree") ||
            (let uu____8380 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____8380 = "LowStar.Monotonic.Buffer.free")
          -> let uu____8384 = translate_expr env e2  in EBufFree uu____8384
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8386;
                  FStar_Extraction_ML_Syntax.loc = uu____8387;_},uu____8388);
             FStar_Extraction_ML_Syntax.mlty = uu____8389;
             FStar_Extraction_ML_Syntax.loc = uu____8390;_},e1::e2::_e3::[])
          when
          let uu____8430 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8430 = "FStar.Buffer.sub" ->
          let uu____8434 =
            let uu____8439 = translate_expr env e1  in
            let uu____8440 = translate_expr env e2  in
            (uu____8439, uu____8440)  in
          EBufSub uu____8434
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8442;
                  FStar_Extraction_ML_Syntax.loc = uu____8443;_},uu____8444);
             FStar_Extraction_ML_Syntax.mlty = uu____8445;
             FStar_Extraction_ML_Syntax.loc = uu____8446;_},e1::e2::_e3::[])
          when
          let uu____8486 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8486 = "LowStar.Monotonic.Buffer.msub" ->
          let uu____8490 =
            let uu____8495 = translate_expr env e1  in
            let uu____8496 = translate_expr env e2  in
            (uu____8495, uu____8496)  in
          EBufSub uu____8490
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8498;
                  FStar_Extraction_ML_Syntax.loc = uu____8499;_},uu____8500);
             FStar_Extraction_ML_Syntax.mlty = uu____8501;
             FStar_Extraction_ML_Syntax.loc = uu____8502;_},e1::e2::[])
          when
          let uu____8535 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8535 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8540;
                  FStar_Extraction_ML_Syntax.loc = uu____8541;_},uu____8542);
             FStar_Extraction_ML_Syntax.mlty = uu____8543;
             FStar_Extraction_ML_Syntax.loc = uu____8544;_},e1::e2::[])
          when
          let uu____8577 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8577 = "FStar.Buffer.offset" ->
          let uu____8581 =
            let uu____8586 = translate_expr env e1  in
            let uu____8587 = translate_expr env e2  in
            (uu____8586, uu____8587)  in
          EBufSub uu____8581
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8589;
                  FStar_Extraction_ML_Syntax.loc = uu____8590;_},uu____8591);
             FStar_Extraction_ML_Syntax.mlty = uu____8592;
             FStar_Extraction_ML_Syntax.loc = uu____8593;_},e1::e2::[])
          when
          let uu____8626 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8626 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____8630 =
            let uu____8635 = translate_expr env e1  in
            let uu____8636 = translate_expr env e2  in
            (uu____8635, uu____8636)  in
          EBufSub uu____8630
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8638;
                  FStar_Extraction_ML_Syntax.loc = uu____8639;_},uu____8640);
             FStar_Extraction_ML_Syntax.mlty = uu____8641;
             FStar_Extraction_ML_Syntax.loc = uu____8642;_},e1::e2::e3::[])
          when
          (((let uu____8684 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____8684 = "FStar.Buffer.upd") ||
              (let uu____8689 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____8689 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____8694 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____8694 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____8699 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____8699 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____8703 =
            let uu____8710 = translate_expr env e1  in
            let uu____8711 = translate_expr env e2  in
            let uu____8712 = translate_expr env e3  in
            (uu____8710, uu____8711, uu____8712)  in
          EBufWrite uu____8703
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8714;
                  FStar_Extraction_ML_Syntax.loc = uu____8715;_},uu____8716);
             FStar_Extraction_ML_Syntax.mlty = uu____8717;
             FStar_Extraction_ML_Syntax.loc = uu____8718;_},e1::e2::[])
          when
          let uu____8751 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8751 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____8755 =
            let uu____8762 = translate_expr env e1  in
            let uu____8763 = translate_expr env e2  in
            (uu____8762, (EConstant (UInt32, "0")), uu____8763)  in
          EBufWrite uu____8755
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____8767;
             FStar_Extraction_ML_Syntax.loc = uu____8768;_},uu____8769::[])
          when
          let uu____8787 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8787 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____8792;
             FStar_Extraction_ML_Syntax.loc = uu____8793;_},uu____8794::[])
          when
          let uu____8812 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8812 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8817;
                  FStar_Extraction_ML_Syntax.loc = uu____8818;_},uu____8819);
             FStar_Extraction_ML_Syntax.mlty = uu____8820;
             FStar_Extraction_ML_Syntax.loc = uu____8821;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____8877 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____8877 = "FStar.Buffer.blit") ||
             (let uu____8882 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____8882 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____8887 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____8887 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____8891 =
            let uu____8902 = translate_expr env e1  in
            let uu____8903 = translate_expr env e2  in
            let uu____8904 = translate_expr env e3  in
            let uu____8905 = translate_expr env e4  in
            let uu____8906 = translate_expr env e5  in
            (uu____8902, uu____8903, uu____8904, uu____8905, uu____8906)  in
          EBufBlit uu____8891
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8908;
                  FStar_Extraction_ML_Syntax.loc = uu____8909;_},uu____8910);
             FStar_Extraction_ML_Syntax.mlty = uu____8911;
             FStar_Extraction_ML_Syntax.loc = uu____8912;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____8958 =
            let uu____8965 = translate_expr env e1  in
            let uu____8966 = translate_expr env e2  in
            let uu____8967 = translate_expr env e3  in
            (uu____8965, uu____8966, uu____8967)  in
          EBufFill uu____8958
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____8969;
             FStar_Extraction_ML_Syntax.loc = uu____8970;_},uu____8971::[])
          when
          let uu____8989 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8989 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8994;
                  FStar_Extraction_ML_Syntax.loc = uu____8995;_},uu____8996);
             FStar_Extraction_ML_Syntax.mlty = uu____8997;
             FStar_Extraction_ML_Syntax.loc = uu____8998;_},_ebuf::_eseq::[])
          when
          (((let uu____9033 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____9033 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____9038 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____9038 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____9043 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____9043 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____9048 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____9048 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____9053;
             FStar_Extraction_ML_Syntax.loc = uu____9054;_},e1::[])
          when
          let uu____9073 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____9073 = "Obj.repr" ->
          let uu____9077 =
            let uu____9082 = translate_expr env e1  in (uu____9082, TAny)  in
          ECast uu____9077
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____9085;
             FStar_Extraction_ML_Syntax.loc = uu____9086;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____9111 = FStar_Util.must (mk_width m)  in
          let uu____9112 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____9111 uu____9112 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____9114;
             FStar_Extraction_ML_Syntax.loc = uu____9115;_},args)
          when is_bool_op op ->
          let uu____9138 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____9138 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____9140;
             FStar_Extraction_ML_Syntax.loc = uu____9141;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____9143;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____9144;_}::[])
          when is_machine_int m ->
          let uu____9181 =
            let uu____9187 = FStar_Util.must (mk_width m)  in (uu____9187, c)
             in
          EConstant uu____9181
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____9190;
             FStar_Extraction_ML_Syntax.loc = uu____9191;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____9193;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____9194;_}::[])
          when is_machine_int m ->
          let uu____9231 =
            let uu____9237 = FStar_Util.must (mk_width m)  in (uu____9237, c)
             in
          EConstant uu____9231
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____9239;
             FStar_Extraction_ML_Syntax.loc = uu____9240;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____9242;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____9243;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____9268 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____9270;
             FStar_Extraction_ML_Syntax.loc = uu____9271;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____9273;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____9274;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____9303 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____9305;
             FStar_Extraction_ML_Syntax.loc = uu____9306;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____9308;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____9309;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____9336 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[],"buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____9338;
             FStar_Extraction_ML_Syntax.loc = uu____9339;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____9341;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____9342;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____9369 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____9372;
             FStar_Extraction_ML_Syntax.loc = uu____9373;_},arg::[])
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
            let uu____9416 =
              let uu____9421 = translate_expr env arg  in
              (uu____9421, (TInt UInt64))  in
            ECast uu____9416
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____9426 =
                 let uu____9431 = translate_expr env arg  in
                 (uu____9431, (TInt UInt32))  in
               ECast uu____9426)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____9436 =
                   let uu____9441 = translate_expr env arg  in
                   (uu____9441, (TInt UInt16))  in
                 ECast uu____9436)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____9446 =
                     let uu____9451 = translate_expr env arg  in
                     (uu____9451, (TInt UInt8))  in
                   ECast uu____9446)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____9456 =
                       let uu____9461 = translate_expr env arg  in
                       (uu____9461, (TInt Int64))  in
                     ECast uu____9456)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____9466 =
                         let uu____9471 = translate_expr env arg  in
                         (uu____9471, (TInt Int32))  in
                       ECast uu____9466)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____9476 =
                           let uu____9481 = translate_expr env arg  in
                           (uu____9481, (TInt Int16))  in
                         ECast uu____9476)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____9486 =
                             let uu____9491 = translate_expr env arg  in
                             (uu____9491, (TInt Int8))  in
                           ECast uu____9486)
                        else
                          (let uu____9494 =
                             let uu____9501 =
                               let uu____9504 = translate_expr env arg  in
                               [uu____9504]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____9501)
                              in
                           EApp uu____9494)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____9536 =
            let uu____9543 = translate_expr env head1  in
            let uu____9544 = FStar_List.map (translate_expr env) args  in
            (uu____9543, uu____9544)  in
          EApp uu____9536
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____9564 =
            let uu____9571 = translate_expr env head1  in
            let uu____9572 = FStar_List.map (translate_type env) ty_args  in
            (uu____9571, uu____9572)  in
          ETypApp uu____9564
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____9586 =
            let uu____9591 = translate_expr env e1  in
            let uu____9592 = translate_type env t_to  in
            (uu____9591, uu____9592)  in
          ECast uu____9586
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____9593,fields) ->
          let uu____9621 =
            let uu____9633 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____9634 =
              FStar_List.map
                (fun uu____9659  ->
                   match uu____9659 with
                   | (field,expr) ->
                       let uu____9683 = translate_expr env expr  in
                       (field, uu____9683)) fields
               in
            (uu____9633, uu____9634)  in
          EFlat uu____9621
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____9700 =
            let uu____9708 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____9709 = translate_expr env e1  in
            (uu____9708, uu____9709, (FStar_Pervasives_Native.snd path))  in
          EField uu____9700
      | FStar_Extraction_ML_Syntax.MLE_Let uu____9715 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____9737) ->
          let uu____9754 =
            let uu____9756 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____9756
             in
          failwith uu____9754
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____9771 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____9771
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____9783 = FStar_List.map (translate_expr env) es  in
          ETuple uu____9783
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____9789,cons1),es) ->
          let uu____9810 =
            let uu____9820 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____9821 = FStar_List.map (translate_expr env) es  in
            (uu____9820, cons1, uu____9821)  in
          ECons uu____9810
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____9865 =
            let uu____9877 = translate_expr env1 body  in
            let uu____9878 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____9877, uu____9878)  in
          EFun uu____9865
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____9909 =
            let uu____9916 = translate_expr env e1  in
            let uu____9917 = translate_expr env e2  in
            let uu____9918 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____9916, uu____9917, uu____9918)  in
          EIfThenElse uu____9909
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____9929 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____9940 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____9965 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > (Prims.parse_int "0")
          then
            let uu____9989 =
              let uu____10004 = FStar_List.map (translate_type env) ts  in
              (lid, uu____10004)  in
            TApp uu____9989
          else TQualified lid
      | uu____10019 ->
          let uu____10020 =
            let uu____10022 =
              FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
            FStar_Util.format1
              "invalid argument: expected MLTY_Named, got %s" uu____10022
             in
          failwith uu____10020

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
    fun uu____10071  ->
      match uu____10071 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____10125 = translate_pat env pat  in
            (match uu____10125 with
             | (env1,pat1) ->
                 let uu____10145 = translate_expr env1 expr  in
                 (pat1, uu____10145))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___7_10153  ->
    match uu___7_10153 with
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
          let uu____10232 =
            let uu____10233 =
              let uu____10239 = translate_width sw  in (uu____10239, s)  in
            PConstant uu____10233  in
          (env, uu____10232)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____10270,cons1),ps) ->
          let uu____10285 =
            FStar_List.fold_left
              (fun uu____10311  ->
                 fun p1  ->
                   match uu____10311 with
                   | (env1,acc) ->
                       let uu____10343 = translate_pat env1 p1  in
                       (match uu____10343 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____10285 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____10403,ps) ->
          let uu____10425 =
            FStar_List.fold_left
              (fun uu____10468  ->
                 fun uu____10469  ->
                   match (uu____10468, uu____10469) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____10567 = translate_pat env1 p1  in
                       (match uu____10567 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____10425 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____10668 =
            FStar_List.fold_left
              (fun uu____10694  ->
                 fun p1  ->
                   match uu____10694 with
                   | (env1,acc) ->
                       let uu____10726 = translate_pat env1 p1  in
                       (match uu____10726 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____10668 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____10783 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____10792 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____10809 =
            let uu____10811 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____10811
              (FStar_Util.for_some
                 (fun c1  ->
                    c1 = (FStar_Char.char_of_int (Prims.parse_int "0"))))
             in
          if uu____10809
          then
            let uu____10826 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____10826
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____10853) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____10871 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____10873 ->
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
          let uu____10903 =
            let uu____10910 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____10910)  in
          EApp uu____10903
