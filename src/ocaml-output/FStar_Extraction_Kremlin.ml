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
  fun projectee  ->
    match projectee with | DGlobal _0 -> true | uu____766 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____877 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____1002 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____1109 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DUnusedRetainedForBackwardsCompat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DUnusedRetainedForBackwardsCompat _0 -> true
    | uu____1241 -> false
  
let (__proj__DUnusedRetainedForBackwardsCompat__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  =
  fun projectee  ->
    match projectee with | DUnusedRetainedForBackwardsCompat _0 -> _0
  
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____1358 -> false
  
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
    | uu____1499 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____1567 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ * Prims.string Prims.list))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1660 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1671 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1682 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1693 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1704 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1715 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1726 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1737 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1750 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1771 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1784 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1807 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1830 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____1851 -> false
  
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | IfDef  -> true | uu____1862 -> false
  
let (uu___is_Macro : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Macro  -> true | uu____1873 -> false
  
let (uu___is_Deprecated : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Deprecated _0 -> true | uu____1886 -> false
  
let (__proj__Deprecated__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Deprecated _0 -> _0 
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1907 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1918 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1929 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1942 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1972 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____2020 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____2053 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____2071 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____2114 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____2157 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____2200 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____2239 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____2268 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____2305 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____2346 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____2383 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____2424 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____2465 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____2524 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____2577 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____2612 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____2642 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____2653 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____2666 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____2687 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____2698 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____2710 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____2740 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____2799 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____2843 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____2880 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2919 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2953 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____3005 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____3043 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____3073 -> false
  
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
let (uu___is_EAbortT : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortT _0 -> true | uu____3198 -> false
  
let (__proj__EAbortT__item___0 : expr -> (Prims.string * typ)) =
  fun projectee  -> match projectee with | EAbortT _0 -> _0 
let (uu___is_EComment : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EComment _0 -> true | uu____3240 -> false
  
let (__proj__EComment__item___0 :
  expr -> (Prims.string * expr * Prims.string)) =
  fun projectee  -> match projectee with | EComment _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____3282 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____3293 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____3304 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____3315 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____3326 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____3337 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____3348 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____3359 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____3370 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____3381 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____3392 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____3403 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____3414 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____3425 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____3436 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____3447 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____3458 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____3469 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____3480 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____3491 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____3502 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____3513 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____3524 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____3535 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____3546 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____3557 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____3570 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____3592 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____3618 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____3660 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____3692 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____3737 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____3770 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____3781 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____3792 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____3803 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____3814 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____3825 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____3836 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____3847 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____3858 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____3869 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____3918 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____3937 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____3955 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____3975 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____4017 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____4028 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____4044 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____4076 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____4112 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____4175 -> false
  
let (__proj__TTuple__item___0 : typ -> typ Prims.list) =
  fun projectee  -> match projectee with | TTuple _0 -> _0 
let (uu___is_TConstBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TConstBuf _0 -> true | uu____4200 -> false
  
let (__proj__TConstBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TConstBuf _0 -> _0 
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
  'Auu____4295 'Auu____4296 'Auu____4297 .
    ('Auu____4295 * 'Auu____4296 * 'Auu____4297) -> 'Auu____4295
  = fun uu____4308  -> match uu____4308 with | (x,uu____4316,uu____4317) -> x 
let snd3 :
  'Auu____4327 'Auu____4328 'Auu____4329 .
    ('Auu____4327 * 'Auu____4328 * 'Auu____4329) -> 'Auu____4328
  = fun uu____4340  -> match uu____4340 with | (uu____4347,x,uu____4349) -> x 
let thd3 :
  'Auu____4359 'Auu____4360 'Auu____4361 .
    ('Auu____4359 * 'Auu____4360 * 'Auu____4361) -> 'Auu____4361
  = fun uu____4372  -> match uu____4372 with | (uu____4379,uu____4380,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___0_4390  ->
    match uu___0_4390 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____4402 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___1_4412  ->
    match uu___1_4412 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____4421 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___2_4442  ->
    match uu___2_4442 with
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
    | uu____4487 -> FStar_Pervasives_Native.None
  
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
      let uu___167_4643 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___167_4643.names_t);
        module_name = (uu___167_4643.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___171_4657 = env  in
      {
        names = (uu___171_4657.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___171_4657.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____4672 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____4672 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___182_4696  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___181_4703 ->
          let uu____4705 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4705
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___191_4725  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___190_4734 ->
          let uu____4736 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4736
  
let add_binders :
  'Auu____4747 . env -> (Prims.string * 'Auu____4747) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____4782  ->
             match uu____4782 with | (name,uu____4789) -> extend env1 name)
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
      | uu____4841 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun m  ->
    let uu____5067 = m  in
    match uu____5067 with
    | (module_name,modul,uu____5082) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____5117 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___3_5131  ->
         match uu___3_5131 with
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
         | uu____5144 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____5148 =
      FStar_List.choose
        (fun uu___4_5155  ->
           match uu___4_5155 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____5162 -> FStar_Pervasives_Native.None) flags
       in
    match uu____5148 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____5175 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____5189 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____5191 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____5196) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5223;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5226;_} when
            FStar_Util.for_some
              (fun uu___5_5231  ->
                 match uu___5_5231 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____5234 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            let arg_names =
              match e.FStar_Extraction_ML_Syntax.expr with
              | FStar_Extraction_ML_Syntax.MLE_Fun (args,uu____5257) ->
                  FStar_List.map FStar_Pervasives_Native.fst args
              | uu____5279 -> []  in
            if (FStar_List.length tvars) = Prims.int_zero
            then
              let uu____5287 =
                let uu____5288 =
                  let uu____5314 = translate_cc meta  in
                  let uu____5317 = translate_flags meta  in
                  let uu____5320 = translate_type env t0  in
                  (uu____5314, uu____5317, name1, uu____5320, arg_names)  in
                DExternal uu____5288  in
              FStar_Pervasives_Native.Some uu____5287
            else
              ((let uu____5339 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____5339);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5345;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____5348;
                FStar_Extraction_ML_Syntax.loc = uu____5349;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5351;_} ->
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
               let rec find_return_type eff i uu___6_5408 =
                 match uu___6_5408 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5417,eff1,t)
                     when i > Prims.int_zero ->
                     find_return_type eff1 (i - Prims.int_one) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____5437 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____5437 with
               | (i,eff,t) ->
                   (if i > Prims.int_zero
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____5463 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____5463 msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5481) ->
                           let uu____5482 = translate_flags meta  in
                           MustDisappear :: uu____5482
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____5485 = translate_flags meta  in
                           MustDisappear :: uu____5485
                       | uu____5488 -> translate_flags meta  in
                     try
                       (fun uu___365_5497  ->
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
                         ((let uu____5529 =
                             let uu____5535 =
                               let uu____5537 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____5537 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____5535)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____5529);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5563;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5566;_} ->
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
                 (fun uu___392_5603  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____5627 =
                       let uu____5633 =
                         let uu____5635 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____5637 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____5635
                           uu____5637
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____5633)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____5627);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5655;
            FStar_Extraction_ML_Syntax.mllb_def = uu____5656;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____5657;
            FStar_Extraction_ML_Syntax.print_typ = uu____5658;_} ->
            ((let uu____5665 =
                let uu____5671 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____5671)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____5665);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____5678 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____5678
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____5692 = ty  in
      match uu____5692 with
      | (uu____5695,uu____5696,uu____5697,uu____5698,flags,uu____5700) ->
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
                     (let uu____5774 =
                        let uu____5775 =
                          let uu____5795 = translate_flags flags1  in
                          let uu____5798 = translate_type env1 t  in
                          (name1, uu____5795, (FStar_List.length args),
                            uu____5798)
                           in
                        DTypeAlias uu____5775  in
                      FStar_Pervasives_Native.Some uu____5774)
             | (uu____5811,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____5856 =
                   let uu____5857 =
                     let uu____5889 = translate_flags flags1  in
                     let uu____5892 =
                       FStar_List.map
                         (fun uu____5924  ->
                            match uu____5924 with
                            | (f,t) ->
                                let uu____5944 =
                                  let uu____5950 = translate_type env1 t  in
                                  (uu____5950, false)  in
                                (f, uu____5944)) fields
                        in
                     (name1, uu____5889, (FStar_List.length args),
                       uu____5892)
                      in
                   DTypeFlat uu____5857  in
                 FStar_Pervasives_Native.Some uu____5856
             | (uu____5983,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____6033 =
                   let uu____6034 =
                     let uu____6073 =
                       FStar_List.map
                         (fun uu____6126  ->
                            match uu____6126 with
                            | (cons1,ts) ->
                                let uu____6174 =
                                  FStar_List.map
                                    (fun uu____6206  ->
                                       match uu____6206 with
                                       | (name2,t) ->
                                           let uu____6226 =
                                             let uu____6232 =
                                               translate_type env1 t  in
                                             (uu____6232, false)  in
                                           (name2, uu____6226)) ts
                                   in
                                (cons1, uu____6174)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____6073)
                      in
                   DTypeVariant uu____6034  in
                 FStar_Pervasives_Native.Some uu____6033
             | (uu____6285,name,_mangled_name,uu____6288,uu____6289,uu____6290)
                 ->
                 ((let uu____6306 =
                     let uu____6312 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____6312)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____6306);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____6320 = find_t env name  in TBound uu____6320
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____6323,t2) ->
          let uu____6325 =
            let uu____6330 = translate_type env t1  in
            let uu____6331 = translate_type env t2  in
            (uu____6330, uu____6331)  in
          TArrow uu____6325
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6335 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6335 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6342 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6342 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____6359 = FStar_Util.must (mk_width m)  in TInt uu____6359
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____6373 = FStar_Util.must (mk_width m)  in TInt uu____6373
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6378 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6378 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____6382::arg::uu____6384::[],p) when
          (((let uu____6390 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6390 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____6395 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6395 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____6400 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6400 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____6405 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6405 = "FStar.HyperStack.ST.s_mref")
          -> let uu____6409 = translate_type env arg  in TBuf uu____6409
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____6411::[],p) when
          ((((((((((let uu____6417 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6417 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____6422 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6422 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____6427 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6427 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____6432 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6432 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____6437 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6437 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____6442 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6442 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____6447 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6447 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____6452 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6452 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____6457 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6457 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____6462 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6462 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____6467 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6467 = "FStar.HyperStack.ST.mmmref")
          -> let uu____6471 = translate_type env arg  in TBuf uu____6471
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____6473::uu____6474::[],p) when
          let uu____6478 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6478 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____6482 = translate_type env arg  in TBuf uu____6482
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6487 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6487 = "LowStar.ConstBuffer.const_buffer" ->
          let uu____6491 = translate_type env arg  in TConstBuf uu____6491
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____6498 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6498 = "FStar.Buffer.buffer") ||
                        (let uu____6503 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____6503 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____6508 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____6508 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____6513 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6513 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____6518 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6518 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____6523 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6523 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____6528 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6528 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____6533 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6533 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____6538 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6538 = "FStar.HyperStack.mmref"))
                ||
                (let uu____6543 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6543 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____6548 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6548 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____6553 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6553 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____6558 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6558 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____6563 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6563 = "FStar.HyperStack.ST.mmref")
          -> let uu____6567 = translate_type env arg  in TBuf uu____6567
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6568::arg::[],p) when
          (let uu____6575 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6575 = "FStar.HyperStack.s_ref") ||
            (let uu____6580 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6580 = "FStar.HyperStack.ST.s_ref")
          -> let uu____6584 = translate_type env arg  in TBuf uu____6584
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6585::[],p) when
          let uu____6589 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6589 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____6641 = FStar_List.map (translate_type env) args  in
          TTuple uu____6641
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > Prims.int_zero
          then
            let uu____6652 =
              let uu____6667 = FStar_List.map (translate_type env) args  in
              (lid, uu____6667)  in
            TApp uu____6652
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____6685 = FStar_List.map (translate_type env) ts  in
          TTuple uu____6685

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
    fun uu____6703  ->
      match uu____6703 with
      | (name,typ) ->
          let uu____6713 = translate_type env typ  in
          { name; typ = uu____6713; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____6720 = find env name  in EBound uu____6720
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____6734 =
            let uu____6739 = FStar_Util.must (mk_op op)  in
            let uu____6740 = FStar_Util.must (mk_width m)  in
            (uu____6739, uu____6740)  in
          EOp uu____6734
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____6750 =
            let uu____6755 = FStar_Util.must (mk_bool_op op)  in
            (uu____6755, Bool)  in
          EOp uu____6750
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
            let uu____6778 = translate_type env typ  in
            { name; typ = uu____6778; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____6805 =
            let uu____6816 = translate_expr env expr  in
            let uu____6817 = translate_branches env branches  in
            (uu____6816, uu____6817)  in
          EMatch uu____6805
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6831;
                  FStar_Extraction_ML_Syntax.loc = uu____6832;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6834;
             FStar_Extraction_ML_Syntax.loc = uu____6835;_},arg::[])
          when
          let uu____6841 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6841 = "FStar.Dyn.undyn" ->
          let uu____6845 =
            let uu____6850 = translate_expr env arg  in
            let uu____6851 = translate_type env t  in
            (uu____6850, uu____6851)  in
          ECast uu____6845
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6853;
                  FStar_Extraction_ML_Syntax.loc = uu____6854;_},uu____6855);
             FStar_Extraction_ML_Syntax.mlty = uu____6856;
             FStar_Extraction_ML_Syntax.loc = uu____6857;_},uu____6858)
          when
          let uu____6867 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6867 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6872;
                  FStar_Extraction_ML_Syntax.loc = uu____6873;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6875;
             FStar_Extraction_ML_Syntax.loc = uu____6876;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_String
                                                                s);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____6878;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____6879;_}::[])
          when
          let uu____6885 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6885 = "LowStar.Failure.failwith" ->
          let uu____6889 =
            let uu____6895 = translate_type env t  in (s, uu____6895)  in
          EAbortT uu____6889
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6898;
                  FStar_Extraction_ML_Syntax.loc = uu____6899;_},uu____6900);
             FStar_Extraction_ML_Syntax.mlty = uu____6901;
             FStar_Extraction_ML_Syntax.loc = uu____6902;_},arg::[])
          when
          ((let uu____6912 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6912 = "FStar.HyperStack.All.failwith") ||
             (let uu____6917 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6917 = "FStar.Error.unexpected"))
            ||
            (let uu____6922 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6922 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____6927;
               FStar_Extraction_ML_Syntax.loc = uu____6928;_} -> EAbortS msg
           | uu____6930 ->
               let print7 =
                 let uu____6932 =
                   let uu____6933 =
                     let uu____6934 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____6934
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____6933  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____6932
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
                  FStar_Extraction_ML_Syntax.mlty = uu____6941;
                  FStar_Extraction_ML_Syntax.loc = uu____6942;_},uu____6943);
             FStar_Extraction_ML_Syntax.mlty = uu____6944;
             FStar_Extraction_ML_Syntax.loc = uu____6945;_},e1::[])
          when
          (let uu____6955 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6955 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____6960 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6960 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6965;
                  FStar_Extraction_ML_Syntax.loc = uu____6966;_},uu____6967);
             FStar_Extraction_ML_Syntax.mlty = uu____6968;
             FStar_Extraction_ML_Syntax.loc = uu____6969;_},e1::e2::[])
          when
          ((((let uu____6980 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6980 = "FStar.Buffer.index") ||
               (let uu____6985 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6985 = "FStar.Buffer.op_Array_Access"))
              ||
              (let uu____6990 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6990 = "LowStar.Monotonic.Buffer.index"))
             ||
             (let uu____6995 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6995 = "LowStar.UninitializedBuffer.uindex"))
            ||
            (let uu____7000 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7000 = "LowStar.ConstBuffer.index")
          ->
          let uu____7004 =
            let uu____7009 = translate_expr env e1  in
            let uu____7010 = translate_expr env e2  in
            (uu____7009, uu____7010)  in
          EBufRead uu____7004
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7012;
                  FStar_Extraction_ML_Syntax.loc = uu____7013;_},uu____7014);
             FStar_Extraction_ML_Syntax.mlty = uu____7015;
             FStar_Extraction_ML_Syntax.loc = uu____7016;_},e1::[])
          when
          let uu____7024 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7024 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____7028 =
            let uu____7033 = translate_expr env e1  in
            (uu____7033, (EConstant (UInt32, "0")))  in
          EBufRead uu____7028
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7037;
                  FStar_Extraction_ML_Syntax.loc = uu____7038;_},uu____7039);
             FStar_Extraction_ML_Syntax.mlty = uu____7040;
             FStar_Extraction_ML_Syntax.loc = uu____7041;_},e1::e2::[])
          when
          ((let uu____7052 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7052 = "FStar.Buffer.create") ||
             (let uu____7057 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7057 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____7062 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7062 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____7066 =
            let uu____7073 = translate_expr env e1  in
            let uu____7074 = translate_expr env e2  in
            (Stack, uu____7073, uu____7074)  in
          EBufCreate uu____7066
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7076;
                  FStar_Extraction_ML_Syntax.loc = uu____7077;_},uu____7078);
             FStar_Extraction_ML_Syntax.mlty = uu____7079;
             FStar_Extraction_ML_Syntax.loc = uu____7080;_},elen::[])
          when
          let uu____7088 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7088 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____7092 =
            let uu____7097 = translate_expr env elen  in (Stack, uu____7097)
             in
          EBufCreateNoInit uu____7092
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7099;
                  FStar_Extraction_ML_Syntax.loc = uu____7100;_},uu____7101);
             FStar_Extraction_ML_Syntax.mlty = uu____7102;
             FStar_Extraction_ML_Syntax.loc = uu____7103;_},init1::[])
          when
          let uu____7111 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7111 = "FStar.HyperStack.ST.salloc" ->
          let uu____7115 =
            let uu____7122 = translate_expr env init1  in
            (Stack, uu____7122, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7115
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7126;
                  FStar_Extraction_ML_Syntax.loc = uu____7127;_},uu____7128);
             FStar_Extraction_ML_Syntax.mlty = uu____7129;
             FStar_Extraction_ML_Syntax.loc = uu____7130;_},e2::[])
          when
          ((let uu____7140 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7140 = "FStar.Buffer.createL") ||
             (let uu____7145 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7145 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____7150 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7150 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____7154 =
            let uu____7161 =
              let uu____7164 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7164  in
            (Stack, uu____7161)  in
          EBufCreateL uu____7154
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7170;
                  FStar_Extraction_ML_Syntax.loc = uu____7171;_},uu____7172);
             FStar_Extraction_ML_Syntax.mlty = uu____7173;
             FStar_Extraction_ML_Syntax.loc = uu____7174;_},_erid::e2::[])
          when
          (let uu____7185 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7185 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____7190 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7190 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____7194 =
            let uu____7201 =
              let uu____7204 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7204  in
            (Eternal, uu____7201)  in
          EBufCreateL uu____7194
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7210;
                  FStar_Extraction_ML_Syntax.loc = uu____7211;_},uu____7212);
             FStar_Extraction_ML_Syntax.mlty = uu____7213;
             FStar_Extraction_ML_Syntax.loc = uu____7214;_},_rid::init1::[])
          when
          (let uu____7225 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7225 = "FStar.HyperStack.ST.ralloc") ||
            (let uu____7230 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7230 = "FStar.HyperStack.ST.ralloc_drgn")
          ->
          let uu____7234 =
            let uu____7241 = translate_expr env init1  in
            (Eternal, uu____7241, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7234
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7245;
                  FStar_Extraction_ML_Syntax.loc = uu____7246;_},uu____7247);
             FStar_Extraction_ML_Syntax.mlty = uu____7248;
             FStar_Extraction_ML_Syntax.loc = uu____7249;_},_e0::e1::e2::[])
          when
          ((let uu____7261 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7261 = "FStar.Buffer.rcreate") ||
             (let uu____7266 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7266 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____7271 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7271 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____7275 =
            let uu____7282 = translate_expr env e1  in
            let uu____7283 = translate_expr env e2  in
            (Eternal, uu____7282, uu____7283)  in
          EBufCreate uu____7275
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7285;
                  FStar_Extraction_ML_Syntax.loc = uu____7286;_},uu____7287);
             FStar_Extraction_ML_Syntax.mlty = uu____7288;
             FStar_Extraction_ML_Syntax.loc = uu____7289;_},uu____7290)
          when
          (((((let uu____7301 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7301 = "LowStar.Monotonic.Buffer.mgcmalloc_and_blit") ||
                (let uu____7306 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____7306 = "LowStar.Monotonic.Buffer.mmalloc_and_blit"))
               ||
               (let uu____7311 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____7311 = "LowStar.Monotonic.Buffer.malloca_and_blit"))
              ||
              (let uu____7316 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7316 = "LowStar.ImmutableBuffer.igcmalloc_and_blit"))
             ||
             (let uu____7321 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7321 = "LowStar.ImmutableBuffer.imalloc_and_blit"))
            ||
            (let uu____7326 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7326 = "LowStar.ImmutableBuffer.ialloca_and_blit")
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
                  FStar_Extraction_ML_Syntax.mlty = uu____7332;
                  FStar_Extraction_ML_Syntax.loc = uu____7333;_},uu____7334);
             FStar_Extraction_ML_Syntax.mlty = uu____7335;
             FStar_Extraction_ML_Syntax.loc = uu____7336;_},_erid::elen::[])
          when
          let uu____7345 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7345 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____7349 =
            let uu____7354 = translate_expr env elen  in
            (Eternal, uu____7354)  in
          EBufCreateNoInit uu____7349
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7356;
                  FStar_Extraction_ML_Syntax.loc = uu____7357;_},uu____7358);
             FStar_Extraction_ML_Syntax.mlty = uu____7359;
             FStar_Extraction_ML_Syntax.loc = uu____7360;_},_rid::init1::[])
          when
          (let uu____7371 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7371 = "FStar.HyperStack.ST.ralloc_mm") ||
            (let uu____7376 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7376 = "FStar.HyperStack.ST.ralloc_drgn_mm")
          ->
          let uu____7380 =
            let uu____7387 = translate_expr env init1  in
            (ManuallyManaged, uu____7387, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7380
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7391;
                  FStar_Extraction_ML_Syntax.loc = uu____7392;_},uu____7393);
             FStar_Extraction_ML_Syntax.mlty = uu____7394;
             FStar_Extraction_ML_Syntax.loc = uu____7395;_},_e0::e1::e2::[])
          when
          (((let uu____7407 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7407 = "FStar.Buffer.rcreate_mm") ||
              (let uu____7412 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7412 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____7417 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7417 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____7422 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7422 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____7426 =
            let uu____7433 = translate_expr env e1  in
            let uu____7434 = translate_expr env e2  in
            (ManuallyManaged, uu____7433, uu____7434)  in
          EBufCreate uu____7426
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7436;
                  FStar_Extraction_ML_Syntax.loc = uu____7437;_},uu____7438);
             FStar_Extraction_ML_Syntax.mlty = uu____7439;
             FStar_Extraction_ML_Syntax.loc = uu____7440;_},_erid::elen::[])
          when
          let uu____7449 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7449 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____7453 =
            let uu____7458 = translate_expr env elen  in
            (ManuallyManaged, uu____7458)  in
          EBufCreateNoInit uu____7453
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7460;
                  FStar_Extraction_ML_Syntax.loc = uu____7461;_},uu____7462);
             FStar_Extraction_ML_Syntax.mlty = uu____7463;
             FStar_Extraction_ML_Syntax.loc = uu____7464;_},e2::[])
          when
          let uu____7472 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7472 = "FStar.HyperStack.ST.rfree" ->
          let uu____7476 = translate_expr env e2  in EBufFree uu____7476
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7478;
                  FStar_Extraction_ML_Syntax.loc = uu____7479;_},uu____7480);
             FStar_Extraction_ML_Syntax.mlty = uu____7481;
             FStar_Extraction_ML_Syntax.loc = uu____7482;_},e2::[])
          when
          (let uu____7492 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7492 = "FStar.Buffer.rfree") ||
            (let uu____7497 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7497 = "LowStar.Monotonic.Buffer.free")
          -> let uu____7501 = translate_expr env e2  in EBufFree uu____7501
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
             FStar_Extraction_ML_Syntax.loc = uu____7507;_},e1::e2::_e3::[])
          when
          let uu____7517 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7517 = "FStar.Buffer.sub" ->
          let uu____7521 =
            let uu____7526 = translate_expr env e1  in
            let uu____7527 = translate_expr env e2  in
            (uu____7526, uu____7527)  in
          EBufSub uu____7521
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7529;
                  FStar_Extraction_ML_Syntax.loc = uu____7530;_},uu____7531);
             FStar_Extraction_ML_Syntax.mlty = uu____7532;
             FStar_Extraction_ML_Syntax.loc = uu____7533;_},e1::e2::_e3::[])
          when
          (let uu____7545 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7545 = "LowStar.Monotonic.Buffer.msub") ||
            (let uu____7550 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7550 = "LowStar.ConstBuffer.sub")
          ->
          let uu____7554 =
            let uu____7559 = translate_expr env e1  in
            let uu____7560 = translate_expr env e2  in
            (uu____7559, uu____7560)  in
          EBufSub uu____7554
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7562;
                  FStar_Extraction_ML_Syntax.loc = uu____7563;_},uu____7564);
             FStar_Extraction_ML_Syntax.mlty = uu____7565;
             FStar_Extraction_ML_Syntax.loc = uu____7566;_},e1::e2::[])
          when
          let uu____7575 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7575 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7580;
                  FStar_Extraction_ML_Syntax.loc = uu____7581;_},uu____7582);
             FStar_Extraction_ML_Syntax.mlty = uu____7583;
             FStar_Extraction_ML_Syntax.loc = uu____7584;_},e1::e2::[])
          when
          let uu____7593 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7593 = "FStar.Buffer.offset" ->
          let uu____7597 =
            let uu____7602 = translate_expr env e1  in
            let uu____7603 = translate_expr env e2  in
            (uu____7602, uu____7603)  in
          EBufSub uu____7597
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7605;
                  FStar_Extraction_ML_Syntax.loc = uu____7606;_},uu____7607);
             FStar_Extraction_ML_Syntax.mlty = uu____7608;
             FStar_Extraction_ML_Syntax.loc = uu____7609;_},e1::e2::[])
          when
          let uu____7618 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7618 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____7622 =
            let uu____7627 = translate_expr env e1  in
            let uu____7628 = translate_expr env e2  in
            (uu____7627, uu____7628)  in
          EBufSub uu____7622
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7630;
                  FStar_Extraction_ML_Syntax.loc = uu____7631;_},uu____7632);
             FStar_Extraction_ML_Syntax.mlty = uu____7633;
             FStar_Extraction_ML_Syntax.loc = uu____7634;_},e1::e2::e3::[])
          when
          (((let uu____7646 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7646 = "FStar.Buffer.upd") ||
              (let uu____7651 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7651 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____7656 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7656 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____7661 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7661 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____7665 =
            let uu____7672 = translate_expr env e1  in
            let uu____7673 = translate_expr env e2  in
            let uu____7674 = translate_expr env e3  in
            (uu____7672, uu____7673, uu____7674)  in
          EBufWrite uu____7665
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7676;
                  FStar_Extraction_ML_Syntax.loc = uu____7677;_},uu____7678);
             FStar_Extraction_ML_Syntax.mlty = uu____7679;
             FStar_Extraction_ML_Syntax.loc = uu____7680;_},e1::e2::[])
          when
          let uu____7689 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7689 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____7693 =
            let uu____7700 = translate_expr env e1  in
            let uu____7701 = translate_expr env e2  in
            (uu____7700, (EConstant (UInt32, "0")), uu____7701)  in
          EBufWrite uu____7693
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7705;
             FStar_Extraction_ML_Syntax.loc = uu____7706;_},uu____7707::[])
          when
          let uu____7710 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7710 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7715;
             FStar_Extraction_ML_Syntax.loc = uu____7716;_},uu____7717::[])
          when
          let uu____7720 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7720 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7725;
                  FStar_Extraction_ML_Syntax.loc = uu____7726;_},uu____7727);
             FStar_Extraction_ML_Syntax.mlty = uu____7728;
             FStar_Extraction_ML_Syntax.loc = uu____7729;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____7743 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7743 = "FStar.Buffer.blit") ||
             (let uu____7748 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7748 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____7753 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7753 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____7757 =
            let uu____7768 = translate_expr env e1  in
            let uu____7769 = translate_expr env e2  in
            let uu____7770 = translate_expr env e3  in
            let uu____7771 = translate_expr env e4  in
            let uu____7772 = translate_expr env e5  in
            (uu____7768, uu____7769, uu____7770, uu____7771, uu____7772)  in
          EBufBlit uu____7757
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7774;
                  FStar_Extraction_ML_Syntax.loc = uu____7775;_},uu____7776);
             FStar_Extraction_ML_Syntax.mlty = uu____7777;
             FStar_Extraction_ML_Syntax.loc = uu____7778;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____7794 =
            let uu____7801 = translate_expr env e1  in
            let uu____7802 = translate_expr env e2  in
            let uu____7803 = translate_expr env e3  in
            (uu____7801, uu____7802, uu____7803)  in
          EBufFill uu____7794
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7805;
             FStar_Extraction_ML_Syntax.loc = uu____7806;_},uu____7807::[])
          when
          let uu____7810 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7810 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7815;
                  FStar_Extraction_ML_Syntax.loc = uu____7816;_},uu____7817);
             FStar_Extraction_ML_Syntax.mlty = uu____7818;
             FStar_Extraction_ML_Syntax.loc = uu____7819;_},_rid::[])
          when
          (let uu____7829 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7829 = "FStar.HyperStack.ST.free_drgn") ||
            (let uu____7834 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7834 = "FStar.HyperStack.ST.new_drgn")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7839;
                  FStar_Extraction_ML_Syntax.loc = uu____7840;_},uu____7841);
             FStar_Extraction_ML_Syntax.mlty = uu____7842;
             FStar_Extraction_ML_Syntax.loc = uu____7843;_},_ebuf::_eseq::[])
          when
          (((let uu____7854 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7854 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____7859 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7859 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____7864 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7864 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____7869 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7869 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7874;
                  FStar_Extraction_ML_Syntax.loc = uu____7875;_},uu____7876);
             FStar_Extraction_ML_Syntax.mlty = uu____7877;
             FStar_Extraction_ML_Syntax.loc = uu____7878;_},e1::[])
          when
          (let uu____7888 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7888 = "LowStar.ConstBuffer.of_buffer") ||
            (let uu____7893 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7893 = "LowStar.ConstBuffer.of_ibuffer")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7898;
                  FStar_Extraction_ML_Syntax.loc = uu____7899;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____7901;
             FStar_Extraction_ML_Syntax.loc = uu____7902;_},e1::[])
          when
          ((let uu____7910 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7910 = "LowStar.ConstBuffer.cast") ||
             (let uu____7915 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7915 = "LowStar.ConstBuffer.to_buffer"))
            ||
            (let uu____7920 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7920 = "LowStar.ConstBuffer.to_ibuffer")
          ->
          let uu____7924 =
            let uu____7929 = translate_expr env e1  in
            let uu____7930 =
              let uu____7931 = translate_type env t  in TBuf uu____7931  in
            (uu____7929, uu____7930)  in
          ECast uu____7924
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7933;
             FStar_Extraction_ML_Syntax.loc = uu____7934;_},e1::[])
          when
          let uu____7938 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7938 = "Obj.repr" ->
          let uu____7942 =
            let uu____7947 = translate_expr env e1  in (uu____7947, TAny)  in
          ECast uu____7942
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7950;
             FStar_Extraction_ML_Syntax.loc = uu____7951;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____7967 = FStar_Util.must (mk_width m)  in
          let uu____7968 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____7967 uu____7968 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7970;
             FStar_Extraction_ML_Syntax.loc = uu____7971;_},args)
          when is_bool_op op ->
          let uu____7985 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____7985 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7987;
             FStar_Extraction_ML_Syntax.loc = uu____7988;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7990;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7991;_}::[])
          when is_machine_int m ->
          let uu____8016 =
            let uu____8022 = FStar_Util.must (mk_width m)  in (uu____8022, c)
             in
          EConstant uu____8016
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____8025;
             FStar_Extraction_ML_Syntax.loc = uu____8026;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8028;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8029;_}::[])
          when is_machine_int m ->
          let uu____8054 =
            let uu____8060 = FStar_Util.must (mk_width m)  in (uu____8060, c)
             in
          EConstant uu____8054
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8062;
             FStar_Extraction_ML_Syntax.loc = uu____8063;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8065;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8066;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8079 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8081;
             FStar_Extraction_ML_Syntax.loc = uu____8082;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8084;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8085;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8102 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8104;
             FStar_Extraction_ML_Syntax.loc = uu____8105;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8107;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8108;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8123 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8126;
                  FStar_Extraction_ML_Syntax.loc = uu____8127;_},uu____8128);
             FStar_Extraction_ML_Syntax.mlty = uu____8129;
             FStar_Extraction_ML_Syntax.loc = uu____8130;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = ebefore;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8132;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8133;_}::e1::
           { FStar_Extraction_ML_Syntax.expr = eafter;
             FStar_Extraction_ML_Syntax.mlty = uu____8136;
             FStar_Extraction_ML_Syntax.loc = uu____8137;_}::[])
          when
          let uu____8144 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8144 = "C.comment_gen" ->
          (match (ebefore, eafter) with
           | (FStar_Extraction_ML_Syntax.MLE_Const
              (FStar_Extraction_ML_Syntax.MLC_String
              sbefore),FStar_Extraction_ML_Syntax.MLE_Const
              (FStar_Extraction_ML_Syntax.MLC_String safter)) ->
               (if FStar_Util.contains sbefore "*/"
                then failwith "Before Comment contains end-of-comment marker"
                else ();
                if FStar_Util.contains safter "*/"
                then failwith "After Comment contains end-of-comment marker"
                else ();
                (let uu____8164 =
                   let uu____8173 = translate_expr env e1  in
                   (sbefore, uu____8173, safter)  in
                 EComment uu____8164))
           | uu____8176 ->
               failwith "Cannot extract comment applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("C"::[],"comment_gen");
             FStar_Extraction_ML_Syntax.mlty = uu____8182;
             FStar_Extraction_ML_Syntax.loc = uu____8183;_},args)
          ->
          let uu____8197 =
            let uu____8199 =
              FStar_Util.string_of_int (FStar_List.length args)  in
            Prims.op_Hat
              "comment_gen called with wrong number of arguments: "
              uu____8199
             in
          failwith uu____8197
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[],"buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8202;
             FStar_Extraction_ML_Syntax.loc = uu____8203;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8205;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8206;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____8221 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____8224;
             FStar_Extraction_ML_Syntax.loc = uu____8225;_},arg::[])
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
            let uu____8253 =
              let uu____8258 = translate_expr env arg  in
              (uu____8258, (TInt UInt64))  in
            ECast uu____8253
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____8263 =
                 let uu____8268 = translate_expr env arg  in
                 (uu____8268, (TInt UInt32))  in
               ECast uu____8263)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____8273 =
                   let uu____8278 = translate_expr env arg  in
                   (uu____8278, (TInt UInt16))  in
                 ECast uu____8273)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____8283 =
                     let uu____8288 = translate_expr env arg  in
                     (uu____8288, (TInt UInt8))  in
                   ECast uu____8283)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____8293 =
                       let uu____8298 = translate_expr env arg  in
                       (uu____8298, (TInt Int64))  in
                     ECast uu____8293)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____8303 =
                         let uu____8308 = translate_expr env arg  in
                         (uu____8308, (TInt Int32))  in
                       ECast uu____8303)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____8313 =
                           let uu____8318 = translate_expr env arg  in
                           (uu____8318, (TInt Int16))  in
                         ECast uu____8313)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____8323 =
                             let uu____8328 = translate_expr env arg  in
                             (uu____8328, (TInt Int8))  in
                           ECast uu____8323)
                        else
                          (let uu____8331 =
                             let uu____8338 =
                               let uu____8341 = translate_expr env arg  in
                               [uu____8341]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____8338)
                              in
                           EApp uu____8331)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____8361 =
            let uu____8368 = translate_expr env head1  in
            let uu____8369 = FStar_List.map (translate_expr env) args  in
            (uu____8368, uu____8369)  in
          EApp uu____8361
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____8380 =
            let uu____8387 = translate_expr env head1  in
            let uu____8388 = FStar_List.map (translate_type env) ty_args  in
            (uu____8387, uu____8388)  in
          ETypApp uu____8380
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____8396 =
            let uu____8401 = translate_expr env e1  in
            let uu____8402 = translate_type env t_to  in
            (uu____8401, uu____8402)  in
          ECast uu____8396
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____8403,fields) ->
          let uu____8425 =
            let uu____8437 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8438 =
              FStar_List.map
                (fun uu____8460  ->
                   match uu____8460 with
                   | (field,expr) ->
                       let uu____8475 = translate_expr env expr  in
                       (field, uu____8475)) fields
               in
            (uu____8437, uu____8438)  in
          EFlat uu____8425
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____8486 =
            let uu____8494 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____8495 = translate_expr env e1  in
            (uu____8494, uu____8495, (FStar_Pervasives_Native.snd path))  in
          EField uu____8486
      | FStar_Extraction_ML_Syntax.MLE_Let uu____8501 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____8514) ->
          let uu____8519 =
            let uu____8521 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____8521
             in
          failwith uu____8519
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____8533 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____8533
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____8539 = FStar_List.map (translate_expr env) es  in
          ETuple uu____8539
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____8542,cons1),es) ->
          let uu____8557 =
            let uu____8567 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8568 = FStar_List.map (translate_expr env) es  in
            (uu____8567, cons1, uu____8568)  in
          ECons uu____8557
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____8594 =
            let uu____8603 = translate_expr env1 body  in
            let uu____8604 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____8603, uu____8604)  in
          EFun uu____8594
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____8614 =
            let uu____8621 = translate_expr env e1  in
            let uu____8622 = translate_expr env e2  in
            let uu____8623 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____8621, uu____8622, uu____8623)  in
          EIfThenElse uu____8614
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____8625 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____8633 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____8649 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > Prims.int_zero
          then
            let uu____8667 =
              let uu____8682 = FStar_List.map (translate_type env) ts  in
              (lid, uu____8682)  in
            TApp uu____8667
          else TQualified lid
      | uu____8697 ->
          let uu____8698 =
            let uu____8700 =
              FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
            FStar_Util.format1
              "invalid argument: expected MLTY_Named, got %s" uu____8700
             in
          failwith uu____8698

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
    fun uu____8734  ->
      match uu____8734 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____8761 = translate_pat env pat  in
            (match uu____8761 with
             | (env1,pat1) ->
                 let uu____8772 = translate_expr env1 expr  in
                 (pat1, uu____8772))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___7_8780  ->
    match uu___7_8780 with
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
          let uu____8847 =
            let uu____8848 =
              let uu____8854 = translate_width sw  in (uu____8854, s)  in
            PConstant uu____8848  in
          (env, uu____8847)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____8864,cons1),ps) ->
          let uu____8879 =
            FStar_List.fold_left
              (fun uu____8899  ->
                 fun p1  ->
                   match uu____8899 with
                   | (env1,acc) ->
                       let uu____8919 = translate_pat env1 p1  in
                       (match uu____8919 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8879 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____8949,ps) ->
          let uu____8971 =
            FStar_List.fold_left
              (fun uu____9008  ->
                 fun uu____9009  ->
                   match (uu____9008, uu____9009) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____9089 = translate_pat env1 p1  in
                       (match uu____9089 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____8971 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____9160 =
            FStar_List.fold_left
              (fun uu____9180  ->
                 fun p1  ->
                   match uu____9180 with
                   | (env1,acc) ->
                       let uu____9200 = translate_pat env1 p1  in
                       (match uu____9200 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____9160 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____9227 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____9233 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____9247 =
            let uu____9249 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____9249
              (FStar_Util.for_some
                 (fun c1  -> c1 = (FStar_Char.char_of_int Prims.int_zero)))
             in
          if uu____9247
          then
            let uu____9264 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____9264
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____9291) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____9309 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____9311 ->
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
          let uu____9335 =
            let uu____9342 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____9342)  in
          EApp uu____9335

let (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____9354  ->
    match uu____9354 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____9403 = m  in
               match uu____9403 with
               | (path,uu____9418,uu____9419) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___1645_9437  ->
                  match () with
                  | () ->
                      ((let uu____9441 =
                          let uu____9443 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____9443  in
                        if uu____9441
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____9449 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____9449))) ()
             with
             | uu___1644_9452 ->
                 ((let uu____9456 = FStar_Util.print_exn uu___1644_9452  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____9456);
                  FStar_Pervasives_Native.None)) modules
  