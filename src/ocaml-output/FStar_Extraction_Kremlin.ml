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
  | TConstBuf of typ 
let (uu___is_DGlobal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DGlobal _0 -> true | uu____743 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____854 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____979 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____1086 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DUnusedRetainedForBackwardsCompat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DUnusedRetainedForBackwardsCompat _0 -> true
    | uu____1218 -> false
  
let (__proj__DUnusedRetainedForBackwardsCompat__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  =
  fun projectee  ->
    match projectee with | DUnusedRetainedForBackwardsCompat _0 -> _0
  
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____1335 -> false
  
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
    | uu____1476 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____1544 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ * Prims.string Prims.list))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1637 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1648 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1659 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1670 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1681 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1692 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1703 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1714 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1727 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1748 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1761 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1784 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1807 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____1828 -> false
  
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | IfDef  -> true | uu____1839 -> false
  
let (uu___is_Macro : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Macro  -> true | uu____1850 -> false
  
let (uu___is_Deprecated : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Deprecated _0 -> true | uu____1863 -> false
  
let (__proj__Deprecated__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Deprecated _0 -> _0 
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1884 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1895 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1906 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1919 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1949 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____1997 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____2030 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____2048 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____2091 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____2134 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____2177 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____2216 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____2245 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____2282 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____2323 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____2360 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____2401 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____2442 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____2501 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____2554 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____2589 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____2619 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____2630 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____2643 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____2664 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____2675 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____2687 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____2717 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____2776 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____2820 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____2857 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2896 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2930 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2982 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____3020 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____3050 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____3094 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____3116 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____3139 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____3169 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____3180 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____3191 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____3202 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____3213 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____3224 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____3235 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____3246 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____3257 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____3268 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____3279 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____3290 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____3301 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____3312 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____3323 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____3334 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____3345 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____3356 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____3367 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____3378 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____3389 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____3400 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____3411 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____3422 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____3433 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____3444 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____3457 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____3479 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____3505 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____3547 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____3579 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____3624 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____3657 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____3668 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____3679 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____3690 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____3701 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____3712 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____3723 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____3734 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____3745 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____3756 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____3805 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____3824 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____3842 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____3862 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____3904 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____3915 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____3931 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____3963 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____3999 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____4062 -> false
  
let (__proj__TTuple__item___0 : typ -> typ Prims.list) =
  fun projectee  -> match projectee with | TTuple _0 -> _0 
let (uu___is_TConstBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TConstBuf _0 -> true | uu____4087 -> false
  
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
  'Auu____4182 'Auu____4183 'Auu____4184 .
    ('Auu____4182 * 'Auu____4183 * 'Auu____4184) -> 'Auu____4182
  = fun uu____4195  -> match uu____4195 with | (x,uu____4203,uu____4204) -> x 
let snd3 :
  'Auu____4214 'Auu____4215 'Auu____4216 .
    ('Auu____4214 * 'Auu____4215 * 'Auu____4216) -> 'Auu____4215
  = fun uu____4227  -> match uu____4227 with | (uu____4234,x,uu____4236) -> x 
let thd3 :
  'Auu____4246 'Auu____4247 'Auu____4248 .
    ('Auu____4246 * 'Auu____4247 * 'Auu____4248) -> 'Auu____4248
  = fun uu____4259  -> match uu____4259 with | (uu____4266,uu____4267,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___0_4277  ->
    match uu___0_4277 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____4289 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___1_4299  ->
    match uu___1_4299 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____4308 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___2_4329  ->
    match uu___2_4329 with
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
    | uu____4374 -> FStar_Pervasives_Native.None
  
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
      let uu___165_4530 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___165_4530.names_t);
        module_name = (uu___165_4530.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___169_4544 = env  in
      {
        names = (uu___169_4544.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___169_4544.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____4559 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____4559 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___180_4583  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___179_4590 ->
          let uu____4592 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4592
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___189_4612  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___188_4621 ->
          let uu____4623 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4623
  
let add_binders :
  'Auu____4634 . env -> (Prims.string * 'Auu____4634) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____4669  ->
             match uu____4669 with | (name,uu____4676) -> extend env1 name)
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
      | uu____4728 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun m  ->
    let uu____4954 = m  in
    match uu____4954 with
    | (module_name,modul,uu____4969) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____5004 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___3_5018  ->
         match uu___3_5018 with
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
         | uu____5031 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____5035 =
      FStar_List.choose
        (fun uu___4_5042  ->
           match uu___4_5042 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____5049 -> FStar_Pervasives_Native.None) flags
       in
    match uu____5035 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____5062 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____5076 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____5078 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____5083) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5110;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5113;_} when
            FStar_Util.for_some
              (fun uu___5_5118  ->
                 match uu___5_5118 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____5121 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            let arg_names =
              match e.FStar_Extraction_ML_Syntax.expr with
              | FStar_Extraction_ML_Syntax.MLE_Fun (args,uu____5144) ->
                  FStar_List.map FStar_Pervasives_Native.fst args
              | uu____5166 -> []  in
            if (FStar_List.length tvars) = Prims.int_zero
            then
              let uu____5174 =
                let uu____5175 =
                  let uu____5201 = translate_cc meta  in
                  let uu____5204 = translate_flags meta  in
                  let uu____5207 = translate_type env t0  in
                  (uu____5201, uu____5204, name1, uu____5207, arg_names)  in
                DExternal uu____5175  in
              FStar_Pervasives_Native.Some uu____5174
            else
              ((let uu____5226 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____5226);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5232;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____5235;
                FStar_Extraction_ML_Syntax.loc = uu____5236;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5238;_} ->
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
               let rec find_return_type eff i uu___6_5295 =
                 match uu___6_5295 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5304,eff1,t)
                     when i > Prims.int_zero ->
                     find_return_type eff1 (i - Prims.int_one) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____5324 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____5324 with
               | (i,eff,t) ->
                   (if i > Prims.int_zero
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____5350 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____5350 msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5368) ->
                           let uu____5369 = translate_flags meta  in
                           MustDisappear :: uu____5369
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____5372 = translate_flags meta  in
                           MustDisappear :: uu____5372
                       | uu____5375 -> translate_flags meta  in
                     try
                       (fun uu___363_5384  ->
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
                         ((let uu____5416 =
                             let uu____5422 =
                               let uu____5424 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____5424 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____5422)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____5416);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5450;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5453;_} ->
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
                 (fun uu___390_5490  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____5514 =
                       let uu____5520 =
                         let uu____5522 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____5524 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____5522
                           uu____5524
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____5520)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____5514);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5542;
            FStar_Extraction_ML_Syntax.mllb_def = uu____5543;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____5544;
            FStar_Extraction_ML_Syntax.print_typ = uu____5545;_} ->
            ((let uu____5552 =
                let uu____5558 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____5558)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____5552);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____5565 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____5565
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____5579 = ty  in
      match uu____5579 with
      | (uu____5582,uu____5583,uu____5584,uu____5585,flags,uu____5587) ->
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
                     (let uu____5661 =
                        let uu____5662 =
                          let uu____5682 = translate_flags flags1  in
                          let uu____5685 = translate_type env1 t  in
                          (name1, uu____5682, (FStar_List.length args),
                            uu____5685)
                           in
                        DTypeAlias uu____5662  in
                      FStar_Pervasives_Native.Some uu____5661)
             | (uu____5698,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____5743 =
                   let uu____5744 =
                     let uu____5776 = translate_flags flags1  in
                     let uu____5779 =
                       FStar_List.map
                         (fun uu____5811  ->
                            match uu____5811 with
                            | (f,t) ->
                                let uu____5831 =
                                  let uu____5837 = translate_type env1 t  in
                                  (uu____5837, false)  in
                                (f, uu____5831)) fields
                        in
                     (name1, uu____5776, (FStar_List.length args),
                       uu____5779)
                      in
                   DTypeFlat uu____5744  in
                 FStar_Pervasives_Native.Some uu____5743
             | (uu____5870,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____5920 =
                   let uu____5921 =
                     let uu____5960 =
                       FStar_List.map
                         (fun uu____6013  ->
                            match uu____6013 with
                            | (cons1,ts) ->
                                let uu____6061 =
                                  FStar_List.map
                                    (fun uu____6093  ->
                                       match uu____6093 with
                                       | (name2,t) ->
                                           let uu____6113 =
                                             let uu____6119 =
                                               translate_type env1 t  in
                                             (uu____6119, false)  in
                                           (name2, uu____6113)) ts
                                   in
                                (cons1, uu____6061)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____5960)
                      in
                   DTypeVariant uu____5921  in
                 FStar_Pervasives_Native.Some uu____5920
             | (uu____6172,name,_mangled_name,uu____6175,uu____6176,uu____6177)
                 ->
                 ((let uu____6193 =
                     let uu____6199 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____6199)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____6193);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____6207 = find_t env name  in TBound uu____6207
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____6210,t2) ->
          let uu____6212 =
            let uu____6217 = translate_type env t1  in
            let uu____6218 = translate_type env t2  in
            (uu____6217, uu____6218)  in
          TArrow uu____6212
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6222 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6222 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6229 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6229 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____6246 = FStar_Util.must (mk_width m)  in TInt uu____6246
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____6260 = FStar_Util.must (mk_width m)  in TInt uu____6260
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6265 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6265 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____6269::arg::uu____6271::[],p) when
          (((let uu____6277 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6277 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____6282 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6282 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____6287 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6287 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____6292 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6292 = "FStar.HyperStack.ST.s_mref")
          -> let uu____6296 = translate_type env arg  in TBuf uu____6296
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____6298::[],p) when
          ((((((((((let uu____6304 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6304 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____6309 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6309 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____6314 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6314 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____6319 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6319 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____6324 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6324 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____6329 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6329 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____6334 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6334 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____6339 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6339 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____6344 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6344 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____6349 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6349 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____6354 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6354 = "FStar.HyperStack.ST.mmmref")
          -> let uu____6358 = translate_type env arg  in TBuf uu____6358
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____6360::uu____6361::[],p) when
          let uu____6365 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6365 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____6369 = translate_type env arg  in TBuf uu____6369
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6374 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6374 = "LowStar.ConstBuffer.const_buffer" ->
          let uu____6378 = translate_type env arg  in TConstBuf uu____6378
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____6385 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6385 = "FStar.Buffer.buffer") ||
                        (let uu____6390 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____6390 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____6395 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____6395 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____6400 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6400 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____6405 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6405 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____6410 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6410 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____6415 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6415 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____6420 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6420 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____6425 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6425 = "FStar.HyperStack.mmref"))
                ||
                (let uu____6430 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6430 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____6435 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6435 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____6440 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6440 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____6445 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6445 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____6450 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6450 = "FStar.HyperStack.ST.mmref")
          -> let uu____6454 = translate_type env arg  in TBuf uu____6454
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6455::arg::[],p) when
          (let uu____6462 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6462 = "FStar.HyperStack.s_ref") ||
            (let uu____6467 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6467 = "FStar.HyperStack.ST.s_ref")
          -> let uu____6471 = translate_type env arg  in TBuf uu____6471
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6472::[],p) when
          let uu____6476 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6476 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____6528 = FStar_List.map (translate_type env) args  in
          TTuple uu____6528
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > Prims.int_zero
          then
            let uu____6539 =
              let uu____6554 = FStar_List.map (translate_type env) args  in
              (lid, uu____6554)  in
            TApp uu____6539
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____6572 = FStar_List.map (translate_type env) ts  in
          TTuple uu____6572

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
    fun uu____6590  ->
      match uu____6590 with
      | (name,typ) ->
          let uu____6600 = translate_type env typ  in
          { name; typ = uu____6600; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____6607 = find env name  in EBound uu____6607
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____6621 =
            let uu____6626 = FStar_Util.must (mk_op op)  in
            let uu____6627 = FStar_Util.must (mk_width m)  in
            (uu____6626, uu____6627)  in
          EOp uu____6621
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____6637 =
            let uu____6642 = FStar_Util.must (mk_bool_op op)  in
            (uu____6642, Bool)  in
          EOp uu____6637
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
            let uu____6665 = translate_type env typ  in
            { name; typ = uu____6665; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____6692 =
            let uu____6703 = translate_expr env expr  in
            let uu____6704 = translate_branches env branches  in
            (uu____6703, uu____6704)  in
          EMatch uu____6692
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6718;
                  FStar_Extraction_ML_Syntax.loc = uu____6719;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6721;
             FStar_Extraction_ML_Syntax.loc = uu____6722;_},arg::[])
          when
          let uu____6728 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6728 = "FStar.Dyn.undyn" ->
          let uu____6732 =
            let uu____6737 = translate_expr env arg  in
            let uu____6738 = translate_type env t  in
            (uu____6737, uu____6738)  in
          ECast uu____6732
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6740;
                  FStar_Extraction_ML_Syntax.loc = uu____6741;_},uu____6742);
             FStar_Extraction_ML_Syntax.mlty = uu____6743;
             FStar_Extraction_ML_Syntax.loc = uu____6744;_},uu____6745)
          when
          let uu____6754 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6754 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6759;
                  FStar_Extraction_ML_Syntax.loc = uu____6760;_},uu____6761);
             FStar_Extraction_ML_Syntax.mlty = uu____6762;
             FStar_Extraction_ML_Syntax.loc = uu____6763;_},arg::[])
          when
          ((let uu____6773 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6773 = "FStar.HyperStack.All.failwith") ||
             (let uu____6778 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6778 = "FStar.Error.unexpected"))
            ||
            (let uu____6783 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6783 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____6788;
               FStar_Extraction_ML_Syntax.loc = uu____6789;_} -> EAbortS msg
           | uu____6791 ->
               let print7 =
                 let uu____6793 =
                   let uu____6794 =
                     let uu____6795 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____6795
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____6794  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____6793
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
                  FStar_Extraction_ML_Syntax.mlty = uu____6802;
                  FStar_Extraction_ML_Syntax.loc = uu____6803;_},uu____6804);
             FStar_Extraction_ML_Syntax.mlty = uu____6805;
             FStar_Extraction_ML_Syntax.loc = uu____6806;_},e1::[])
          when
          (let uu____6816 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6816 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____6821 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6821 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6826;
                  FStar_Extraction_ML_Syntax.loc = uu____6827;_},uu____6828);
             FStar_Extraction_ML_Syntax.mlty = uu____6829;
             FStar_Extraction_ML_Syntax.loc = uu____6830;_},e1::e2::[])
          when
          ((((let uu____6841 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6841 = "FStar.Buffer.index") ||
               (let uu____6846 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6846 = "FStar.Buffer.op_Array_Access"))
              ||
              (let uu____6851 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6851 = "LowStar.Monotonic.Buffer.index"))
             ||
             (let uu____6856 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6856 = "LowStar.UninitializedBuffer.uindex"))
            ||
            (let uu____6861 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6861 = "LowStar.ConstBuffer.index")
          ->
          let uu____6865 =
            let uu____6870 = translate_expr env e1  in
            let uu____6871 = translate_expr env e2  in
            (uu____6870, uu____6871)  in
          EBufRead uu____6865
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6873;
                  FStar_Extraction_ML_Syntax.loc = uu____6874;_},uu____6875);
             FStar_Extraction_ML_Syntax.mlty = uu____6876;
             FStar_Extraction_ML_Syntax.loc = uu____6877;_},e1::[])
          when
          let uu____6885 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6885 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____6889 =
            let uu____6894 = translate_expr env e1  in
            (uu____6894, (EConstant (UInt32, "0")))  in
          EBufRead uu____6889
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
             FStar_Extraction_ML_Syntax.loc = uu____6902;_},e1::e2::[])
          when
          ((let uu____6913 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6913 = "FStar.Buffer.create") ||
             (let uu____6918 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6918 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____6923 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6923 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____6927 =
            let uu____6934 = translate_expr env e1  in
            let uu____6935 = translate_expr env e2  in
            (Stack, uu____6934, uu____6935)  in
          EBufCreate uu____6927
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6937;
                  FStar_Extraction_ML_Syntax.loc = uu____6938;_},uu____6939);
             FStar_Extraction_ML_Syntax.mlty = uu____6940;
             FStar_Extraction_ML_Syntax.loc = uu____6941;_},elen::[])
          when
          let uu____6949 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6949 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____6953 =
            let uu____6958 = translate_expr env elen  in (Stack, uu____6958)
             in
          EBufCreateNoInit uu____6953
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6960;
                  FStar_Extraction_ML_Syntax.loc = uu____6961;_},uu____6962);
             FStar_Extraction_ML_Syntax.mlty = uu____6963;
             FStar_Extraction_ML_Syntax.loc = uu____6964;_},init1::[])
          when
          let uu____6972 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6972 = "FStar.HyperStack.ST.salloc" ->
          let uu____6976 =
            let uu____6983 = translate_expr env init1  in
            (Stack, uu____6983, (EConstant (UInt32, "1")))  in
          EBufCreate uu____6976
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6987;
                  FStar_Extraction_ML_Syntax.loc = uu____6988;_},uu____6989);
             FStar_Extraction_ML_Syntax.mlty = uu____6990;
             FStar_Extraction_ML_Syntax.loc = uu____6991;_},e2::[])
          when
          ((let uu____7001 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7001 = "FStar.Buffer.createL") ||
             (let uu____7006 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7006 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____7011 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7011 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____7015 =
            let uu____7022 =
              let uu____7025 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7025  in
            (Stack, uu____7022)  in
          EBufCreateL uu____7015
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7031;
                  FStar_Extraction_ML_Syntax.loc = uu____7032;_},uu____7033);
             FStar_Extraction_ML_Syntax.mlty = uu____7034;
             FStar_Extraction_ML_Syntax.loc = uu____7035;_},_erid::e2::[])
          when
          (let uu____7046 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7046 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____7051 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7051 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____7055 =
            let uu____7062 =
              let uu____7065 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7065  in
            (Eternal, uu____7062)  in
          EBufCreateL uu____7055
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7071;
                  FStar_Extraction_ML_Syntax.loc = uu____7072;_},uu____7073);
             FStar_Extraction_ML_Syntax.mlty = uu____7074;
             FStar_Extraction_ML_Syntax.loc = uu____7075;_},_rid::init1::[])
          when
          let uu____7084 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7084 = "FStar.HyperStack.ST.ralloc" ->
          let uu____7088 =
            let uu____7095 = translate_expr env init1  in
            (Eternal, uu____7095, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7088
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
             FStar_Extraction_ML_Syntax.loc = uu____7103;_},_e0::e1::e2::[])
          when
          ((let uu____7115 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7115 = "FStar.Buffer.rcreate") ||
             (let uu____7120 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7120 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____7125 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7125 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____7129 =
            let uu____7136 = translate_expr env e1  in
            let uu____7137 = translate_expr env e2  in
            (Eternal, uu____7136, uu____7137)  in
          EBufCreate uu____7129
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7139;
                  FStar_Extraction_ML_Syntax.loc = uu____7140;_},uu____7141);
             FStar_Extraction_ML_Syntax.mlty = uu____7142;
             FStar_Extraction_ML_Syntax.loc = uu____7143;_},uu____7144)
          when
          (((((let uu____7155 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7155 = "LowStar.Monotonic.Buffer.mgcmalloc_and_blit") ||
                (let uu____7160 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____7160 = "LowStar.Monotonic.Buffer.mmalloc_and_blit"))
               ||
               (let uu____7165 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____7165 = "LowStar.Monotonic.Buffer.malloca_and_blit"))
              ||
              (let uu____7170 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7170 = "LowStar.ImmutableBuffer.igcmalloc_and_blit"))
             ||
             (let uu____7175 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7175 = "LowStar.ImmutableBuffer.imalloc_and_blit"))
            ||
            (let uu____7180 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7180 = "LowStar.ImmutableBuffer.ialloca_and_blit")
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
                  FStar_Extraction_ML_Syntax.mlty = uu____7186;
                  FStar_Extraction_ML_Syntax.loc = uu____7187;_},uu____7188);
             FStar_Extraction_ML_Syntax.mlty = uu____7189;
             FStar_Extraction_ML_Syntax.loc = uu____7190;_},_erid::elen::[])
          when
          let uu____7199 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7199 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____7203 =
            let uu____7208 = translate_expr env elen  in
            (Eternal, uu____7208)  in
          EBufCreateNoInit uu____7203
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
          let uu____7223 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7223 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____7227 =
            let uu____7234 = translate_expr env init1  in
            (ManuallyManaged, uu____7234, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7227
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7238;
                  FStar_Extraction_ML_Syntax.loc = uu____7239;_},uu____7240);
             FStar_Extraction_ML_Syntax.mlty = uu____7241;
             FStar_Extraction_ML_Syntax.loc = uu____7242;_},_e0::e1::e2::[])
          when
          (((let uu____7254 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7254 = "FStar.Buffer.rcreate_mm") ||
              (let uu____7259 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7259 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____7264 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7264 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____7269 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7269 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____7273 =
            let uu____7280 = translate_expr env e1  in
            let uu____7281 = translate_expr env e2  in
            (ManuallyManaged, uu____7280, uu____7281)  in
          EBufCreate uu____7273
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7283;
                  FStar_Extraction_ML_Syntax.loc = uu____7284;_},uu____7285);
             FStar_Extraction_ML_Syntax.mlty = uu____7286;
             FStar_Extraction_ML_Syntax.loc = uu____7287;_},_erid::elen::[])
          when
          let uu____7296 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7296 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____7300 =
            let uu____7305 = translate_expr env elen  in
            (ManuallyManaged, uu____7305)  in
          EBufCreateNoInit uu____7300
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7307;
                  FStar_Extraction_ML_Syntax.loc = uu____7308;_},uu____7309);
             FStar_Extraction_ML_Syntax.mlty = uu____7310;
             FStar_Extraction_ML_Syntax.loc = uu____7311;_},e2::[])
          when
          let uu____7319 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7319 = "FStar.HyperStack.ST.rfree" ->
          let uu____7323 = translate_expr env e2  in EBufFree uu____7323
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7325;
                  FStar_Extraction_ML_Syntax.loc = uu____7326;_},uu____7327);
             FStar_Extraction_ML_Syntax.mlty = uu____7328;
             FStar_Extraction_ML_Syntax.loc = uu____7329;_},e2::[])
          when
          (let uu____7339 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7339 = "FStar.Buffer.rfree") ||
            (let uu____7344 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7344 = "LowStar.Monotonic.Buffer.free")
          -> let uu____7348 = translate_expr env e2  in EBufFree uu____7348
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7350;
                  FStar_Extraction_ML_Syntax.loc = uu____7351;_},uu____7352);
             FStar_Extraction_ML_Syntax.mlty = uu____7353;
             FStar_Extraction_ML_Syntax.loc = uu____7354;_},e1::e2::_e3::[])
          when
          let uu____7364 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7364 = "FStar.Buffer.sub" ->
          let uu____7368 =
            let uu____7373 = translate_expr env e1  in
            let uu____7374 = translate_expr env e2  in
            (uu____7373, uu____7374)  in
          EBufSub uu____7368
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7376;
                  FStar_Extraction_ML_Syntax.loc = uu____7377;_},uu____7378);
             FStar_Extraction_ML_Syntax.mlty = uu____7379;
             FStar_Extraction_ML_Syntax.loc = uu____7380;_},e1::e2::_e3::[])
          when
          (let uu____7392 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7392 = "LowStar.Monotonic.Buffer.msub") ||
            (let uu____7397 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7397 = "LowStar.ConstBuffer.sub")
          ->
          let uu____7401 =
            let uu____7406 = translate_expr env e1  in
            let uu____7407 = translate_expr env e2  in
            (uu____7406, uu____7407)  in
          EBufSub uu____7401
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7409;
                  FStar_Extraction_ML_Syntax.loc = uu____7410;_},uu____7411);
             FStar_Extraction_ML_Syntax.mlty = uu____7412;
             FStar_Extraction_ML_Syntax.loc = uu____7413;_},e1::e2::[])
          when
          let uu____7422 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7422 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7427;
                  FStar_Extraction_ML_Syntax.loc = uu____7428;_},uu____7429);
             FStar_Extraction_ML_Syntax.mlty = uu____7430;
             FStar_Extraction_ML_Syntax.loc = uu____7431;_},e1::e2::[])
          when
          let uu____7440 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7440 = "FStar.Buffer.offset" ->
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
             FStar_Extraction_ML_Syntax.loc = uu____7456;_},e1::e2::[])
          when
          let uu____7465 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7465 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____7469 =
            let uu____7474 = translate_expr env e1  in
            let uu____7475 = translate_expr env e2  in
            (uu____7474, uu____7475)  in
          EBufSub uu____7469
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7477;
                  FStar_Extraction_ML_Syntax.loc = uu____7478;_},uu____7479);
             FStar_Extraction_ML_Syntax.mlty = uu____7480;
             FStar_Extraction_ML_Syntax.loc = uu____7481;_},e1::e2::e3::[])
          when
          (((let uu____7493 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7493 = "FStar.Buffer.upd") ||
              (let uu____7498 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7498 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____7503 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7503 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____7508 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7508 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____7512 =
            let uu____7519 = translate_expr env e1  in
            let uu____7520 = translate_expr env e2  in
            let uu____7521 = translate_expr env e3  in
            (uu____7519, uu____7520, uu____7521)  in
          EBufWrite uu____7512
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7523;
                  FStar_Extraction_ML_Syntax.loc = uu____7524;_},uu____7525);
             FStar_Extraction_ML_Syntax.mlty = uu____7526;
             FStar_Extraction_ML_Syntax.loc = uu____7527;_},e1::e2::[])
          when
          let uu____7536 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7536 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____7540 =
            let uu____7547 = translate_expr env e1  in
            let uu____7548 = translate_expr env e2  in
            (uu____7547, (EConstant (UInt32, "0")), uu____7548)  in
          EBufWrite uu____7540
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7552;
             FStar_Extraction_ML_Syntax.loc = uu____7553;_},uu____7554::[])
          when
          let uu____7557 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7557 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7562;
             FStar_Extraction_ML_Syntax.loc = uu____7563;_},uu____7564::[])
          when
          let uu____7567 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7567 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7572;
                  FStar_Extraction_ML_Syntax.loc = uu____7573;_},uu____7574);
             FStar_Extraction_ML_Syntax.mlty = uu____7575;
             FStar_Extraction_ML_Syntax.loc = uu____7576;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____7590 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7590 = "FStar.Buffer.blit") ||
             (let uu____7595 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7595 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____7600 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7600 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____7604 =
            let uu____7615 = translate_expr env e1  in
            let uu____7616 = translate_expr env e2  in
            let uu____7617 = translate_expr env e3  in
            let uu____7618 = translate_expr env e4  in
            let uu____7619 = translate_expr env e5  in
            (uu____7615, uu____7616, uu____7617, uu____7618, uu____7619)  in
          EBufBlit uu____7604
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7621;
                  FStar_Extraction_ML_Syntax.loc = uu____7622;_},uu____7623);
             FStar_Extraction_ML_Syntax.mlty = uu____7624;
             FStar_Extraction_ML_Syntax.loc = uu____7625;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____7641 =
            let uu____7648 = translate_expr env e1  in
            let uu____7649 = translate_expr env e2  in
            let uu____7650 = translate_expr env e3  in
            (uu____7648, uu____7649, uu____7650)  in
          EBufFill uu____7641
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7652;
             FStar_Extraction_ML_Syntax.loc = uu____7653;_},uu____7654::[])
          when
          let uu____7657 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7657 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7662;
                  FStar_Extraction_ML_Syntax.loc = uu____7663;_},uu____7664);
             FStar_Extraction_ML_Syntax.mlty = uu____7665;
             FStar_Extraction_ML_Syntax.loc = uu____7666;_},_ebuf::_eseq::[])
          when
          (((let uu____7677 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7677 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____7682 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7682 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____7687 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7687 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____7692 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7692 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
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
             FStar_Extraction_ML_Syntax.loc = uu____7701;_},e1::[])
          when
          (let uu____7711 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7711 = "LowStar.ConstBuffer.of_buffer") ||
            (let uu____7716 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7716 = "LowStar.ConstBuffer.of_ibuffer")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7721;
                  FStar_Extraction_ML_Syntax.loc = uu____7722;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____7724;
             FStar_Extraction_ML_Syntax.loc = uu____7725;_},e1::[])
          when
          ((let uu____7733 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7733 = "LowStar.ConstBuffer.cast") ||
             (let uu____7738 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7738 = "LowStar.ConstBuffer.to_buffer"))
            ||
            (let uu____7743 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7743 = "LowStar.ConstBuffer.to_ibuffer")
          ->
          let uu____7747 =
            let uu____7752 = translate_expr env e1  in
            let uu____7753 =
              let uu____7754 = translate_type env t  in TBuf uu____7754  in
            (uu____7752, uu____7753)  in
          ECast uu____7747
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7756;
             FStar_Extraction_ML_Syntax.loc = uu____7757;_},e1::[])
          when
          let uu____7761 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7761 = "Obj.repr" ->
          let uu____7765 =
            let uu____7770 = translate_expr env e1  in (uu____7770, TAny)  in
          ECast uu____7765
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7773;
             FStar_Extraction_ML_Syntax.loc = uu____7774;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____7790 = FStar_Util.must (mk_width m)  in
          let uu____7791 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____7790 uu____7791 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7793;
             FStar_Extraction_ML_Syntax.loc = uu____7794;_},args)
          when is_bool_op op ->
          let uu____7808 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____7808 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7810;
             FStar_Extraction_ML_Syntax.loc = uu____7811;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7813;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7814;_}::[])
          when is_machine_int m ->
          let uu____7839 =
            let uu____7845 = FStar_Util.must (mk_width m)  in (uu____7845, c)
             in
          EConstant uu____7839
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7848;
             FStar_Extraction_ML_Syntax.loc = uu____7849;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7851;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7852;_}::[])
          when is_machine_int m ->
          let uu____7877 =
            let uu____7883 = FStar_Util.must (mk_width m)  in (uu____7883, c)
             in
          EConstant uu____7877
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7885;
             FStar_Extraction_ML_Syntax.loc = uu____7886;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7888;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7889;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7902 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7904;
             FStar_Extraction_ML_Syntax.loc = uu____7905;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7907;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7908;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7925 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7927;
             FStar_Extraction_ML_Syntax.loc = uu____7928;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7930;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7931;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____7946 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[],"buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7948;
             FStar_Extraction_ML_Syntax.loc = uu____7949;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7951;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7952;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____7967 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____7970;
             FStar_Extraction_ML_Syntax.loc = uu____7971;_},arg::[])
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
            let uu____7999 =
              let uu____8004 = translate_expr env arg  in
              (uu____8004, (TInt UInt64))  in
            ECast uu____7999
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____8009 =
                 let uu____8014 = translate_expr env arg  in
                 (uu____8014, (TInt UInt32))  in
               ECast uu____8009)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____8019 =
                   let uu____8024 = translate_expr env arg  in
                   (uu____8024, (TInt UInt16))  in
                 ECast uu____8019)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____8029 =
                     let uu____8034 = translate_expr env arg  in
                     (uu____8034, (TInt UInt8))  in
                   ECast uu____8029)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____8039 =
                       let uu____8044 = translate_expr env arg  in
                       (uu____8044, (TInt Int64))  in
                     ECast uu____8039)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____8049 =
                         let uu____8054 = translate_expr env arg  in
                         (uu____8054, (TInt Int32))  in
                       ECast uu____8049)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____8059 =
                           let uu____8064 = translate_expr env arg  in
                           (uu____8064, (TInt Int16))  in
                         ECast uu____8059)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____8069 =
                             let uu____8074 = translate_expr env arg  in
                             (uu____8074, (TInt Int8))  in
                           ECast uu____8069)
                        else
                          (let uu____8077 =
                             let uu____8084 =
                               let uu____8087 = translate_expr env arg  in
                               [uu____8087]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____8084)
                              in
                           EApp uu____8077)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____8107 =
            let uu____8114 = translate_expr env head1  in
            let uu____8115 = FStar_List.map (translate_expr env) args  in
            (uu____8114, uu____8115)  in
          EApp uu____8107
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____8126 =
            let uu____8133 = translate_expr env head1  in
            let uu____8134 = FStar_List.map (translate_type env) ty_args  in
            (uu____8133, uu____8134)  in
          ETypApp uu____8126
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____8142 =
            let uu____8147 = translate_expr env e1  in
            let uu____8148 = translate_type env t_to  in
            (uu____8147, uu____8148)  in
          ECast uu____8142
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____8149,fields) ->
          let uu____8171 =
            let uu____8183 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8184 =
              FStar_List.map
                (fun uu____8206  ->
                   match uu____8206 with
                   | (field,expr) ->
                       let uu____8221 = translate_expr env expr  in
                       (field, uu____8221)) fields
               in
            (uu____8183, uu____8184)  in
          EFlat uu____8171
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____8232 =
            let uu____8240 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____8241 = translate_expr env e1  in
            (uu____8240, uu____8241, (FStar_Pervasives_Native.snd path))  in
          EField uu____8232
      | FStar_Extraction_ML_Syntax.MLE_Let uu____8247 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____8260) ->
          let uu____8265 =
            let uu____8267 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____8267
             in
          failwith uu____8265
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____8279 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____8279
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____8285 = FStar_List.map (translate_expr env) es  in
          ETuple uu____8285
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____8288,cons1),es) ->
          let uu____8303 =
            let uu____8313 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8314 = FStar_List.map (translate_expr env) es  in
            (uu____8313, cons1, uu____8314)  in
          ECons uu____8303
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____8340 =
            let uu____8349 = translate_expr env1 body  in
            let uu____8350 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____8349, uu____8350)  in
          EFun uu____8340
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____8360 =
            let uu____8367 = translate_expr env e1  in
            let uu____8368 = translate_expr env e2  in
            let uu____8369 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____8367, uu____8368, uu____8369)  in
          EIfThenElse uu____8360
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____8371 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____8379 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____8395 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > Prims.int_zero
          then
            let uu____8413 =
              let uu____8428 = FStar_List.map (translate_type env) ts  in
              (lid, uu____8428)  in
            TApp uu____8413
          else TQualified lid
      | uu____8443 ->
          let uu____8444 =
            let uu____8446 =
              FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
            FStar_Util.format1
              "invalid argument: expected MLTY_Named, got %s" uu____8446
             in
          failwith uu____8444

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
    fun uu____8480  ->
      match uu____8480 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____8507 = translate_pat env pat  in
            (match uu____8507 with
             | (env1,pat1) ->
                 let uu____8518 = translate_expr env1 expr  in
                 (pat1, uu____8518))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___7_8526  ->
    match uu___7_8526 with
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
          let uu____8593 =
            let uu____8594 =
              let uu____8600 = translate_width sw  in (uu____8600, s)  in
            PConstant uu____8594  in
          (env, uu____8593)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____8610,cons1),ps) ->
          let uu____8625 =
            FStar_List.fold_left
              (fun uu____8645  ->
                 fun p1  ->
                   match uu____8645 with
                   | (env1,acc) ->
                       let uu____8665 = translate_pat env1 p1  in
                       (match uu____8665 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8625 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____8695,ps) ->
          let uu____8717 =
            FStar_List.fold_left
              (fun uu____8754  ->
                 fun uu____8755  ->
                   match (uu____8754, uu____8755) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____8835 = translate_pat env1 p1  in
                       (match uu____8835 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____8717 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____8906 =
            FStar_List.fold_left
              (fun uu____8926  ->
                 fun p1  ->
                   match uu____8926 with
                   | (env1,acc) ->
                       let uu____8946 = translate_pat env1 p1  in
                       (match uu____8946 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8906 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____8973 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____8979 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____8993 =
            let uu____8995 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____8995
              (FStar_Util.for_some
                 (fun c1  -> c1 = (FStar_Char.char_of_int Prims.int_zero)))
             in
          if uu____8993
          then
            let uu____9010 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____9010
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____9037) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____9055 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____9057 ->
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
          let uu____9081 =
            let uu____9088 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____9088)  in
          EApp uu____9081

let (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____9100  ->
    match uu____9100 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____9149 = m  in
               match uu____9149 with
               | (path,uu____9164,uu____9165) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___1561_9183  ->
                  match () with
                  | () ->
                      ((let uu____9187 =
                          let uu____9189 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____9189  in
                        if uu____9187
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____9195 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____9195))) ()
             with
             | uu___1560_9198 ->
                 ((let uu____9202 = FStar_Util.print_exn uu___1560_9198  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____9202);
                  FStar_Pervasives_Native.None)) modules
  