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
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____4947  ->
    match uu____4947 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____4996 = m  in
               match uu____4996 with
               | (path,uu____5011,uu____5012) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___231_5030  ->
                  match () with
                  | () ->
                      ((let uu____5034 =
                          let uu____5036 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____5036  in
                        if uu____5034
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____5042 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____5042))) ()
             with
             | e ->
                 ((let uu____5051 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____5051);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____5054  ->
    match uu____5054 with
    | (module_name,modul,uu____5069) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____5104 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___3_5118  ->
         match uu___3_5118 with
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
         | uu____5131 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____5135 =
      FStar_List.choose
        (fun uu___4_5142  ->
           match uu___4_5142 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____5149 -> FStar_Pervasives_Native.None) flags
       in
    match uu____5135 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____5162 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____5176 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____5178 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____5183) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5210;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5213;_} when
            FStar_Util.for_some
              (fun uu___5_5218  ->
                 match uu___5_5218 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____5221 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            let arg_names =
              match e.FStar_Extraction_ML_Syntax.expr with
              | FStar_Extraction_ML_Syntax.MLE_Fun (args,uu____5244) ->
                  FStar_List.map FStar_Pervasives_Native.fst args
              | uu____5266 -> []  in
            if (FStar_List.length tvars) = Prims.int_zero
            then
              let uu____5274 =
                let uu____5275 =
                  let uu____5301 = translate_cc meta  in
                  let uu____5304 = translate_flags meta  in
                  let uu____5307 = translate_type env t0  in
                  (uu____5301, uu____5304, name1, uu____5307, arg_names)  in
                DExternal uu____5275  in
              FStar_Pervasives_Native.Some uu____5274
            else
              ((let uu____5326 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____5326);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5332;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____5335;
                FStar_Extraction_ML_Syntax.loc = uu____5336;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5338;_} ->
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
               let rec find_return_type eff i uu___6_5395 =
                 match uu___6_5395 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5404,eff1,t)
                     when i > Prims.int_zero ->
                     find_return_type eff1 (i - Prims.int_one) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____5424 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____5424 with
               | (i,eff,t) ->
                   (if i > Prims.int_zero
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____5450 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____5450 msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5468) ->
                           let uu____5469 = translate_flags meta  in
                           MustDisappear :: uu____5469
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____5472 = translate_flags meta  in
                           MustDisappear :: uu____5472
                       | uu____5475 -> translate_flags meta  in
                     try
                       (fun uu___379_5484  ->
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
                         ((let uu____5516 =
                             let uu____5522 =
                               let uu____5524 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____5524 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____5522)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____5516);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5550;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5553;_} ->
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
                 (fun uu___406_5590  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____5614 =
                       let uu____5620 =
                         let uu____5622 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____5624 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____5622
                           uu____5624
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____5620)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____5614);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5642;
            FStar_Extraction_ML_Syntax.mllb_def = uu____5643;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____5644;
            FStar_Extraction_ML_Syntax.print_typ = uu____5645;_} ->
            ((let uu____5652 =
                let uu____5658 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____5658)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____5652);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____5665 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____5665
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____5679 = ty  in
      match uu____5679 with
      | (uu____5682,uu____5683,uu____5684,uu____5685,flags,uu____5687) ->
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
                     (let uu____5761 =
                        let uu____5762 =
                          let uu____5782 = translate_flags flags1  in
                          let uu____5785 = translate_type env1 t  in
                          (name1, uu____5782, (FStar_List.length args),
                            uu____5785)
                           in
                        DTypeAlias uu____5762  in
                      FStar_Pervasives_Native.Some uu____5761)
             | (uu____5798,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____5843 =
                   let uu____5844 =
                     let uu____5876 = translate_flags flags1  in
                     let uu____5879 =
                       FStar_List.map
                         (fun uu____5911  ->
                            match uu____5911 with
                            | (f,t) ->
                                let uu____5931 =
                                  let uu____5937 = translate_type env1 t  in
                                  (uu____5937, false)  in
                                (f, uu____5931)) fields
                        in
                     (name1, uu____5876, (FStar_List.length args),
                       uu____5879)
                      in
                   DTypeFlat uu____5844  in
                 FStar_Pervasives_Native.Some uu____5843
             | (uu____5970,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____6020 =
                   let uu____6021 =
                     let uu____6060 =
                       FStar_List.map
                         (fun uu____6113  ->
                            match uu____6113 with
                            | (cons1,ts) ->
                                let uu____6161 =
                                  FStar_List.map
                                    (fun uu____6193  ->
                                       match uu____6193 with
                                       | (name2,t) ->
                                           let uu____6213 =
                                             let uu____6219 =
                                               translate_type env1 t  in
                                             (uu____6219, false)  in
                                           (name2, uu____6213)) ts
                                   in
                                (cons1, uu____6161)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____6060)
                      in
                   DTypeVariant uu____6021  in
                 FStar_Pervasives_Native.Some uu____6020
             | (uu____6272,name,_mangled_name,uu____6275,uu____6276,uu____6277)
                 ->
                 ((let uu____6293 =
                     let uu____6299 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____6299)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____6293);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____6307 = find_t env name  in TBound uu____6307
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____6310,t2) ->
          let uu____6312 =
            let uu____6317 = translate_type env t1  in
            let uu____6318 = translate_type env t2  in
            (uu____6317, uu____6318)  in
          TArrow uu____6312
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6322 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6322 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6329 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6329 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____6346 = FStar_Util.must (mk_width m)  in TInt uu____6346
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____6360 = FStar_Util.must (mk_width m)  in TInt uu____6360
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6365 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6365 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____6369::arg::uu____6371::[],p) when
          (((let uu____6377 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6377 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____6382 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6382 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____6387 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6387 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____6392 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6392 = "FStar.HyperStack.ST.s_mref")
          -> let uu____6396 = translate_type env arg  in TBuf uu____6396
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____6398::[],p) when
          ((((((((((let uu____6404 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6404 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____6409 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6409 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____6414 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6414 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____6419 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6419 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____6424 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6424 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____6429 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6429 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____6434 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6434 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____6439 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6439 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____6444 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6444 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____6449 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6449 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____6454 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6454 = "FStar.HyperStack.ST.mmmref")
          -> let uu____6458 = translate_type env arg  in TBuf uu____6458
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____6460::uu____6461::[],p) when
          let uu____6465 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6465 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____6469 = translate_type env arg  in TBuf uu____6469
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6474 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6474 = "LowStar.ConstBuffer.const_buffer" ->
          let uu____6478 = translate_type env arg  in TConstBuf uu____6478
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____6485 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6485 = "FStar.Buffer.buffer") ||
                        (let uu____6490 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____6490 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____6495 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____6495 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____6500 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6500 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____6505 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6505 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____6510 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6510 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____6515 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6515 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____6520 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6520 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____6525 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6525 = "FStar.HyperStack.mmref"))
                ||
                (let uu____6530 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6530 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____6535 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6535 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____6540 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6540 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____6545 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6545 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____6550 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6550 = "FStar.HyperStack.ST.mmref")
          -> let uu____6554 = translate_type env arg  in TBuf uu____6554
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6555::arg::[],p) when
          (let uu____6562 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6562 = "FStar.HyperStack.s_ref") ||
            (let uu____6567 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6567 = "FStar.HyperStack.ST.s_ref")
          -> let uu____6571 = translate_type env arg  in TBuf uu____6571
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6572::[],p) when
          let uu____6576 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6576 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____6628 = FStar_List.map (translate_type env) args  in
          TTuple uu____6628
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > Prims.int_zero
          then
            let uu____6639 =
              let uu____6654 = FStar_List.map (translate_type env) args  in
              (lid, uu____6654)  in
            TApp uu____6639
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____6672 = FStar_List.map (translate_type env) ts  in
          TTuple uu____6672

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
    fun uu____6690  ->
      match uu____6690 with
      | (name,typ) ->
          let uu____6700 = translate_type env typ  in
          { name; typ = uu____6700; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____6707 = find env name  in EBound uu____6707
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____6721 =
            let uu____6726 = FStar_Util.must (mk_op op)  in
            let uu____6727 = FStar_Util.must (mk_width m)  in
            (uu____6726, uu____6727)  in
          EOp uu____6721
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____6737 =
            let uu____6742 = FStar_Util.must (mk_bool_op op)  in
            (uu____6742, Bool)  in
          EOp uu____6737
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
            let uu____6765 = translate_type env typ  in
            { name; typ = uu____6765; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____6792 =
            let uu____6803 = translate_expr env expr  in
            let uu____6804 = translate_branches env branches  in
            (uu____6803, uu____6804)  in
          EMatch uu____6792
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6818;
                  FStar_Extraction_ML_Syntax.loc = uu____6819;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6821;
             FStar_Extraction_ML_Syntax.loc = uu____6822;_},arg::[])
          when
          let uu____6828 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6828 = "FStar.Dyn.undyn" ->
          let uu____6832 =
            let uu____6837 = translate_expr env arg  in
            let uu____6838 = translate_type env t  in
            (uu____6837, uu____6838)  in
          ECast uu____6832
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6840;
                  FStar_Extraction_ML_Syntax.loc = uu____6841;_},uu____6842);
             FStar_Extraction_ML_Syntax.mlty = uu____6843;
             FStar_Extraction_ML_Syntax.loc = uu____6844;_},uu____6845)
          when
          let uu____6854 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6854 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6859;
                  FStar_Extraction_ML_Syntax.loc = uu____6860;_},uu____6861);
             FStar_Extraction_ML_Syntax.mlty = uu____6862;
             FStar_Extraction_ML_Syntax.loc = uu____6863;_},arg::[])
          when
          ((let uu____6873 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6873 = "FStar.HyperStack.All.failwith") ||
             (let uu____6878 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6878 = "FStar.Error.unexpected"))
            ||
            (let uu____6883 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6883 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____6888;
               FStar_Extraction_ML_Syntax.loc = uu____6889;_} -> EAbortS msg
           | uu____6891 ->
               let print7 =
                 let uu____6893 =
                   let uu____6894 =
                     let uu____6895 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____6895
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____6894  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____6893
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
                  FStar_Extraction_ML_Syntax.mlty = uu____6902;
                  FStar_Extraction_ML_Syntax.loc = uu____6903;_},uu____6904);
             FStar_Extraction_ML_Syntax.mlty = uu____6905;
             FStar_Extraction_ML_Syntax.loc = uu____6906;_},e1::[])
          when
          (let uu____6916 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6916 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____6921 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6921 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6926;
                  FStar_Extraction_ML_Syntax.loc = uu____6927;_},uu____6928);
             FStar_Extraction_ML_Syntax.mlty = uu____6929;
             FStar_Extraction_ML_Syntax.loc = uu____6930;_},e1::e2::[])
          when
          ((((let uu____6941 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6941 = "FStar.Buffer.index") ||
               (let uu____6946 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6946 = "FStar.Buffer.op_Array_Access"))
              ||
              (let uu____6951 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6951 = "LowStar.Monotonic.Buffer.index"))
             ||
             (let uu____6956 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6956 = "LowStar.UninitializedBuffer.uindex"))
            ||
            (let uu____6961 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6961 = "LowStar.ConstBuffer.index")
          ->
          let uu____6965 =
            let uu____6970 = translate_expr env e1  in
            let uu____6971 = translate_expr env e2  in
            (uu____6970, uu____6971)  in
          EBufRead uu____6965
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6973;
                  FStar_Extraction_ML_Syntax.loc = uu____6974;_},uu____6975);
             FStar_Extraction_ML_Syntax.mlty = uu____6976;
             FStar_Extraction_ML_Syntax.loc = uu____6977;_},e1::[])
          when
          let uu____6985 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6985 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____6989 =
            let uu____6994 = translate_expr env e1  in
            (uu____6994, (EConstant (UInt32, "0")))  in
          EBufRead uu____6989
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6998;
                  FStar_Extraction_ML_Syntax.loc = uu____6999;_},uu____7000);
             FStar_Extraction_ML_Syntax.mlty = uu____7001;
             FStar_Extraction_ML_Syntax.loc = uu____7002;_},e1::e2::[])
          when
          ((let uu____7013 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7013 = "FStar.Buffer.create") ||
             (let uu____7018 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7018 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____7023 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7023 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____7027 =
            let uu____7034 = translate_expr env e1  in
            let uu____7035 = translate_expr env e2  in
            (Stack, uu____7034, uu____7035)  in
          EBufCreate uu____7027
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
             FStar_Extraction_ML_Syntax.loc = uu____7041;_},elen::[])
          when
          let uu____7049 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7049 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____7053 =
            let uu____7058 = translate_expr env elen  in (Stack, uu____7058)
             in
          EBufCreateNoInit uu____7053
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7060;
                  FStar_Extraction_ML_Syntax.loc = uu____7061;_},uu____7062);
             FStar_Extraction_ML_Syntax.mlty = uu____7063;
             FStar_Extraction_ML_Syntax.loc = uu____7064;_},init1::[])
          when
          let uu____7072 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7072 = "FStar.HyperStack.ST.salloc" ->
          let uu____7076 =
            let uu____7083 = translate_expr env init1  in
            (Stack, uu____7083, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7076
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7087;
                  FStar_Extraction_ML_Syntax.loc = uu____7088;_},uu____7089);
             FStar_Extraction_ML_Syntax.mlty = uu____7090;
             FStar_Extraction_ML_Syntax.loc = uu____7091;_},e2::[])
          when
          ((let uu____7101 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7101 = "FStar.Buffer.createL") ||
             (let uu____7106 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7106 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____7111 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7111 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____7115 =
            let uu____7122 =
              let uu____7125 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7125  in
            (Stack, uu____7122)  in
          EBufCreateL uu____7115
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7131;
                  FStar_Extraction_ML_Syntax.loc = uu____7132;_},uu____7133);
             FStar_Extraction_ML_Syntax.mlty = uu____7134;
             FStar_Extraction_ML_Syntax.loc = uu____7135;_},_erid::e2::[])
          when
          (let uu____7146 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7146 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____7151 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7151 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____7155 =
            let uu____7162 =
              let uu____7165 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7165  in
            (Eternal, uu____7162)  in
          EBufCreateL uu____7155
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7171;
                  FStar_Extraction_ML_Syntax.loc = uu____7172;_},uu____7173);
             FStar_Extraction_ML_Syntax.mlty = uu____7174;
             FStar_Extraction_ML_Syntax.loc = uu____7175;_},_rid::init1::[])
          when
          let uu____7184 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7184 = "FStar.HyperStack.ST.ralloc" ->
          let uu____7188 =
            let uu____7195 = translate_expr env init1  in
            (Eternal, uu____7195, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7188
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7199;
                  FStar_Extraction_ML_Syntax.loc = uu____7200;_},uu____7201);
             FStar_Extraction_ML_Syntax.mlty = uu____7202;
             FStar_Extraction_ML_Syntax.loc = uu____7203;_},_e0::e1::e2::[])
          when
          ((let uu____7215 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7215 = "FStar.Buffer.rcreate") ||
             (let uu____7220 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7220 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____7225 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7225 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____7229 =
            let uu____7236 = translate_expr env e1  in
            let uu____7237 = translate_expr env e2  in
            (Eternal, uu____7236, uu____7237)  in
          EBufCreate uu____7229
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7239;
                  FStar_Extraction_ML_Syntax.loc = uu____7240;_},uu____7241);
             FStar_Extraction_ML_Syntax.mlty = uu____7242;
             FStar_Extraction_ML_Syntax.loc = uu____7243;_},uu____7244)
          when
          (((((let uu____7255 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7255 = "LowStar.Monotonic.Buffer.mgcmalloc_and_blit") ||
                (let uu____7260 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____7260 = "LowStar.Monotonic.Buffer.mmalloc_and_blit"))
               ||
               (let uu____7265 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____7265 = "LowStar.Monotonic.Buffer.malloca_and_blit"))
              ||
              (let uu____7270 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7270 = "LowStar.ImmutableBuffer.igcmalloc_and_blit"))
             ||
             (let uu____7275 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7275 = "LowStar.ImmutableBuffer.imalloc_and_blit"))
            ||
            (let uu____7280 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7280 = "LowStar.ImmutableBuffer.ialloca_and_blit")
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
                  FStar_Extraction_ML_Syntax.mlty = uu____7286;
                  FStar_Extraction_ML_Syntax.loc = uu____7287;_},uu____7288);
             FStar_Extraction_ML_Syntax.mlty = uu____7289;
             FStar_Extraction_ML_Syntax.loc = uu____7290;_},_erid::elen::[])
          when
          let uu____7299 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7299 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____7303 =
            let uu____7308 = translate_expr env elen  in
            (Eternal, uu____7308)  in
          EBufCreateNoInit uu____7303
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7310;
                  FStar_Extraction_ML_Syntax.loc = uu____7311;_},uu____7312);
             FStar_Extraction_ML_Syntax.mlty = uu____7313;
             FStar_Extraction_ML_Syntax.loc = uu____7314;_},_rid::init1::[])
          when
          let uu____7323 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7323 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____7327 =
            let uu____7334 = translate_expr env init1  in
            (ManuallyManaged, uu____7334, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7327
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7338;
                  FStar_Extraction_ML_Syntax.loc = uu____7339;_},uu____7340);
             FStar_Extraction_ML_Syntax.mlty = uu____7341;
             FStar_Extraction_ML_Syntax.loc = uu____7342;_},_e0::e1::e2::[])
          when
          (((let uu____7354 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7354 = "FStar.Buffer.rcreate_mm") ||
              (let uu____7359 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7359 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____7364 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7364 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____7369 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7369 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____7373 =
            let uu____7380 = translate_expr env e1  in
            let uu____7381 = translate_expr env e2  in
            (ManuallyManaged, uu____7380, uu____7381)  in
          EBufCreate uu____7373
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
             FStar_Extraction_ML_Syntax.loc = uu____7387;_},_erid::elen::[])
          when
          let uu____7396 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7396 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____7400 =
            let uu____7405 = translate_expr env elen  in
            (ManuallyManaged, uu____7405)  in
          EBufCreateNoInit uu____7400
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7407;
                  FStar_Extraction_ML_Syntax.loc = uu____7408;_},uu____7409);
             FStar_Extraction_ML_Syntax.mlty = uu____7410;
             FStar_Extraction_ML_Syntax.loc = uu____7411;_},e2::[])
          when
          let uu____7419 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7419 = "FStar.HyperStack.ST.rfree" ->
          let uu____7423 = translate_expr env e2  in EBufFree uu____7423
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7425;
                  FStar_Extraction_ML_Syntax.loc = uu____7426;_},uu____7427);
             FStar_Extraction_ML_Syntax.mlty = uu____7428;
             FStar_Extraction_ML_Syntax.loc = uu____7429;_},e2::[])
          when
          (let uu____7439 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7439 = "FStar.Buffer.rfree") ||
            (let uu____7444 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7444 = "LowStar.Monotonic.Buffer.free")
          -> let uu____7448 = translate_expr env e2  in EBufFree uu____7448
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7450;
                  FStar_Extraction_ML_Syntax.loc = uu____7451;_},uu____7452);
             FStar_Extraction_ML_Syntax.mlty = uu____7453;
             FStar_Extraction_ML_Syntax.loc = uu____7454;_},e1::e2::_e3::[])
          when
          let uu____7464 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7464 = "FStar.Buffer.sub" ->
          let uu____7468 =
            let uu____7473 = translate_expr env e1  in
            let uu____7474 = translate_expr env e2  in
            (uu____7473, uu____7474)  in
          EBufSub uu____7468
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7476;
                  FStar_Extraction_ML_Syntax.loc = uu____7477;_},uu____7478);
             FStar_Extraction_ML_Syntax.mlty = uu____7479;
             FStar_Extraction_ML_Syntax.loc = uu____7480;_},e1::e2::_e3::[])
          when
          (let uu____7492 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7492 = "LowStar.Monotonic.Buffer.msub") ||
            (let uu____7497 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7497 = "LowStar.ConstBuffer.sub")
          ->
          let uu____7501 =
            let uu____7506 = translate_expr env e1  in
            let uu____7507 = translate_expr env e2  in
            (uu____7506, uu____7507)  in
          EBufSub uu____7501
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7509;
                  FStar_Extraction_ML_Syntax.loc = uu____7510;_},uu____7511);
             FStar_Extraction_ML_Syntax.mlty = uu____7512;
             FStar_Extraction_ML_Syntax.loc = uu____7513;_},e1::e2::[])
          when
          let uu____7522 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7522 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7527;
                  FStar_Extraction_ML_Syntax.loc = uu____7528;_},uu____7529);
             FStar_Extraction_ML_Syntax.mlty = uu____7530;
             FStar_Extraction_ML_Syntax.loc = uu____7531;_},e1::e2::[])
          when
          let uu____7540 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7540 = "FStar.Buffer.offset" ->
          let uu____7544 =
            let uu____7549 = translate_expr env e1  in
            let uu____7550 = translate_expr env e2  in
            (uu____7549, uu____7550)  in
          EBufSub uu____7544
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7552;
                  FStar_Extraction_ML_Syntax.loc = uu____7553;_},uu____7554);
             FStar_Extraction_ML_Syntax.mlty = uu____7555;
             FStar_Extraction_ML_Syntax.loc = uu____7556;_},e1::e2::[])
          when
          let uu____7565 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7565 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____7569 =
            let uu____7574 = translate_expr env e1  in
            let uu____7575 = translate_expr env e2  in
            (uu____7574, uu____7575)  in
          EBufSub uu____7569
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7577;
                  FStar_Extraction_ML_Syntax.loc = uu____7578;_},uu____7579);
             FStar_Extraction_ML_Syntax.mlty = uu____7580;
             FStar_Extraction_ML_Syntax.loc = uu____7581;_},e1::e2::e3::[])
          when
          (((let uu____7593 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7593 = "FStar.Buffer.upd") ||
              (let uu____7598 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7598 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____7603 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7603 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____7608 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7608 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____7612 =
            let uu____7619 = translate_expr env e1  in
            let uu____7620 = translate_expr env e2  in
            let uu____7621 = translate_expr env e3  in
            (uu____7619, uu____7620, uu____7621)  in
          EBufWrite uu____7612
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7623;
                  FStar_Extraction_ML_Syntax.loc = uu____7624;_},uu____7625);
             FStar_Extraction_ML_Syntax.mlty = uu____7626;
             FStar_Extraction_ML_Syntax.loc = uu____7627;_},e1::e2::[])
          when
          let uu____7636 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7636 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____7640 =
            let uu____7647 = translate_expr env e1  in
            let uu____7648 = translate_expr env e2  in
            (uu____7647, (EConstant (UInt32, "0")), uu____7648)  in
          EBufWrite uu____7640
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7652;
             FStar_Extraction_ML_Syntax.loc = uu____7653;_},uu____7654::[])
          when
          let uu____7657 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7657 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7662;
             FStar_Extraction_ML_Syntax.loc = uu____7663;_},uu____7664::[])
          when
          let uu____7667 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7667 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7672;
                  FStar_Extraction_ML_Syntax.loc = uu____7673;_},uu____7674);
             FStar_Extraction_ML_Syntax.mlty = uu____7675;
             FStar_Extraction_ML_Syntax.loc = uu____7676;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____7690 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7690 = "FStar.Buffer.blit") ||
             (let uu____7695 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7695 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____7700 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7700 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____7704 =
            let uu____7715 = translate_expr env e1  in
            let uu____7716 = translate_expr env e2  in
            let uu____7717 = translate_expr env e3  in
            let uu____7718 = translate_expr env e4  in
            let uu____7719 = translate_expr env e5  in
            (uu____7715, uu____7716, uu____7717, uu____7718, uu____7719)  in
          EBufBlit uu____7704
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7721;
                  FStar_Extraction_ML_Syntax.loc = uu____7722;_},uu____7723);
             FStar_Extraction_ML_Syntax.mlty = uu____7724;
             FStar_Extraction_ML_Syntax.loc = uu____7725;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____7741 =
            let uu____7748 = translate_expr env e1  in
            let uu____7749 = translate_expr env e2  in
            let uu____7750 = translate_expr env e3  in
            (uu____7748, uu____7749, uu____7750)  in
          EBufFill uu____7741
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7752;
             FStar_Extraction_ML_Syntax.loc = uu____7753;_},uu____7754::[])
          when
          let uu____7757 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7757 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7762;
                  FStar_Extraction_ML_Syntax.loc = uu____7763;_},uu____7764);
             FStar_Extraction_ML_Syntax.mlty = uu____7765;
             FStar_Extraction_ML_Syntax.loc = uu____7766;_},_ebuf::_eseq::[])
          when
          (((let uu____7777 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7777 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____7782 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7782 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____7787 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7787 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____7792 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7792 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7797;
                  FStar_Extraction_ML_Syntax.loc = uu____7798;_},uu____7799);
             FStar_Extraction_ML_Syntax.mlty = uu____7800;
             FStar_Extraction_ML_Syntax.loc = uu____7801;_},e1::[])
          when
          (let uu____7811 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7811 = "LowStar.ConstBuffer.of_buffer") ||
            (let uu____7816 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7816 = "LowStar.ConstBuffer.of_ibuffer")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7821;
                  FStar_Extraction_ML_Syntax.loc = uu____7822;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____7824;
             FStar_Extraction_ML_Syntax.loc = uu____7825;_},e1::[])
          when
          ((let uu____7833 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7833 = "LowStar.ConstBuffer.cast") ||
             (let uu____7838 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7838 = "LowStar.ConstBuffer.to_buffer"))
            ||
            (let uu____7843 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7843 = "LowStar.ConstBuffer.to_ibuffer")
          ->
          let uu____7847 =
            let uu____7852 = translate_expr env e1  in
            let uu____7853 =
              let uu____7854 = translate_type env t  in TBuf uu____7854  in
            (uu____7852, uu____7853)  in
          ECast uu____7847
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7856;
             FStar_Extraction_ML_Syntax.loc = uu____7857;_},e1::[])
          when
          let uu____7861 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7861 = "Obj.repr" ->
          let uu____7865 =
            let uu____7870 = translate_expr env e1  in (uu____7870, TAny)  in
          ECast uu____7865
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7873;
             FStar_Extraction_ML_Syntax.loc = uu____7874;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____7890 = FStar_Util.must (mk_width m)  in
          let uu____7891 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____7890 uu____7891 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7893;
             FStar_Extraction_ML_Syntax.loc = uu____7894;_},args)
          when is_bool_op op ->
          let uu____7908 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____7908 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7910;
             FStar_Extraction_ML_Syntax.loc = uu____7911;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7913;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7914;_}::[])
          when is_machine_int m ->
          let uu____7939 =
            let uu____7945 = FStar_Util.must (mk_width m)  in (uu____7945, c)
             in
          EConstant uu____7939
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7948;
             FStar_Extraction_ML_Syntax.loc = uu____7949;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7951;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7952;_}::[])
          when is_machine_int m ->
          let uu____7977 =
            let uu____7983 = FStar_Util.must (mk_width m)  in (uu____7983, c)
             in
          EConstant uu____7977
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____7985;
             FStar_Extraction_ML_Syntax.loc = uu____7986;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7988;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7989;_}::[])
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
               ("C"::"Compat"::"String"::[],"of_literal");
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
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8025 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8027;
             FStar_Extraction_ML_Syntax.loc = uu____8028;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8030;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8031;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8046 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[],"buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8048;
             FStar_Extraction_ML_Syntax.loc = uu____8049;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8051;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8052;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____8067 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____8070;
             FStar_Extraction_ML_Syntax.loc = uu____8071;_},arg::[])
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
            let uu____8099 =
              let uu____8104 = translate_expr env arg  in
              (uu____8104, (TInt UInt64))  in
            ECast uu____8099
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____8109 =
                 let uu____8114 = translate_expr env arg  in
                 (uu____8114, (TInt UInt32))  in
               ECast uu____8109)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____8119 =
                   let uu____8124 = translate_expr env arg  in
                   (uu____8124, (TInt UInt16))  in
                 ECast uu____8119)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____8129 =
                     let uu____8134 = translate_expr env arg  in
                     (uu____8134, (TInt UInt8))  in
                   ECast uu____8129)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____8139 =
                       let uu____8144 = translate_expr env arg  in
                       (uu____8144, (TInt Int64))  in
                     ECast uu____8139)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____8149 =
                         let uu____8154 = translate_expr env arg  in
                         (uu____8154, (TInt Int32))  in
                       ECast uu____8149)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____8159 =
                           let uu____8164 = translate_expr env arg  in
                           (uu____8164, (TInt Int16))  in
                         ECast uu____8159)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____8169 =
                             let uu____8174 = translate_expr env arg  in
                             (uu____8174, (TInt Int8))  in
                           ECast uu____8169)
                        else
                          (let uu____8177 =
                             let uu____8184 =
                               let uu____8187 = translate_expr env arg  in
                               [uu____8187]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____8184)
                              in
                           EApp uu____8177)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____8207 =
            let uu____8214 = translate_expr env head1  in
            let uu____8215 = FStar_List.map (translate_expr env) args  in
            (uu____8214, uu____8215)  in
          EApp uu____8207
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____8226 =
            let uu____8233 = translate_expr env head1  in
            let uu____8234 = FStar_List.map (translate_type env) ty_args  in
            (uu____8233, uu____8234)  in
          ETypApp uu____8226
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____8242 =
            let uu____8247 = translate_expr env e1  in
            let uu____8248 = translate_type env t_to  in
            (uu____8247, uu____8248)  in
          ECast uu____8242
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____8249,fields) ->
          let uu____8271 =
            let uu____8283 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8284 =
              FStar_List.map
                (fun uu____8306  ->
                   match uu____8306 with
                   | (field,expr) ->
                       let uu____8321 = translate_expr env expr  in
                       (field, uu____8321)) fields
               in
            (uu____8283, uu____8284)  in
          EFlat uu____8271
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____8332 =
            let uu____8340 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____8341 = translate_expr env e1  in
            (uu____8340, uu____8341, (FStar_Pervasives_Native.snd path))  in
          EField uu____8332
      | FStar_Extraction_ML_Syntax.MLE_Let uu____8347 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____8360) ->
          let uu____8365 =
            let uu____8367 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____8367
             in
          failwith uu____8365
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____8379 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____8379
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____8385 = FStar_List.map (translate_expr env) es  in
          ETuple uu____8385
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____8388,cons1),es) ->
          let uu____8403 =
            let uu____8413 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8414 = FStar_List.map (translate_expr env) es  in
            (uu____8413, cons1, uu____8414)  in
          ECons uu____8403
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____8440 =
            let uu____8449 = translate_expr env1 body  in
            let uu____8450 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____8449, uu____8450)  in
          EFun uu____8440
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____8460 =
            let uu____8467 = translate_expr env e1  in
            let uu____8468 = translate_expr env e2  in
            let uu____8469 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____8467, uu____8468, uu____8469)  in
          EIfThenElse uu____8460
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____8471 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____8479 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____8495 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > Prims.int_zero
          then
            let uu____8513 =
              let uu____8528 = FStar_List.map (translate_type env) ts  in
              (lid, uu____8528)  in
            TApp uu____8513
          else TQualified lid
      | uu____8543 ->
          let uu____8544 =
            let uu____8546 =
              FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
            FStar_Util.format1
              "invalid argument: expected MLTY_Named, got %s" uu____8546
             in
          failwith uu____8544

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
    fun uu____8580  ->
      match uu____8580 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____8607 = translate_pat env pat  in
            (match uu____8607 with
             | (env1,pat1) ->
                 let uu____8618 = translate_expr env1 expr  in
                 (pat1, uu____8618))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___7_8626  ->
    match uu___7_8626 with
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
          let uu____8693 =
            let uu____8694 =
              let uu____8700 = translate_width sw  in (uu____8700, s)  in
            PConstant uu____8694  in
          (env, uu____8693)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____8710,cons1),ps) ->
          let uu____8725 =
            FStar_List.fold_left
              (fun uu____8745  ->
                 fun p1  ->
                   match uu____8745 with
                   | (env1,acc) ->
                       let uu____8765 = translate_pat env1 p1  in
                       (match uu____8765 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8725 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____8795,ps) ->
          let uu____8817 =
            FStar_List.fold_left
              (fun uu____8854  ->
                 fun uu____8855  ->
                   match (uu____8854, uu____8855) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____8935 = translate_pat env1 p1  in
                       (match uu____8935 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____8817 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____9006 =
            FStar_List.fold_left
              (fun uu____9026  ->
                 fun p1  ->
                   match uu____9026 with
                   | (env1,acc) ->
                       let uu____9046 = translate_pat env1 p1  in
                       (match uu____9046 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____9006 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____9073 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____9079 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____9093 =
            let uu____9095 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____9095
              (FStar_Util.for_some
                 (fun c1  -> c1 = (FStar_Char.char_of_int Prims.int_zero)))
             in
          if uu____9093
          then
            let uu____9110 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____9110
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____9137) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____9155 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____9157 ->
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
          let uu____9181 =
            let uu____9188 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____9188)  in
          EApp uu____9181
