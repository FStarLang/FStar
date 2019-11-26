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
    match projectee with | DGlobal _0 -> true | uu____753 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____864 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____989 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____1096 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DUnusedRetainedForBackwardsCompat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DUnusedRetainedForBackwardsCompat _0 -> true
    | uu____1228 -> false
  
let (__proj__DUnusedRetainedForBackwardsCompat__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  =
  fun projectee  ->
    match projectee with | DUnusedRetainedForBackwardsCompat _0 -> _0
  
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____1345 -> false
  
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
    | uu____1486 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____1554 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ * Prims.string Prims.list))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1647 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1658 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1669 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1680 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1691 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1702 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1713 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1724 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1737 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1758 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1771 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1794 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1817 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____1838 -> false
  
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | IfDef  -> true | uu____1849 -> false
  
let (uu___is_Macro : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Macro  -> true | uu____1860 -> false
  
let (uu___is_Deprecated : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Deprecated _0 -> true | uu____1873 -> false
  
let (__proj__Deprecated__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Deprecated _0 -> _0 
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1894 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1905 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1916 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1929 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1959 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____2007 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____2040 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____2058 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____2101 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____2144 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____2187 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____2226 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____2255 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____2292 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____2333 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____2370 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____2411 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____2452 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____2511 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____2564 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____2599 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____2629 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____2640 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____2653 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____2674 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____2685 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____2697 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____2727 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____2786 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____2830 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____2867 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2906 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2940 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____2992 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____3030 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____3060 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____3104 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____3126 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____3149 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_EAbortT : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortT _0 -> true | uu____3185 -> false
  
let (__proj__EAbortT__item___0 : expr -> (Prims.string * typ)) =
  fun projectee  -> match projectee with | EAbortT _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____3218 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____3229 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____3240 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____3251 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____3262 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____3273 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____3284 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____3295 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____3306 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____3317 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____3328 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____3339 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____3350 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____3361 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____3372 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____3383 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____3394 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____3405 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____3416 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____3427 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____3438 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____3449 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____3460 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____3471 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____3482 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____3493 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____3506 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____3528 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____3554 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____3596 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____3628 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____3673 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____3706 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____3717 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____3728 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____3739 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____3750 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____3761 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____3772 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____3783 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____3794 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____3805 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____3854 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____3873 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____3891 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____3911 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____3953 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____3964 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____3980 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____4012 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____4048 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____4111 -> false
  
let (__proj__TTuple__item___0 : typ -> typ Prims.list) =
  fun projectee  -> match projectee with | TTuple _0 -> _0 
let (uu___is_TConstBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TConstBuf _0 -> true | uu____4136 -> false
  
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
  'Auu____4231 'Auu____4232 'Auu____4233 .
    ('Auu____4231 * 'Auu____4232 * 'Auu____4233) -> 'Auu____4231
  = fun uu____4244  -> match uu____4244 with | (x,uu____4252,uu____4253) -> x 
let snd3 :
  'Auu____4263 'Auu____4264 'Auu____4265 .
    ('Auu____4263 * 'Auu____4264 * 'Auu____4265) -> 'Auu____4264
  = fun uu____4276  -> match uu____4276 with | (uu____4283,x,uu____4285) -> x 
let thd3 :
  'Auu____4295 'Auu____4296 'Auu____4297 .
    ('Auu____4295 * 'Auu____4296 * 'Auu____4297) -> 'Auu____4297
  = fun uu____4308  -> match uu____4308 with | (uu____4315,uu____4316,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___0_4326  ->
    match uu___0_4326 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____4338 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___1_4348  ->
    match uu___1_4348 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____4357 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___2_4378  ->
    match uu___2_4378 with
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
    | uu____4423 -> FStar_Pervasives_Native.None
  
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
      let uu___166_4579 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___166_4579.names_t);
        module_name = (uu___166_4579.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___170_4593 = env  in
      {
        names = (uu___170_4593.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___170_4593.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____4608 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____4608 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___181_4632  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___180_4639 ->
          let uu____4641 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4641
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___190_4661  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___189_4670 ->
          let uu____4672 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4672
  
let add_binders :
  'Auu____4683 . env -> (Prims.string * 'Auu____4683) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____4718  ->
             match uu____4718 with | (name,uu____4725) -> extend env1 name)
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
      | uu____4777 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____4996  ->
    match uu____4996 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____5045 = m  in
               match uu____5045 with
               | (path,uu____5060,uu____5061) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___232_5079  ->
                  match () with
                  | () ->
                      ((let uu____5083 =
                          let uu____5085 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____5085  in
                        if uu____5083
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____5091 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____5091))) ()
             with
             | e ->
                 ((let uu____5100 = FStar_Util.print_exn e  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____5100);
                  FStar_Pervasives_Native.None)) modules

and (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun uu____5103  ->
    match uu____5103 with
    | (module_name,modul,uu____5118) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____5153 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___3_5167  ->
         match uu___3_5167 with
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
         | uu____5180 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____5184 =
      FStar_List.choose
        (fun uu___4_5191  ->
           match uu___4_5191 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____5198 -> FStar_Pervasives_Native.None) flags
       in
    match uu____5184 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____5211 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____5225 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____5227 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____5232) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5259;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5262;_} when
            FStar_Util.for_some
              (fun uu___5_5267  ->
                 match uu___5_5267 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____5270 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            let arg_names =
              match e.FStar_Extraction_ML_Syntax.expr with
              | FStar_Extraction_ML_Syntax.MLE_Fun (args,uu____5293) ->
                  FStar_List.map FStar_Pervasives_Native.fst args
              | uu____5315 -> []  in
            if (FStar_List.length tvars) = Prims.int_zero
            then
              let uu____5323 =
                let uu____5324 =
                  let uu____5350 = translate_cc meta  in
                  let uu____5353 = translate_flags meta  in
                  let uu____5356 = translate_type env t0  in
                  (uu____5350, uu____5353, name1, uu____5356, arg_names)  in
                DExternal uu____5324  in
              FStar_Pervasives_Native.Some uu____5323
            else
              ((let uu____5375 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____5375);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5381;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____5384;
                FStar_Extraction_ML_Syntax.loc = uu____5385;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5387;_} ->
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
               let rec find_return_type eff i uu___6_5444 =
                 match uu___6_5444 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5453,eff1,t)
                     when i > Prims.int_zero ->
                     find_return_type eff1 (i - Prims.int_one) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____5473 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____5473 with
               | (i,eff,t) ->
                   (if i > Prims.int_zero
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____5499 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____5499 msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5517) ->
                           let uu____5518 = translate_flags meta  in
                           MustDisappear :: uu____5518
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____5521 = translate_flags meta  in
                           MustDisappear :: uu____5521
                       | uu____5524 -> translate_flags meta  in
                     try
                       (fun uu___380_5533  ->
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
                         ((let uu____5565 =
                             let uu____5571 =
                               let uu____5573 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____5573 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____5571)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____5565);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5599;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5602;_} ->
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
                 (fun uu___407_5639  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____5663 =
                       let uu____5669 =
                         let uu____5671 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____5673 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____5671
                           uu____5673
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____5669)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____5663);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5691;
            FStar_Extraction_ML_Syntax.mllb_def = uu____5692;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____5693;
            FStar_Extraction_ML_Syntax.print_typ = uu____5694;_} ->
            ((let uu____5701 =
                let uu____5707 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____5707)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____5701);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____5714 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____5714
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____5728 = ty  in
      match uu____5728 with
      | (uu____5731,uu____5732,uu____5733,uu____5734,flags,uu____5736) ->
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
                     (let uu____5810 =
                        let uu____5811 =
                          let uu____5831 = translate_flags flags1  in
                          let uu____5834 = translate_type env1 t  in
                          (name1, uu____5831, (FStar_List.length args),
                            uu____5834)
                           in
                        DTypeAlias uu____5811  in
                      FStar_Pervasives_Native.Some uu____5810)
             | (uu____5847,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____5892 =
                   let uu____5893 =
                     let uu____5925 = translate_flags flags1  in
                     let uu____5928 =
                       FStar_List.map
                         (fun uu____5960  ->
                            match uu____5960 with
                            | (f,t) ->
                                let uu____5980 =
                                  let uu____5986 = translate_type env1 t  in
                                  (uu____5986, false)  in
                                (f, uu____5980)) fields
                        in
                     (name1, uu____5925, (FStar_List.length args),
                       uu____5928)
                      in
                   DTypeFlat uu____5893  in
                 FStar_Pervasives_Native.Some uu____5892
             | (uu____6019,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____6069 =
                   let uu____6070 =
                     let uu____6109 =
                       FStar_List.map
                         (fun uu____6162  ->
                            match uu____6162 with
                            | (cons1,ts) ->
                                let uu____6210 =
                                  FStar_List.map
                                    (fun uu____6242  ->
                                       match uu____6242 with
                                       | (name2,t) ->
                                           let uu____6262 =
                                             let uu____6268 =
                                               translate_type env1 t  in
                                             (uu____6268, false)  in
                                           (name2, uu____6262)) ts
                                   in
                                (cons1, uu____6210)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____6109)
                      in
                   DTypeVariant uu____6070  in
                 FStar_Pervasives_Native.Some uu____6069
             | (uu____6321,name,_mangled_name,uu____6324,uu____6325,uu____6326)
                 ->
                 ((let uu____6342 =
                     let uu____6348 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____6348)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____6342);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____6356 = find_t env name  in TBound uu____6356
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____6359,t2) ->
          let uu____6361 =
            let uu____6366 = translate_type env t1  in
            let uu____6367 = translate_type env t2  in
            (uu____6366, uu____6367)  in
          TArrow uu____6361
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6371 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6371 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6378 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6378 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____6395 = FStar_Util.must (mk_width m)  in TInt uu____6395
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____6409 = FStar_Util.must (mk_width m)  in TInt uu____6409
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6414 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6414 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____6418::arg::uu____6420::[],p) when
          (((let uu____6426 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6426 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____6431 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6431 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____6436 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6436 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____6441 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6441 = "FStar.HyperStack.ST.s_mref")
          -> let uu____6445 = translate_type env arg  in TBuf uu____6445
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____6447::[],p) when
          ((((((((((let uu____6453 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6453 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____6458 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6458 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____6463 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6463 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____6468 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6468 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____6473 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6473 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____6478 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6478 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____6483 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6483 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____6488 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6488 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____6493 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6493 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____6498 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6498 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____6503 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6503 = "FStar.HyperStack.ST.mmmref")
          -> let uu____6507 = translate_type env arg  in TBuf uu____6507
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____6509::uu____6510::[],p) when
          let uu____6514 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6514 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____6518 = translate_type env arg  in TBuf uu____6518
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6523 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6523 = "LowStar.ConstBuffer.const_buffer" ->
          let uu____6527 = translate_type env arg  in TConstBuf uu____6527
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____6534 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6534 = "FStar.Buffer.buffer") ||
                        (let uu____6539 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____6539 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____6544 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____6544 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____6549 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6549 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____6554 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6554 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____6559 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6559 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____6564 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6564 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____6569 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6569 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____6574 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6574 = "FStar.HyperStack.mmref"))
                ||
                (let uu____6579 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6579 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____6584 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6584 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____6589 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6589 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____6594 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6594 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____6599 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6599 = "FStar.HyperStack.ST.mmref")
          -> let uu____6603 = translate_type env arg  in TBuf uu____6603
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6604::arg::[],p) when
          (let uu____6611 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6611 = "FStar.HyperStack.s_ref") ||
            (let uu____6616 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6616 = "FStar.HyperStack.ST.s_ref")
          -> let uu____6620 = translate_type env arg  in TBuf uu____6620
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6621::[],p) when
          let uu____6625 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6625 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____6677 = FStar_List.map (translate_type env) args  in
          TTuple uu____6677
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > Prims.int_zero
          then
            let uu____6688 =
              let uu____6703 = FStar_List.map (translate_type env) args  in
              (lid, uu____6703)  in
            TApp uu____6688
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____6721 = FStar_List.map (translate_type env) ts  in
          TTuple uu____6721

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
    fun uu____6739  ->
      match uu____6739 with
      | (name,typ) ->
          let uu____6749 = translate_type env typ  in
          { name; typ = uu____6749; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____6756 = find env name  in EBound uu____6756
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____6770 =
            let uu____6775 = FStar_Util.must (mk_op op)  in
            let uu____6776 = FStar_Util.must (mk_width m)  in
            (uu____6775, uu____6776)  in
          EOp uu____6770
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____6786 =
            let uu____6791 = FStar_Util.must (mk_bool_op op)  in
            (uu____6791, Bool)  in
          EOp uu____6786
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
            let uu____6814 = translate_type env typ  in
            { name; typ = uu____6814; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____6841 =
            let uu____6852 = translate_expr env expr  in
            let uu____6853 = translate_branches env branches  in
            (uu____6852, uu____6853)  in
          EMatch uu____6841
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6867;
                  FStar_Extraction_ML_Syntax.loc = uu____6868;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6870;
             FStar_Extraction_ML_Syntax.loc = uu____6871;_},arg::[])
          when
          let uu____6877 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6877 = "FStar.Dyn.undyn" ->
          let uu____6881 =
            let uu____6886 = translate_expr env arg  in
            let uu____6887 = translate_type env t  in
            (uu____6886, uu____6887)  in
          ECast uu____6881
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6889;
                  FStar_Extraction_ML_Syntax.loc = uu____6890;_},uu____6891);
             FStar_Extraction_ML_Syntax.mlty = uu____6892;
             FStar_Extraction_ML_Syntax.loc = uu____6893;_},uu____6894)
          when
          let uu____6903 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6903 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6908;
                  FStar_Extraction_ML_Syntax.loc = uu____6909;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6911;
             FStar_Extraction_ML_Syntax.loc = uu____6912;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_String
                                                                s);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____6914;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____6915;_}::[])
          when
          let uu____6921 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6921 = "LowStar.Failure.failwith" ->
          let uu____6925 =
            let uu____6931 = translate_type env t  in (s, uu____6931)  in
          EAbortT uu____6925
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6934;
                  FStar_Extraction_ML_Syntax.loc = uu____6935;_},uu____6936);
             FStar_Extraction_ML_Syntax.mlty = uu____6937;
             FStar_Extraction_ML_Syntax.loc = uu____6938;_},arg::[])
          when
          ((let uu____6948 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6948 = "FStar.HyperStack.All.failwith") ||
             (let uu____6953 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6953 = "FStar.Error.unexpected"))
            ||
            (let uu____6958 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6958 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____6963;
               FStar_Extraction_ML_Syntax.loc = uu____6964;_} -> EAbortS msg
           | uu____6966 ->
               let print7 =
                 let uu____6968 =
                   let uu____6969 =
                     let uu____6970 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____6970
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____6969  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____6968
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
                  FStar_Extraction_ML_Syntax.mlty = uu____6977;
                  FStar_Extraction_ML_Syntax.loc = uu____6978;_},uu____6979);
             FStar_Extraction_ML_Syntax.mlty = uu____6980;
             FStar_Extraction_ML_Syntax.loc = uu____6981;_},e1::[])
          when
          (let uu____6991 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6991 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____6996 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6996 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7001;
                  FStar_Extraction_ML_Syntax.loc = uu____7002;_},uu____7003);
             FStar_Extraction_ML_Syntax.mlty = uu____7004;
             FStar_Extraction_ML_Syntax.loc = uu____7005;_},e1::e2::[])
          when
          ((((let uu____7016 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7016 = "FStar.Buffer.index") ||
               (let uu____7021 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____7021 = "FStar.Buffer.op_Array_Access"))
              ||
              (let uu____7026 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7026 = "LowStar.Monotonic.Buffer.index"))
             ||
             (let uu____7031 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7031 = "LowStar.UninitializedBuffer.uindex"))
            ||
            (let uu____7036 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7036 = "LowStar.ConstBuffer.index")
          ->
          let uu____7040 =
            let uu____7045 = translate_expr env e1  in
            let uu____7046 = translate_expr env e2  in
            (uu____7045, uu____7046)  in
          EBufRead uu____7040
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7048;
                  FStar_Extraction_ML_Syntax.loc = uu____7049;_},uu____7050);
             FStar_Extraction_ML_Syntax.mlty = uu____7051;
             FStar_Extraction_ML_Syntax.loc = uu____7052;_},e1::[])
          when
          let uu____7060 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7060 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____7064 =
            let uu____7069 = translate_expr env e1  in
            (uu____7069, (EConstant (UInt32, "0")))  in
          EBufRead uu____7064
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7073;
                  FStar_Extraction_ML_Syntax.loc = uu____7074;_},uu____7075);
             FStar_Extraction_ML_Syntax.mlty = uu____7076;
             FStar_Extraction_ML_Syntax.loc = uu____7077;_},e1::e2::[])
          when
          ((let uu____7088 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7088 = "FStar.Buffer.create") ||
             (let uu____7093 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7093 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____7098 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7098 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____7102 =
            let uu____7109 = translate_expr env e1  in
            let uu____7110 = translate_expr env e2  in
            (Stack, uu____7109, uu____7110)  in
          EBufCreate uu____7102
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7112;
                  FStar_Extraction_ML_Syntax.loc = uu____7113;_},uu____7114);
             FStar_Extraction_ML_Syntax.mlty = uu____7115;
             FStar_Extraction_ML_Syntax.loc = uu____7116;_},elen::[])
          when
          let uu____7124 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7124 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____7128 =
            let uu____7133 = translate_expr env elen  in (Stack, uu____7133)
             in
          EBufCreateNoInit uu____7128
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7135;
                  FStar_Extraction_ML_Syntax.loc = uu____7136;_},uu____7137);
             FStar_Extraction_ML_Syntax.mlty = uu____7138;
             FStar_Extraction_ML_Syntax.loc = uu____7139;_},init1::[])
          when
          let uu____7147 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7147 = "FStar.HyperStack.ST.salloc" ->
          let uu____7151 =
            let uu____7158 = translate_expr env init1  in
            (Stack, uu____7158, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7151
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7162;
                  FStar_Extraction_ML_Syntax.loc = uu____7163;_},uu____7164);
             FStar_Extraction_ML_Syntax.mlty = uu____7165;
             FStar_Extraction_ML_Syntax.loc = uu____7166;_},e2::[])
          when
          ((let uu____7176 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7176 = "FStar.Buffer.createL") ||
             (let uu____7181 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7181 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____7186 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7186 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____7190 =
            let uu____7197 =
              let uu____7200 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7200  in
            (Stack, uu____7197)  in
          EBufCreateL uu____7190
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7206;
                  FStar_Extraction_ML_Syntax.loc = uu____7207;_},uu____7208);
             FStar_Extraction_ML_Syntax.mlty = uu____7209;
             FStar_Extraction_ML_Syntax.loc = uu____7210;_},_erid::e2::[])
          when
          (let uu____7221 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7221 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____7226 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7226 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____7230 =
            let uu____7237 =
              let uu____7240 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7240  in
            (Eternal, uu____7237)  in
          EBufCreateL uu____7230
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7246;
                  FStar_Extraction_ML_Syntax.loc = uu____7247;_},uu____7248);
             FStar_Extraction_ML_Syntax.mlty = uu____7249;
             FStar_Extraction_ML_Syntax.loc = uu____7250;_},_rid::init1::[])
          when
          let uu____7259 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7259 = "FStar.HyperStack.ST.ralloc" ->
          let uu____7263 =
            let uu____7270 = translate_expr env init1  in
            (Eternal, uu____7270, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7263
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7274;
                  FStar_Extraction_ML_Syntax.loc = uu____7275;_},uu____7276);
             FStar_Extraction_ML_Syntax.mlty = uu____7277;
             FStar_Extraction_ML_Syntax.loc = uu____7278;_},_e0::e1::e2::[])
          when
          ((let uu____7290 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7290 = "FStar.Buffer.rcreate") ||
             (let uu____7295 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7295 = "LowStar.Monotonic.Buffer.mgcmalloc"))
            ||
            (let uu____7300 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7300 = "LowStar.ImmutableBuffer.igcmalloc")
          ->
          let uu____7304 =
            let uu____7311 = translate_expr env e1  in
            let uu____7312 = translate_expr env e2  in
            (Eternal, uu____7311, uu____7312)  in
          EBufCreate uu____7304
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
             FStar_Extraction_ML_Syntax.loc = uu____7318;_},uu____7319)
          when
          (((((let uu____7330 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7330 = "LowStar.Monotonic.Buffer.mgcmalloc_and_blit") ||
                (let uu____7335 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____7335 = "LowStar.Monotonic.Buffer.mmalloc_and_blit"))
               ||
               (let uu____7340 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____7340 = "LowStar.Monotonic.Buffer.malloca_and_blit"))
              ||
              (let uu____7345 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7345 = "LowStar.ImmutableBuffer.igcmalloc_and_blit"))
             ||
             (let uu____7350 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7350 = "LowStar.ImmutableBuffer.imalloc_and_blit"))
            ||
            (let uu____7355 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7355 = "LowStar.ImmutableBuffer.ialloca_and_blit")
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
                  FStar_Extraction_ML_Syntax.mlty = uu____7361;
                  FStar_Extraction_ML_Syntax.loc = uu____7362;_},uu____7363);
             FStar_Extraction_ML_Syntax.mlty = uu____7364;
             FStar_Extraction_ML_Syntax.loc = uu____7365;_},_erid::elen::[])
          when
          let uu____7374 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7374 = "LowStar.UninitializedBuffer.ugcmalloc" ->
          let uu____7378 =
            let uu____7383 = translate_expr env elen  in
            (Eternal, uu____7383)  in
          EBufCreateNoInit uu____7378
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7385;
                  FStar_Extraction_ML_Syntax.loc = uu____7386;_},uu____7387);
             FStar_Extraction_ML_Syntax.mlty = uu____7388;
             FStar_Extraction_ML_Syntax.loc = uu____7389;_},_rid::init1::[])
          when
          let uu____7398 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7398 = "FStar.HyperStack.ST.ralloc_mm" ->
          let uu____7402 =
            let uu____7409 = translate_expr env init1  in
            (ManuallyManaged, uu____7409, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7402
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7413;
                  FStar_Extraction_ML_Syntax.loc = uu____7414;_},uu____7415);
             FStar_Extraction_ML_Syntax.mlty = uu____7416;
             FStar_Extraction_ML_Syntax.loc = uu____7417;_},_e0::e1::e2::[])
          when
          (((let uu____7429 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7429 = "FStar.Buffer.rcreate_mm") ||
              (let uu____7434 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7434 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____7439 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7439 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____7444 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7444 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____7448 =
            let uu____7455 = translate_expr env e1  in
            let uu____7456 = translate_expr env e2  in
            (ManuallyManaged, uu____7455, uu____7456)  in
          EBufCreate uu____7448
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7458;
                  FStar_Extraction_ML_Syntax.loc = uu____7459;_},uu____7460);
             FStar_Extraction_ML_Syntax.mlty = uu____7461;
             FStar_Extraction_ML_Syntax.loc = uu____7462;_},_erid::elen::[])
          when
          let uu____7471 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7471 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____7475 =
            let uu____7480 = translate_expr env elen  in
            (ManuallyManaged, uu____7480)  in
          EBufCreateNoInit uu____7475
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7482;
                  FStar_Extraction_ML_Syntax.loc = uu____7483;_},uu____7484);
             FStar_Extraction_ML_Syntax.mlty = uu____7485;
             FStar_Extraction_ML_Syntax.loc = uu____7486;_},e2::[])
          when
          let uu____7494 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7494 = "FStar.HyperStack.ST.rfree" ->
          let uu____7498 = translate_expr env e2  in EBufFree uu____7498
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7500;
                  FStar_Extraction_ML_Syntax.loc = uu____7501;_},uu____7502);
             FStar_Extraction_ML_Syntax.mlty = uu____7503;
             FStar_Extraction_ML_Syntax.loc = uu____7504;_},e2::[])
          when
          (let uu____7514 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7514 = "FStar.Buffer.rfree") ||
            (let uu____7519 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7519 = "LowStar.Monotonic.Buffer.free")
          -> let uu____7523 = translate_expr env e2  in EBufFree uu____7523
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7525;
                  FStar_Extraction_ML_Syntax.loc = uu____7526;_},uu____7527);
             FStar_Extraction_ML_Syntax.mlty = uu____7528;
             FStar_Extraction_ML_Syntax.loc = uu____7529;_},e1::e2::_e3::[])
          when
          let uu____7539 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7539 = "FStar.Buffer.sub" ->
          let uu____7543 =
            let uu____7548 = translate_expr env e1  in
            let uu____7549 = translate_expr env e2  in
            (uu____7548, uu____7549)  in
          EBufSub uu____7543
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7551;
                  FStar_Extraction_ML_Syntax.loc = uu____7552;_},uu____7553);
             FStar_Extraction_ML_Syntax.mlty = uu____7554;
             FStar_Extraction_ML_Syntax.loc = uu____7555;_},e1::e2::_e3::[])
          when
          (let uu____7567 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7567 = "LowStar.Monotonic.Buffer.msub") ||
            (let uu____7572 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7572 = "LowStar.ConstBuffer.sub")
          ->
          let uu____7576 =
            let uu____7581 = translate_expr env e1  in
            let uu____7582 = translate_expr env e2  in
            (uu____7581, uu____7582)  in
          EBufSub uu____7576
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7584;
                  FStar_Extraction_ML_Syntax.loc = uu____7585;_},uu____7586);
             FStar_Extraction_ML_Syntax.mlty = uu____7587;
             FStar_Extraction_ML_Syntax.loc = uu____7588;_},e1::e2::[])
          when
          let uu____7597 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7597 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7602;
                  FStar_Extraction_ML_Syntax.loc = uu____7603;_},uu____7604);
             FStar_Extraction_ML_Syntax.mlty = uu____7605;
             FStar_Extraction_ML_Syntax.loc = uu____7606;_},e1::e2::[])
          when
          let uu____7615 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7615 = "FStar.Buffer.offset" ->
          let uu____7619 =
            let uu____7624 = translate_expr env e1  in
            let uu____7625 = translate_expr env e2  in
            (uu____7624, uu____7625)  in
          EBufSub uu____7619
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7627;
                  FStar_Extraction_ML_Syntax.loc = uu____7628;_},uu____7629);
             FStar_Extraction_ML_Syntax.mlty = uu____7630;
             FStar_Extraction_ML_Syntax.loc = uu____7631;_},e1::e2::[])
          when
          let uu____7640 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7640 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____7644 =
            let uu____7649 = translate_expr env e1  in
            let uu____7650 = translate_expr env e2  in
            (uu____7649, uu____7650)  in
          EBufSub uu____7644
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7652;
                  FStar_Extraction_ML_Syntax.loc = uu____7653;_},uu____7654);
             FStar_Extraction_ML_Syntax.mlty = uu____7655;
             FStar_Extraction_ML_Syntax.loc = uu____7656;_},e1::e2::e3::[])
          when
          (((let uu____7668 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7668 = "FStar.Buffer.upd") ||
              (let uu____7673 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7673 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____7678 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7678 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____7683 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7683 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____7687 =
            let uu____7694 = translate_expr env e1  in
            let uu____7695 = translate_expr env e2  in
            let uu____7696 = translate_expr env e3  in
            (uu____7694, uu____7695, uu____7696)  in
          EBufWrite uu____7687
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7698;
                  FStar_Extraction_ML_Syntax.loc = uu____7699;_},uu____7700);
             FStar_Extraction_ML_Syntax.mlty = uu____7701;
             FStar_Extraction_ML_Syntax.loc = uu____7702;_},e1::e2::[])
          when
          let uu____7711 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7711 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____7715 =
            let uu____7722 = translate_expr env e1  in
            let uu____7723 = translate_expr env e2  in
            (uu____7722, (EConstant (UInt32, "0")), uu____7723)  in
          EBufWrite uu____7715
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7727;
             FStar_Extraction_ML_Syntax.loc = uu____7728;_},uu____7729::[])
          when
          let uu____7732 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7732 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7737;
             FStar_Extraction_ML_Syntax.loc = uu____7738;_},uu____7739::[])
          when
          let uu____7742 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7742 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7747;
                  FStar_Extraction_ML_Syntax.loc = uu____7748;_},uu____7749);
             FStar_Extraction_ML_Syntax.mlty = uu____7750;
             FStar_Extraction_ML_Syntax.loc = uu____7751;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____7765 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7765 = "FStar.Buffer.blit") ||
             (let uu____7770 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7770 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____7775 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7775 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____7779 =
            let uu____7790 = translate_expr env e1  in
            let uu____7791 = translate_expr env e2  in
            let uu____7792 = translate_expr env e3  in
            let uu____7793 = translate_expr env e4  in
            let uu____7794 = translate_expr env e5  in
            (uu____7790, uu____7791, uu____7792, uu____7793, uu____7794)  in
          EBufBlit uu____7779
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7796;
                  FStar_Extraction_ML_Syntax.loc = uu____7797;_},uu____7798);
             FStar_Extraction_ML_Syntax.mlty = uu____7799;
             FStar_Extraction_ML_Syntax.loc = uu____7800;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____7816 =
            let uu____7823 = translate_expr env e1  in
            let uu____7824 = translate_expr env e2  in
            let uu____7825 = translate_expr env e3  in
            (uu____7823, uu____7824, uu____7825)  in
          EBufFill uu____7816
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7827;
             FStar_Extraction_ML_Syntax.loc = uu____7828;_},uu____7829::[])
          when
          let uu____7832 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7832 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7837;
                  FStar_Extraction_ML_Syntax.loc = uu____7838;_},uu____7839);
             FStar_Extraction_ML_Syntax.mlty = uu____7840;
             FStar_Extraction_ML_Syntax.loc = uu____7841;_},_ebuf::_eseq::[])
          when
          (((let uu____7852 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7852 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____7857 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7857 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____7862 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7862 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____7867 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7867 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7872;
                  FStar_Extraction_ML_Syntax.loc = uu____7873;_},uu____7874);
             FStar_Extraction_ML_Syntax.mlty = uu____7875;
             FStar_Extraction_ML_Syntax.loc = uu____7876;_},e1::[])
          when
          (let uu____7886 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7886 = "LowStar.ConstBuffer.of_buffer") ||
            (let uu____7891 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7891 = "LowStar.ConstBuffer.of_ibuffer")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7896;
                  FStar_Extraction_ML_Syntax.loc = uu____7897;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____7899;
             FStar_Extraction_ML_Syntax.loc = uu____7900;_},e1::[])
          when
          ((let uu____7908 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7908 = "LowStar.ConstBuffer.cast") ||
             (let uu____7913 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7913 = "LowStar.ConstBuffer.to_buffer"))
            ||
            (let uu____7918 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7918 = "LowStar.ConstBuffer.to_ibuffer")
          ->
          let uu____7922 =
            let uu____7927 = translate_expr env e1  in
            let uu____7928 =
              let uu____7929 = translate_type env t  in TBuf uu____7929  in
            (uu____7927, uu____7928)  in
          ECast uu____7922
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7931;
             FStar_Extraction_ML_Syntax.loc = uu____7932;_},e1::[])
          when
          let uu____7936 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7936 = "Obj.repr" ->
          let uu____7940 =
            let uu____7945 = translate_expr env e1  in (uu____7945, TAny)  in
          ECast uu____7940
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7948;
             FStar_Extraction_ML_Syntax.loc = uu____7949;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____7965 = FStar_Util.must (mk_width m)  in
          let uu____7966 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____7965 uu____7966 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____7968;
             FStar_Extraction_ML_Syntax.loc = uu____7969;_},args)
          when is_bool_op op ->
          let uu____7983 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____7983 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____7985;
             FStar_Extraction_ML_Syntax.loc = uu____7986;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____7988;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____7989;_}::[])
          when is_machine_int m ->
          let uu____8014 =
            let uu____8020 = FStar_Util.must (mk_width m)  in (uu____8020, c)
             in
          EConstant uu____8014
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____8023;
             FStar_Extraction_ML_Syntax.loc = uu____8024;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8026;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8027;_}::[])
          when is_machine_int m ->
          let uu____8052 =
            let uu____8058 = FStar_Util.must (mk_width m)  in (uu____8058, c)
             in
          EConstant uu____8052
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8060;
             FStar_Extraction_ML_Syntax.loc = uu____8061;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8063;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8064;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8077 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8079;
             FStar_Extraction_ML_Syntax.loc = uu____8080;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8082;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8083;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8100 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8102;
             FStar_Extraction_ML_Syntax.loc = uu____8103;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8105;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8106;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8121 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[],"buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8123;
             FStar_Extraction_ML_Syntax.loc = uu____8124;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8126;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8127;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____8142 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____8145;
             FStar_Extraction_ML_Syntax.loc = uu____8146;_},arg::[])
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
            let uu____8174 =
              let uu____8179 = translate_expr env arg  in
              (uu____8179, (TInt UInt64))  in
            ECast uu____8174
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____8184 =
                 let uu____8189 = translate_expr env arg  in
                 (uu____8189, (TInt UInt32))  in
               ECast uu____8184)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____8194 =
                   let uu____8199 = translate_expr env arg  in
                   (uu____8199, (TInt UInt16))  in
                 ECast uu____8194)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____8204 =
                     let uu____8209 = translate_expr env arg  in
                     (uu____8209, (TInt UInt8))  in
                   ECast uu____8204)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____8214 =
                       let uu____8219 = translate_expr env arg  in
                       (uu____8219, (TInt Int64))  in
                     ECast uu____8214)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____8224 =
                         let uu____8229 = translate_expr env arg  in
                         (uu____8229, (TInt Int32))  in
                       ECast uu____8224)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____8234 =
                           let uu____8239 = translate_expr env arg  in
                           (uu____8239, (TInt Int16))  in
                         ECast uu____8234)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____8244 =
                             let uu____8249 = translate_expr env arg  in
                             (uu____8249, (TInt Int8))  in
                           ECast uu____8244)
                        else
                          (let uu____8252 =
                             let uu____8259 =
                               let uu____8262 = translate_expr env arg  in
                               [uu____8262]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____8259)
                              in
                           EApp uu____8252)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____8282 =
            let uu____8289 = translate_expr env head1  in
            let uu____8290 = FStar_List.map (translate_expr env) args  in
            (uu____8289, uu____8290)  in
          EApp uu____8282
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____8301 =
            let uu____8308 = translate_expr env head1  in
            let uu____8309 = FStar_List.map (translate_type env) ty_args  in
            (uu____8308, uu____8309)  in
          ETypApp uu____8301
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____8317 =
            let uu____8322 = translate_expr env e1  in
            let uu____8323 = translate_type env t_to  in
            (uu____8322, uu____8323)  in
          ECast uu____8317
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____8324,fields) ->
          let uu____8346 =
            let uu____8358 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8359 =
              FStar_List.map
                (fun uu____8381  ->
                   match uu____8381 with
                   | (field,expr) ->
                       let uu____8396 = translate_expr env expr  in
                       (field, uu____8396)) fields
               in
            (uu____8358, uu____8359)  in
          EFlat uu____8346
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____8407 =
            let uu____8415 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____8416 = translate_expr env e1  in
            (uu____8415, uu____8416, (FStar_Pervasives_Native.snd path))  in
          EField uu____8407
      | FStar_Extraction_ML_Syntax.MLE_Let uu____8422 ->
          failwith "todo: translate_expr [MLE_Let]"
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____8435) ->
          let uu____8440 =
            let uu____8442 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____8442
             in
          failwith uu____8440
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____8454 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____8454
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____8460 = FStar_List.map (translate_expr env) es  in
          ETuple uu____8460
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____8463,cons1),es) ->
          let uu____8478 =
            let uu____8488 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8489 = FStar_List.map (translate_expr env) es  in
            (uu____8488, cons1, uu____8489)  in
          ECons uu____8478
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____8515 =
            let uu____8524 = translate_expr env1 body  in
            let uu____8525 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____8524, uu____8525)  in
          EFun uu____8515
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____8535 =
            let uu____8542 = translate_expr env e1  in
            let uu____8543 = translate_expr env e2  in
            let uu____8544 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____8542, uu____8543, uu____8544)  in
          EIfThenElse uu____8535
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____8546 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____8554 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____8570 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > Prims.int_zero
          then
            let uu____8588 =
              let uu____8603 = FStar_List.map (translate_type env) ts  in
              (lid, uu____8603)  in
            TApp uu____8588
          else TQualified lid
      | uu____8618 ->
          let uu____8619 =
            let uu____8621 =
              FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
            FStar_Util.format1
              "invalid argument: expected MLTY_Named, got %s" uu____8621
             in
          failwith uu____8619

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
    fun uu____8655  ->
      match uu____8655 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____8682 = translate_pat env pat  in
            (match uu____8682 with
             | (env1,pat1) ->
                 let uu____8693 = translate_expr env1 expr  in
                 (pat1, uu____8693))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___7_8701  ->
    match uu___7_8701 with
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
          let uu____8768 =
            let uu____8769 =
              let uu____8775 = translate_width sw  in (uu____8775, s)  in
            PConstant uu____8769  in
          (env, uu____8768)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____8785,cons1),ps) ->
          let uu____8800 =
            FStar_List.fold_left
              (fun uu____8820  ->
                 fun p1  ->
                   match uu____8820 with
                   | (env1,acc) ->
                       let uu____8840 = translate_pat env1 p1  in
                       (match uu____8840 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8800 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____8870,ps) ->
          let uu____8892 =
            FStar_List.fold_left
              (fun uu____8929  ->
                 fun uu____8930  ->
                   match (uu____8929, uu____8930) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____9010 = translate_pat env1 p1  in
                       (match uu____9010 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____8892 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____9081 =
            FStar_List.fold_left
              (fun uu____9101  ->
                 fun p1  ->
                   match uu____9101 with
                   | (env1,acc) ->
                       let uu____9121 = translate_pat env1 p1  in
                       (match uu____9121 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____9081 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____9148 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____9154 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____9168 =
            let uu____9170 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____9170
              (FStar_Util.for_some
                 (fun c1  -> c1 = (FStar_Char.char_of_int Prims.int_zero)))
             in
          if uu____9168
          then
            let uu____9185 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____9185
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____9212) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____9230 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____9232 ->
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
          let uu____9256 =
            let uu____9263 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____9263)  in
          EApp uu____9256
