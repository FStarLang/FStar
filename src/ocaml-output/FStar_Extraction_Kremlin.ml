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
  fun projectee  ->
    match projectee with | DGlobal _0 -> true | uu____772 -> false
  
let (__proj__DGlobal__item___0 :
  decl ->
    (flag Prims.list * (Prims.string Prims.list * Prims.string) * Prims.int *
      typ * expr))
  = fun projectee  -> match projectee with | DGlobal _0 -> _0 
let (uu___is_DFunction : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DFunction _0 -> true | uu____883 -> false
  
let (__proj__DFunction__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * Prims.int * typ *
      (Prims.string Prims.list * Prims.string) * binder Prims.list * expr))
  = fun projectee  -> match projectee with | DFunction _0 -> _0 
let (uu___is_DTypeAlias : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeAlias _0 -> true | uu____1008 -> false
  
let (__proj__DTypeAlias__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      typ))
  = fun projectee  -> match projectee with | DTypeAlias _0 -> _0 
let (uu___is_DTypeFlat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeFlat _0 -> true | uu____1115 -> false
  
let (__proj__DTypeFlat__item___0 :
  decl ->
    ((Prims.string Prims.list * Prims.string) * flag Prims.list * Prims.int *
      (Prims.string * (typ * Prims.bool)) Prims.list))
  = fun projectee  -> match projectee with | DTypeFlat _0 -> _0 
let (uu___is_DUnusedRetainedForBackwardsCompat : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DUnusedRetainedForBackwardsCompat _0 -> true
    | uu____1247 -> false
  
let (__proj__DUnusedRetainedForBackwardsCompat__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ))
  =
  fun projectee  ->
    match projectee with | DUnusedRetainedForBackwardsCompat _0 -> _0
  
let (uu___is_DTypeVariant : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DTypeVariant _0 -> true | uu____1364 -> false
  
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
    | uu____1505 -> false
  
let (__proj__DTypeAbstractStruct__item___0 :
  decl -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | DTypeAbstractStruct _0 -> _0 
let (uu___is_DExternal : decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | DExternal _0 -> true | uu____1573 -> false
  
let (__proj__DExternal__item___0 :
  decl ->
    (cc FStar_Pervasives_Native.option * flag Prims.list * (Prims.string
      Prims.list * Prims.string) * typ * Prims.string Prims.list))
  = fun projectee  -> match projectee with | DExternal _0 -> _0 
let (uu___is_StdCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | StdCall  -> true | uu____1666 -> false
  
let (uu___is_CDecl : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | CDecl  -> true | uu____1677 -> false
  
let (uu___is_FastCall : cc -> Prims.bool) =
  fun projectee  ->
    match projectee with | FastCall  -> true | uu____1688 -> false
  
let (uu___is_Private : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Private  -> true | uu____1699 -> false
  
let (uu___is_WipeBody : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | WipeBody  -> true | uu____1710 -> false
  
let (uu___is_CInline : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInline  -> true | uu____1721 -> false
  
let (uu___is_Substitute : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Substitute  -> true | uu____1732 -> false
  
let (uu___is_GCType : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | GCType  -> true | uu____1743 -> false
  
let (uu___is_Comment : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comment _0 -> true | uu____1756 -> false
  
let (__proj__Comment__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Comment _0 -> _0 
let (uu___is_MustDisappear : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MustDisappear  -> true | uu____1777 -> false
  
let (uu___is_Const : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____1790 -> false
  
let (__proj__Const__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_Prologue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Prologue _0 -> true | uu____1813 -> false
  
let (__proj__Prologue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Prologue _0 -> _0 
let (uu___is_Epilogue : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Epilogue _0 -> true | uu____1836 -> false
  
let (__proj__Epilogue__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Epilogue _0 -> _0 
let (uu___is_Abstract : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abstract  -> true | uu____1857 -> false
  
let (uu___is_IfDef : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | IfDef  -> true | uu____1868 -> false
  
let (uu___is_Macro : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Macro  -> true | uu____1879 -> false
  
let (uu___is_Deprecated : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | Deprecated _0 -> true | uu____1892 -> false
  
let (__proj__Deprecated__item___0 : flag -> Prims.string) =
  fun projectee  -> match projectee with | Deprecated _0 -> _0 
let (uu___is_Eternal : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eternal  -> true | uu____1913 -> false
  
let (uu___is_Stack : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stack  -> true | uu____1924 -> false
  
let (uu___is_ManuallyManaged : lifetime -> Prims.bool) =
  fun projectee  ->
    match projectee with | ManuallyManaged  -> true | uu____1935 -> false
  
let (uu___is_EBound : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBound _0 -> true | uu____1948 -> false
  
let (__proj__EBound__item___0 : expr -> Prims.int) =
  fun projectee  -> match projectee with | EBound _0 -> _0 
let (uu___is_EQualified : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EQualified _0 -> true | uu____1978 -> false
  
let (__proj__EQualified__item___0 :
  expr -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | EQualified _0 -> _0 
let (uu___is_EConstant : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EConstant _0 -> true | uu____2026 -> false
  
let (__proj__EConstant__item___0 : expr -> (width * Prims.string)) =
  fun projectee  -> match projectee with | EConstant _0 -> _0 
let (uu___is_EUnit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EUnit  -> true | uu____2059 -> false
  
let (uu___is_EApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EApp _0 -> true | uu____2077 -> false
  
let (__proj__EApp__item___0 : expr -> (expr * expr Prims.list)) =
  fun projectee  -> match projectee with | EApp _0 -> _0 
let (uu___is_ETypApp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETypApp _0 -> true | uu____2120 -> false
  
let (__proj__ETypApp__item___0 : expr -> (expr * typ Prims.list)) =
  fun projectee  -> match projectee with | ETypApp _0 -> _0 
let (uu___is_ELet : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ELet _0 -> true | uu____2163 -> false
  
let (__proj__ELet__item___0 : expr -> (binder * expr * expr)) =
  fun projectee  -> match projectee with | ELet _0 -> _0 
let (uu___is_EIfThenElse : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EIfThenElse _0 -> true | uu____2206 -> false
  
let (__proj__EIfThenElse__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EIfThenElse _0 -> _0 
let (uu___is_ESequence : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ESequence _0 -> true | uu____2245 -> false
  
let (__proj__ESequence__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ESequence _0 -> _0 
let (uu___is_EAssign : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAssign _0 -> true | uu____2274 -> false
  
let (__proj__EAssign__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EAssign _0 -> _0 
let (uu___is_EBufCreate : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreate _0 -> true | uu____2311 -> false
  
let (__proj__EBufCreate__item___0 : expr -> (lifetime * expr * expr)) =
  fun projectee  -> match projectee with | EBufCreate _0 -> _0 
let (uu___is_EBufRead : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufRead _0 -> true | uu____2352 -> false
  
let (__proj__EBufRead__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufRead _0 -> _0 
let (uu___is_EBufWrite : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufWrite _0 -> true | uu____2389 -> false
  
let (__proj__EBufWrite__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufWrite _0 -> _0 
let (uu___is_EBufSub : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufSub _0 -> true | uu____2430 -> false
  
let (__proj__EBufSub__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EBufSub _0 -> _0 
let (uu___is_EBufBlit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufBlit _0 -> true | uu____2471 -> false
  
let (__proj__EBufBlit__item___0 : expr -> (expr * expr * expr * expr * expr))
  = fun projectee  -> match projectee with | EBufBlit _0 -> _0 
let (uu___is_EMatch : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EMatch _0 -> true | uu____2530 -> false
  
let (__proj__EMatch__item___0 : expr -> (expr * (pattern * expr) Prims.list))
  = fun projectee  -> match projectee with | EMatch _0 -> _0 
let (uu___is_EOp : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EOp _0 -> true | uu____2583 -> false
  
let (__proj__EOp__item___0 : expr -> (op * width)) =
  fun projectee  -> match projectee with | EOp _0 -> _0 
let (uu___is_ECast : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECast _0 -> true | uu____2618 -> false
  
let (__proj__ECast__item___0 : expr -> (expr * typ)) =
  fun projectee  -> match projectee with | ECast _0 -> _0 
let (uu___is_EPushFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPushFrame  -> true | uu____2648 -> false
  
let (uu___is_EPopFrame : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EPopFrame  -> true | uu____2659 -> false
  
let (uu___is_EBool : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBool _0 -> true | uu____2672 -> false
  
let (__proj__EBool__item___0 : expr -> Prims.bool) =
  fun projectee  -> match projectee with | EBool _0 -> _0 
let (uu___is_EAny : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAny  -> true | uu____2693 -> false
  
let (uu___is_EAbort : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbort  -> true | uu____2704 -> false
  
let (uu___is_EReturn : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EReturn _0 -> true | uu____2716 -> false
  
let (__proj__EReturn__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EReturn _0 -> _0 
let (uu___is_EFlat : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFlat _0 -> true | uu____2746 -> false
  
let (__proj__EFlat__item___0 :
  expr -> (typ * (Prims.string * expr) Prims.list)) =
  fun projectee  -> match projectee with | EFlat _0 -> _0 
let (uu___is_EField : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EField _0 -> true | uu____2805 -> false
  
let (__proj__EField__item___0 : expr -> (typ * expr * Prims.string)) =
  fun projectee  -> match projectee with | EField _0 -> _0 
let (uu___is_EWhile : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWhile _0 -> true | uu____2849 -> false
  
let (__proj__EWhile__item___0 : expr -> (expr * expr)) =
  fun projectee  -> match projectee with | EWhile _0 -> _0 
let (uu___is_EBufCreateL : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateL _0 -> true | uu____2886 -> false
  
let (__proj__EBufCreateL__item___0 : expr -> (lifetime * expr Prims.list)) =
  fun projectee  -> match projectee with | EBufCreateL _0 -> _0 
let (uu___is_ETuple : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ETuple _0 -> true | uu____2925 -> false
  
let (__proj__ETuple__item___0 : expr -> expr Prims.list) =
  fun projectee  -> match projectee with | ETuple _0 -> _0 
let (uu___is_ECons : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | ECons _0 -> true | uu____2959 -> false
  
let (__proj__ECons__item___0 :
  expr -> (typ * Prims.string * expr Prims.list)) =
  fun projectee  -> match projectee with | ECons _0 -> _0 
let (uu___is_EBufFill : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFill _0 -> true | uu____3011 -> false
  
let (__proj__EBufFill__item___0 : expr -> (expr * expr * expr)) =
  fun projectee  -> match projectee with | EBufFill _0 -> _0 
let (uu___is_EString : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EString _0 -> true | uu____3049 -> false
  
let (__proj__EString__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EString _0 -> _0 
let (uu___is_EFun : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EFun _0 -> true | uu____3079 -> false
  
let (__proj__EFun__item___0 : expr -> (binder Prims.list * expr * typ)) =
  fun projectee  -> match projectee with | EFun _0 -> _0 
let (uu___is_EAbortS : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortS _0 -> true | uu____3123 -> false
  
let (__proj__EAbortS__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EAbortS _0 -> _0 
let (uu___is_EBufFree : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufFree _0 -> true | uu____3145 -> false
  
let (__proj__EBufFree__item___0 : expr -> expr) =
  fun projectee  -> match projectee with | EBufFree _0 -> _0 
let (uu___is_EBufCreateNoInit : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EBufCreateNoInit _0 -> true | uu____3168 -> false
  
let (__proj__EBufCreateNoInit__item___0 : expr -> (lifetime * expr)) =
  fun projectee  -> match projectee with | EBufCreateNoInit _0 -> _0 
let (uu___is_EAbortT : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EAbortT _0 -> true | uu____3204 -> false
  
let (__proj__EAbortT__item___0 : expr -> (Prims.string * typ)) =
  fun projectee  -> match projectee with | EAbortT _0 -> _0 
let (uu___is_EComment : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with | EComment _0 -> true | uu____3246 -> false
  
let (__proj__EComment__item___0 :
  expr -> (Prims.string * expr * Prims.string)) =
  fun projectee  -> match projectee with | EComment _0 -> _0 
let (uu___is_EStandaloneComment : expr -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | EStandaloneComment _0 -> true
    | uu____3290 -> false
  
let (__proj__EStandaloneComment__item___0 : expr -> Prims.string) =
  fun projectee  -> match projectee with | EStandaloneComment _0 -> _0 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee  -> match projectee with | Add  -> true | uu____3311 -> false 
let (uu___is_AddW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | AddW  -> true | uu____3322 -> false
  
let (uu___is_Sub : op -> Prims.bool) =
  fun projectee  -> match projectee with | Sub  -> true | uu____3333 -> false 
let (uu___is_SubW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | SubW  -> true | uu____3344 -> false
  
let (uu___is_Div : op -> Prims.bool) =
  fun projectee  -> match projectee with | Div  -> true | uu____3355 -> false 
let (uu___is_DivW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | DivW  -> true | uu____3366 -> false
  
let (uu___is_Mult : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult  -> true | uu____3377 -> false
  
let (uu___is_MultW : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | MultW  -> true | uu____3388 -> false
  
let (uu___is_Mod : op -> Prims.bool) =
  fun projectee  -> match projectee with | Mod  -> true | uu____3399 -> false 
let (uu___is_BOr : op -> Prims.bool) =
  fun projectee  -> match projectee with | BOr  -> true | uu____3410 -> false 
let (uu___is_BAnd : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BAnd  -> true | uu____3421 -> false
  
let (uu___is_BXor : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BXor  -> true | uu____3432 -> false
  
let (uu___is_BShiftL : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftL  -> true | uu____3443 -> false
  
let (uu___is_BShiftR : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BShiftR  -> true | uu____3454 -> false
  
let (uu___is_BNot : op -> Prims.bool) =
  fun projectee  ->
    match projectee with | BNot  -> true | uu____3465 -> false
  
let (uu___is_Eq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Eq  -> true | uu____3476 -> false 
let (uu___is_Neq : op -> Prims.bool) =
  fun projectee  -> match projectee with | Neq  -> true | uu____3487 -> false 
let (uu___is_Lt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lt  -> true | uu____3498 -> false 
let (uu___is_Lte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Lte  -> true | uu____3509 -> false 
let (uu___is_Gt : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gt  -> true | uu____3520 -> false 
let (uu___is_Gte : op -> Prims.bool) =
  fun projectee  -> match projectee with | Gte  -> true | uu____3531 -> false 
let (uu___is_And : op -> Prims.bool) =
  fun projectee  -> match projectee with | And  -> true | uu____3542 -> false 
let (uu___is_Or : op -> Prims.bool) =
  fun projectee  -> match projectee with | Or  -> true | uu____3553 -> false 
let (uu___is_Xor : op -> Prims.bool) =
  fun projectee  -> match projectee with | Xor  -> true | uu____3564 -> false 
let (uu___is_Not : op -> Prims.bool) =
  fun projectee  -> match projectee with | Not  -> true | uu____3575 -> false 
let (uu___is_PUnit : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PUnit  -> true | uu____3586 -> false
  
let (uu___is_PBool : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PBool _0 -> true | uu____3599 -> false
  
let (__proj__PBool__item___0 : pattern -> Prims.bool) =
  fun projectee  -> match projectee with | PBool _0 -> _0 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PVar _0 -> true | uu____3621 -> false
  
let (__proj__PVar__item___0 : pattern -> binder) =
  fun projectee  -> match projectee with | PVar _0 -> _0 
let (uu___is_PCons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PCons _0 -> true | uu____3647 -> false
  
let (__proj__PCons__item___0 :
  pattern -> (Prims.string * pattern Prims.list)) =
  fun projectee  -> match projectee with | PCons _0 -> _0 
let (uu___is_PTuple : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PTuple _0 -> true | uu____3689 -> false
  
let (__proj__PTuple__item___0 : pattern -> pattern Prims.list) =
  fun projectee  -> match projectee with | PTuple _0 -> _0 
let (uu___is_PRecord : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PRecord _0 -> true | uu____3721 -> false
  
let (__proj__PRecord__item___0 :
  pattern -> (Prims.string * pattern) Prims.list) =
  fun projectee  -> match projectee with | PRecord _0 -> _0 
let (uu___is_PConstant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | PConstant _0 -> true | uu____3766 -> false
  
let (__proj__PConstant__item___0 : pattern -> (width * Prims.string)) =
  fun projectee  -> match projectee with | PConstant _0 -> _0 
let (uu___is_UInt8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt8  -> true | uu____3799 -> false
  
let (uu___is_UInt16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt16  -> true | uu____3810 -> false
  
let (uu___is_UInt32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt32  -> true | uu____3821 -> false
  
let (uu___is_UInt64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | UInt64  -> true | uu____3832 -> false
  
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____3843 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____3854 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____3865 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____3876 -> false
  
let (uu___is_Bool : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool  -> true | uu____3887 -> false
  
let (uu___is_CInt : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | CInt  -> true | uu____3898 -> false
  
let (__proj__Mkbinder__item__name : binder -> Prims.string) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> name 
let (__proj__Mkbinder__item__typ : binder -> typ) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> typ 
let (__proj__Mkbinder__item__mut : binder -> Prims.bool) =
  fun projectee  -> match projectee with | { name; typ; mut;_} -> mut 
let (uu___is_TInt : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TInt _0 -> true | uu____3947 -> false
  
let (__proj__TInt__item___0 : typ -> width) =
  fun projectee  -> match projectee with | TInt _0 -> _0 
let (uu___is_TBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBuf _0 -> true | uu____3966 -> false
  
let (__proj__TBuf__item___0 : typ -> typ) =
  fun projectee  -> match projectee with | TBuf _0 -> _0 
let (uu___is_TUnit : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TUnit  -> true | uu____3984 -> false
  
let (uu___is_TQualified : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TQualified _0 -> true | uu____4004 -> false
  
let (__proj__TQualified__item___0 :
  typ -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | TQualified _0 -> _0 
let (uu___is_TBool : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBool  -> true | uu____4046 -> false
  
let (uu___is_TAny : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TAny  -> true | uu____4057 -> false
  
let (uu___is_TArrow : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TArrow _0 -> true | uu____4073 -> false
  
let (__proj__TArrow__item___0 : typ -> (typ * typ)) =
  fun projectee  -> match projectee with | TArrow _0 -> _0 
let (uu___is_TBound : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TBound _0 -> true | uu____4105 -> false
  
let (__proj__TBound__item___0 : typ -> Prims.int) =
  fun projectee  -> match projectee with | TBound _0 -> _0 
let (uu___is_TApp : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TApp _0 -> true | uu____4141 -> false
  
let (__proj__TApp__item___0 :
  typ -> ((Prims.string Prims.list * Prims.string) * typ Prims.list)) =
  fun projectee  -> match projectee with | TApp _0 -> _0 
let (uu___is_TTuple : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TTuple _0 -> true | uu____4204 -> false
  
let (__proj__TTuple__item___0 : typ -> typ Prims.list) =
  fun projectee  -> match projectee with | TTuple _0 -> _0 
let (uu___is_TConstBuf : typ -> Prims.bool) =
  fun projectee  ->
    match projectee with | TConstBuf _0 -> true | uu____4229 -> false
  
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
  'Auu____4324 'Auu____4325 'Auu____4326 .
    ('Auu____4324 * 'Auu____4325 * 'Auu____4326) -> 'Auu____4324
  = fun uu____4337  -> match uu____4337 with | (x,uu____4345,uu____4346) -> x 
let snd3 :
  'Auu____4356 'Auu____4357 'Auu____4358 .
    ('Auu____4356 * 'Auu____4357 * 'Auu____4358) -> 'Auu____4357
  = fun uu____4369  -> match uu____4369 with | (uu____4376,x,uu____4378) -> x 
let thd3 :
  'Auu____4388 'Auu____4389 'Auu____4390 .
    ('Auu____4388 * 'Auu____4389 * 'Auu____4390) -> 'Auu____4390
  = fun uu____4401  -> match uu____4401 with | (uu____4408,uu____4409,x) -> x 
let (mk_width : Prims.string -> width FStar_Pervasives_Native.option) =
  fun uu___0_4419  ->
    match uu___0_4419 with
    | "UInt8" -> FStar_Pervasives_Native.Some UInt8
    | "UInt16" -> FStar_Pervasives_Native.Some UInt16
    | "UInt32" -> FStar_Pervasives_Native.Some UInt32
    | "UInt64" -> FStar_Pervasives_Native.Some UInt64
    | "Int8" -> FStar_Pervasives_Native.Some Int8
    | "Int16" -> FStar_Pervasives_Native.Some Int16
    | "Int32" -> FStar_Pervasives_Native.Some Int32
    | "Int64" -> FStar_Pervasives_Native.Some Int64
    | uu____4431 -> FStar_Pervasives_Native.None
  
let (mk_bool_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___1_4441  ->
    match uu___1_4441 with
    | "op_Negation" -> FStar_Pervasives_Native.Some Not
    | "op_AmpAmp" -> FStar_Pervasives_Native.Some And
    | "op_BarBar" -> FStar_Pervasives_Native.Some Or
    | "op_Equality" -> FStar_Pervasives_Native.Some Eq
    | "op_disEquality" -> FStar_Pervasives_Native.Some Neq
    | uu____4450 -> FStar_Pervasives_Native.None
  
let (is_bool_op : Prims.string -> Prims.bool) =
  fun op  -> (mk_bool_op op) <> FStar_Pervasives_Native.None 
let (mk_op : Prims.string -> op FStar_Pervasives_Native.option) =
  fun uu___2_4471  ->
    match uu___2_4471 with
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
    | uu____4516 -> FStar_Pervasives_Native.None
  
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
      let uu___168_4672 = env  in
      {
        names = ({ pretty = x } :: (env.names));
        names_t = (uu___168_4672.names_t);
        module_name = (uu___168_4672.module_name)
      }
  
let (extend_t : env -> Prims.string -> env) =
  fun env  ->
    fun x  ->
      let uu___172_4686 = env  in
      {
        names = (uu___172_4686.names);
        names_t = (x :: (env.names_t));
        module_name = (uu___172_4686.module_name)
      }
  
let (find_name : env -> Prims.string -> name) =
  fun env  ->
    fun x  ->
      let uu____4701 =
        FStar_List.tryFind (fun name  -> name.pretty = x) env.names  in
      match uu____4701 with
      | FStar_Pervasives_Native.Some name -> name
      | FStar_Pervasives_Native.None  ->
          failwith "internal error: name not found"
  
let (find : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___183_4725  ->
           match () with
           | () -> FStar_List.index (fun name  -> name.pretty = x) env.names)
          ()
      with
      | uu___182_4732 ->
          let uu____4734 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4734
  
let (find_t : env -> Prims.string -> Prims.int) =
  fun env  ->
    fun x  ->
      try
        (fun uu___192_4754  ->
           match () with
           | () -> FStar_List.index (fun name  -> name = x) env.names_t) ()
      with
      | uu___191_4763 ->
          let uu____4765 =
            FStar_Util.format1 "Internal error: name not found %s\n" x  in
          failwith uu____4765
  
let add_binders :
  'Auu____4776 . env -> (Prims.string * 'Auu____4776) Prims.list -> env =
  fun env  ->
    fun binders  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____4811  ->
             match uu____4811 with | (name,uu____4818) -> extend env1 name)
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
      | uu____4870 ->
          failwith "Argument of FStar.Buffer.createL is not a list literal!"
       in
    list_elements [] e2
  
let rec (translate_module :
  (FStar_Extraction_ML_Syntax.mlpath * (FStar_Extraction_ML_Syntax.mlsig *
    FStar_Extraction_ML_Syntax.mlmodule) FStar_Pervasives_Native.option *
    FStar_Extraction_ML_Syntax.mllib) -> file)
  =
  fun m  ->
    let uu____5096 = m  in
    match uu____5096 with
    | (module_name,modul,uu____5111) ->
        let module_name1 =
          FStar_List.append (FStar_Pervasives_Native.fst module_name)
            [FStar_Pervasives_Native.snd module_name]
           in
        let program =
          match modul with
          | FStar_Pervasives_Native.Some (_signature,decls) ->
              FStar_List.collect (translate_decl (empty module_name1)) decls
          | uu____5146 ->
              failwith "Unexpected standalone interface or nested modules"
           in
        ((FStar_String.concat "_" module_name1), program)

and (translate_flags :
  FStar_Extraction_ML_Syntax.meta Prims.list -> flag Prims.list) =
  fun flags  ->
    FStar_List.choose
      (fun uu___3_5160  ->
         match uu___3_5160 with
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
         | uu____5173 -> FStar_Pervasives_Native.None) flags

and (translate_cc :
  FStar_Extraction_ML_Syntax.meta Prims.list ->
    cc FStar_Pervasives_Native.option)
  =
  fun flags  ->
    let uu____5177 =
      FStar_List.choose
        (fun uu___4_5184  ->
           match uu___4_5184 with
           | FStar_Extraction_ML_Syntax.CCConv s ->
               FStar_Pervasives_Native.Some s
           | uu____5191 -> FStar_Pervasives_Native.None) flags
       in
    match uu____5177 with
    | "stdcall"::[] -> FStar_Pervasives_Native.Some StdCall
    | "fastcall"::[] -> FStar_Pervasives_Native.Some FastCall
    | "cdecl"::[] -> FStar_Pervasives_Native.Some CDecl
    | uu____5204 -> FStar_Pervasives_Native.None

and (translate_decl :
  env -> FStar_Extraction_ML_Syntax.mlmodule1 -> decl Prims.list) =
  fun env  ->
    fun d  ->
      match d with
      | FStar_Extraction_ML_Syntax.MLM_Let (flavor,lbs) ->
          FStar_List.choose (translate_let env flavor) lbs
      | FStar_Extraction_ML_Syntax.MLM_Loc uu____5218 -> []
      | FStar_Extraction_ML_Syntax.MLM_Ty tys ->
          FStar_List.choose (translate_type_decl env) tys
      | FStar_Extraction_ML_Syntax.MLM_Top uu____5220 ->
          failwith "todo: translate_decl [MLM_Top]"
      | FStar_Extraction_ML_Syntax.MLM_Exn (m,uu____5225) ->
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5252;
            FStar_Extraction_ML_Syntax.mllb_def = e;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5255;_} when
            FStar_Util.for_some
              (fun uu___5_5260  ->
                 match uu___5_5260 with
                 | FStar_Extraction_ML_Syntax.Assumed  -> true
                 | uu____5263 -> false) meta
            ->
            let name1 = ((env.module_name), name)  in
            let arg_names =
              match e.FStar_Extraction_ML_Syntax.expr with
              | FStar_Extraction_ML_Syntax.MLE_Fun (args,uu____5286) ->
                  FStar_List.map FStar_Pervasives_Native.fst args
              | uu____5308 -> []  in
            if (FStar_List.length tvars) = Prims.int_zero
            then
              let uu____5316 =
                let uu____5317 =
                  let uu____5343 = translate_cc meta  in
                  let uu____5346 = translate_flags meta  in
                  let uu____5349 = translate_type env t0  in
                  (uu____5343, uu____5346, name1, uu____5349, arg_names)  in
                DExternal uu____5317  in
              FStar_Pervasives_Native.Some uu____5316
            else
              ((let uu____5368 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath name1  in
                FStar_Util.print1_warning
                  "Not extracting %s to KreMLin (polymorphic assumes are not supported)\n"
                  uu____5368);
               FStar_Pervasives_Native.None)
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.Some (tvars,t0);
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5374;
            FStar_Extraction_ML_Syntax.mllb_def =
              {
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Fun (args,body);
                FStar_Extraction_ML_Syntax.mlty = uu____5377;
                FStar_Extraction_ML_Syntax.loc = uu____5378;_};
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5380;_} ->
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
               let rec find_return_type eff i uu___6_5437 =
                 match uu___6_5437 with
                 | FStar_Extraction_ML_Syntax.MLTY_Fun (uu____5446,eff1,t)
                     when i > Prims.int_zero ->
                     find_return_type eff1 (i - Prims.int_one) t
                 | t -> (i, eff, t)  in
               let name1 = ((env2.module_name), name)  in
               let uu____5466 =
                 find_return_type FStar_Extraction_ML_Syntax.E_PURE
                   (FStar_List.length args) t0
                  in
               match uu____5466 with
               | (i,eff,t) ->
                   (if i > Prims.int_zero
                    then
                      (let msg =
                         "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction"
                          in
                       let uu____5492 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath name1
                          in
                       FStar_Util.print2_warning
                         "Not extracting %s to KreMLin (%s)\n" uu____5492 msg)
                    else ();
                    (let t1 = translate_type env2 t  in
                     let binders = translate_binders env2 args  in
                     let env3 = add_binders env2 args  in
                     let cc = translate_cc meta  in
                     let meta1 =
                       match (eff, t1) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5510) ->
                           let uu____5511 = translate_flags meta  in
                           MustDisappear :: uu____5511
                       | (FStar_Extraction_ML_Syntax.E_PURE ,TUnit ) ->
                           let uu____5514 = translate_flags meta  in
                           MustDisappear :: uu____5514
                       | uu____5517 -> translate_flags meta  in
                     try
                       (fun uu___366_5526  ->
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
                         ((let uu____5558 =
                             let uu____5564 =
                               let uu____5566 =
                                 FStar_Extraction_ML_Syntax.string_of_mlpath
                                   name1
                                  in
                               FStar_Util.format2
                                 "Error while extracting %s to KreMLin (%s)\n"
                                 uu____5566 msg
                                in
                             (FStar_Errors.Warning_FunctionNotExtacted,
                               uu____5564)
                              in
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             uu____5558);
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
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5592;
            FStar_Extraction_ML_Syntax.mllb_def = expr;
            FStar_Extraction_ML_Syntax.mllb_meta = meta;
            FStar_Extraction_ML_Syntax.print_typ = uu____5595;_} ->
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
                 (fun uu___393_5632  ->
                    match () with
                    | () ->
                        let expr1 = translate_expr env1 expr  in
                        FStar_Pervasives_Native.Some
                          (DGlobal
                             (meta1, name1, (FStar_List.length tvars), t1,
                               expr1))) ()
               with
               | e ->
                   ((let uu____5656 =
                       let uu____5662 =
                         let uu____5664 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath name1
                            in
                         let uu____5666 = FStar_Util.print_exn e  in
                         FStar_Util.format2
                           "Error extracting %s to KreMLin (%s)\n" uu____5664
                           uu____5666
                          in
                       (FStar_Errors.Warning_DefinitionNotTranslated,
                         uu____5662)
                        in
                     FStar_Errors.log_issue FStar_Range.dummyRange uu____5656);
                    FStar_Pervasives_Native.Some
                      (DGlobal
                         (meta1, name1, (FStar_List.length tvars), t1, EAny))))
        | { FStar_Extraction_ML_Syntax.mllb_name = name;
            FStar_Extraction_ML_Syntax.mllb_tysc = ts;
            FStar_Extraction_ML_Syntax.mllb_add_unit = uu____5684;
            FStar_Extraction_ML_Syntax.mllb_def = uu____5685;
            FStar_Extraction_ML_Syntax.mllb_meta = uu____5686;
            FStar_Extraction_ML_Syntax.print_typ = uu____5687;_} ->
            ((let uu____5694 =
                let uu____5700 =
                  FStar_Util.format1 "Not extracting %s to KreMLin\n" name
                   in
                (FStar_Errors.Warning_DefinitionNotTranslated, uu____5700)
                 in
              FStar_Errors.log_issue FStar_Range.dummyRange uu____5694);
             (match ts with
              | FStar_Pervasives_Native.Some (idents,t) ->
                  let uu____5707 =
                    FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
                  FStar_Util.print2 "Type scheme is: forall %s. %s\n"
                    (FStar_String.concat ", " idents) uu____5707
              | FStar_Pervasives_Native.None  -> ());
             FStar_Pervasives_Native.None)

and (translate_type_decl :
  env ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ty  ->
      let uu____5721 = ty  in
      match uu____5721 with
      | (uu____5724,uu____5725,uu____5726,uu____5727,flags,uu____5729) ->
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
                     (let uu____5803 =
                        let uu____5804 =
                          let uu____5824 = translate_flags flags1  in
                          let uu____5827 = translate_type env1 t  in
                          (name1, uu____5824, (FStar_List.length args),
                            uu____5827)
                           in
                        DTypeAlias uu____5804  in
                      FStar_Pervasives_Native.Some uu____5803)
             | (uu____5840,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_Record fields)) ->
                 let name1 = ((env.module_name), name)  in
                 let env1 =
                   FStar_List.fold_left
                     (fun env1  -> fun name2  -> extend_t env1 name2) env
                     args
                    in
                 let uu____5885 =
                   let uu____5886 =
                     let uu____5918 = translate_flags flags1  in
                     let uu____5921 =
                       FStar_List.map
                         (fun uu____5953  ->
                            match uu____5953 with
                            | (f,t) ->
                                let uu____5973 =
                                  let uu____5979 = translate_type env1 t  in
                                  (uu____5979, false)  in
                                (f, uu____5973)) fields
                        in
                     (name1, uu____5918, (FStar_List.length args),
                       uu____5921)
                      in
                   DTypeFlat uu____5886  in
                 FStar_Pervasives_Native.Some uu____5885
             | (uu____6012,name,_mangled_name,args,flags1,FStar_Pervasives_Native.Some
                (FStar_Extraction_ML_Syntax.MLTD_DType branches)) ->
                 let name1 = ((env.module_name), name)  in
                 let flags2 = translate_flags flags1  in
                 let env1 = FStar_List.fold_left extend_t env args  in
                 let uu____6062 =
                   let uu____6063 =
                     let uu____6102 =
                       FStar_List.map
                         (fun uu____6155  ->
                            match uu____6155 with
                            | (cons1,ts) ->
                                let uu____6203 =
                                  FStar_List.map
                                    (fun uu____6235  ->
                                       match uu____6235 with
                                       | (name2,t) ->
                                           let uu____6255 =
                                             let uu____6261 =
                                               translate_type env1 t  in
                                             (uu____6261, false)  in
                                           (name2, uu____6255)) ts
                                   in
                                (cons1, uu____6203)) branches
                        in
                     (name1, flags2, (FStar_List.length args), uu____6102)
                      in
                   DTypeVariant uu____6063  in
                 FStar_Pervasives_Native.Some uu____6062
             | (uu____6314,name,_mangled_name,uu____6317,uu____6318,uu____6319)
                 ->
                 ((let uu____6335 =
                     let uu____6341 =
                       FStar_Util.format1
                         "Error extracting type definition %s to KreMLin\n"
                         name
                        in
                     (FStar_Errors.Warning_DefinitionNotTranslated,
                       uu____6341)
                      in
                   FStar_Errors.log_issue FStar_Range.dummyRange uu____6335);
                  FStar_Pervasives_Native.None))

and (translate_type : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Tuple [] -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Var name ->
          let uu____6349 = find_t env name  in TBound uu____6349
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,uu____6352,t2) ->
          let uu____6354 =
            let uu____6359 = translate_type env t1  in
            let uu____6360 = translate_type env t2  in
            (uu____6359, uu____6360)  in
          TArrow uu____6354
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6364 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6364 = "Prims.unit" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],p) when
          let uu____6371 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6371 = "Prims.bool" -> TBool
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t")) when
          is_machine_int m ->
          let uu____6388 = FStar_Util.must (mk_width m)  in TInt uu____6388
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],("FStar"::m::[],"t'")) when
          is_machine_int m ->
          let uu____6402 = FStar_Util.must (mk_width m)  in TInt uu____6402
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6407 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6407 = "FStar.Monotonic.HyperStack.mem" -> TUnit
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (uu____6411::arg::uu____6413::[],p) when
          (((let uu____6419 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6419 = "FStar.Monotonic.HyperStack.s_mref") ||
              (let uu____6424 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6424 = "FStar.Monotonic.HyperHeap.mrref"))
             ||
             (let uu____6429 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6429 = "FStar.HyperStack.ST.m_rref"))
            ||
            (let uu____6434 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6434 = "FStar.HyperStack.ST.s_mref")
          -> let uu____6438 = translate_type env arg  in TBuf uu____6438
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::uu____6440::[],p) when
          ((((((((((let uu____6446 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6446 = "FStar.Monotonic.HyperStack.mreference") ||
                     (let uu____6451 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6451 = "FStar.Monotonic.HyperStack.mstackref"))
                    ||
                    (let uu____6456 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6456 = "FStar.Monotonic.HyperStack.mref"))
                   ||
                   (let uu____6461 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6461 = "FStar.Monotonic.HyperStack.mmmstackref"))
                  ||
                  (let uu____6466 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6466 = "FStar.Monotonic.HyperStack.mmmref"))
                 ||
                 (let uu____6471 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6471 = "FStar.Monotonic.Heap.mref"))
                ||
                (let uu____6476 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6476 = "FStar.HyperStack.ST.mreference"))
               ||
               (let uu____6481 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6481 = "FStar.HyperStack.ST.mstackref"))
              ||
              (let uu____6486 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6486 = "FStar.HyperStack.ST.mref"))
             ||
             (let uu____6491 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6491 = "FStar.HyperStack.ST.mmmstackref"))
            ||
            (let uu____6496 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6496 = "FStar.HyperStack.ST.mmmref")
          -> let uu____6500 = translate_type env arg  in TBuf uu____6500
      | FStar_Extraction_ML_Syntax.MLTY_Named
          (arg::uu____6502::uu____6503::[],p) when
          let uu____6507 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6507 = "LowStar.Monotonic.Buffer.mbuffer" ->
          let uu____6511 = translate_type env arg  in TBuf uu____6511
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          let uu____6516 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6516 = "LowStar.ConstBuffer.const_buffer" ->
          let uu____6520 = translate_type env arg  in TConstBuf uu____6520
      | FStar_Extraction_ML_Syntax.MLTY_Named (arg::[],p) when
          (((((((((((((let uu____6527 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6527 = "FStar.Buffer.buffer") ||
                        (let uu____6532 =
                           FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                         uu____6532 = "LowStar.Buffer.buffer"))
                       ||
                       (let uu____6537 =
                          FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                        uu____6537 = "LowStar.ImmutableBuffer.ibuffer"))
                      ||
                      (let uu____6542 =
                         FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                       uu____6542 = "LowStar.UninitializedBuffer.ubuffer"))
                     ||
                     (let uu____6547 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                      uu____6547 = "FStar.HyperStack.reference"))
                    ||
                    (let uu____6552 =
                       FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                     uu____6552 = "FStar.HyperStack.stackref"))
                   ||
                   (let uu____6557 =
                      FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                    uu____6557 = "FStar.HyperStack.ref"))
                  ||
                  (let uu____6562 =
                     FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                   uu____6562 = "FStar.HyperStack.mmstackref"))
                 ||
                 (let uu____6567 =
                    FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                  uu____6567 = "FStar.HyperStack.mmref"))
                ||
                (let uu____6572 =
                   FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                 uu____6572 = "FStar.HyperStack.ST.reference"))
               ||
               (let uu____6577 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____6577 = "FStar.HyperStack.ST.stackref"))
              ||
              (let uu____6582 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____6582 = "FStar.HyperStack.ST.ref"))
             ||
             (let uu____6587 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6587 = "FStar.HyperStack.ST.mmstackref"))
            ||
            (let uu____6592 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6592 = "FStar.HyperStack.ST.mmref")
          -> let uu____6596 = translate_type env arg  in TBuf uu____6596
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6597::arg::[],p) when
          (let uu____6604 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6604 = "FStar.HyperStack.s_ref") ||
            (let uu____6609 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6609 = "FStar.HyperStack.ST.s_ref")
          -> let uu____6613 = translate_type env arg  in TBuf uu____6613
      | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6614::[],p) when
          let uu____6618 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6618 = "FStar.Ghost.erased" -> TAny
      | FStar_Extraction_ML_Syntax.MLTY_Named ([],(path,type_name)) ->
          TQualified (path, type_name)
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,(ns,t1)) when
          ((ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"; "Native"])) &&
            (FStar_Util.starts_with t1 "tuple")
          ->
          let uu____6670 = FStar_List.map (translate_type env) args  in
          TTuple uu____6670
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,lid) ->
          if (FStar_List.length args) > Prims.int_zero
          then
            let uu____6681 =
              let uu____6696 = FStar_List.map (translate_type env) args  in
              (lid, uu____6696)  in
            TApp uu____6681
          else TQualified lid
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____6714 = FStar_List.map (translate_type env) ts  in
          TTuple uu____6714

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
    fun uu____6732  ->
      match uu____6732 with
      | (name,typ) ->
          let uu____6742 = translate_type env typ  in
          { name; typ = uu____6742; mut = false }

and (translate_expr : env -> FStar_Extraction_ML_Syntax.mlexpr -> expr) =
  fun env  ->
    fun e  ->
      match e.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_Tuple [] -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
      | FStar_Extraction_ML_Syntax.MLE_Var name ->
          let uu____6749 = find env name  in EBound uu____6749
      | FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op) when
          (is_machine_int m) && (is_op op) ->
          let uu____6763 =
            let uu____6768 = FStar_Util.must (mk_op op)  in
            let uu____6769 = FStar_Util.must (mk_width m)  in
            (uu____6768, uu____6769)  in
          EOp uu____6763
      | FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op) when
          is_bool_op op ->
          let uu____6779 =
            let uu____6784 = FStar_Util.must (mk_bool_op op)  in
            (uu____6784, Bool)  in
          EOp uu____6779
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
            let uu____6807 = translate_type env typ  in
            { name; typ = uu____6807; mut = false }  in
          let body1 = translate_expr env body  in
          let env1 = extend env name  in
          let continuation1 = translate_expr env1 continuation  in
          ELet (binder, body1, continuation1)
      | FStar_Extraction_ML_Syntax.MLE_Match (expr,branches) ->
          let uu____6834 =
            let uu____6845 = translate_expr env expr  in
            let uu____6846 = translate_branches env branches  in
            (uu____6845, uu____6846)  in
          EMatch uu____6834
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6860;
                  FStar_Extraction_ML_Syntax.loc = uu____6861;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6863;
             FStar_Extraction_ML_Syntax.loc = uu____6864;_},arg::[])
          when
          let uu____6870 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6870 = "FStar.Dyn.undyn" ->
          let uu____6874 =
            let uu____6879 = translate_expr env arg  in
            let uu____6880 = translate_type env t  in
            (uu____6879, uu____6880)  in
          ECast uu____6874
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6882;
                  FStar_Extraction_ML_Syntax.loc = uu____6883;_},uu____6884);
             FStar_Extraction_ML_Syntax.mlty = uu____6885;
             FStar_Extraction_ML_Syntax.loc = uu____6886;_},uu____6887)
          when
          let uu____6896 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6896 = "Prims.admit" -> EAbort
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6901;
                  FStar_Extraction_ML_Syntax.loc = uu____6902;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____6904;
             FStar_Extraction_ML_Syntax.loc = uu____6905;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_String
                                                                s);
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____6907;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____6908;_}::[])
          when
          let uu____6914 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____6914 = "LowStar.Failure.failwith" ->
          let uu____6918 =
            let uu____6924 = translate_type env t  in (s, uu____6924)  in
          EAbortT uu____6918
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6927;
                  FStar_Extraction_ML_Syntax.loc = uu____6928;_},uu____6929);
             FStar_Extraction_ML_Syntax.mlty = uu____6930;
             FStar_Extraction_ML_Syntax.loc = uu____6931;_},arg::[])
          when
          ((let uu____6941 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____6941 = "FStar.HyperStack.All.failwith") ||
             (let uu____6946 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____6946 = "FStar.Error.unexpected"))
            ||
            (let uu____6951 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6951 = "FStar.Error.unreachable")
          ->
          (match arg with
           | {
               FStar_Extraction_ML_Syntax.expr =
                 FStar_Extraction_ML_Syntax.MLE_Const
                 (FStar_Extraction_ML_Syntax.MLC_String msg);
               FStar_Extraction_ML_Syntax.mlty = uu____6956;
               FStar_Extraction_ML_Syntax.loc = uu____6957;_} -> EAbortS msg
           | uu____6959 ->
               let print7 =
                 let uu____6961 =
                   let uu____6962 =
                     let uu____6963 =
                       FStar_Ident.lid_of_str
                         "FStar.HyperStack.IO.print_string"
                        in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____6963
                      in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____6962  in
                 FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top uu____6961
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
                  FStar_Extraction_ML_Syntax.mlty = uu____6970;
                  FStar_Extraction_ML_Syntax.loc = uu____6971;_},uu____6972);
             FStar_Extraction_ML_Syntax.mlty = uu____6973;
             FStar_Extraction_ML_Syntax.loc = uu____6974;_},e1::[])
          when
          (let uu____6984 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____6984 = "LowStar.ToFStarBuffer.new_to_old_st") ||
            (let uu____6989 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____6989 = "LowStar.ToFStarBuffer.old_to_new_st")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____6994;
                  FStar_Extraction_ML_Syntax.loc = uu____6995;_},uu____6996);
             FStar_Extraction_ML_Syntax.mlty = uu____6997;
             FStar_Extraction_ML_Syntax.loc = uu____6998;_},e1::e2::[])
          when
          ((((let uu____7009 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7009 = "FStar.Buffer.index") ||
               (let uu____7014 =
                  FStar_Extraction_ML_Syntax.string_of_mlpath p  in
                uu____7014 = "FStar.Buffer.op_Array_Access"))
              ||
              (let uu____7019 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7019 = "LowStar.Monotonic.Buffer.index"))
             ||
             (let uu____7024 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7024 = "LowStar.UninitializedBuffer.uindex"))
            ||
            (let uu____7029 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7029 = "LowStar.ConstBuffer.index")
          ->
          let uu____7033 =
            let uu____7038 = translate_expr env e1  in
            let uu____7039 = translate_expr env e2  in
            (uu____7038, uu____7039)  in
          EBufRead uu____7033
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7041;
                  FStar_Extraction_ML_Syntax.loc = uu____7042;_},uu____7043);
             FStar_Extraction_ML_Syntax.mlty = uu____7044;
             FStar_Extraction_ML_Syntax.loc = uu____7045;_},e1::[])
          when
          let uu____7053 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7053 = "FStar.HyperStack.ST.op_Bang" ->
          let uu____7057 =
            let uu____7062 = translate_expr env e1  in
            (uu____7062, (EConstant (UInt32, "0")))  in
          EBufRead uu____7057
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7066;
                  FStar_Extraction_ML_Syntax.loc = uu____7067;_},uu____7068);
             FStar_Extraction_ML_Syntax.mlty = uu____7069;
             FStar_Extraction_ML_Syntax.loc = uu____7070;_},e1::e2::[])
          when
          ((let uu____7081 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7081 = "FStar.Buffer.create") ||
             (let uu____7086 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7086 = "LowStar.Monotonic.Buffer.malloca"))
            ||
            (let uu____7091 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7091 = "LowStar.ImmutableBuffer.ialloca")
          ->
          let uu____7095 =
            let uu____7102 = translate_expr env e1  in
            let uu____7103 = translate_expr env e2  in
            (Stack, uu____7102, uu____7103)  in
          EBufCreate uu____7095
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7105;
                  FStar_Extraction_ML_Syntax.loc = uu____7106;_},uu____7107);
             FStar_Extraction_ML_Syntax.mlty = uu____7108;
             FStar_Extraction_ML_Syntax.loc = uu____7109;_},elen::[])
          when
          let uu____7117 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7117 = "LowStar.UninitializedBuffer.ualloca" ->
          let uu____7121 =
            let uu____7126 = translate_expr env elen  in (Stack, uu____7126)
             in
          EBufCreateNoInit uu____7121
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7128;
                  FStar_Extraction_ML_Syntax.loc = uu____7129;_},uu____7130);
             FStar_Extraction_ML_Syntax.mlty = uu____7131;
             FStar_Extraction_ML_Syntax.loc = uu____7132;_},init1::[])
          when
          let uu____7140 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7140 = "FStar.HyperStack.ST.salloc" ->
          let uu____7144 =
            let uu____7151 = translate_expr env init1  in
            (Stack, uu____7151, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7144
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7155;
                  FStar_Extraction_ML_Syntax.loc = uu____7156;_},uu____7157);
             FStar_Extraction_ML_Syntax.mlty = uu____7158;
             FStar_Extraction_ML_Syntax.loc = uu____7159;_},e2::[])
          when
          ((let uu____7169 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7169 = "FStar.Buffer.createL") ||
             (let uu____7174 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7174 = "LowStar.Monotonic.Buffer.malloca_of_list"))
            ||
            (let uu____7179 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7179 = "LowStar.ImmutableBuffer.ialloca_of_list")
          ->
          let uu____7183 =
            let uu____7190 =
              let uu____7193 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7193  in
            (Stack, uu____7190)  in
          EBufCreateL uu____7183
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
             FStar_Extraction_ML_Syntax.loc = uu____7203;_},_erid::e2::[])
          when
          (let uu____7214 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7214 = "LowStar.Monotonic.Buffer.mgcmalloc_of_list") ||
            (let uu____7219 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7219 = "LowStar.ImmutableBuffer.igcmalloc_of_list")
          ->
          let uu____7223 =
            let uu____7230 =
              let uu____7233 = list_elements e2  in
              FStar_List.map (translate_expr env) uu____7233  in
            (Eternal, uu____7230)  in
          EBufCreateL uu____7223
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
             FStar_Extraction_ML_Syntax.loc = uu____7243;_},_rid::init1::[])
          when
          (let uu____7254 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7254 = "FStar.HyperStack.ST.ralloc") ||
            (let uu____7259 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7259 = "FStar.HyperStack.ST.ralloc_drgn")
          ->
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
          (let uu____7400 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7400 = "FStar.HyperStack.ST.ralloc_mm") ||
            (let uu____7405 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7405 = "FStar.HyperStack.ST.ralloc_drgn_mm")
          ->
          let uu____7409 =
            let uu____7416 = translate_expr env init1  in
            (ManuallyManaged, uu____7416, (EConstant (UInt32, "1")))  in
          EBufCreate uu____7409
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7420;
                  FStar_Extraction_ML_Syntax.loc = uu____7421;_},uu____7422);
             FStar_Extraction_ML_Syntax.mlty = uu____7423;
             FStar_Extraction_ML_Syntax.loc = uu____7424;_},_e0::e1::e2::[])
          when
          (((let uu____7436 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7436 = "FStar.Buffer.rcreate_mm") ||
              (let uu____7441 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7441 = "LowStar.Monotonic.Buffer.mmalloc"))
             ||
             (let uu____7446 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7446 = "LowStar.Monotonic.Buffer.mmalloc"))
            ||
            (let uu____7451 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7451 = "LowStar.ImmutableBuffer.imalloc")
          ->
          let uu____7455 =
            let uu____7462 = translate_expr env e1  in
            let uu____7463 = translate_expr env e2  in
            (ManuallyManaged, uu____7462, uu____7463)  in
          EBufCreate uu____7455
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7465;
                  FStar_Extraction_ML_Syntax.loc = uu____7466;_},uu____7467);
             FStar_Extraction_ML_Syntax.mlty = uu____7468;
             FStar_Extraction_ML_Syntax.loc = uu____7469;_},_erid::elen::[])
          when
          let uu____7478 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7478 = "LowStar.UninitializedBuffer.umalloc" ->
          let uu____7482 =
            let uu____7487 = translate_expr env elen  in
            (ManuallyManaged, uu____7487)  in
          EBufCreateNoInit uu____7482
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7489;
                  FStar_Extraction_ML_Syntax.loc = uu____7490;_},uu____7491);
             FStar_Extraction_ML_Syntax.mlty = uu____7492;
             FStar_Extraction_ML_Syntax.loc = uu____7493;_},e2::[])
          when
          let uu____7501 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7501 = "FStar.HyperStack.ST.rfree" ->
          let uu____7505 = translate_expr env e2  in EBufFree uu____7505
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7507;
                  FStar_Extraction_ML_Syntax.loc = uu____7508;_},uu____7509);
             FStar_Extraction_ML_Syntax.mlty = uu____7510;
             FStar_Extraction_ML_Syntax.loc = uu____7511;_},e2::[])
          when
          (let uu____7521 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7521 = "FStar.Buffer.rfree") ||
            (let uu____7526 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7526 = "LowStar.Monotonic.Buffer.free")
          -> let uu____7530 = translate_expr env e2  in EBufFree uu____7530
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7532;
                  FStar_Extraction_ML_Syntax.loc = uu____7533;_},uu____7534);
             FStar_Extraction_ML_Syntax.mlty = uu____7535;
             FStar_Extraction_ML_Syntax.loc = uu____7536;_},e1::e2::_e3::[])
          when
          let uu____7546 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7546 = "FStar.Buffer.sub" ->
          let uu____7550 =
            let uu____7555 = translate_expr env e1  in
            let uu____7556 = translate_expr env e2  in
            (uu____7555, uu____7556)  in
          EBufSub uu____7550
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7558;
                  FStar_Extraction_ML_Syntax.loc = uu____7559;_},uu____7560);
             FStar_Extraction_ML_Syntax.mlty = uu____7561;
             FStar_Extraction_ML_Syntax.loc = uu____7562;_},e1::e2::_e3::[])
          when
          (let uu____7574 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7574 = "LowStar.Monotonic.Buffer.msub") ||
            (let uu____7579 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7579 = "LowStar.ConstBuffer.sub")
          ->
          let uu____7583 =
            let uu____7588 = translate_expr env e1  in
            let uu____7589 = translate_expr env e2  in
            (uu____7588, uu____7589)  in
          EBufSub uu____7583
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7591;
                  FStar_Extraction_ML_Syntax.loc = uu____7592;_},uu____7593);
             FStar_Extraction_ML_Syntax.mlty = uu____7594;
             FStar_Extraction_ML_Syntax.loc = uu____7595;_},e1::e2::[])
          when
          let uu____7604 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7604 = "FStar.Buffer.join" -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7609;
                  FStar_Extraction_ML_Syntax.loc = uu____7610;_},uu____7611);
             FStar_Extraction_ML_Syntax.mlty = uu____7612;
             FStar_Extraction_ML_Syntax.loc = uu____7613;_},e1::e2::[])
          when
          let uu____7622 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7622 = "FStar.Buffer.offset" ->
          let uu____7626 =
            let uu____7631 = translate_expr env e1  in
            let uu____7632 = translate_expr env e2  in
            (uu____7631, uu____7632)  in
          EBufSub uu____7626
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7634;
                  FStar_Extraction_ML_Syntax.loc = uu____7635;_},uu____7636);
             FStar_Extraction_ML_Syntax.mlty = uu____7637;
             FStar_Extraction_ML_Syntax.loc = uu____7638;_},e1::e2::[])
          when
          let uu____7647 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7647 = "LowStar.Monotonic.Buffer.moffset" ->
          let uu____7651 =
            let uu____7656 = translate_expr env e1  in
            let uu____7657 = translate_expr env e2  in
            (uu____7656, uu____7657)  in
          EBufSub uu____7651
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7659;
                  FStar_Extraction_ML_Syntax.loc = uu____7660;_},uu____7661);
             FStar_Extraction_ML_Syntax.mlty = uu____7662;
             FStar_Extraction_ML_Syntax.loc = uu____7663;_},e1::e2::e3::[])
          when
          (((let uu____7675 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7675 = "FStar.Buffer.upd") ||
              (let uu____7680 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7680 = "FStar.Buffer.op_Array_Assignment"))
             ||
             (let uu____7685 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7685 = "LowStar.Monotonic.Buffer.upd'"))
            ||
            (let uu____7690 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7690 = "LowStar.UninitializedBuffer.uupd")
          ->
          let uu____7694 =
            let uu____7701 = translate_expr env e1  in
            let uu____7702 = translate_expr env e2  in
            let uu____7703 = translate_expr env e3  in
            (uu____7701, uu____7702, uu____7703)  in
          EBufWrite uu____7694
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7705;
                  FStar_Extraction_ML_Syntax.loc = uu____7706;_},uu____7707);
             FStar_Extraction_ML_Syntax.mlty = uu____7708;
             FStar_Extraction_ML_Syntax.loc = uu____7709;_},e1::e2::[])
          when
          let uu____7718 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7718 = "FStar.HyperStack.ST.op_Colon_Equals" ->
          let uu____7722 =
            let uu____7729 = translate_expr env e1  in
            let uu____7730 = translate_expr env e2  in
            (uu____7729, (EConstant (UInt32, "0")), uu____7730)  in
          EBufWrite uu____7722
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7734;
             FStar_Extraction_ML_Syntax.loc = uu____7735;_},uu____7736::[])
          when
          let uu____7739 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7739 = "FStar.HyperStack.ST.push_frame" -> EPushFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7744;
             FStar_Extraction_ML_Syntax.loc = uu____7745;_},uu____7746::[])
          when
          let uu____7749 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7749 = "FStar.HyperStack.ST.pop_frame" -> EPopFrame
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7754;
                  FStar_Extraction_ML_Syntax.loc = uu____7755;_},uu____7756);
             FStar_Extraction_ML_Syntax.mlty = uu____7757;
             FStar_Extraction_ML_Syntax.loc = uu____7758;_},e1::e2::e3::e4::e5::[])
          when
          ((let uu____7772 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7772 = "FStar.Buffer.blit") ||
             (let uu____7777 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7777 = "LowStar.Monotonic.Buffer.blit"))
            ||
            (let uu____7782 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7782 = "LowStar.UninitializedBuffer.ublit")
          ->
          let uu____7786 =
            let uu____7797 = translate_expr env e1  in
            let uu____7798 = translate_expr env e2  in
            let uu____7799 = translate_expr env e3  in
            let uu____7800 = translate_expr env e4  in
            let uu____7801 = translate_expr env e5  in
            (uu____7797, uu____7798, uu____7799, uu____7800, uu____7801)  in
          EBufBlit uu____7786
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7803;
                  FStar_Extraction_ML_Syntax.loc = uu____7804;_},uu____7805);
             FStar_Extraction_ML_Syntax.mlty = uu____7806;
             FStar_Extraction_ML_Syntax.loc = uu____7807;_},e1::e2::e3::[])
          when
          let s = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill")
          ->
          let uu____7823 =
            let uu____7830 = translate_expr env e1  in
            let uu____7831 = translate_expr env e2  in
            let uu____7832 = translate_expr env e3  in
            (uu____7830, uu____7831, uu____7832)  in
          EBufFill uu____7823
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7834;
             FStar_Extraction_ML_Syntax.loc = uu____7835;_},uu____7836::[])
          when
          let uu____7839 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7839 = "FStar.HyperStack.ST.get" -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7844;
                  FStar_Extraction_ML_Syntax.loc = uu____7845;_},uu____7846);
             FStar_Extraction_ML_Syntax.mlty = uu____7847;
             FStar_Extraction_ML_Syntax.loc = uu____7848;_},_rid::[])
          when
          (let uu____7858 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7858 = "FStar.HyperStack.ST.free_drgn") ||
            (let uu____7863 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7863 = "FStar.HyperStack.ST.new_drgn")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7868;
                  FStar_Extraction_ML_Syntax.loc = uu____7869;_},uu____7870);
             FStar_Extraction_ML_Syntax.mlty = uu____7871;
             FStar_Extraction_ML_Syntax.loc = uu____7872;_},_ebuf::_eseq::[])
          when
          (((let uu____7883 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7883 = "LowStar.Monotonic.Buffer.witness_p") ||
              (let uu____7888 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                  in
               uu____7888 = "LowStar.Monotonic.Buffer.recall_p"))
             ||
             (let uu____7893 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7893 = "LowStar.ImmutableBuffer.witness_contents"))
            ||
            (let uu____7898 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7898 = "LowStar.ImmutableBuffer.recall_contents")
          -> EUnit
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7903;
                  FStar_Extraction_ML_Syntax.loc = uu____7904;_},uu____7905);
             FStar_Extraction_ML_Syntax.mlty = uu____7906;
             FStar_Extraction_ML_Syntax.loc = uu____7907;_},e1::[])
          when
          (let uu____7917 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
           uu____7917 = "LowStar.ConstBuffer.of_buffer") ||
            (let uu____7922 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7922 = "LowStar.ConstBuffer.of_ibuffer")
          -> translate_expr env e1
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7927;
                  FStar_Extraction_ML_Syntax.loc = uu____7928;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____7930;
             FStar_Extraction_ML_Syntax.loc = uu____7931;_},_eqal::e1::[])
          when
          let uu____7938 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7938 = "LowStar.ConstBuffer.of_qbuf" ->
          let uu____7942 =
            let uu____7947 = translate_expr env e1  in
            let uu____7948 =
              let uu____7949 = translate_type env t  in TConstBuf uu____7949
               in
            (uu____7947, uu____7948)  in
          ECast uu____7942
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____7951;
                  FStar_Extraction_ML_Syntax.loc = uu____7952;_},t::[]);
             FStar_Extraction_ML_Syntax.mlty = uu____7954;
             FStar_Extraction_ML_Syntax.loc = uu____7955;_},e1::[])
          when
          ((let uu____7963 = FStar_Extraction_ML_Syntax.string_of_mlpath p
               in
            uu____7963 = "LowStar.ConstBuffer.cast") ||
             (let uu____7968 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                 in
              uu____7968 = "LowStar.ConstBuffer.to_buffer"))
            ||
            (let uu____7973 = FStar_Extraction_ML_Syntax.string_of_mlpath p
                in
             uu____7973 = "LowStar.ConstBuffer.to_ibuffer")
          ->
          let uu____7977 =
            let uu____7982 = translate_expr env e1  in
            let uu____7983 =
              let uu____7984 = translate_type env t  in TBuf uu____7984  in
            (uu____7982, uu____7983)  in
          ECast uu____7977
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____7986;
             FStar_Extraction_ML_Syntax.loc = uu____7987;_},e1::[])
          when
          let uu____7991 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____7991 = "Obj.repr" ->
          let uu____7995 =
            let uu____8000 = translate_expr env e1  in (uu____8000, TAny)  in
          ECast uu____7995
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____8003;
             FStar_Extraction_ML_Syntax.loc = uu____8004;_},args)
          when (is_machine_int m) && (is_op op) ->
          let uu____8020 = FStar_Util.must (mk_width m)  in
          let uu____8021 = FStar_Util.must (mk_op op)  in
          mk_op_app env uu____8020 uu____8021 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name ("Prims"::[],op);
             FStar_Extraction_ML_Syntax.mlty = uu____8023;
             FStar_Extraction_ML_Syntax.loc = uu____8024;_},args)
          when is_bool_op op ->
          let uu____8038 = FStar_Util.must (mk_bool_op op)  in
          mk_op_app env Bool uu____8038 args
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"int_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____8040;
             FStar_Extraction_ML_Syntax.loc = uu____8041;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8043;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8044;_}::[])
          when is_machine_int m ->
          let uu____8069 =
            let uu____8075 = FStar_Util.must (mk_width m)  in (uu____8075, c)
             in
          EConstant uu____8069
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::m::[],"uint_to_t");
             FStar_Extraction_ML_Syntax.mlty = uu____8078;
             FStar_Extraction_ML_Syntax.loc = uu____8079;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                =
                                                                FStar_Extraction_ML_Syntax.MLE_Const
                                                                (FStar_Extraction_ML_Syntax.MLC_Int
                                                                (c,FStar_Pervasives_Native.None
                                                                 ));
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8081;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8082;_}::[])
          when is_machine_int m ->
          let uu____8107 =
            let uu____8113 = FStar_Util.must (mk_width m)  in (uu____8113, c)
             in
          EConstant uu____8107
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::[],"string_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8115;
             FStar_Extraction_ML_Syntax.loc = uu____8116;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8118;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8119;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8132 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"Compat"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8134;
             FStar_Extraction_ML_Syntax.loc = uu____8135;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8137;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8138;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8155 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("C"::"String"::[],"of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8157;
             FStar_Extraction_ML_Syntax.loc = uu____8158;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8160;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8161;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) -> EString s
           | uu____8176 ->
               failwith
                 "Cannot extract string_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_TApp
               ({
                  FStar_Extraction_ML_Syntax.expr =
                    FStar_Extraction_ML_Syntax.MLE_Name p;
                  FStar_Extraction_ML_Syntax.mlty = uu____8179;
                  FStar_Extraction_ML_Syntax.loc = uu____8180;_},uu____8181);
             FStar_Extraction_ML_Syntax.mlty = uu____8182;
             FStar_Extraction_ML_Syntax.loc = uu____8183;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = ebefore;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8185;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8186;_}::e1::
           { FStar_Extraction_ML_Syntax.expr = eafter;
             FStar_Extraction_ML_Syntax.mlty = uu____8189;
             FStar_Extraction_ML_Syntax.loc = uu____8190;_}::[])
          when
          let uu____8197 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8197 = "LowStar.Comment.comment_gen" ->
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
                (let uu____8217 =
                   let uu____8226 = translate_expr env e1  in
                   (sbefore, uu____8226, safter)  in
                 EComment uu____8217))
           | uu____8229 ->
               failwith "Cannot extract comment applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name p;
             FStar_Extraction_ML_Syntax.mlty = uu____8236;
             FStar_Extraction_ML_Syntax.loc = uu____8237;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8239;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8240;_}::[])
          when
          let uu____8243 = FStar_Extraction_ML_Syntax.string_of_mlpath p  in
          uu____8243 = "LowStar.Comment.comment" ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               (if FStar_Util.contains s "*/"
                then
                  failwith
                    "Standalone Comment contains end-of-comment marker"
                else ();
                EStandaloneComment s)
           | uu____8255 ->
               failwith "Cannot extract comment applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("LowStar"::"Literal"::[],"buffer_of_literal");
             FStar_Extraction_ML_Syntax.mlty = uu____8257;
             FStar_Extraction_ML_Syntax.loc = uu____8258;_},{
                                                              FStar_Extraction_ML_Syntax.expr
                                                                = e1;
                                                              FStar_Extraction_ML_Syntax.mlty
                                                                = uu____8260;
                                                              FStar_Extraction_ML_Syntax.loc
                                                                = uu____8261;_}::[])
          ->
          (match e1 with
           | FStar_Extraction_ML_Syntax.MLE_Const
               (FStar_Extraction_ML_Syntax.MLC_String s) ->
               ECast ((EString s), (TBuf (TInt UInt8)))
           | uu____8276 ->
               failwith
                 "Cannot extract buffer_of_literal applied to a non-literal")
      | FStar_Extraction_ML_Syntax.MLE_App
          ({
             FStar_Extraction_ML_Syntax.expr =
               FStar_Extraction_ML_Syntax.MLE_Name
               ("FStar"::"Int"::"Cast"::[],c);
             FStar_Extraction_ML_Syntax.mlty = uu____8279;
             FStar_Extraction_ML_Syntax.loc = uu____8280;_},arg::[])
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
            let uu____8308 =
              let uu____8313 = translate_expr env arg  in
              (uu____8313, (TInt UInt64))  in
            ECast uu____8308
          else
            if (FStar_Util.ends_with c "uint32") && is_known_type
            then
              (let uu____8318 =
                 let uu____8323 = translate_expr env arg  in
                 (uu____8323, (TInt UInt32))  in
               ECast uu____8318)
            else
              if (FStar_Util.ends_with c "uint16") && is_known_type
              then
                (let uu____8328 =
                   let uu____8333 = translate_expr env arg  in
                   (uu____8333, (TInt UInt16))  in
                 ECast uu____8328)
              else
                if (FStar_Util.ends_with c "uint8") && is_known_type
                then
                  (let uu____8338 =
                     let uu____8343 = translate_expr env arg  in
                     (uu____8343, (TInt UInt8))  in
                   ECast uu____8338)
                else
                  if (FStar_Util.ends_with c "int64") && is_known_type
                  then
                    (let uu____8348 =
                       let uu____8353 = translate_expr env arg  in
                       (uu____8353, (TInt Int64))  in
                     ECast uu____8348)
                  else
                    if (FStar_Util.ends_with c "int32") && is_known_type
                    then
                      (let uu____8358 =
                         let uu____8363 = translate_expr env arg  in
                         (uu____8363, (TInt Int32))  in
                       ECast uu____8358)
                    else
                      if (FStar_Util.ends_with c "int16") && is_known_type
                      then
                        (let uu____8368 =
                           let uu____8373 = translate_expr env arg  in
                           (uu____8373, (TInt Int16))  in
                         ECast uu____8368)
                      else
                        if (FStar_Util.ends_with c "int8") && is_known_type
                        then
                          (let uu____8378 =
                             let uu____8383 = translate_expr env arg  in
                             (uu____8383, (TInt Int8))  in
                           ECast uu____8378)
                        else
                          (let uu____8386 =
                             let uu____8393 =
                               let uu____8396 = translate_expr env arg  in
                               [uu____8396]  in
                             ((EQualified (["FStar"; "Int"; "Cast"], c)),
                               uu____8393)
                              in
                           EApp uu____8386)
      | FStar_Extraction_ML_Syntax.MLE_App (head1,args) ->
          let uu____8416 =
            let uu____8423 = translate_expr env head1  in
            let uu____8424 = FStar_List.map (translate_expr env) args  in
            (uu____8423, uu____8424)  in
          EApp uu____8416
      | FStar_Extraction_ML_Syntax.MLE_TApp (head1,ty_args) ->
          let uu____8435 =
            let uu____8442 = translate_expr env head1  in
            let uu____8443 = FStar_List.map (translate_type env) ty_args  in
            (uu____8442, uu____8443)  in
          ETypApp uu____8435
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1,t_from,t_to) ->
          let uu____8451 =
            let uu____8456 = translate_expr env e1  in
            let uu____8457 = translate_type env t_to  in
            (uu____8456, uu____8457)  in
          ECast uu____8451
      | FStar_Extraction_ML_Syntax.MLE_Record (uu____8458,fields) ->
          let uu____8480 =
            let uu____8492 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8493 =
              FStar_List.map
                (fun uu____8515  ->
                   match uu____8515 with
                   | (field,expr) ->
                       let uu____8530 = translate_expr env expr  in
                       (field, uu____8530)) fields
               in
            (uu____8492, uu____8493)  in
          EFlat uu____8480
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1,path) ->
          let uu____8541 =
            let uu____8549 =
              assert_lid env e1.FStar_Extraction_ML_Syntax.mlty  in
            let uu____8550 = translate_expr env e1  in
            (uu____8549, uu____8550, (FStar_Pervasives_Native.snd path))  in
          EField uu____8541
      | FStar_Extraction_ML_Syntax.MLE_Let uu____8556 ->
          let uu____8567 =
            let uu____8569 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") e  in
            FStar_Util.format1 "todo: translate_expr [MLE_Let] (expr is: %s)"
              uu____8569
             in
          failwith uu____8567
      | FStar_Extraction_ML_Syntax.MLE_App (head1,uu____8579) ->
          let uu____8584 =
            let uu____8586 =
              FStar_Extraction_ML_Code.string_of_mlexpr ([], "") head1  in
            FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)"
              uu____8586
             in
          failwith uu____8584
      | FStar_Extraction_ML_Syntax.MLE_Seq seqs ->
          let uu____8598 = FStar_List.map (translate_expr env) seqs  in
          ESequence uu____8598
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____8604 = FStar_List.map (translate_expr env) es  in
          ETuple uu____8604
      | FStar_Extraction_ML_Syntax.MLE_CTor ((uu____8607,cons1),es) ->
          let uu____8622 =
            let uu____8632 = assert_lid env e.FStar_Extraction_ML_Syntax.mlty
               in
            let uu____8633 = FStar_List.map (translate_expr env) es  in
            (uu____8632, cons1, uu____8633)  in
          ECons uu____8622
      | FStar_Extraction_ML_Syntax.MLE_Fun (args,body) ->
          let binders = translate_binders env args  in
          let env1 = add_binders env args  in
          let uu____8659 =
            let uu____8668 = translate_expr env1 body  in
            let uu____8669 =
              translate_type env1 body.FStar_Extraction_ML_Syntax.mlty  in
            (binders, uu____8668, uu____8669)  in
          EFun uu____8659
      | FStar_Extraction_ML_Syntax.MLE_If (e1,e2,e3) ->
          let uu____8679 =
            let uu____8686 = translate_expr env e1  in
            let uu____8687 = translate_expr env e2  in
            let uu____8688 =
              match e3 with
              | FStar_Pervasives_Native.None  -> EUnit
              | FStar_Pervasives_Native.Some e31 -> translate_expr env e31
               in
            (uu____8686, uu____8687, uu____8688)  in
          EIfThenElse uu____8679
      | FStar_Extraction_ML_Syntax.MLE_Raise uu____8690 ->
          failwith "todo: translate_expr [MLE_Raise]"
      | FStar_Extraction_ML_Syntax.MLE_Try uu____8698 ->
          failwith "todo: translate_expr [MLE_Try]"
      | FStar_Extraction_ML_Syntax.MLE_Coerce uu____8714 ->
          failwith "todo: translate_expr [MLE_Coerce]"

and (assert_lid : env -> FStar_Extraction_ML_Syntax.mlty -> typ) =
  fun env  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Named (ts,lid) ->
          if (FStar_List.length ts) > Prims.int_zero
          then
            let uu____8732 =
              let uu____8747 = FStar_List.map (translate_type env) ts  in
              (lid, uu____8747)  in
            TApp uu____8732
          else TQualified lid
      | uu____8762 ->
          let uu____8763 =
            let uu____8765 =
              FStar_Extraction_ML_Code.string_of_mlty ([], "") t  in
            FStar_Util.format1
              "invalid argument: expected MLTY_Named, got %s" uu____8765
             in
          failwith uu____8763

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
    fun uu____8799  ->
      match uu____8799 with
      | (pat,guard,expr) ->
          if guard = FStar_Pervasives_Native.None
          then
            let uu____8826 = translate_pat env pat  in
            (match uu____8826 with
             | (env1,pat1) ->
                 let uu____8837 = translate_expr env1 expr  in
                 (pat1, uu____8837))
          else failwith "todo: translate_branch"

and (translate_width :
  (FStar_Const.signedness * FStar_Const.width) FStar_Pervasives_Native.option
    -> width)
  =
  fun uu___7_8845  ->
    match uu___7_8845 with
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
          let uu____8912 =
            let uu____8913 =
              let uu____8919 = translate_width sw  in (uu____8919, s)  in
            PConstant uu____8913  in
          (env, uu____8912)
      | FStar_Extraction_ML_Syntax.MLP_Var name ->
          let env1 = extend env name  in
          (env1, (PVar { name; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_Wild  ->
          let env1 = extend env "_"  in
          (env1, (PVar { name = "_"; typ = TAny; mut = false }))
      | FStar_Extraction_ML_Syntax.MLP_CTor ((uu____8929,cons1),ps) ->
          let uu____8944 =
            FStar_List.fold_left
              (fun uu____8964  ->
                 fun p1  ->
                   match uu____8964 with
                   | (env1,acc) ->
                       let uu____8984 = translate_pat env1 p1  in
                       (match uu____8984 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____8944 with
           | (env1,ps1) -> (env1, (PCons (cons1, (FStar_List.rev ps1)))))
      | FStar_Extraction_ML_Syntax.MLP_Record (uu____9014,ps) ->
          let uu____9036 =
            FStar_List.fold_left
              (fun uu____9073  ->
                 fun uu____9074  ->
                   match (uu____9073, uu____9074) with
                   | ((env1,acc),(field,p1)) ->
                       let uu____9154 = translate_pat env1 p1  in
                       (match uu____9154 with
                        | (env2,p2) -> (env2, ((field, p2) :: acc))))
              (env, []) ps
             in
          (match uu____9036 with
           | (env1,ps1) -> (env1, (PRecord (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
          let uu____9225 =
            FStar_List.fold_left
              (fun uu____9245  ->
                 fun p1  ->
                   match uu____9245 with
                   | (env1,acc) ->
                       let uu____9265 = translate_pat env1 p1  in
                       (match uu____9265 with
                        | (env2,p2) -> (env2, (p2 :: acc)))) (env, []) ps
             in
          (match uu____9225 with
           | (env1,ps1) -> (env1, (PTuple (FStar_List.rev ps1))))
      | FStar_Extraction_ML_Syntax.MLP_Const uu____9292 ->
          failwith "todo: translate_pat [MLP_Const]"
      | FStar_Extraction_ML_Syntax.MLP_Branch uu____9298 ->
          failwith "todo: translate_pat [MLP_Branch]"

and (translate_constant : FStar_Extraction_ML_Syntax.mlconstant -> expr) =
  fun c  ->
    match c with
    | FStar_Extraction_ML_Syntax.MLC_Unit  -> EUnit
    | FStar_Extraction_ML_Syntax.MLC_Bool b -> EBool b
    | FStar_Extraction_ML_Syntax.MLC_String s ->
        ((let uu____9312 =
            let uu____9314 = FStar_String.list_of_string s  in
            FStar_All.pipe_right uu____9314
              (FStar_Util.for_some
                 (fun c1  -> c1 = (FStar_Char.char_of_int Prims.int_zero)))
             in
          if uu____9312
          then
            let uu____9329 =
              FStar_Util.format1
                "Refusing to translate a string literal that contains a null character: %s"
                s
               in
            failwith uu____9329
          else ());
         EString s)
    | FStar_Extraction_ML_Syntax.MLC_Char c1 ->
        let i = FStar_Util.int_of_char c1  in
        let s = FStar_Util.string_of_int i  in
        let c2 = EConstant (UInt32, s)  in
        let char_of_int1 = EQualified (["FStar"; "Char"], "char_of_int")  in
        EApp (char_of_int1, [c2])
    | FStar_Extraction_ML_Syntax.MLC_Int
        (s,FStar_Pervasives_Native.Some uu____9356) ->
        failwith
          "impossible: machine integer not desugared to a function call"
    | FStar_Extraction_ML_Syntax.MLC_Float uu____9374 ->
        failwith "todo: translate_expr [MLC_Float]"
    | FStar_Extraction_ML_Syntax.MLC_Bytes uu____9376 ->
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
          let uu____9401 =
            let uu____9408 = FStar_List.map (translate_expr env) args  in
            ((EOp (op, w)), uu____9408)  in
          EApp uu____9401

let (translate : FStar_Extraction_ML_Syntax.mllib -> file Prims.list) =
  fun uu____9420  ->
    match uu____9420 with
    | FStar_Extraction_ML_Syntax.MLLib modules ->
        FStar_List.filter_map
          (fun m  ->
             let m_name =
               let uu____9469 = m  in
               match uu____9469 with
               | (path,uu____9484,uu____9485) ->
                   FStar_Extraction_ML_Syntax.string_of_mlpath path
                in
             try
               (fun uu___1670_9503  ->
                  match () with
                  | () ->
                      ((let uu____9507 =
                          let uu____9509 = FStar_Options.silent ()  in
                          Prims.op_Negation uu____9509  in
                        if uu____9507
                        then
                          FStar_Util.print1
                            "Attempting to translate module %s\n" m_name
                        else ());
                       (let uu____9515 = translate_module m  in
                        FStar_Pervasives_Native.Some uu____9515))) ()
             with
             | uu___1669_9518 ->
                 ((let uu____9522 = FStar_Util.print_exn uu___1669_9518  in
                   FStar_Util.print2
                     "Unable to translate module: %s because:\n  %s\n" m_name
                     uu____9522);
                  FStar_Pervasives_Native.None)) modules
  